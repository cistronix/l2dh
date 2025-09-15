/* l2dhd.c — Layer-2 DH responder (v2+id): X448 KEX + Ed25519 auth
 * - One-shot by default: exits after successful FINISH (prints key)
 *   Use --loop to keep serving multiple sessions.
 * - --exec "cmd": after success, runs cmd with env vars (no stdin)
 * - Non-VLAN EtherType cBPF filter; promisc option
 * - Restart-safe: won’t get stuck resending FINISH(R)
 * - Optional anti-replay LRU for recent HELLO tuples
 * - -q: quiet, suppress all success printing (only hook runs)
 *
 * Build:
 *   cc -O2 -Wall -Wextra -DOPENSSL_API_COMPAT=0x10100000L -o l2dhd l2dhd.c -lcrypto
 */
#define _GNU_SOURCE
#include <arpa/inet.h>
#include <errno.h>
#include <signal.h>
#include <linux/if_packet.h>
#include <linux/if_ether.h>
#include <linux/filter.h>
#include <net/if.h>
#include <poll.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <time.h>
#include <unistd.h>
#include <ctype.h>
#include <sys/types.h>
#include <sys/wait.h>

#include <openssl/evp.h>
#include <openssl/hmac.h>
#include <openssl/sha.h>
#include <openssl/rand.h>
#include <openssl/crypto.h>

#define DEFAULT_ETHERTYPE 0x88B5
#define MIN_ETH_PAYLOAD   46
#define MAX_FRAME_SIZE    2048
#define HDR_NO_VLAN       (ETH_ALEN*2 + 2)

static const uint8_t MAGIC[4] = { 'L','2','D','H' };
#define PROTO_VER 2
#define TYPE_HELLO  1
#define TYPE_FINISH 2

#define X448_PUBLEN     56
#define ED25519_PUBLEN  32
#define ED25519_SIGLEN  64
#define NONCE_LEN       32
#define HMAC_LEN        64

static const unsigned char TAG_FIN_I[4] = { 'F','I','N','I' };
static const unsigned char TAG_FIN_R[4] = { 'F','I','N','R' };

#define FLAG_TIME_REQUEST 0x01

#if defined(__has_include)
# if __has_include(<endian.h>)
#  include <endian.h>
# endif
#endif
#ifndef htobe64
static inline uint64_t htobe64_u64(uint64_t x){uint32_t hi=(uint32_t)(x>>32),lo=(uint32_t)x;hi=htonl(hi);lo=htonl(lo);return ((uint64_t)lo<<32)|hi;}
#else
# define htobe64_u64(x) htobe64((x))
#endif

// ---------- time/log ----------
static uint64_t now_ms(){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return (uint64_t)t.tv_sec*1000ULL + (uint64_t)(t.tv_nsec/1000000ULL); }
static int g_verbose=0;
static const char* ts(){ static char b[32]; struct timespec tv; clock_gettime(CLOCK_REALTIME,&tv); struct tm tm; localtime_r(&tv.tv_sec,&tm); snprintf(b,sizeof(b),"%02d:%02d:%02d.%03ld",tm.tm_hour,tm.tm_min,tm.tm_sec,tv.tv_nsec/1000000); return b; }
#define DBG1(f,...) do{ if(g_verbose>=1) fprintf(stderr,"[%s] " f "\n",ts(),##__VA_ARGS__);}while(0)
#define DBG2(f,...) do{ if(g_verbose>=2) fprintf(stderr,"[%s] " f "\n",ts(),##__VA_ARGS__);}while(0)
static void hexdump2(const char *lab,const unsigned char *p,size_t n){ if(g_verbose<2) return; fprintf(stderr,"[%s] %s (%zu):",ts(),lab,n); for(size_t i=0;i<n;i++){ if(i%16==0) fprintf(stderr,"\n  "); fprintf(stderr,"%02x ",p[i]); } fprintf(stderr,"\n"); }

// ---------- replay LRU (optional) ----------
#ifndef L2DH_LRU_SIZE
#define L2DH_LRU_SIZE 16
#endif
typedef struct {
  unsigned char edpub[ED25519_PUBLEN];
  unsigned char xpub[X448_PUBLEN];
  unsigned char nonce[NONCE_LEN];
  uint64_t      seen_ms;
  int           used;
} hello_tuple_t;
typedef struct {
  hello_tuple_t ent[L2DH_LRU_SIZE];
  int           next;
  uint32_t      window_ms; // 0 disables
} lru_t;
static void lru_init(lru_t *lru, uint32_t window_ms){ memset(lru,0,sizeof(*lru)); lru->window_ms=window_ms; }
static int lru_contains_fresh(lru_t *lru,const unsigned char edpub[32],const unsigned char xpub[56],const unsigned char nonce[32]){
  if(lru->window_ms==0) return 0;
  uint64_t now = now_ms();
  for(int i=0;i<L2DH_LRU_SIZE;i++){
    if(!lru->ent[i].used) continue;
    if((now - lru->ent[i].seen_ms) > lru->window_ms){ lru->ent[i].used=0; continue; }
    if(memcmp(lru->ent[i].edpub, edpub, 32)==0 &&
       memcmp(lru->ent[i].xpub,  xpub,  56)==0 &&
       memcmp(lru->ent[i].nonce, nonce, 32)==0) return 1;
  }
  return 0;
}
static void lru_remember(lru_t *lru,const unsigned char edpub[32],const unsigned char xpub[56],const unsigned char nonce[32]){
  if(lru->window_ms==0) return;
  int idx = lru->next++ % L2DH_LRU_SIZE;
  memcpy(lru->ent[idx].edpub, edpub, 32);
  memcpy(lru->ent[idx].xpub,  xpub,  56);
  memcpy(lru->ent[idx].nonce, nonce, 32);
  lru->ent[idx].seen_ms = now_ms();
  lru->ent[idx].used    = 1;
}

// ---------- config ----------
typedef struct {
  const char *ifname;
  unsigned char smac[ETH_ALEN]; int have_smac;
  unsigned ethertype;
  int timeout_sec;   // <0 infinite (IDLE wait)
  int retry_ms;
  int promisc;
  int no_bpf;
  int raw_only;
  int sep_group;
  int quiet;                // -q: suppress success printing (hook still runs)
  // pinned keys
  unsigned char my_ed25519_priv[32]; int have_my_priv;
  unsigned char peer_ed25519_pub[32]; int have_peer_pub;
  // behavior
  int loop_mode;             // default 0 (exit after success); --loop sets 1
  int max_resends;           // -1 unlimited; default 10
  uint32_t replay_window_ms; // default 30s; 0 disable
  // exec hook
  const char *exec_cmd;      // --exec "cmd"; NULL = off
} cfg_t;

#pragma pack(push,1)
typedef struct {
  uint8_t  magic[4];
  uint8_t  ver;
  uint8_t  type;
  uint8_t  flags;      // FLAG_TIME_REQUEST
  uint8_t  id_len;     // 0..32
  uint8_t  x448_pub[X448_PUBLEN];
  uint8_t  nonce[NONCE_LEN];
  uint8_t  ed25519_pub[ED25519_PUBLEN];
  uint16_t keylen_be;
  uint8_t  id[32];     // as sent; not NUL-terminated
  uint8_t  sig[ED25519_SIGLEN];
} hello_v2_t;

typedef struct {
  uint8_t  magic[4];
  uint8_t  ver;
  uint8_t  type;
  uint8_t  flags;
  uint8_t  reserved;
  uint64_t time_sec_be;
  uint32_t time_nsec_be;
  uint8_t  mac[HMAC_LEN];
} finish_v2_t;
#pragma pack(pop)

// ---------- crypto helpers ----------
static void sha512(const void *d,size_t n,unsigned char out[64]){ SHA512_CTX c; SHA512_Init(&c); SHA512_Update(&c,d,n); SHA512_Final(out,&c); }
static int hkdf_sha512(const unsigned char *ikm,size_t ikm_len,const unsigned char *salt,size_t salt_len,const unsigned char *info,size_t info_len,unsigned char *okm,size_t okm_len){
  unsigned char zeros[SHA512_DIGEST_LENGTH]={0}; if(!salt||!salt_len){ salt=zeros; salt_len=sizeof(zeros); }
  unsigned char prk[SHA512_DIGEST_LENGTH]; unsigned int prk_len;
  if(!HMAC(EVP_sha512(),salt,(int)salt_len,ikm,ikm_len,prk,&prk_len)) return 0;
  unsigned char t[SHA512_DIGEST_LENGTH]; size_t tlen=0,pos=0; unsigned char ctr=1;
  while(pos<okm_len){ HMAC_CTX *ctx=HMAC_CTX_new(); if(!ctx) return 0;
    if(HMAC_Init_ex(ctx,prk,(int)prk_len,EVP_sha512(),NULL)!=1){ HMAC_CTX_free(ctx); return 0; }
    if(tlen) HMAC_Update(ctx,t,tlen); if(info&&info_len) HMAC_Update(ctx,info,info_len); HMAC_Update(ctx,&ctr,1);
    unsigned int outlen=0; HMAC_Final(ctx,t,&outlen); HMAC_CTX_free(ctx);
    tlen=outlen; size_t c=(okm_len-pos<tlen)?(okm_len-pos):tlen; memcpy(okm+pos,t,c); pos+=c; ctr++; }
  OPENSSL_cleanse(prk,sizeof(prk)); OPENSSL_cleanse(t,sizeof(t)); return 1;
}
static int x448_keygen(EVP_PKEY **out_priv,unsigned char pub[X448_PUBLEN]){ int ok=0; EVP_PKEY_CTX *k=EVP_PKEY_CTX_new_id(EVP_PKEY_X448,NULL); if(!k) return 0; if(EVP_PKEY_keygen_init(k)!=1) goto done; if(EVP_PKEY_keygen(k,out_priv)!=1) goto done; size_t L=X448_PUBLEN; if(EVP_PKEY_get_raw_public_key(*out_priv,pub,&L)!=1||L!=X448_PUBLEN) goto done; ok=1; done: EVP_PKEY_CTX_free(k); return ok; }
static int x448_derive(const EVP_PKEY *my_priv,const unsigned char peer_pub[X448_PUBLEN],unsigned char **out,size_t *outlen){
  int ok=0; EVP_PKEY *peer=EVP_PKEY_new_raw_public_key(EVP_PKEY_X448,NULL,peer_pub,X448_PUBLEN); EVP_PKEY_CTX *d=NULL; if(!peer) goto done;
  d=EVP_PKEY_CTX_new((EVP_PKEY*)my_priv,NULL); if(!d) goto done; if(EVP_PKEY_derive_init(d)!=1) goto done; if(EVP_PKEY_derive_set_peer(d,peer)!=1) goto done;
  if(EVP_PKEY_derive(d,NULL,outlen)!=1) goto done; *out=OPENSSL_malloc(*outlen); if(!*out) goto done; if(EVP_PKEY_derive(d,*out,outlen)!=1) goto done; ok=1;
done: if(!ok && *out){ OPENSSL_free(*out); *out=NULL; *outlen=0; } EVP_PKEY_free(peer); EVP_PKEY_CTX_free(d); return ok; }
static int ed25519_sign(const unsigned char priv[32],const unsigned char *msg,size_t msglen,unsigned char sig_out[ED25519_SIGLEN]){
  int ok=0; EVP_PKEY *p=EVP_PKEY_new_raw_private_key(EVP_PKEY_ED25519,NULL,priv,32); if(!p) return 0; EVP_MD_CTX *md=EVP_MD_CTX_new(); if(!md){ EVP_PKEY_free(p); return 0; }
  if(EVP_DigestSignInit(md,NULL,NULL,NULL,p)!=1) goto done; size_t sl=ED25519_SIGLEN; if(EVP_DigestSign(md,sig_out,&sl,msg,msglen)!=1 || sl!=ED25519_SIGLEN) goto done; ok=1;
done: EVP_MD_CTX_free(md); EVP_PKEY_free(p); return ok;
}
static int ed25519_pub_from_priv(const unsigned char priv[32],unsigned char pub_out[32]){ EVP_PKEY *p=EVP_PKEY_new_raw_private_key(EVP_PKEY_ED25519,NULL,priv,32); if(!p) return 0; size_t L=32; int r=(EVP_PKEY_get_raw_public_key(p,pub_out,&L)==1 && L==32); EVP_PKEY_free(p); return r; }
static int ed25519_verify(const unsigned char pub[32],const unsigned char *msg,size_t msglen,const unsigned char sig[ED25519_SIGLEN]){
  int ok=0; EVP_PKEY *p=EVP_PKEY_new_raw_public_key(EVP_PKEY_ED25519,NULL,pub,32); if(!p) return 0; EVP_MD_CTX *md=EVP_MD_CTX_new(); if(!md){ EVP_PKEY_free(p); return 0; }
  if(EVP_DigestVerifyInit(md,NULL,NULL,NULL,p)!=1) goto done; if(EVP_DigestVerify(md,sig,ED25519_SIGLEN,msg,msglen)!=1) goto done; ok=1;
done: EVP_MD_CTX_free(md); EVP_PKEY_free(p); return ok;
}

static void build_hello_sigmsg_v2(uint8_t type,uint8_t flags,uint16_t keylen_be,
                                  uint8_t id_len,const uint8_t id[32],
                                  const uint8_t xpub[X448_PUBLEN],
                                  const uint8_t nonce[NONCE_LEN],
                                  const uint8_t edpub[ED25519_PUBLEN],
                                  unsigned char **out,size_t *outlen){
  const char ctx[]="L2DHv2\0";
  size_t len=sizeof(ctx)+1+1+2+1+32+X448_PUBLEN+NONCE_LEN+ED25519_PUBLEN;
  *out=OPENSSL_malloc(len); unsigned char *p=*out;
  memcpy(p,ctx,sizeof(ctx)); p+=sizeof(ctx);
  *p++=type; *p++=flags; memcpy(p,&keylen_be,2); p+=2;
  *p++=id_len; memcpy(p,id,32); p+=32;
  memcpy(p,xpub,X448_PUBLEN); p+=X448_PUBLEN;
  memcpy(p,nonce,NONCE_LEN);  p+=NONCE_LEN;
  memcpy(p,edpub,ED25519_PUBLEN); p+=ED25519_PUBLEN;
  *outlen=len;
}
static void transcript_hash_v2(const hello_v2_t *a,const hello_v2_t *b,unsigned char th[64]){
  const hello_v2_t *first=(memcmp(a->ed25519_pub,b->ed25519_pub,32)<=0)?a:b;
  const hello_v2_t *second=(first==a)?b:a;
  unsigned char buf[sizeof(hello_v2_t)*2]; size_t off=0;
  memcpy(buf+off,first,sizeof(*first)); off+=sizeof(*first);
  memcpy(buf+off,second,sizeof(*second)); off+=sizeof(*second);
  sha512(buf,off,th);
}

// ---------- BPF (non-VLAN at offset 12) ----------
static int install_cBPF_ethertype_filter(int fd,uint16_t proto){
  struct sock_filter code[]={
    BPF_STMT(BPF_LD|BPF_H|BPF_ABS,12),
    BPF_JUMP(BPF_JMP|BPF_JEQ|BPF_K,htons(proto),0,1),
    BPF_STMT(BPF_RET|BPF_K,0),
    BPF_STMT(BPF_RET|BPF_K,0xFFFF),
  };
  struct sock_fprog fprog={ .len=(unsigned short)(sizeof(code)/sizeof(code[0])), .filter=code };
  if(setsockopt(fd,SOL_SOCKET,SO_ATTACH_FILTER,&fprog,sizeof(fprog))<0){
    fprintf(stderr,"SO_ATTACH_FILTER failed: %s (len=%u)\n",strerror(errno),fprog.len); return -1;
  }
  return 0;
}

// ---------- I/O ----------
static int open_rx(const cfg_t *cfg,int *ifindex,int *mtu,unsigned char smac_out[ETH_ALEN]){
  int fd=socket(AF_PACKET,SOCK_RAW,htons(ETH_P_ALL)); if(fd<0){ perror("socket(RX)"); return -1; }
  struct ifreq ifr; memset(&ifr,0,sizeof(ifr)); snprintf(ifr.ifr_name,sizeof(ifr.ifr_name),"%s",cfg->ifname);
  if(ioctl(fd,SIOCGIFINDEX,&ifr)<0){ perror("SIOCGIFINDEX"); close(fd); return -1; } *ifindex=ifr.ifr_ifindex;
  if(ioctl(fd,SIOCGIFMTU,&ifr)<0){ perror("SIOCGIFMTU"); close(fd); return -1; } *mtu=ifr.ifr_mtu;
  if(!cfg->have_smac){ if(ioctl(fd,SIOCGIFHWADDR,&ifr)<0){ perror("SIOCGIFHWADDR"); close(fd); return -1; } memcpy(smac_out,ifr.ifr_hwaddr.sa_data,ETH_ALEN); } else memcpy(smac_out,cfg->smac,ETH_ALEN);
  struct sockaddr_ll sll={0}; sll.sll_family=AF_PACKET; sll.sll_protocol=htons(ETH_P_ALL); sll.sll_ifindex=*ifindex;
  if(bind(fd,(struct sockaddr*)&sll,sizeof(sll))<0){ perror("bind(RX)"); close(fd); return -1; }
  if(cfg->promisc){ struct packet_mreq mr={0}; mr.mr_ifindex=*ifindex; mr.mr_type=PACKET_MR_PROMISC; if(setsockopt(fd,SOL_PACKET,PACKET_ADD_MEMBERSHIP,&mr,sizeof(mr))<0) perror("promisc"); else DBG1("Promiscuous mode enabled on RX socket"); }
  int one=1; if(setsockopt(fd,SOL_PACKET,PACKET_IGNORE_OUTGOING,&one,sizeof(one))<0) perror("PACKET_IGNORE_OUTGOING"); else DBG1("RX will ignore locally-originated frames");
  if(!cfg->no_bpf){ if(install_cBPF_ethertype_filter(fd,(uint16_t)cfg->ethertype)==0) DBG1("cBPF installed: EtherType 0x%04x (non-VLAN only)",cfg->ethertype); else DBG1("BPF install failed; continuing without filter (higher CPU)"); }
  return fd;
}
static int open_tx(const cfg_t *cfg,int ifindex){
  int fd=socket(AF_PACKET,SOCK_RAW,htons((unsigned short)cfg->ethertype)); if(fd<0){ perror("socket(TX)"); return -1; }
  struct sockaddr_ll sll={0}; sll.sll_family=AF_PACKET; sll.sll_protocol=htons((unsigned short)cfg->ethertype); sll.sll_ifindex=ifindex;
  if(bind(fd,(struct sockaddr*)&sll,sizeof(sll))<0){ perror("bind(TX)"); close(fd); return -1; }
  return fd;
}
static int send_l2(const cfg_t *cfg,int tx_fd,int ifindex,const unsigned char smac[ETH_ALEN],const unsigned char dmac[ETH_ALEN],const void *payload,size_t payload_len,const char *what){
  (void)ifindex;
  unsigned char frame[MAX_FRAME_SIZE]; size_t off=0;
  memcpy(frame+off,dmac,ETH_ALEN); off+=ETH_ALEN; memcpy(frame+off,smac,ETH_ALEN); off+=ETH_ALEN;
  uint16_t et=htons((uint16_t)cfg->ethertype); memcpy(frame+off,&et,2); off+=2;
  memcpy(frame+off,payload,payload_len); size_t plen=payload_len; if(plen<MIN_ETH_PAYLOAD){ memset(frame+off+plen,0,MIN_ETH_PAYLOAD-plen); plen=MIN_ETH_PAYLOAD; }
  size_t flen=off+plen;
  struct sockaddr_ll to={0}; to.sll_family=AF_PACKET; to.sll_ifindex=ifindex; to.sll_halen=ETH_ALEN; memcpy(to.sll_addr,dmac,ETH_ALEN);
  if(sendto(tx_fd,frame,flen,0,(struct sockaddr*)&to,sizeof(to))<0){ perror("sendto"); return -1; }
  DBG1("Sent %s (%zu payload, frame %zu) to %02x:%02x:%02x:%02x:%02x:%02x",what,payload_len,flen,dmac[0],dmac[1],dmac[2],dmac[3],dmac[4],dmac[5]); return 0;
}

// ---------- misc parsing/printing ----------
static int parse_mac(const char *s,unsigned char mac[ETH_ALEN]){ int v[ETH_ALEN]; if(sscanf(s,"%x:%x:%x:%x:%x:%x",&v[0],&v[1],&v[2],&v[3],&v[4],&v[5])!=6) return -1; for(int i=0;i<ETH_ALEN;i++) mac[i]=(unsigned char)v[i]; return 0; }
static int from_hex(const char *hex,unsigned char *out,size_t expect_len){
  size_t n=0; for(const char *p=hex;*p;++p){ if(*p==':'||*p==' '||*p=='_'||*p=='-') continue; if(!isxdigit((unsigned char)*p)) return -1; n++; }
  if(n!=expect_len*2) return -1; size_t i=0; for(const char *p=hex;*p && i<expect_len;){ while(*p && !isxdigit((unsigned char)*p)) p++; char c1=*p?*p++:'0'; while(*p && !isxdigit((unsigned char)*p)) p++; char c2=*p?*p++:'0'; unsigned v=0; sscanf((char[3]){c1,c2,0},"%02x",&v); out[i++]=(unsigned char)v; } return 0;
}
static void print_hex_grouped(const unsigned char *b,size_t n,int group){
  if(group<=0){ for(size_t i=0;i<n;i++) printf("%02x",b[i]); return; }
  size_t L=n*2; char *hex=(char*)malloc(L+1); if(!hex) return; for(size_t i=0;i<n;i++) sprintf(hex+2*i,"%02x",b[i]); hex[L]=0;
  for(size_t i=0;i<L;i++){ putchar(hex[i]); if(((int)((i+1)%group))==0 && i+1<L) putchar(':'); } free(hex);
}
static char *b64(const unsigned char *in,size_t inlen){ size_t outlen=4*((inlen+2)/3); unsigned char *out=OPENSSL_malloc(outlen+1); if(!out) return NULL; int n=EVP_EncodeBlock(out,in,(int)inlen); if(n<0){OPENSSL_free(out);return NULL;} out[n]='\0'; return (char*)out; }
// ---------- child reaper ----------
static void reap_children(int sig){
  (void)sig;
  int saved = errno;
  // Reap all exited children without blocking
  while (waitpid(-1, NULL, WNOHANG) > 0) { /* no-op */ }
  errno = saved;
}
static void setup_sigchld_reaper(void){
  struct sigaction sa;
  memset(&sa, 0, sizeof(sa));
  sa.sa_handler = reap_children;
  sigemptyset(&sa.sa_mask);
  sa.sa_flags = SA_RESTART | SA_NOCLDSTOP;
  sigaction(SIGCHLD, &sa, NULL);
}

// ---------- exec hook helpers ----------
static void mac_to_str(const unsigned char mac[ETH_ALEN], char out[18]){
  snprintf(out, 18, "%02x:%02x:%02x:%02x:%02x:%02x", mac[0],mac[1],mac[2],mac[3],mac[4],mac[5]);
}
static char *to_hex(const unsigned char *b, size_t n){
  size_t L = n*2; char *s = (char*)malloc(L+1); if(!s) return NULL;
  for(size_t i=0;i<n;i++) sprintf(s+2*i, "%02x", b[i]); s[L]=0; return s;
}
static char *to_hex_grouped(const unsigned char *b, size_t n, int group){
  if(group<=0) return NULL;
  size_t hexchars = n*2;
  size_t separators = (group>0 && hexchars>0) ? ((hexchars-1)/group) : 0;
  size_t L = hexchars + separators;
  char *s = (char*)malloc(L+1); if(!s) return NULL;
  size_t pos=0, cnt=0;
  for(size_t i=0;i<n;i++){
    char hh[3]; sprintf(hh,"%02x",b[i]);
    s[pos++]=hh[0]; cnt++; if((cnt%group)==0 && (i!=n-1)) s[pos++]=':';
    s[pos++]=hh[1]; cnt++; if((cnt%group)==0 && (i!=n-1)) s[pos++]=':';
  }
  s[pos]=0; return s;
}
static int set_env_kv(const char *k, const char *v){
  if(!k || !v) return -1; return setenv(k, v, 1);
}
static int run_exec_hook(const cfg_t *cfg,
                         const char *id,
                         const unsigned char *K, size_t keylen,
                         const unsigned char fp[32],
                         const unsigned char peer_mac[ETH_ALEN]){
  if(!cfg->exec_cmd) return 0;

  // Prepare strings
  char *key_hex = to_hex(K, keylen);
  char *key_b64 = b64(K, keylen);
  char fp8[17]; for(int i=0;i<8;i++) sprintf(fp8+2*i,"%02x",fp[i]); fp8[16]=0;
  char lenbuf[16]; snprintf(lenbuf,sizeof(lenbuf),"%zu", keylen);
  char macstr[18]; mac_to_str(peer_mac, macstr);

  // Optional grouped/parts
  char *key_hex_grouped = NULL;
  if(cfg->sep_group > 0){
    key_hex_grouped = to_hex_grouped(K, keylen, cfg->sep_group);
  }

  pid_t pid = fork();
  if(pid < 0){
    perror("fork");
    goto cleanup;
  }
  if(pid == 0){
    // Child: set env and exec
    set_env_kv("L2DH_ID", id ? id : "");
    if(key_hex) set_env_kv("L2DH_KEY_HEX", key_hex);
    if(key_b64) set_env_kv("L2DH_KEY_B64", key_b64);
    set_env_kv("L2DH_FP8", fp8);
    set_env_kv("L2DH_LEN", lenbuf);
    set_env_kv("L2DH_PEER_MAC", macstr);
    if(key_hex_grouped){
      set_env_kv("L2DH_KEY_HEX_GROUPED", key_hex_grouped);
      size_t total_hex = keylen*2;
      int parts = (int)((total_hex + cfg->sep_group - 1) / cfg->sep_group);
      char cntbuf[16]; snprintf(cntbuf,sizeof(cntbuf), "%d", parts);
      set_env_kv("L2DH_KEY_HEX_COUNT", cntbuf);
      if(key_hex){
        for(int i=0;i<parts;i++){
          size_t start = (size_t)i * (size_t)cfg->sep_group;
          size_t remain = total_hex - start;
          size_t thislen = remain < (size_t)cfg->sep_group ? remain : (size_t)cfg->sep_group;
          char name[32]; snprintf(name,sizeof(name), "L2DH_KEY_HEX_%d", i+1);
          char *val = (char*)malloc(thislen+1);
          if(val){
            memcpy(val, key_hex + start, thislen); val[thislen]=0;
            set_env_kv(name, val);
            // leak val intentionally in child (exec soon)
          }
        }
      }
    }
    execl("/bin/sh","sh","-c",cfg->exec_cmd,(char*)NULL);
    _exit(127);
  }

cleanup:
  if(key_hex) free(key_hex);
  if(key_b64) OPENSSL_free(key_b64);
  if(key_hex_grouped) free(key_hex_grouped);
  return 0;
}

// ---------- config helpers ----------
static void trim(char *s){ char *p=s; while(*p && isspace((unsigned char)*p)) p++; if(p!=s) memmove(s,p,strlen(s)+1); size_t n=strlen(s); while(n>0 && isspace((unsigned char)s[n-1])) s[--n]=0; }
static int parse_bool(const char *v){ if(!v) return 0; if(!strcasecmp(v,"1")||!strcasecmp(v,"true")||!strcasecmp(v,"yes")||!strcasecmp(v,"on")) return 1; return 0; }
static int load_config(const char *path,cfg_t *cfg){
  FILE *f=fopen(path,"r"); if(!f){ perror("fopen(config)"); return -1; }
  char line[1024]; int lineno=0;
  while(fgets(line,sizeof(line),f)){ lineno++; char *h=strchr(line,'#'); if(h) *h=0; char *s=strchr(line,';'); if(s) *s=0; trim(line); if(!*line) continue;
    char *eq=strchr(line,'='); if(!eq) continue; *eq=0; char *k=line; trim(k); char *v=eq+1; trim(v); if(!*k) continue;
    if(!strcasecmp(k,"ifname")) cfg->ifname=strdup(v);
    else if(!strcasecmp(k,"src_mac")){ if(parse_mac(v,cfg->smac)==0) cfg->have_smac=1; }
    else if(!strcasecmp(k,"ethertype")) cfg->ethertype=(unsigned)strtoul(v,NULL,16);
    else if(!strcasecmp(k,"promisc")) cfg->promisc=parse_bool(v);
    else if(!strcasecmp(k,"no_bpf")) cfg->no_bpf=parse_bool(v);
    else if(!strcasecmp(k,"retry_ms")){ cfg->retry_ms=atoi(v); if(cfg->retry_ms<100) cfg->retry_ms=100; }
    else if(!strcasecmp(k,"timeout")) cfg->timeout_sec=atoi(v);
    else if(!strcasecmp(k,"raw")) cfg->raw_only=parse_bool(v);
    else if(!strcasecmp(k,"separate")){ cfg->sep_group=atoi(v); if(cfg->sep_group<0) cfg->sep_group=0; }
    else if(!strcasecmp(k,"my_ed25519_priv")){ if(from_hex(v,cfg->my_ed25519_priv,32)==0) cfg->have_my_priv=1; else fprintf(stderr,"config:%d bad my_ed25519_priv\n",lineno); }
    else if(!strcasecmp(k,"peer_ed25519_pub")){ if(from_hex(v,cfg->peer_ed25519_pub,32)==0) cfg->have_peer_pub=1; else fprintf(stderr,"config:%d bad peer_ed25519_pub\n",lineno); }
    else if(!strcasecmp(k,"max_resends")) cfg->max_resends=atoi(v);
    else if(!strcasecmp(k,"replay_window_sec")){ int s=atoi(v); cfg->replay_window_ms = (s<=0)?0:(uint32_t)(s*1000); }
    else if(!strcasecmp(k,"loop")) cfg->loop_mode=parse_bool(v);
    else if(!strcasecmp(k,"exec")) cfg->exec_cmd=strdup(v);
    else if(!strcasecmp(k,"quiet")) cfg->quiet=parse_bool(v);
  }
  fclose(f); return 0;
}

// ---------- main ----------
int main(int argc,char **argv){
  cfg_t cfg={0};
  cfg.ethertype=DEFAULT_ETHERTYPE;
  cfg.timeout_sec=-1;
  cfg.retry_ms=1000;
  cfg.sep_group=0;
  cfg.quiet=0;
  cfg.max_resends=10;
  cfg.replay_window_ms=30*1000;
  cfg.loop_mode=0; // one-shot default
  cfg.exec_cmd=NULL;

  const char *cfgpath=NULL; for(int i=1;i<argc;i++){ if(!strcmp(argv[i],"-c") && i+1<argc){ cfgpath=argv[i+1]; break; } }
  if(cfgpath){ if(load_config(cfgpath,&cfg)!=0){ fprintf(stderr,"Failed to load config: %s\n", cfgpath); return 1; } }

  for(int i=1;i<argc;i++){
    if(!strcmp(argv[i],"-c")){ i++; continue; }
    if(!strcmp(argv[i],"-i") && i+1<argc){ cfg.ifname=argv[++i]; continue; }
    if(!strcmp(argv[i],"-s") && i+1<argc){ if(parse_mac(argv[++i],cfg.smac)==0) cfg.have_smac=1; else { fprintf(stderr,"Bad src MAC\n"); return 1; } continue; }
    if(!strcmp(argv[i],"-y") && i+1<argc){ cfg.ethertype=(unsigned)strtoul(argv[++i],NULL,16); continue; }
    if(!strcmp(argv[i],"-q")){ cfg.quiet=1; continue; }
    if(!strcmp(argv[i],"--retry-ms") && i+1<argc){ cfg.retry_ms=atoi(argv[++i]); if(cfg.retry_ms<100) cfg.retry_ms=100; continue; }
    if(!strcmp(argv[i],"--timeout") && i+1<argc){ cfg.timeout_sec=atoi(argv[++i]); continue; }
    if(!strcmp(argv[i],"--promisc")){ cfg.promisc=1; continue; }
    if(!strcmp(argv[i],"--no-bpf")){ cfg.no_bpf=1; continue; }
    if(!strcmp(argv[i],"--raw")){ cfg.raw_only=1; continue; }
    if(!strcmp(argv[i],"--separate") && i+1<argc){ cfg.sep_group=atoi(argv[++i]); if(cfg.sep_group<0) cfg.sep_group=0; continue; }
    if(!strcmp(argv[i],"--my-ed25519-priv") && i+1<argc){ if(from_hex(argv[++i],cfg.my_ed25519_priv,32)==0) cfg.have_my_priv=1; else {fprintf(stderr,"Bad my_ed25519_priv\n"); return 1;} continue; }
    if(!strcmp(argv[i],"--peer-ed25519-pub") && i+1<argc){ if(from_hex(argv[++i],cfg.peer_ed25519_pub,32)==0) cfg.have_peer_pub=1; else {fprintf(stderr,"Bad peer_ed25519_pub\n"); return 1;} continue; }
    if(!strcmp(argv[i],"--max-resends") && i+1<argc){ cfg.max_resends=atoi(argv[++i]); continue; }
    if(!strcmp(argv[i],"--replay-window-sec") && i+1<argc){ int s=atoi(argv[++i]); cfg.replay_window_ms=(s<=0)?0:(uint32_t)(s*1000); continue; }
    if(!strcmp(argv[i],"--loop")){ cfg.loop_mode=1; continue; }
    if(!strcmp(argv[i],"--exec") && i+1<argc){ cfg.exec_cmd=argv[++i]; continue; }
    if(!strcmp(argv[i],"-v")){ g_verbose=g_verbose<1?1:g_verbose; continue; }
    if(!strcmp(argv[i],"-vv")){ g_verbose=2; continue; }
  }

  if(!cfg.ifname || !cfg.have_my_priv || !cfg.have_peer_pub){ fprintf(stderr,"Missing required args\n"); return 1; }

  // Ensure any forked hook children are reaped (prevents zombies)
  setup_sigchld_reaper();

  int ifindex=0, mtu=0; unsigned char smac[ETH_ALEN];
  int rx_fd=open_rx(&cfg,&ifindex,&mtu,smac); if(rx_fd<0) return 1;
  int tx_fd=open_tx(&cfg,ifindex); if(tx_fd<0){ close(rx_fd); return 1; }

  DBG1("Interface=%s ifindex=%d MTU=%d", cfg.ifname, ifindex, mtu);
  DBG1("Ethertype=0x%04x VLAN=no", cfg.ethertype);
  DBG1("Mode: %s | Timeout=%s | Retry=%dms | MaxResends=%d | ReplayWindow=%u ms | Loop=%s | Exec=%s",
       cfg.promisc ? "promisc" : "non-promisc",
       (cfg.timeout_sec<0)?"infinite":"set",
       cfg.retry_ms, cfg.max_resends, (unsigned)cfg.replay_window_ms,
       cfg.loop_mode ? "on" : "off",
       cfg.exec_cmd ? cfg.exec_cmd : "(none)");

  lru_t lru; lru_init(&lru, cfg.replay_window_ms);

  for(;;){
    // ----- IDLE: wait HELLO(I) -----
    hello_v2_t hi; unsigned char rxbuf[2048]; unsigned char reply_dmac[ETH_ALEN]={0};
    int got_hi=0;
    struct timespec start_wait; clock_gettime(CLOCK_MONOTONIC,&start_wait);

    while(!got_hi){
      struct pollfd pfd={.fd=rx_fd,.events=POLLIN};
      int pr=poll(&pfd,1,1000);
      if(pr>0 && (pfd.revents&POLLIN)){
        ssize_t n=recvfrom(rx_fd,rxbuf,sizeof(rxbuf),0,NULL,NULL);
        if(n<14) continue;
        if(ntohs(*(uint16_t*)(rxbuf+12))!=(uint16_t)cfg.ethertype) continue;
        if(14+sizeof(hello_v2_t)>(size_t)n) continue;
        hello_v2_t *m=(hello_v2_t*)(rxbuf+14);
        if(memcmp(m->magic,MAGIC,4)!=0 || m->ver!=PROTO_VER || m->type!=TYPE_HELLO) continue;
        if(memcmp(m->ed25519_pub,cfg.peer_ed25519_pub,32)!=0){ DBG1("rx HELLO wrong pinned pub"); continue; }

        // Optional anti-replay (drop exact tuple seen very recently)
        if(lru_contains_fresh(&lru, m->ed25519_pub, m->x448_pub, m->nonce)){
          DBG1("rx HELLO(I) dropped (recent replay)"); continue;
        }

        // verify HELLO sig
        unsigned char *msg=NULL; size_t msglen=0;
        build_hello_sigmsg_v2(TYPE_HELLO,m->flags,m->keylen_be,m->id_len,m->id,m->x448_pub,m->nonce,m->ed25519_pub,&msg,&msglen);
        if(!ed25519_verify(m->ed25519_pub,msg,msglen,m->sig)){ DBG1("rx HELLO bad sig"); OPENSSL_free(msg); continue; }
        OPENSSL_free(msg);

        memcpy(&hi,m,sizeof(hi)); memcpy(reply_dmac,rxbuf+6,ETH_ALEN); got_hi=1; DBG1("rx HELLO OK");
        lru_remember(&lru, m->ed25519_pub, m->x448_pub, m->nonce);
      }

      if(cfg.timeout_sec>=0){
        struct timespec now; clock_gettime(CLOCK_MONOTONIC,&now);
        int elapsed=(int)((now.tv_sec-start_wait.tv_sec)+(now.tv_nsec-start_wait.tv_nsec)/1e9);
        if(elapsed>=cfg.timeout_sec){
          fprintf(stderr,"[%s] ERROR: timeout waiting HELLO(I) — staying in IDLE\n",ts());
          break;
        }
      }
    }

    if(!got_hi) continue; // timed out in IDLE

    // ----- Build HELLO(R) -----
    EVP_PKEY *eph_priv=NULL; unsigned char xpub[X448_PUBLEN];
    if(!x448_keygen(&eph_priv,xpub)){ close(rx_fd); close(tx_fd); return 1; }
    unsigned char nonce[NONCE_LEN]; if(RAND_bytes(nonce,NONCE_LEN)!=1){ fprintf(stderr,"RAND_bytes failed\n"); close(rx_fd); close(tx_fd); EVP_PKEY_free(eph_priv); return 1; }
    unsigned char my_edpub[32]; if(!ed25519_pub_from_priv(cfg.my_ed25519_priv,my_edpub)){ fprintf(stderr,"Cannot get Ed25519 pub\n"); close(rx_fd); close(tx_fd); EVP_PKEY_free(eph_priv); return 1; }

    hello_v2_t hr; memset(&hr,0,sizeof(hr)); memcpy(hr.magic,MAGIC,4); hr.ver=PROTO_VER; hr.type=TYPE_HELLO; hr.flags=0;
    memcpy(hr.x448_pub,xpub,X448_PUBLEN); memcpy(hr.nonce,nonce,NONCE_LEN); memcpy(hr.ed25519_pub,my_edpub,32);
    hr.keylen_be = hi.keylen_be; hr.id_len = hi.id_len; memcpy(hr.id, hi.id, 32);

    unsigned char *sigmsg=NULL; size_t siglen=0;
    build_hello_sigmsg_v2(TYPE_HELLO,hr.flags,hr.keylen_be,hr.id_len,hr.id,hr.x448_pub,hr.nonce,hr.ed25519_pub,&sigmsg,&siglen);
    if(!ed25519_sign(cfg.my_ed25519_priv,sigmsg,siglen,hr.sig)){ fprintf(stderr,"Ed25519 sign failed\n"); OPENSSL_free(sigmsg); close(rx_fd); close(tx_fd); EVP_PKEY_free(eph_priv); return 1; }
    OPENSSL_free(sigmsg);

    // ----- derive -----
    unsigned char *ss=NULL; size_t ss_len=0;
    if(!x448_derive(eph_priv,hi.x448_pub,&ss,&ss_len)){ fprintf(stderr,"X448 derive failed\n"); close(rx_fd); close(tx_fd); EVP_PKEY_free(eph_priv); return 1; }
    EVP_PKEY_free(eph_priv); eph_priv=NULL;

    uint16_t keylen = ntohs(hi.keylen_be);
    if(keylen<16) keylen=16; if(keylen>4096) keylen=4096;

    unsigned char *K=OPENSSL_malloc(keylen); if(!K){ fprintf(stderr,"OOM K\n"); OPENSSL_cleanse(ss,ss_len); OPENSSL_free(ss); close(rx_fd); close(tx_fd); return 1; }
    unsigned char Kmac[HMAC_LEN];
    const unsigned char info_key[]="L2DHv2 key"; const unsigned char info_mac[]="L2DHv2 mac";
    if(!hkdf_sha512(ss,ss_len,NULL,0,info_key,sizeof(info_key)-1,K,keylen) ||
       !hkdf_sha512(ss,ss_len,NULL,0,info_mac,sizeof(info_mac)-1,Kmac,sizeof(Kmac))){
      fprintf(stderr,"HKDF failed\n"); OPENSSL_cleanse(ss,ss_len); OPENSSL_free(ss); OPENSSL_cleanse(K,keylen); OPENSSL_free(K); close(rx_fd); close(tx_fd); return 1;
    }
    OPENSSL_cleanse(ss,ss_len); OPENSSL_free(ss);

    unsigned char th[64]; transcript_hash_v2(&hi,&hr,th);

    (void)send_l2(&cfg,tx_fd,ifindex,smac,reply_dmac,&hr,sizeof(hr),"HELLO(R)");

    finish_v2_t fr; memset(&fr,0,sizeof(fr)); memcpy(fr.magic,MAGIC,4); fr.ver=PROTO_VER; fr.type=TYPE_FINISH;
    if(hi.flags & FLAG_TIME_REQUEST){ struct timespec now; clock_gettime(CLOCK_REALTIME,&now); fr.time_sec_be=htobe64_u64((uint64_t)now.tv_sec); fr.time_nsec_be=htonl((uint32_t)(now.tv_nsec>999999999?999999999:now.tv_nsec)); }
    unsigned int maclen=0; HMAC_CTX *h=HMAC_CTX_new(); HMAC_Init_ex(h,Kmac,sizeof(Kmac),EVP_sha512(),NULL);
    HMAC_Update(h,TAG_FIN_R,sizeof(TAG_FIN_R)); HMAC_Update(h,th,sizeof(th));
    HMAC_Update(h,(unsigned char*)&fr.time_sec_be,8); HMAC_Update(h,(unsigned char*)&fr.time_nsec_be,4);
    HMAC_Final(h,fr.mac,&maclen); HMAC_CTX_free(h);

    (void)send_l2(&cfg,tx_fd,ifindex,smac,reply_dmac,&fr,sizeof(fr),"FINISH(R)");

    // ----- wait FINISH(I) with restart/limits -----
    int got_fini_i=0; int resend_count=0;
    uint64_t next_resend = now_ms() + (cfg.retry_ms>0 ? (uint64_t)cfg.retry_ms : 1000);
    uint64_t deadline = (cfg.timeout_sec>=0) ? (now_ms() + (uint64_t)cfg.timeout_sec*1000ULL) : (uint64_t)~0ULL;

    for(;;){
      struct pollfd pfd={.fd=rx_fd,.events=POLLIN}; int pr=poll(&pfd,1,100);
      if(pr>0 && (pfd.revents&POLLIN)){
        unsigned char buf[2048]; ssize_t n=recvfrom(rx_fd,buf,sizeof(buf),0,NULL,NULL); if(n<14) goto timers;
        if(ntohs(*(uint16_t*)(buf+12))==(uint16_t)cfg.ethertype){
          if(n >= (ssize_t)(14+sizeof(finish_v2_t))){
            finish_v2_t *fi=(finish_v2_t*)(buf+14);
            if(memcmp(fi->magic,MAGIC,4)==0 && fi->ver==PROTO_VER && fi->type==TYPE_FINISH){
              unsigned char expect[HMAC_LEN]; unsigned int elen=0; HMAC_CTX *vh=HMAC_CTX_new();
              HMAC_Init_ex(vh,Kmac,sizeof(Kmac),EVP_sha512(),NULL); HMAC_Update(vh,TAG_FIN_I,sizeof(TAG_FIN_I)); HMAC_Update(vh,th,sizeof(th)); HMAC_Final(vh,expect,&elen); HMAC_CTX_free(vh);
              if(elen==HMAC_LEN && CRYPTO_memcmp(expect,fi->mac,HMAC_LEN)==0){ DBG1("rx FINISH(I) OK"); got_fini_i=1; break; }
            }
          }
          if(n >= (ssize_t)(14+sizeof(hello_v2_t))){
            hello_v2_t *m=(hello_v2_t*)(buf+14);
            if(memcmp(m->magic,MAGIC,4)==0 && m->ver==PROTO_VER && m->type==TYPE_HELLO &&
               memcmp(m->ed25519_pub,cfg.peer_ed25519_pub,32)==0){
              unsigned char *msg2=NULL; size_t msg2len=0;
              build_hello_sigmsg_v2(TYPE_HELLO,m->flags,m->keylen_be,m->id_len,m->id,m->x448_pub,m->nonce,m->ed25519_pub,&msg2,&msg2len);
              int sigok = ed25519_verify(m->ed25519_pub,msg2,msg2len,m->sig);
              OPENSSL_free(msg2);
              if(sigok){
                DBG1("rx HELLO(I) while awaiting FINISH(I) -> restarting");
                OPENSSL_cleanse(K,keylen); OPENSSL_free(K);
                goto next_session;
              }
            }
          }
        }
      }
timers:;
      uint64_t now = now_ms();
      if(now >= next_resend){
        (void)send_l2(&cfg,tx_fd,ifindex,smac,reply_dmac,&fr,sizeof(fr),"FINISH(R,resend)");
        resend_count++;
        next_resend += (cfg.retry_ms>0 ? (uint64_t)cfg.retry_ms : 1000);
        if(cfg.max_resends >= 0 && resend_count > cfg.max_resends){
          DBG1("Max FINISH(R) resends reached -> abandoning session");
          OPENSSL_cleanse(K,keylen); OPENSSL_free(K);
          goto next_session;
        }
      }
      if(now >= deadline){
        DBG1("Timeout waiting for FINISH(I) -> abandoning session");
        OPENSSL_cleanse(K,keylen); OPENSSL_free(K);
        goto next_session;
      }
    }

// ----- Success / print -----
{
  char idbuf[33]={0}; const char *id_print=NULL;
  if(hi.id_len>0){ memcpy(idbuf,hi.id,hi.id_len); idbuf[hi.id_len]=0; id_print=idbuf; }

  unsigned char fp[32];
  SHA256(K, keylen, fp);

  // Run hook regardless of --raw/!raw
  run_exec_hook(&cfg, id_print, K, keylen, fp, reply_dmac);

  if(!cfg.quiet){
    if(cfg.raw_only){
      if(id_print) printf("%s:", id_print);
      print_hex_grouped(K,keylen,cfg.sep_group); putchar('\n');
    }else{
      printf("=== L2DH v2 success (responder, X448/Ed25519) ===\n");
      if(id_print) printf("Identifier: %s\n", id_print);
      printf("Session key (%u bytes):\n  hex = ", (unsigned)keylen);
      if(id_print) printf("%s:", id_print);
      print_hex_grouped(K,keylen,cfg.sep_group); printf("\n");
      char *b64str=b64(K,keylen); if(b64str){ printf("  b64 = %s\n", b64str); OPENSSL_free(b64str); }
      printf("Fingerprint (SHA-256(key) first 8 bytes): "); for(int i=0;i<8;i++){ printf("%02x",fp[i]); if(i==3) printf(" "); } printf("\n");
    }
  }
}

    // cleanse
    OPENSSL_cleanse(K,keylen); OPENSSL_free(K);

    // OPTIONAL: remember successful tuple to drop replays for a short window
    lru_remember(&lru, hi.ed25519_pub, hr.x448_pub, hr.nonce);

    if(!cfg.loop_mode){
      close(rx_fd); close(tx_fd);
      return 0;  // one-shot success
    }

next_session:
    ; // continue main loop
  }

  close(rx_fd); close(tx_fd);
  return 0;
}

