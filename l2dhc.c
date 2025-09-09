/* l2dhc.c — Layer-2 DH initiator (v2+id): X448 KEX + Ed25519 auth
 * - Resends HELLO(I) and FINISH(I) every --retry-ms until answer/timeout
 * - Identifier (<=32 ASCII) carried over the wire; printed on both sides
 * - Initiator chooses derived key length (--keylen)
 * - Optional time request (-t) to set clock from responder
 * - Config file (-c key=value); CLI overrides
 * - --raw / --separate N formatting
 *
 * Build:
 *   cc -O2 -Wall -Wextra -DOPENSSL_API_COMPAT=0x10100000L -o l2dhc l2dhc.c -lcrypto
 */

#define _GNU_SOURCE
#include <arpa/inet.h>
#include <errno.h>
#include <linux/if_packet.h>
#include <linux/if_ether.h>
#include <net/if.h>
#include <poll.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <time.h>
#include <unistd.h>
#include <ctype.h>

#include <openssl/evp.h>
#include <openssl/hmac.h>
#include <openssl/sha.h>
#include <openssl/rand.h>
#include <openssl/crypto.h>

#define DEFAULT_ETHERTYPE 0x88B5
#define MIN_ETH_PAYLOAD   46
#define MAX_FRAME_SIZE    2048

static const uint8_t MAGIC[4] = { 'L','2','D','H' };
#define PROTO_VER 2
#define TYPE_HELLO  1
#define TYPE_FINISH 2

#define X448_PUBLEN     56
#define ED25519_PUBLEN  32
#define ED25519_SIGLEN  64
#define NONCE_LEN       32
#define HMAC_LEN        64  // HMAC-SHA512

static const unsigned char TAG_FIN_I[4] = { 'F','I','N','I' };
static const unsigned char TAG_FIN_R[4] = { 'F','I','N','R' };

#define FLAG_TIME_REQUEST 0x01

// ---------- endian helpers ----------
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
#ifndef be64toh
static inline uint64_t be64toh_u64(uint64_t x){uint32_t hi=(uint32_t)(x>>32),lo=(uint32_t)x;hi=ntohl(hi);lo=ntohl(lo);return ((uint64_t)lo<<32)|hi;}
#else
# define be64toh_u64(x) be64toh((x))
#endif

// ---------- logging ----------
static int g_verbose=0;
static const char* ts(){ static char b[32]; struct timespec tv; clock_gettime(CLOCK_REALTIME,&tv); struct tm tm; localtime_r(&tv.tv_sec,&tm); snprintf(b,sizeof(b),"%02d:%02d:%02d.%03ld",tm.tm_hour,tm.tm_min,tm.tm_sec,tv.tv_nsec/1000000); return b; }
#define DBG1(f,...) do{ if(g_verbose>=1) fprintf(stderr,"[%s] " f "\n",ts(),##__VA_ARGS__);}while(0)
#define DBG2(f,...) do{ if(g_verbose>=2) fprintf(stderr,"[%s] " f "\n",ts(),##__VA_ARGS__);}while(0)
static void hexdump2(const char *lab, const unsigned char *p, size_t n){ if(g_verbose<2) return; fprintf(stderr,"[%s] %s (%zu):",ts(),lab,n); for(size_t i=0;i<n;i++){ if(i%16==0) fprintf(stderr,"\n  "); fprintf(stderr,"%02x ",p[i]); } fprintf(stderr,"\n"); }

// ---------- utils ----------
static uint64_t now_ms(){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return (uint64_t)t.tv_sec*1000ULL + (uint64_t)(t.tv_nsec/1000000ULL); }

static void print_hex_grouped(const unsigned char *b,size_t n,int group){
  if(group<=0){ for(size_t i=0;i<n;i++) printf("%02x",b[i]); return; }
  size_t L=n*2; char *hex=(char*)malloc(L+1); if(!hex) return;
  for(size_t i=0;i<n;i++) sprintf(hex+2*i,"%02x",b[i]); hex[L]=0;
  for(size_t i=0;i<L;i++){ putchar(hex[i]); if(((int)((i+1)%group))==0 && i+1<L) putchar(':'); }
  free(hex);
}
static char *b64(const unsigned char *in,size_t inlen){ size_t outlen=4*((inlen+2)/3); unsigned char *out=OPENSSL_malloc(outlen+1); if(!out) return NULL; int n=EVP_EncodeBlock(out,in,(int)inlen); if(n<0){OPENSSL_free(out);return NULL;} out[n]='\0'; return (char*)out; }

static int parse_mac(const char *s, unsigned char mac[ETH_ALEN]) {
  int v[ETH_ALEN]; if (sscanf(s,"%x:%x:%x:%x:%x:%x",&v[0],&v[1],&v[2],&v[3],&v[4],&v[5])!=6) return -1;
  for(int i=0;i<ETH_ALEN;i++) mac[i]=(unsigned char)v[i]; return 0;
}
static int from_hex(const char *hex, unsigned char *out, size_t expect_len){
  size_t n=0; for(const char *p=hex;*p;++p){ if(*p==':'||*p==' '||*p=='_'||*p=='-') continue; if(!isxdigit((unsigned char)*p)) return -1; n++; }
  if(n!=expect_len*2) return -1;
  size_t i=0; for(const char *p=hex; *p && i<expect_len;){
    while(*p && !isxdigit((unsigned char)*p)) p++;
    char c1=*p?*p++:'0'; while(*p && !isxdigit((unsigned char)*p)) p++;
    char c2=*p?*p++:'0'; unsigned v=0; sscanf((char[3]){c1,c2,0}, "%02x", &v); out[i++]=(unsigned char)v;
  }
  return 0;
}

// ---------- config ----------
typedef struct {
  const char *ifname;
  unsigned char smac[ETH_ALEN]; int have_smac;
  unsigned char dmac[ETH_ALEN]; int have_dmac;
  unsigned ethertype;
  int promisc;
  int timeout_sec;       // overall
  int retry_ms;
  int raw_only;
  int sep_group;
  int want_time;         // -t request + set
  const char *identifier;// <=32 ASCII, sent on wire
  int keylen;            // derived length in bytes
  // auth
  unsigned char my_ed25519_priv[32]; int have_my_priv;
  unsigned char peer_ed25519_pub[32]; int have_peer_pub;
} cfg_t;

static void trim(char *s){ char *p=s; while(*p && isspace((unsigned char)*p)) p++; if(p!=s) memmove(s,p,strlen(p)+1); size_t n=strlen(s); while(n>0 && isspace((unsigned char)s[n-1])) s[--n]=0; }
static int parse_bool(const char *v){ if(!v) return 0; if(!strcasecmp(v,"1")||!strcasecmp(v,"true")||!strcasecmp(v,"yes")||!strcasecmp(v,"on")) return 1; return 0; }
static int load_config(const char *path,cfg_t *cfg){
  FILE *f=fopen(path,"r"); if(!f){ perror("fopen(config)"); return -1; }
  char line[1024]; int lineno=0;
  while(fgets(line,sizeof(line),f)){ lineno++; char *h=strchr(line,'#'); if(h) *h=0; char *s=strchr(line,';'); if(s) *s=0; trim(line); if(!*line) continue;
    char *eq=strchr(line,'='); if(!eq) continue; *eq=0; char *k=line; trim(k); char *v=eq+1; trim(v); if(!*k) continue;
    if(!strcasecmp(k,"ifname")) cfg->ifname=strdup(v);
    else if(!strcasecmp(k,"src_mac")){ if(parse_mac(v,cfg->smac)==0) cfg->have_smac=1; }
    else if(!strcasecmp(k,"dest_mac")){ if(parse_mac(v,cfg->dmac)==0) cfg->have_dmac=1; }
    else if(!strcasecmp(k,"ethertype")) cfg->ethertype=(unsigned)strtoul(v,NULL,16);
    else if(!strcasecmp(k,"promisc")) cfg->promisc=parse_bool(v);
    else if(!strcasecmp(k,"retry_ms")){ cfg->retry_ms=atoi(v); if(cfg->retry_ms<100) cfg->retry_ms=100; }
    else if(!strcasecmp(k,"timeout")) cfg->timeout_sec=atoi(v);
    else if(!strcasecmp(k,"raw")) cfg->raw_only=parse_bool(v);
    else if(!strcasecmp(k,"separate")){ cfg->sep_group=atoi(v); if(cfg->sep_group<0) cfg->sep_group=0; }
    else if(!strcasecmp(k,"identifier")) cfg->identifier=strdup(v);
    else if(!strcasecmp(k,"keylen")) cfg->keylen=atoi(v);
    else if(!strcasecmp(k,"time")) cfg->want_time=parse_bool(v);
    else if(!strcasecmp(k,"my_ed25519_priv")){ if(from_hex(v,cfg->my_ed25519_priv,32)==0) cfg->have_my_priv=1; else fprintf(stderr,"config:%d bad my_ed25519_priv\n",lineno); }
    else if(!strcasecmp(k,"peer_ed25519_pub")){ if(from_hex(v,cfg->peer_ed25519_pub,32)==0) cfg->have_peer_pub=1; else fprintf(stderr,"config:%d bad peer_ed25519_pub\n",lineno); }
  }
  fclose(f); return 0;
}

// ---------- protocol structs ----------
#pragma pack(push,1)
typedef struct {
  uint8_t  magic[4];
  uint8_t  ver;
  uint8_t  type;
  uint8_t  flags;      // FLAG_TIME_REQUEST bit
  uint8_t  id_len;     // 0..32
  uint8_t  x448_pub[X448_PUBLEN];
  uint8_t  nonce[NONCE_LEN];
  uint8_t  ed25519_pub[ED25519_PUBLEN];
  uint16_t keylen_be;  // initiator-chosen
  uint8_t  id[32];     // raw bytes (ASCII), not NUL-terminated
  uint8_t  sig[ED25519_SIGLEN];
} hello_v2_t;

typedef struct {
  uint8_t  magic[4];
  uint8_t  ver;
  uint8_t  type;           // TYPE_FINISH
  uint8_t  flags;          // reserved
  uint8_t  reserved;
  uint64_t time_sec_be;    // if requested
  uint32_t time_nsec_be;
  uint8_t  mac[HMAC_LEN];  // HMAC-SHA512
} finish_v2_t;
#pragma pack(pop)

// ---------- crypto helpers ----------
static void sha512(const void *d,size_t n,unsigned char out[64]){ SHA512_CTX c; SHA512_Init(&c); SHA512_Update(&c,d,n); SHA512_Final(out,&c); }

static int hkdf_sha512(const unsigned char *ikm,size_t ikm_len,
                       const unsigned char *salt,size_t salt_len,
                       const unsigned char *info,size_t info_len,
                       unsigned char *okm,size_t okm_len){
  unsigned char zeros[SHA512_DIGEST_LENGTH]={0};
  if(!salt||!salt_len){ salt=zeros; salt_len=sizeof(zeros); }
  unsigned char prk[SHA512_DIGEST_LENGTH]; unsigned int prk_len;
  if(!HMAC(EVP_sha512(),salt,(int)salt_len,ikm,ikm_len,prk,&prk_len)) return 0;
  unsigned char t[SHA512_DIGEST_LENGTH]; size_t tlen=0,pos=0; unsigned char ctr=1;
  while(pos<okm_len){
    HMAC_CTX *ctx=HMAC_CTX_new(); if(!ctx) return 0;
    if(HMAC_Init_ex(ctx,prk,(int)prk_len,EVP_sha512(),NULL)!=1){ HMAC_CTX_free(ctx); return 0; }
    if(tlen) HMAC_Update(ctx,t,tlen);
    if(info&&info_len) HMAC_Update(ctx,info,info_len);
    HMAC_Update(ctx,&ctr,1);
    unsigned int outlen=0; HMAC_Final(ctx,t,&outlen); HMAC_CTX_free(ctx);
    tlen=outlen; size_t c=(okm_len-pos<tlen)?(okm_len-pos):tlen; memcpy(okm+pos,t,c); pos+=c; ctr++;
  }
  OPENSSL_cleanse(prk,sizeof(prk)); OPENSSL_cleanse(t,sizeof(t)); return 1;
}

static int x448_keygen(EVP_PKEY **out_priv, unsigned char pub[X448_PUBLEN]){
  int ok=0; EVP_PKEY_CTX *kctx=EVP_PKEY_CTX_new_id(EVP_PKEY_X448,NULL); if(!kctx) return 0;
  if(EVP_PKEY_keygen_init(kctx)!=1) goto done;
  if(EVP_PKEY_keygen(kctx,out_priv)!=1) goto done;
  size_t publen=X448_PUBLEN;
  if(EVP_PKEY_get_raw_public_key(*out_priv,pub,&publen)!=1 || publen!=X448_PUBLEN) goto done;
  ok=1;
done: EVP_PKEY_CTX_free(kctx); if(!ok) fprintf(stderr,"X448 keygen failed\n"); return ok;
}
static int x448_derive(const EVP_PKEY *my_priv,const unsigned char peer_pub[X448_PUBLEN],
                       unsigned char **out,size_t *outlen){
  int ok=0; EVP_PKEY *peer=EVP_PKEY_new_raw_public_key(EVP_PKEY_X448,NULL,peer_pub,X448_PUBLEN);
  EVP_PKEY_CTX *dctx=NULL; if(!peer) goto done;
  dctx=EVP_PKEY_CTX_new((EVP_PKEY*)my_priv,NULL); if(!dctx) goto done;
  if(EVP_PKEY_derive_init(dctx)!=1) goto done;
  if(EVP_PKEY_derive_set_peer(dctx,peer)!=1) goto done;
  if(EVP_PKEY_derive(dctx,NULL,outlen)!=1) goto done;
  *out=OPENSSL_malloc(*outlen); if(!*out) goto done;
  if(EVP_PKEY_derive(dctx,*out,outlen)!=1) goto done;
  ok=1;
done: if(!ok && *out){ OPENSSL_free(*out); *out=NULL; *outlen=0; } EVP_PKEY_free(peer); EVP_PKEY_CTX_free(dctx); return ok;
}
static int ed25519_sign(const unsigned char priv[32],const unsigned char *msg,size_t msglen,unsigned char sig_out[ED25519_SIGLEN]){
  int ok=0; EVP_PKEY *p=EVP_PKEY_new_raw_private_key(EVP_PKEY_ED25519,NULL,priv,32); if(!p) return 0;
  EVP_MD_CTX *md=EVP_MD_CTX_new(); if(!md){ EVP_PKEY_free(p); return 0; }
  if(EVP_DigestSignInit(md,NULL,NULL,NULL,p)!=1) goto done;
  size_t siglen=ED25519_SIGLEN;
  if(EVP_DigestSign(md,sig_out,&siglen,msg,msglen)!=1 || siglen!=ED25519_SIGLEN) goto done;
  ok=1;
done: EVP_MD_CTX_free(md); EVP_PKEY_free(p); return ok;
}
static int ed25519_pub_from_priv(const unsigned char priv[32], unsigned char pub_out[32]){
  EVP_PKEY *p=EVP_PKEY_new_raw_private_key(EVP_PKEY_ED25519,NULL,priv,32); if(!p) return 0;
  size_t publen=32; int r=(EVP_PKEY_get_raw_public_key(p,pub_out,&publen)==1 && publen==32); EVP_PKEY_free(p); return r;
}
static int ed25519_verify(const unsigned char pub[32],const unsigned char *msg,size_t msglen,const unsigned char sig[ED25519_SIGLEN]){
  int ok=0; EVP_PKEY *p=EVP_PKEY_new_raw_public_key(EVP_PKEY_ED25519,NULL,pub,32); if(!p) return 0;
  EVP_MD_CTX *md=EVP_MD_CTX_new(); if(!md){ EVP_PKEY_free(p); return 0; }
  if(EVP_DigestVerifyInit(md,NULL,NULL,NULL,p)!=1) goto done;
  if(EVP_DigestVerify(md,sig,ED25519_SIGLEN,msg,msglen)!=1) goto done;
  ok=1;
done: EVP_MD_CTX_free(md); EVP_PKEY_free(p); return ok;
}

// signature context includes identifier
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

// ---------- sockets ----------
static int open_rx(const cfg_t *cfg,int *ifindex,int *mtu,unsigned char smac_out[ETH_ALEN]){
  int fd=socket(AF_PACKET,SOCK_RAW,htons(ETH_P_ALL)); if(fd<0){ perror("socket(RX)"); return -1; }
  struct ifreq ifr; memset(&ifr,0,sizeof(ifr)); snprintf(ifr.ifr_name,sizeof(ifr.ifr_name),"%s",cfg->ifname);
  if(ioctl(fd,SIOCGIFINDEX,&ifr)<0){ perror("SIOCGIFINDEX"); close(fd); return -1; } *ifindex=ifr.ifr_ifindex;
  if(ioctl(fd,SIOCGIFMTU,&ifr)<0){ perror("SIOCGIFMTU"); close(fd); return -1; } *mtu=ifr.ifr_mtu;
  if(!cfg->have_smac){ if(ioctl(fd,SIOCGIFHWADDR,&ifr)<0){ perror("SIOCGIFHWADDR"); close(fd); return -1;} memcpy(smac_out,ifr.ifr_hwaddr.sa_data,ETH_ALEN);} else memcpy(smac_out,cfg->smac,ETH_ALEN);
  struct sockaddr_ll sll={0}; sll.sll_family=AF_PACKET; sll.sll_protocol=htons(ETH_P_ALL); sll.sll_ifindex=*ifindex;
  if(bind(fd,(struct sockaddr*)&sll,sizeof(sll))<0){ perror("bind(RX)"); close(fd); return -1; }
  int one=1; if(setsockopt(fd,SOL_PACKET,PACKET_IGNORE_OUTGOING,&one,sizeof(one))<0) perror("PACKET_IGNORE_OUTGOING");
  if(cfg->promisc){ struct packet_mreq mr={0}; mr.mr_ifindex=*ifindex; mr.mr_type=PACKET_MR_PROMISC; if(setsockopt(fd,SOL_PACKET,PACKET_ADD_MEMBERSHIP,&mr,sizeof(mr))<0) perror("promisc"); }
  return fd;
}
static int open_tx(const cfg_t *cfg,int ifindex){
  int fd=socket(AF_PACKET,SOCK_RAW,htons((unsigned short)cfg->ethertype)); if(fd<0){ perror("socket(TX)"); return -1; }
  struct sockaddr_ll sll={0}; sll.sll_family=AF_PACKET; sll.sll_protocol=htons((unsigned short)cfg->ethertype); sll.sll_ifindex=ifindex;
  if(bind(fd,(struct sockaddr*)&sll,sizeof(sll))<0){ perror("bind(TX)"); close(fd); return -1; }
  return fd;
}
static int send_l2(const cfg_t *cfg,int tx_fd,int ifindex,const unsigned char smac[ETH_ALEN],const unsigned char dmac[ETH_ALEN],const void *payload,size_t payload_len,const char *what){
  unsigned char frame[MAX_FRAME_SIZE]; size_t off=0;
  memcpy(frame+off,dmac,ETH_ALEN); off+=ETH_ALEN;
  memcpy(frame+off,smac,ETH_ALEN); off+=ETH_ALEN;
  uint16_t et=htons((uint16_t)cfg->ethertype); memcpy(frame+off,&et,2); off+=2;
  memcpy(frame+off,payload,payload_len); size_t plen=payload_len;
  if(plen<MIN_ETH_PAYLOAD){ memset(frame+off+plen,0,MIN_ETH_PAYLOAD-plen); plen=MIN_ETH_PAYLOAD; }
  size_t frame_len=off+plen;
  struct sockaddr_ll to={0}; to.sll_family=AF_PACKET; to.sll_ifindex=ifindex; to.sll_halen=ETH_ALEN; memcpy(to.sll_addr,dmac,ETH_ALEN);
  ssize_t sent=sendto(tx_fd,frame,frame_len,0,(struct sockaddr*)&to,sizeof(to));
  if(sent<0){ perror("sendto"); return -1; }
  DBG1("Sent %s (%zu payload, frame %zu) to %02x:%02x:%02x:%02x:%02x:%02x",what,payload_len,frame_len,dmac[0],dmac[1],dmac[2],dmac[3],dmac[4],dmac[5]);
  return 0;
}

// ---------- usage ----------
static void usage(const char *p){
  fprintf(stderr,
  "Usage: %s -i IFACE -d DEST --my-ed25519-priv HEX32 --peer-ed25519-pub HEX32 [opts]\n"
  "  -c FILE        Load config (key=value); CLI overrides\n"
  "  -y HEX         EtherType (default 88b5)\n"
  "  -s MAC         Override source MAC (default IFACE MAC)\n"
  "  --promisc      Promiscuous RX (normally not needed)\n"
  "  --retry-ms N   Resend interval (default 1000)\n"
  "  --timeout S    Overall timeout (default 20)\n"
  "  --keylen N     Derived key length (bytes, default 32; e.g. 64/128/256)\n"
  "  --identifier STR  Optional identifier (<=32 ASCII), printed on both sides\n"
  "  -t             Request time from responder and set system clock\n"
  "  --raw          Print only key hex\n"
  "  --separate N   Insert ':' every N hex chars in key output\n"
  "  -v / -vv       Verbose / very verbose\n", p);
}

// ---------- main ----------
int main(int argc,char **argv){
  cfg_t cfg={0}; cfg.ethertype=DEFAULT_ETHERTYPE; cfg.retry_ms=1000; cfg.timeout_sec=20; cfg.keylen=32; cfg.sep_group=0;

  const char *cfgpath=NULL;
  for(int i=1;i<argc;i++){ if(!strcmp(argv[i],"-c") && i+1<argc){ cfgpath=argv[i+1]; break; } }
  if(cfgpath){ if(load_config(cfgpath,&cfg)!=0){ fprintf(stderr,"Failed to load config: %s\n", cfgpath); return 1; } }

  for(int i=1;i<argc;i++){
    if(!strcmp(argv[i],"-c")){ i++; continue; }
    if(!strcmp(argv[i],"-i") && i+1<argc){ cfg.ifname=argv[++i]; continue; }
    if(!strcmp(argv[i],"-d") && i+1<argc){ if(parse_mac(argv[++i],cfg.dmac)==0) cfg.have_dmac=1; else {fprintf(stderr,"Bad dest MAC\n"); return 1;} continue; }
    if(!strcmp(argv[i],"-s") && i+1<argc){ if(parse_mac(argv[++i],cfg.smac)==0) cfg.have_smac=1; else {fprintf(stderr,"Bad src MAC\n"); return 1;} continue; }
    if(!strcmp(argv[i],"-y") && i+1<argc){ cfg.ethertype=(unsigned)strtoul(argv[++i],NULL,16); continue; }
    if(!strcmp(argv[i],"--promisc")){ cfg.promisc=1; continue; }
    if(!strcmp(argv[i],"--retry-ms") && i+1<argc){ cfg.retry_ms=atoi(argv[++i]); if(cfg.retry_ms<100) cfg.retry_ms=100; continue; }
    if(!strcmp(argv[i],"--timeout") && i+1<argc){ cfg.timeout_sec=atoi(argv[++i]); continue; }
    if(!strcmp(argv[i],"--raw")){ cfg.raw_only=1; continue; }
    if(!strcmp(argv[i],"--separate") && i+1<argc){ cfg.sep_group=atoi(argv[++i]); if(cfg.sep_group<0) cfg.sep_group=0; continue; }
    if(!strcmp(argv[i],"--keylen") && i+1<argc){ cfg.keylen=atoi(argv[++i]); if(cfg.keylen<16) cfg.keylen=16; if(cfg.keylen>4096) cfg.keylen=4096; continue; }
    if(!strcmp(argv[i],"--identifier") && i+1<argc){ cfg.identifier=argv[++i]; continue; }
    if(!strcmp(argv[i],"-t")){ cfg.want_time=1; continue; }
    if(!strcmp(argv[i],"--my-ed25519-priv") && i+1<argc){ if(from_hex(argv[++i],cfg.my_ed25519_priv,32)==0) cfg.have_my_priv=1; else {fprintf(stderr,"Bad my_ed25519_priv\n"); return 1;} continue; }
    if(!strcmp(argv[i],"--peer-ed25519-pub") && i+1<argc){ if(from_hex(argv[++i],cfg.peer_ed25519_pub,32)==0) cfg.have_peer_pub=1; else {fprintf(stderr,"Bad peer_ed25519_pub\n"); return 1;} continue; }
    if(!strcmp(argv[i],"-v")){ g_verbose=g_verbose<1?1:g_verbose; continue; }
    if(!strcmp(argv[i],"-vv")){ g_verbose=2; continue; }
  }

  if(!cfg.ifname || !cfg.have_dmac || !cfg.have_my_priv || !cfg.have_peer_pub){ usage(argv[0]); return 1; }

  int ifindex=0, mtu=0; unsigned char smac[ETH_ALEN];
  int rx_fd=open_rx(&cfg,&ifindex,&mtu,smac); if(rx_fd<0) return 1;
  int tx_fd=open_tx(&cfg,ifindex); if(tx_fd<0){ close(rx_fd); return 1; }

  DBG1("Interface=%s ifindex=%d MTU=%d", cfg.ifname, ifindex, mtu);
  DBG1("Ethertype=0x%04x VLAN=no", cfg.ethertype);
  DBG1("Mode: %s | Timeout=%ds | Retry=%dms",
       cfg.promisc?"promisc":"non-promisc", cfg.timeout_sec, cfg.retry_ms);

  // x448 ephemeral + hello
  EVP_PKEY *eph_priv=NULL; unsigned char xpub[X448_PUBLEN];
  if(!x448_keygen(&eph_priv,xpub)){ close(rx_fd); close(tx_fd); return 1; }
  unsigned char nonce[NONCE_LEN]; if(RAND_bytes(nonce,NONCE_LEN)!=1){ fprintf(stderr,"RAND_bytes failed\n"); close(rx_fd); close(tx_fd); EVP_PKEY_free(eph_priv); return 1; }
  unsigned char my_edpub[32]; if(!ed25519_pub_from_priv(cfg.my_ed25519_priv,my_edpub)){ fprintf(stderr,"Cannot get Ed25519 pub\n"); close(rx_fd); close(tx_fd); EVP_PKEY_free(eph_priv); return 1; }

  hello_v2_t hi; memset(&hi,0,sizeof(hi));
  memcpy(hi.magic,MAGIC,4); hi.ver=PROTO_VER; hi.type=TYPE_HELLO;
  hi.flags = cfg.want_time ? FLAG_TIME_REQUEST : 0;
  hi.id_len = 0;
  if(cfg.identifier && *cfg.identifier){
    size_t L=strnlen(cfg.identifier,32);
    memcpy(hi.id,cfg.identifier,L);
    hi.id_len=(uint8_t)L;
  }
  memcpy(hi.x448_pub,xpub,X448_PUBLEN);
  memcpy(hi.nonce,nonce,NONCE_LEN);
  memcpy(hi.ed25519_pub,my_edpub,32);
  hi.keylen_be=htons((uint16_t)cfg.keylen);

  unsigned char *sigmsg=NULL; size_t siglen=0;
  build_hello_sigmsg_v2(TYPE_HELLO,hi.flags,hi.keylen_be,hi.id_len,hi.id,hi.x448_pub,hi.nonce,hi.ed25519_pub,&sigmsg,&siglen);
  if(!ed25519_sign(cfg.my_ed25519_priv,sigmsg,siglen,hi.sig)){ fprintf(stderr,"Ed25519 sign failed\n"); OPENSSL_free(sigmsg); close(rx_fd); close(tx_fd); EVP_PKEY_free(eph_priv); return 1; }
  OPENSSL_free(sigmsg);

  // send HELLO(I) initially and start resend schedule
  (void)send_l2(&cfg,tx_fd,ifindex,smac,cfg.dmac,&hi,sizeof(hi),"HELLO(I)");
  uint64_t next_retry = now_ms() + (cfg.retry_ms>0 ? (uint64_t)cfg.retry_ms : 1000);

  // wait HELLO(R)
  unsigned char rxbuf[2048]; hello_v2_t hr; int got_hr=0;
  struct timespec start; clock_gettime(CLOCK_MONOTONIC,&start);

  while(!got_hr){
    struct pollfd pfd={.fd=rx_fd,.events=POLLIN};
    int pr=poll(&pfd,1,100);
    if(pr>0 && (pfd.revents&POLLIN)){
      ssize_t n=recvfrom(rx_fd,rxbuf,sizeof(rxbuf),0,NULL,NULL);
      if(n>= (ssize_t)(14+sizeof(hello_v2_t)) &&
         ntohs(*(uint16_t*)(rxbuf+12))==(uint16_t)cfg.ethertype){
        hello_v2_t *m=(hello_v2_t*)(rxbuf+14);
        if(memcmp(m->magic,MAGIC,4)==0 && m->ver==PROTO_VER && m->type==TYPE_HELLO){
          if(memcmp(m->ed25519_pub,cfg.peer_ed25519_pub,32)!=0){ DBG1("rx HELLO(R) wrong pinned pub"); }
          else {
            unsigned char *peer_sigmsg=NULL; size_t peer_sigmsg_len=0;
            build_hello_sigmsg_v2(TYPE_HELLO,m->flags,m->keylen_be,m->id_len,m->id,m->x448_pub,m->nonce,m->ed25519_pub,&peer_sigmsg,&peer_sigmsg_len);
            if(ed25519_verify(m->ed25519_pub,peer_sigmsg,peer_sigmsg_len,m->sig)){
              memcpy(&hr,m,sizeof(hr)); got_hr=1; DBG1("rx HELLO(R) OK");
            } else { DBG1("rx HELLO(R) bad sig"); }
            OPENSSL_free(peer_sigmsg);
          }
        }
      }
    }
    // resend HELLO(I)
    uint64_t now = now_ms();
    if(!got_hr && now >= next_retry){
      (void)send_l2(&cfg,tx_fd,ifindex,smac,cfg.dmac,&hi,sizeof(hi),"HELLO(I,resend)");
      next_retry = now + (cfg.retry_ms>0 ? (uint64_t)cfg.retry_ms : 1000);
    }
    // timeout?
    if(cfg.timeout_sec>=0){
      struct timespec nowts; clock_gettime(CLOCK_MONOTONIC,&nowts);
      int elapsed=(int)((nowts.tv_sec-start.tv_sec)+(nowts.tv_nsec-start.tv_nsec)/1e9);
      if(elapsed>=cfg.timeout_sec){ fprintf(stderr,"[%s] ERROR: timeout waiting HELLO(R)\n",ts()); close(rx_fd); close(tx_fd); EVP_PKEY_free(eph_priv); return 2; }
    }
  }

  // derive
  unsigned char *ss=NULL; size_t ss_len=0;
  if(!x448_derive(eph_priv,hr.x448_pub,&ss,&ss_len)){ fprintf(stderr,"X448 derive failed\n"); close(rx_fd); close(tx_fd); EVP_PKEY_free(eph_priv); return 1; }
  EVP_PKEY_free(eph_priv);

  uint16_t keylen = ntohs(hi.keylen_be);
  if(keylen<16) keylen=16; if(keylen>4096) keylen=4096;

  unsigned char *K=OPENSSL_malloc(keylen); if(!K){ fprintf(stderr,"OOM K\n"); OPENSSL_free(ss); close(rx_fd); close(tx_fd); return 1; }
  unsigned char Kmac[HMAC_LEN];

  const unsigned char info_key[]="L2DHv2 key";
  const unsigned char info_mac[]="L2DHv2 mac";
  if(!hkdf_sha512(ss,ss_len,NULL,0,info_key,sizeof(info_key)-1,K,keylen) ||
     !hkdf_sha512(ss,ss_len,NULL,0,info_mac,sizeof(info_mac)-1,Kmac,sizeof(Kmac))){
    fprintf(stderr,"HKDF failed\n"); OPENSSL_free(ss); OPENSSL_free(K); close(rx_fd); close(tx_fd); return 1;
  }
  OPENSSL_cleanse(ss,ss_len); OPENSSL_free(ss);

  // transcript hash
  unsigned char th[64]; transcript_hash_v2(&hi,&hr,th);

  // send FINISH(I) and wait FINISH(R)
  finish_v2_t fi; memset(&fi,0,sizeof(fi));
  memcpy(fi.magic,MAGIC,4); fi.ver=PROTO_VER; fi.type=TYPE_FINISH;
  HMAC_CTX *h = HMAC_CTX_new();
  HMAC_Init_ex(h, Kmac, sizeof(Kmac), EVP_sha512(), NULL);
  HMAC_Update(h, TAG_FIN_I, sizeof(TAG_FIN_I));
  HMAC_Update(h, th, sizeof(th));
  unsigned int maclen=0; HMAC_Final(h, fi.mac, &maclen); HMAC_CTX_free(h);

  (void)send_l2(&cfg,tx_fd,ifindex,smac,cfg.dmac,&fi,sizeof(fi),"FINISH(I)");
  next_retry = now_ms() + (cfg.retry_ms>0 ? (uint64_t)cfg.retry_ms : 1000);

  int got_fini_r=0;
  while(!got_fini_r){
    struct pollfd pfd={.fd=rx_fd,.events=POLLIN};
    int pr=poll(&pfd,1,100);
    if(pr>0 && (pfd.revents&POLLIN)){
      ssize_t n=recvfrom(rx_fd,rxbuf,sizeof(rxbuf),0,NULL,NULL);
      if(n>= (ssize_t)(14+sizeof(finish_v2_t)) &&
         ntohs(*(uint16_t*)(rxbuf+12))==(uint16_t)cfg.ethertype){
        finish_v2_t *fr=(finish_v2_t*)(rxbuf+14);
        if(memcmp(fr->magic,MAGIC,4)==0 && fr->ver==PROTO_VER && fr->type==TYPE_FINISH){
          unsigned char expect[HMAC_LEN]; unsigned int elen=0;
          HMAC_CTX *vh = HMAC_CTX_new();
          HMAC_Init_ex(vh, Kmac, sizeof(Kmac), EVP_sha512(), NULL);
          HMAC_Update(vh, TAG_FIN_R, sizeof(TAG_FIN_R));
          HMAC_Update(vh, th, sizeof(th));
          HMAC_Update(vh, (unsigned char*)&fr->time_sec_be, 8);
          HMAC_Update(vh, (unsigned char*)&fr->time_nsec_be, 4);
          HMAC_Final(vh, expect, &elen); HMAC_CTX_free(vh);

          if (elen == HMAC_LEN && CRYPTO_memcmp(expect, fr->mac, HMAC_LEN) == 0) {
            DBG1("rx FINISH(R) OK (HMAC match)");
            if (cfg.want_time && fr->time_sec_be) {
              uint64_t sec = be64toh_u64(fr->time_sec_be);
              uint32_t nsec = ntohl(fr->time_nsec_be);
              struct timespec rt; rt.tv_sec = (time_t)sec; rt.tv_nsec = (long)nsec;
              if (clock_settime(CLOCK_REALTIME, &rt) != 0) {
                fprintf(stderr, "[%s] WARN: clock_settime failed: %s\n", ts(), strerror(errno));
              } else {
                DBG1("System time set to responder time (%llu.%09u)",
                     (unsigned long long)sec, nsec);
              }
            }
            got_fini_r=1; break;
          } else {
            DBG1("rx FINISH(R) HMAC MISMATCH");
            hexdump2("finish_r_mac(expect)", expect, HMAC_LEN);
            hexdump2("finish_r_mac(rx)", fr->mac, HMAC_LEN);
          }
        }
      }
    }
    uint64_t now = now_ms();
    if(!got_fini_r && now >= next_retry){
      (void)send_l2(&cfg,tx_fd,ifindex,smac,cfg.dmac,&fi,sizeof(fi),"FINISH(I,resend)");
      next_retry = now + (cfg.retry_ms>0 ? (uint64_t)cfg.retry_ms : 1000);
    }
    if(cfg.timeout_sec>=0){
      struct timespec nowts; clock_gettime(CLOCK_MONOTONIC,&nowts);
      int elapsed=(int)((nowts.tv_sec-start.tv_sec)+(nowts.tv_nsec-start.tv_nsec)/1e9);
      if(elapsed>=cfg.timeout_sec){ fprintf(stderr,"[%s] ERROR: timeout waiting FINISH(R)\n",ts()); OPENSSL_free(K); close(rx_fd); close(tx_fd); return 3; }
    }
  }

  // ----- Success / print -----
  if (cfg.raw_only) {
    if (cfg.identifier && *cfg.identifier)
      printf("%s:", cfg.identifier);
    print_hex_grouped(K, keylen, cfg.sep_group);
    putchar('\n');
  } else {
    printf("=== L2DH success (initiator) ===\n");
    if (cfg.identifier && *cfg.identifier)
      printf("Identifier: %s\n", cfg.identifier);
    printf("Session key (%u bytes):\n  hex = ", (unsigned)keylen);
    print_hex_grouped(K, keylen, cfg.sep_group);
    char *b = b64(K,keylen);
    if(b){ printf("\n  b64 = %s", b); OPENSSL_free(b); }
    unsigned char fph[32]; SHA256(K,keylen,fph);
    printf("\nFingerprint (SHA-256(key) first 8 bytes): %02x%02x%02x%02x %02x%02x%02x%02x\n",
           fph[0],fph[1],fph[2],fph[3],fph[4],fph[5],fph[6],fph[7]);
  }

  OPENSSL_cleanse(K,keylen); OPENSSL_free(K);
  close(rx_fd); close(tx_fd);
  return 0;
}
