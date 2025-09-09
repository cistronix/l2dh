#!/usr/bin/env bash
# hook.sh — example hook for l2dhd --exec
# - Reads env vars from l2dhd
# - Assembles L2DH_KEY_HEX_1..N into a bash array
# - Prints a JSON object with all fields
# - If jq is present, pretty-prints the JSON

set -euo pipefail

# ---- helpers ----
json_escape() {
  # escape backslash, double-quote, and control characters \n \r \t
  local s=${1-}
  s=${s//\\/\\\\}
  s=${s//\"/\\\"}
  s=${s//$'\n'/\\n}
  s=${s//$'\r'/\\r}
  s=${s//$'\t'/\\t}
  printf '%s' "$s"
}

is_uint() {
  [[ ${1-} =~ ^[0-9]+$ ]]
}

# ---- collect inputs ----
id="${L2DH_ID-}"
len="${L2DH_LEN-}"
key_hex="${L2DH_KEY_HEX-}"
key_b64="${L2DH_KEY_B64-}"
fp8="${L2DH_FP8-}"
peer_mac="${L2DH_PEER_MAC-}"

key_hex_grouped="${L2DH_KEY_HEX_GROUPED-}"
key_hex_count="${L2DH_KEY_HEX_COUNT-}"

# Build bash array from parts if count provided
key_hex_parts=()
if is_uint "${key_hex_count:-}" && (( key_hex_count > 0 )); then
  for (( i=1; i<=key_hex_count; i++ )); do
    var="L2DH_KEY_HEX_${i}"
    part="${!var-}"
    key_hex_parts+=("$part")
  done
fi

# ---- emit JSON (captured) ----
json="$(
  {
    printf '{'

    # required-ish base fields
    printf '"id":"%s",'   "$(json_escape "$id")"
    if is_uint "${len:-}"; then
      printf '"len":%s,' "$len"
    else
      printf '"len":null,'
    fi
    printf '"key_hex":"%s",'  "$(json_escape "$key_hex")"
    printf '"key_b64":"%s",'  "$(json_escape "$key_b64")"
    printf '"fp8":"%s",'      "$(json_escape "$fp8")"
    printf '"peer_mac":"%s",' "$(json_escape "$peer_mac")"

    # optional grouped formatting
    if [[ -n "${key_hex_grouped}" ]]; then
      printf '"key_hex_grouped":"%s",' "$(json_escape "$key_hex_grouped")"
    else
      printf '"key_hex_grouped":null,'
    fi

    if is_uint "${key_hex_count:-}"; then
      printf '"key_hex_count":%s,' "$key_hex_count"
    else
      printf '"key_hex_count":0,'
    fi

    # parts array
    printf '"key_hex_parts":['
    for (( i=0; i<${#key_hex_parts[@]}; i++ )); do
      (( i > 0 )) && printf ','
      printf '"%s"' "$(json_escape "${key_hex_parts[$i]}")"
    done
    printf ']'

    # convenience: RFC3339-ish timestamp from local system clock
    printf ',"received_at":"%s"' "$(date -u +%Y-%m-%dT%H:%M:%SZ 2>/dev/null || true)"

    printf '}\n'
  } 2>/dev/null
)"

# ---- pretty-print if jq is available ----
if command -v jq >/dev/null 2>&1; then
  # -S sorts keys for stable output; drop -S if you prefer original order
  printf '%s' "$json" | jq -S .
else
  # Fallback to compact JSON (original behavior)
  printf '%s' "$json"
fi
