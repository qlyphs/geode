#!/bin/sh
# For each N: prove + verify under /usr/bin/time -l, then verify the written certificate again in
# a fresh process. Appends everything, with the machine load, to the transcript.
# Usage: CARGO_TARGET_DIR=... R3_OUT=<dir for certificate files> ./run.sh <transcript> <N> [<N> ...]
set -eu
BIN="${CARGO_TARGET_DIR:?}/release/r3-cert"
OUT="$1"; shift
: "${R3_OUT:?}"
export R3_OUT
{
  echo "# r3-cert transcript"
  echo "# host: $(sysctl -n machdep.cpu.brand_string), $(sysctl -n hw.ncpu) logical CPUs, $(($(sysctl -n hw.memsize)/1073741824)) GiB"
  echo "# $(rustc --version)"
  echo "# binary sha256: $(shasum -a 256 "$BIN" | cut -d' ' -f1)"
  echo "# lab commit: $(git -C "$(dirname "$0")" rev-parse --short HEAD)"
} >> "$OUT"
for n in "$@"; do
  echo "## N=$n prove+verify | uptime: $(uptime)" >> "$OUT"
  /usr/bin/time -l "$BIN" run "$n" >> "$OUT" 2>&1 || echo "EXIT $?" >> "$OUT"
  echo "## N=$n verify in a fresh process | uptime: $(uptime)" >> "$OUT"
  /usr/bin/time -l "$BIN" verify "$n" "$R3_OUT/cert-$n.bin" >> "$OUT" 2>&1 || echo "EXIT $?" >> "$OUT"
done
