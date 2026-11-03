#!/bin/sh
# Hidden-u measurements: for each N, three prove+verify runs under /usr/bin/time -l, each followed
# by a verification of the written certificate in a fresh process; the load average is recorded.
# Usage: CARGO_TARGET_DIR=... R3_OUT=<dir> ./run-h9.sh <transcript> <N> [<N> ...]
set -eu
BIN="${CARGO_TARGET_DIR:?}/release/r3-cert"
OUT="$1"; shift
: "${R3_OUT:?}"
export R3_OUT
{
  echo "# r3-cert hidden-u measurements"
  echo "# host: $(sysctl -n machdep.cpu.brand_string), $(sysctl -n hw.ncpu) logical CPUs, $(($(sysctl -n hw.memsize)/1073741824)) GiB; $(rustc --version); nice -n 10"
  echo "# binary sha256: $(shasum -a 256 "$BIN" | cut -d' ' -f1); lab commit $(git -C "$(dirname "$0")" rev-parse --short HEAD)"
} >> "$OUT"
for n in "$@"; do
  for k in 1 2 3; do
    echo "## N=$n run $k prove+verify | uptime: $(uptime)" >> "$OUT"
    /usr/bin/time -l nice -n 10 "$BIN" h9 "$n" >> "$OUT" 2>&1 || echo "EXIT $?" >> "$OUT"
    echo "## N=$n run $k fresh verify | uptime: $(uptime)" >> "$OUT"
    /usr/bin/time -l nice -n 10 "$BIN" h9verify "$n" "$R3_OUT/h9-cert-$n.bin" >> "$OUT" 2>&1 || echo "EXIT $?" >> "$OUT"
  done
done
