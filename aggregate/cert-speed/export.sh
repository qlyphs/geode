#!/bin/bash
# export.sh <new empty dir> [commit, default HEAD] [baseline, default 0e7a1c9]: the Docker context
# of cert-speed from committed objects only (never from a working tree): aggregate/r3-cert and
# aggregate/cert-speed of the commit, aggregate/r3-cert of the baseline under base/, and the r7
# vectors both include.
set -euo pipefail
OUT=$1
REPO=$(cd "$(dirname "$0")/../.." && pwd)
C=$(git -C "$REPO" rev-parse "${2:-HEAD}")
B=$(git -C "$REPO" rev-parse "${3:-0e7a1c9}")
[ ! -e "$OUT" ] || [ -z "$(ls -A "$OUT")" ] || { echo "$OUT is not empty" >&2; exit 2; }
mkdir -p "$OUT/src/base"
git -C "$REPO" archive "$C" aggregate/r3-cert aggregate/r7-check/expected.txt aggregate/cert-speed | tar -x -C "$OUT/src" --strip-components=1
git -C "$REPO" archive "$B" aggregate/r3-cert aggregate/r7-check/expected.txt | tar -x -C "$OUT/src/base" --strip-components=1
rm -rf "$OUT/src/r3-cert/transcripts" "$OUT/src/base/r3-cert/transcripts"
cp "$OUT/src/cert-speed/Dockerfile" "$OUT/Dockerfile"
echo "$C" >"$OUT/src/COMMIT"
echo "$B" >"$OUT/src/BASELINE"
chmod +x "$OUT/src/cert-speed/"*.sh
du -sh "$OUT"
