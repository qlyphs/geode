#!/bin/bash
# export.sh <new empty dir> [commit, default HEAD]: the Docker context of cert-prover from
# committed objects only (never from a working tree): aggregate/r3-cert, the r7 vectors it
# includes, and aggregate/r10-jobs.
set -euo pipefail
OUT=$1
REPO=$(cd "$(dirname "$0")/../.." && pwd)
C=$(git -C "$REPO" rev-parse "${2:-HEAD}")
[ ! -e "$OUT" ] || [ -z "$(ls -A "$OUT")" ] || { echo "$OUT is not empty" >&2; exit 2; }
mkdir -p "$OUT/src"
git -C "$REPO" archive "$C" aggregate/r3-cert aggregate/r7-check/expected.txt aggregate/r10-jobs | tar -x -C "$OUT/src" --strip-components=1
rm -rf "$OUT/src/r3-cert/transcripts"
cp "$OUT/src/r10-jobs/Dockerfile" "$OUT/Dockerfile"
echo "$C" >"$OUT/src/COMMIT"
chmod +x "$OUT/src/r10-jobs/"*.sh
du -sh "$OUT"
