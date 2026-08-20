#!/usr/bin/env bash
# Run the cross-check and print the comparison table. Assumes ./build.sh has been run
# (same WORK; default matches build.sh). Fails loudly if the harness binary is missing
# or predates the turn-order cases, instead of silently comparing against a stale build.
set -euo pipefail
WORK=${WORK:-/tmp/vcmi-enginecheck}
HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)

HARNESS="$WORK/vcmi-build/enginecheck"
if [[ ! -x "$HARNESS" ]]; then
    echo "error: $HARNESS not found or not executable." >&2
    echo "Run $HERE/build.sh first (same WORK=$WORK)." >&2
    exit 2
fi
if [[ "$HARNESS" -ot "$HERE/harness.cpp" ]]; then
    echo "error: $HARNESS is older than harness.cpp — rebuild with $HERE/build.sh." >&2
    exit 2
fi

exec python3 "$HERE/compare.py" \
    --harness "$HARNESS" \
    --runtime "$WORK/runtime" "$@"
