#!/usr/bin/env bash
# Build everything the engine cross-check needs, entirely out-of-source.
#
# The VCMI checkout is read-only: both builds put their artefacts under $WORK.
# Run:  ./build.sh && ./run.sh
set -euo pipefail

VCMI_SRC=${VCMI_SRC:-${VCMI_CHECKOUT:-/Users/ivanparfenchuk/Projects/AI/vcmi-upstream}}
WORK=${WORK:-/tmp/vcmi-enginecheck}
HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)

LIB_BUILD="$WORK/vcmi-lib-build"
HARNESS_BUILD="$WORK/vcmi-build"
RUNTIME="$WORK/runtime"

# ---------------------------------------------------------------------------
# 1. libvcmi from source.
#
# The checkout ships a build under $VCMI_SRC/builds, but it is months older than
# the source tree and its enum layout no longer matches the headers, which silently
# corrupts every settings lookup. We always rebuild.
#
# ENABLE_CLIENT stays OFF (we need no graphics), which is why the facade target that
# produces libvcmi.dylib cannot link — it only pulls in the AI backends when the client
# is enabled. We therefore build the `vcmiMain` OBJECT library and link its object files
# directly; see CMakeLists.txt and stubs.cpp.
# ---------------------------------------------------------------------------
echo "==> configuring libvcmi in $LIB_BUILD"
cmake -S "$VCMI_SRC" -B "$LIB_BUILD" \
    -DCMAKE_BUILD_TYPE=RelWithDebInfo \
    -DENABLE_CLIENT=OFF -DENABLE_LAUNCHER=OFF -DENABLE_EDITOR=OFF \
    -DENABLE_TEST=OFF -DENABLE_TRANSLATIONS=OFF -DENABLE_VIDEO=OFF \
    -DENABLE_DISCORD=OFF -DENABLE_MMAI=OFF -DENABLE_NULLKILLER2_AI=OFF \
    -DENABLE_ARENA_AI=OFF -DCOPY_CONFIG_ON_BUILD=OFF

echo "==> building vcmiMain + vcmiLua"
cmake --build "$LIB_BUILD" --target vcmiMain vcmiLua -j"$(sysctl -n hw.ncpu)"

# ---------------------------------------------------------------------------
# 2. The harness itself.
# ---------------------------------------------------------------------------
echo "==> building the harness in $HARNESS_BUILD"
cmake -S "$HERE" -B "$HARNESS_BUILD" -DCMAKE_BUILD_TYPE=RelWithDebInfo \
    -DVCMI_SRC="$VCMI_SRC" \
    -DVCMI_OBJ_DIR="$LIB_BUILD/lib/CMakeFiles/vcmiMain.dir"
cmake --build "$HARNESS_BUILD" -j"$(sysctl -n hw.ncpu)"

# ---------------------------------------------------------------------------
# 3. A working directory the engine will accept.
#
# On macOS VCMIDirs reports dataPaths() = "." only in "development mode", which
# IVCMIDirsUNIX::developmentMode() detects by finding both config/ + Mods/ and a file
# named like a VCMI binary in the current directory (VCMIDirs.cpp:211-217). We give it
# symlinks to the read-only source config and an empty marker file, so the engine loads
# its own config and the H3 data from ~/Library/Application Support/vcmi without us
# writing anything into the checkout.
# ---------------------------------------------------------------------------
echo "==> preparing runtime dir $RUNTIME"
mkdir -p "$RUNTIME"
ln -sfn "$VCMI_SRC/config" "$RUNTIME/config"
ln -sfn "$VCMI_SRC/Mods" "$RUNTIME/Mods"
touch "$RUNTIME/vcmiserver"

echo "==> done. Now run ./run.sh"
