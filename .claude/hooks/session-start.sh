#!/bin/bash
# Bootstraps a cloud session for building the Lean proofs: the Lean toolchain
# (elan), the Python zstandard package, the Rust targets CI lints, and the CI
# build cache (lean/README.md, "Restoring the CI build cache"). Each step is
# skipped when it is already done.
set -euo pipefail

if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ]; then
  exit 0
fi

cd "${CLAUDE_PROJECT_DIR:-.}"

if ! command -v elan >/dev/null 2>&1 && [ ! -x "$HOME/.elan/bin/elan" ]; then
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none >&2
fi
export PATH="$HOME/.elan/bin:$PATH"
echo "export PATH=\"\$HOME/.elan/bin:\$PATH\"" >> "${CLAUDE_ENV_FILE:-/dev/null}"

# The toolchain lean/lean-toolchain names (elan installs it on first use).
(cd lean && lean --version >&2)

python3 -c 'import zstandard' 2>/dev/null || pip install -q zstandard >&2

for t in i686-unknown-linux-gnu aarch64-unknown-linux-gnu armv7-unknown-linux-gnueabihf \
    powerpc64le-unknown-linux-gnu riscv64gc-unknown-linux-gnu; do
  rustup target list --installed 2>/dev/null | grep -qx "$t" || rustup target add "$t" >&2
done

# Emit.lean maps every module it loads (lean/README.md).
sysctl -w vm.max_map_count=262144 >/dev/null 2>&1 || true

# The CI build cache, once: lean/.lake is ignored by git, so the marker goes
# with the build.
marker=lean/.lake/.session-start-cache
if [ ! -f "$marker" ]; then
  set -o pipefail
  python3 ci/fetch_lean_cache.py \
    | python3 -c 'import sys, zstandard; zstandard.ZstdDecompressor().copy_stream(sys.stdin.buffer, sys.stdout.buffer)' \
    | python3 ci/lean_cache.py unpack lean >&2
  touch "$marker"
fi
