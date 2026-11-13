#!/usr/bin/env bash
# Clone EVMYulLean at the pinned commit and apply this project's changes:
# the port to Lean 4.33.1 / mathlib v4.33.1, and `ffi.ByteArray.zeroes` as a
# Lean definition instead of an opaque extern.
set -euo pipefail
cd "$(dirname "$0")/.."
COMMIT=047f63070309f436b66c61e276ab3b6d1169265a
DIR=spec/EVMYulLean
if [ -d "$DIR" ]; then
  echo "$DIR already exists; remove it to fetch again" >&2
  exit 1
fi
git clone https://github.com/NethermindEth/EVMYulLean "$DIR"
git -C "$DIR" checkout -q -b lean-4.33 "$COMMIT"
git -C "$DIR" apply "$PWD/spec/evmyullean-lean-4.33.patch"
echo "Now, in $DIR: lake update && lake exe cache get && lake build EvmYul"
