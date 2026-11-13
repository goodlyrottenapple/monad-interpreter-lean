#!/usr/bin/env bash
# Build the pure interpreter as a closed RV64IM ELF and extract it for Lean.
set -euo pipefail
cd "$(dirname "$0")"
MONAD=${MONAD:-$HOME/monad}
TC=${RISCV_TOOLCHAIN_DIR:-$HOME/riscv_gcc}/bin/riscv64-unknown-elf-
ARCH="-march=rv64im -mabi=lp64 -mcmodel=medany"
FLAGS="$ARCH -O2 -std=gnu++26 -fno-exceptions -fno-rtti -ffunction-sections
  -fdata-sections -fno-pic -fno-jump-tables -w -Wno-template-body
  -DNDEBUG -D_GLIBCXX_HAVE_ALIGNED_ALLOC -D_GNU_SOURCE -DMONAD_ZKVM_ZISK
  -DANKERL_UNORDERED_DENSE_FIXED_LOAD_FACTOR=1
  -I$MONAD/zkvm -I$MONAD -I$MONAD/third_party/ethash_vendor/src
  -I$MONAD/third_party/evmc/include -I$MONAD/third_party/unordered_dense/include
  -I$MONAD/third_party/zkevm-standards/standards -idirafter /usr/include"
SRCS="cxx/pure_interp.cpp cxx/platform.cpp
  $MONAD/category/vm/interpreter/intercode.cpp
  $MONAD/category/vm/runtime/context.cpp
  $MONAD/category/vm/runtime/data.cpp
  $MONAD/category/vm/runtime/exit.cpp"
rm -rf build && mkdir -p build
OBJS=""
for f in $SRCS; do
  b=build/$(basename "$f" .cpp)
  # The platform layer defines memcpy and friends as plain loops; stop GCC
  # from turning those loops back into calls to themselves.
  EXTRA=""
  [ "$(basename "$f")" = platform.cpp ] && EXTRA="-fno-builtin -fno-tree-loop-distribute-patterns"
  ${TC}g++ $FLAGS $EXTRA -S "$f" -o "$b.raw.s"
  python3 tools/lower_w.py < "$b.raw.s" > "$b.s"
  ${TC}g++ $ARCH -c "$b.s" -o "$b.o"
  OBJS="$OBJS $b.o"
done
# setjmp/longjmp are the only objects taken from the toolchain.
(cd build && ${TC}ar x "$(${TC}gcc $ARCH -print-file-name=libc.a)" libc_a-setjmp.o)
${TC}g++ $ARCH -nostartfiles -nostdlib -static -Wl,--gc-sections \
  -Wl,-T,cxx/link.ld -Wl,-Map,build/pure.map $OBJS build/libc_a-setjmp.o \
  -o build/pure.elf
${TC}objdump -d -M no-aliases build/pure.elf > build/pure.dump
${TC}size build/pure.elf
${TC}nm -S --defined-only -C build/pure.elf | python3 tools/symbols.py > build/symbols.txt
