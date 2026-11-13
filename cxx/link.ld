ENTRY(monad_pure_execute)
MEMORY { ROM (rx) : ORIGIN = 0x80000000, LENGTH = 16M
         RAM (rw) : ORIGIN = 0xa0000000, LENGTH = 256M }
SECTIONS {
  .text : { *(.text .text.*) } > ROM
  .rodata : { *(.rodata .rodata.* .srodata .srodata.*) } > RAM
  .data : { *(.data .data.* .sdata .sdata.* .data.rel.ro*) } > RAM
  .bss : { *(.bss .bss.* .sbss .sbss.* COMMON) } > RAM
  . = ALIGN(32);
  monad_pure_heap = .;
  . = . + 64M;
  monad_pure_heap_end = .;
  /DISCARD/ : { *(.eh_frame*) *(.comment) *(.riscv.attributes) *(.note*) }
}
