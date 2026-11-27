/* QEMU's `virt` board with `-bios none` jumps to the start of RAM at
   0x80000000, so `_start` comes first. The harness uses the first 16 MiB of
   the default 128 MiB. QEMU places its device tree near the end of RAM. The
   stack grows down from the end of the 16 MiB. QEMU zero-fills the part of each
   loadable segment beyond its file contents, which covers `.bss`. */
OUTPUT_ARCH(riscv)
ENTRY(_start)

MEMORY
{
  RAM (rwx) : ORIGIN = 0x80000000, LENGTH = 16M
}

SECTIONS
{
  .text : { KEEP(*(.text.start)) *(.text .text.*) } > RAM
  .rodata : ALIGN(4) { *(.srodata .srodata.*) *(.rodata .rodata.*) } > RAM
  .data : ALIGN(4) { *(.sdata .sdata.*) *(.data .data.*) } > RAM
  .bss : ALIGN(4) { *(.sbss .sbss.*) *(.bss .bss.*) } > RAM
  /DISCARD/ : { *(.eh_frame .eh_frame_hdr) }
}

_stack_top = ORIGIN(RAM) + LENGTH(RAM);
