ENTRY(multiboot_entry)

SECTIONS
{
  . = 1M;
  .multiboot : { KEEP(*(.multiboot)) }
  .text : ALIGN(4K) { *(.text.boot) *(.text .text.*) }
  .rodata : ALIGN(4K) { *(.rodata .rodata.*) }
  .data : ALIGN(4K) { *(.data .data.*) }
  .bss : ALIGN(4K) { *(COMMON) *(.bss .bss.*) }
  /DISCARD/ : { *(.comment) *(.eh_frame) *(.note*) }
}
