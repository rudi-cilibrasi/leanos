ENTRY(_start)
SECTIONS {
  . = 0x100000;
  .multiboot : { KEEP(*(.multiboot)) }
  .text : { *(.text .text.*) }
  .rodata : { *(.rodata .rodata.*) }
  .data : { *(.data .data.*) }
  .bss : { *(.bss .bss.*) *(COMMON) }
  ASSERT(. < 0x180000, "fixture overlaps test aperture")
  /DISCARD/ : { *(.comment) *(.note*) }
}
