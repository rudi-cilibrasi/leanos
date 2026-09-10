ENTRY(_start)
SECTIONS {
  . = 0x100000;
  fixture_image_start = .;
  .multiboot : { KEEP(*(.multiboot)) }
  .text : { *(.text .text.*) }
  .rodata : { *(.rodata .rodata.*) }
  .data : { *(.data .data.*) }
  .bss : { *(.bss .bss.*) *(COMMON) }
  fixture_image_end = .;
  ASSERT(. < 0x700000, "fixture overlaps probe virtual address")
  /DISCARD/ : { *(.comment) *(.note*) }
}
