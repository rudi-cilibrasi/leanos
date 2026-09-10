ENTRY(_start)
SECTIONS {
  . = 0x100000;
  .multiboot : { KEEP(*(.multiboot)) }
  .text : { *(.text .text.*) }
  .user ALIGN(4096) : { *(.user) }
  .data ALIGN(4096) : { *(.data .data.*) }
  .bss ALIGN(4096) : { *(.bss .bss.*) *(COMMON) }
  ASSERT(. < 0x1000000, "fixture outside mapped arena")
  /DISCARD/ : { *(.comment) *(.note*) }
}
