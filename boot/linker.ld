ENTRY(multiboot_entry)

SECTIONS
{
  . = 1M;
  .multiboot : { KEEP(*(.multiboot)) }
  __kernel_text_start = .;
  .text : ALIGN(4K) { *(.text.boot) *(.text .text.*) }
  __kernel_text_end = .;
  .rodata : ALIGN(4K) { *(.rodata .rodata.*) }
  .data : ALIGN(4K) { *(.data .data.*) }
  .bss : ALIGN(4K) { *(COMMON) *(.bss .bss.*) }
  . = ALIGN(4K);
  __user_text_start = .;
  .user_text : { *(.user.text) }
  __user_text_end = .;
  . = ALIGN(4K);
  __user_stack_start = .;
  .user_bss : { *(.user.bss) }
  __user_stack_end = .;
  /DISCARD/ : { *(.comment) *(.eh_frame) *(.note*) }
}
