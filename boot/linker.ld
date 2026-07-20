ENTRY(multiboot_entry)

SECTIONS
{
  . = 1M;
  __boot_image_start = .;
  .multiboot : { KEEP(*(.multiboot)) }
  __kernel_text_start = .;
  .text : ALIGN(4K) { *(.text.boot) *(.text .text.*) }
  __kernel_text_end = .;
  .rodata : ALIGN(4K) { *(.rodata .rodata.*) }
  .data : ALIGN(4K) { *(.data .data.*) }
  .df_ist_guard (NOLOAD) : ALIGN(4K) {
    __df_ist_guard_start = .;
    KEEP(*(.df_ist.guard))
    __df_ist_guard_end = .;
  }
  .df_ist_stack (NOLOAD) : ALIGN(4K) {
    __df_ist_stack_start = .;
    KEEP(*(.df_ist.stack))
    __df_ist_stack_end = .;
  }
  .nmi_ist_stack (NOLOAD) : ALIGN(4K) {
    __nmi_ist_stack_start = .;
    KEEP(*(.nmi_ist.stack))
    __nmi_ist_stack_end = .;
  }
  .entry_stack_guard (NOLOAD) : ALIGN(4K) {
    __entry_stack_guard_start = .;
    . += 4K;
    __entry_stack_guard_end = .;
  }
  .entry_stack (NOLOAD) : ALIGN(4K) {
    __entry_stack_start = .;
    KEEP(*(.entry.stack))
    __entry_stack_end = .;
  }
  .bss : ALIGN(4K) { *(COMMON) *(.bss .bss.*) }
  . = ALIGN(4K);
  __user_a_text_start = .;
  .user_a_text : { *(.user.a.text) }
  __user_a_text_end = .;
  . = ALIGN(4K);
  __user_a_stack_start = .;
  .user_a_bss : { *(.user.a.bss) }
  __user_a_stack_end = .;
  . = ALIGN(4K);
  __user_b_text_start = .;
  .user_b_text : { *(.user.b.text) }
  __user_b_text_end = .;
  . = ALIGN(4K);
  __user_b_stack_start = .;
  .user_b_bss : { *(.user.b.bss) }
  __user_b_stack_end = .;
  . = ALIGN(4K);
  __boot_image_end = .;
  /DISCARD/ : { *(.comment) *(.eh_frame) *(.note*) }
}
