/* Linker script for one ring-3 subject (#484), used with `ld -r`.

   It does not choose addresses.  It collects the subject's code into one
   text section and its stack, read-only data, data and bss into one page,
   and scripts/build-subject.sh renames the pair to the slot's input sections
   (`.user.c.text`, `.user.c.bss`).  boot/linker.ld then places those at the
   slot's range, and the Lean boot page plan, generated from the linked ELF,
   is the authority on where they live and how they are mapped.

   Layout of the slot (the plan maps exactly these pages for the subject):

     text page (U/S, read-only, executable)
       subject_template_text  first byte; the entry stub, then all code
     stack page (U/S, writable, no-execute), exactly 4096 bytes
       subject_stack          bottom of the stack
       subject_stack_top      top of the stack, 2048 bytes up
       read-only data, data, bss (at most 2048 bytes)

   The text page holds code only, so the build rule can disassemble every
   executable byte.  Read-only data shares the no-execute stack page.  The
   stack sits at the bottom of its page: an overflow runs into the read-only
   text page and faults instead of corrupting data. */
SECTIONS
{
  .subject.text : {
    subject_template_text = .;
    KEEP(*(.subject.entry))
    *(.text .text.*)
  }
  .subject.bss : {
    subject_stack = .;
    . += 2048;
    subject_stack_top = .;
    *(.rodata .rodata.* .data.rel.ro .data.rel.ro.*)
    *(.data .data.*)
    *(.bss .bss.*)
    *(COMMON)
    /* Fails the link ("cannot move location counter backwards") when the
       data does not fit the page. */
    . = 4096;
  }
  /DISCARD/ : { *(.comment) *(.eh_frame) *(.note .note.*) }
}
