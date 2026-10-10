/* Final link of one subject as a separate, statically linked x86-64
   executable for build-time admission (#492).

   Input is the relocatable object the #484 rule builds with
   subjects/subject.ld (.subject.text and .subject.bss), after the subject
   assembly/ABI policy accepted it.  scripts/build-subject.sh links it with
   this script, runs the Lean checker (leanos-elf-admit,
   LeanOS.ElfAdmission) over the result, and embeds the admitted file in the
   image's reserved range.  The checker, not this script, is the authority:
   it rejects a file whose segments leave the user window, share a page, are
   writable and executable, or misplace the entry point.

   0x1000000 is LeanOS.ElfAdmission.userWindowStart, the first page the boot
   page plan does not map.  Two load segments, each starting on a page:

     text  R-X  the entry stub, then all code
     data  RW-  the 2048-byte stack, read-only data, data and bss */
ENTRY(subject_entry)
PHDRS
{
  text PT_LOAD FLAGS(5);
  data PT_LOAD FLAGS(6);
}
SECTIONS
{
  . = 0x1000000;
  .text : { *(.subject.text) } :text
  . = ALIGN(4096);
  .data : { *(.subject.bss) } :data
  /DISCARD/ : { *(.comment) *(.eh_frame) *(.note .note.*) }
}
