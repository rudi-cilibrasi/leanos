/* The subject entry point (#484), linked first in the subject's text so the
   kernel's code range for the slot starts here.  The kernel enters it at
   CPL3 with RSP at the top of the subject's stack (16-byte aligned) and every
   other general register zero or kernel-chosen.  There is no exit syscall:
   subject_main must not return, and if it does the ud2 below faults and the
   kernel fail-stops. */
.section .subject.entry,"ax",@progbits
.global subject_entry
.type subject_entry, @function
subject_entry:
    call subject_main
    ud2
.size subject_entry, . - subject_entry

.section .note.GNU-stack,"",@progbits
