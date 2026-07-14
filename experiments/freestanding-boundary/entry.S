.global _start
.extern leanos_transition

.section .text.start,"ax",@progbits
_start:
    mov $0x55, %edi
    mov $0x0f, %esi
    call leanos_transition
    cmp $0x5a, %rax
    sete %dil
    xor $1, %dil
    movzbq %dil, %rdi
    mov $60, %rax
    syscall

.section .note.GNU-stack,"",@progbits
