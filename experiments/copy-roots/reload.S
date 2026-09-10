/* Isolated prototype: linked only into isolated execution fixtures.
 * uint64_t leanos_copy_root_reload(uint64_t trusted_root);
 *
 * Caller obligations: the root is an authorized PML4 in the initial 16 MiB
 * physical arena; all intermediate tables/leaves are validated; the current
 * and target roots map this code, the trusted stack and exception-entry data.
 * NMI/fault entry must establish its own closed root. No user pointer is an
 * admissible argument. Integration must check every entry and return path.
 *
 * Return 1 only after an unconditional CR3 reload and matching readback under
 * disabled PCID/PGE. Invalid preconditions or readback terminate in assembly.
 * Same-root reload is intentional: comparing addresses cannot flush a cache.
 */
.section .text.copy_root_reload,"ax",@progbits
.code64
.global leanos_copy_root_reload
.type leanos_copy_root_reload,@function
leanos_copy_root_reload:
    pushfq
    pop %rdx
    test $0x200, %edx
    jnz leanos_copy_root_terminal
    mov %cr4, %rcx
    test $0x20080, %ecx
    jnz leanos_copy_root_terminal
    test %rdi, %rdi
    jz leanos_copy_root_terminal
    test $0xfff, %edi
    jnz leanos_copy_root_terminal
    cmp $0x1000000, %rdi
    jae leanos_copy_root_terminal
    mov %rdi, %cr3
    mov %cr3, %rax
    cmp %rdi, %rax
    jne leanos_copy_root_terminal
    mov $1, %eax
    ret
.size leanos_copy_root_reload, .-leanos_copy_root_reload

.global leanos_copy_root_terminal
.type leanos_copy_root_terminal,@function
leanos_copy_root_terminal:
    cli
1:  hlt
    jmp 1b
.size leanos_copy_root_terminal, .-leanos_copy_root_terminal
.section .note.GNU-stack,"",@progbits
