.section .text
.global extended_state_peer_pke_inject
.type extended_state_peer_pke_inject, @function
extended_state_peer_pke_inject:
    push %rbx
    push %rcx
    push %rdx
    xor %eax, %eax
    cpuid
    cmp $7, %eax
    jb 1f
    mov $7, %eax
    xor %ecx, %ecx
    cpuid
    test $(1 << 3), %ecx
    jz 1f
    mov %cr4, %rax
    or $(1 << 22), %eax
    mov %rax, %cr4
    mov %cr4, %rax
    test $(1 << 22), %eax
    jz 2f
    jmp 3f
1:
    /* KVM cannot expose PKU when the physical host lacks it.  OSXSAVE is a
       separately forbidden live return control and is available because the
       admitted extended-state CPU contract already requires XSAVE. */
    mov $1, %eax
    cpuid
    test $(1 << 26), %ecx
    jz 2f
    mov %cr4, %rax
    or $(1 << 18), %eax
    mov %rax, %cr4
    mov %cr4, %rax
    test $(1 << 18), %eax
    jz 2f
3:
    pop %rdx
    pop %rcx
    pop %rbx
    ret
2:
    ud2
.size extended_state_peer_pke_inject, .-extended_state_peer_pke_inject

.section .note.GNU-stack,"",@progbits
