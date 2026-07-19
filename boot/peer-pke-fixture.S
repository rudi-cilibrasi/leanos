.section .text
.global extended_state_peer_pke_inject
.type extended_state_peer_pke_inject, @function
extended_state_peer_pke_inject:
    mov %cr4, %rax
    or $(1 << 22), %eax
    mov %rax, %cr4
    mov %cr4, %rax
    test $(1 << 22), %eax
    jz 1f
    ret
1:
    ud2
.size extended_state_peer_pke_inject, .-extended_state_peer_pke_inject

.section .note.GNU-stack,"",@progbits
