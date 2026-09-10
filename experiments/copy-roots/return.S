/* Closed-root return primitive; not a C-callable function.
 * Enter by JMP with RSP pointing at the immutable, validated 20-word bank:
 * r15..r8, rdi, rsi, rbp, rdx, rcx, rbx, rax, RIP, CS, RFLAGS, RSP, SS.
 * RDI = authorized pending subject root, RSI = trusted closed root.
 * Both roots/tables and the saved bank remain owned by the caller. Both roots
 * map this code, the complete bank, and all exception-entry data. The target
 * table has already passed policy validation. Numeric checks are not ownership
 * or closure proofs. This primitive does not normalize or validate the frame.
 *
 * Interrupt/fault entry must independently close the root and terminate, even
 * after CR3 installation or during IRET. The guard terminal below only halts;
 * it never reports successful cleanup. No production admission is enabled.
 */
.section .text.closed_root_return,"ax",@progbits
.code64
.global leanos_closed_root_return
.type leanos_closed_root_return,@function
leanos_closed_root_return:
    pushfq
    pop %rdx
    test $0x200, %edx
    jnz leanos_closed_root_return_terminal
    mov %cr4, %rcx
    test $0x20080, %ecx
    jnz leanos_closed_root_return_terminal
    mov %cr3, %rax
    cmp %rsi, %rax
    jne leanos_closed_root_return_terminal
    test %rdi, %rdi
    jz leanos_closed_root_return_terminal
    test $0xfff, %edi
    jnz leanos_closed_root_return_terminal
    cmp $0x1000000, %rdi
    jae leanos_closed_root_return_terminal
    cmp %rsi, %rdi
    je leanos_closed_root_return_terminal
    mov %rdi, %cr3
    mov %cr3, %rax
    cmp %rdi, %rax
    jne leanos_closed_root_return_terminal
    pop %r15
    pop %r14
    pop %r13
    pop %r12
    pop %r11
    pop %r10
    pop %r9
    pop %r8
    pop %rdi
    pop %rsi
    pop %rbp
    pop %rdx
    pop %rcx
    pop %rbx
    pop %rax
    iretq
.size leanos_closed_root_return, .-leanos_closed_root_return

.global leanos_closed_root_return_terminal
.type leanos_closed_root_return_terminal,@function
leanos_closed_root_return_terminal:
    cli
1:  hlt
    jmp 1b
.size leanos_closed_root_return_terminal, .-leanos_closed_root_return_terminal
.section .note.GNU-stack,"",@progbits
