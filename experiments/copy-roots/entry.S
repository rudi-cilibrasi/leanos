/* Qotom no-SMAP entry/return checkpoint.
 *
 * The subject root maps this code, the TSS entry stack, the trusted root
 * words, and the closed-root tables. Every ordinary entry saves all GPRs
 * before using scratch registers, records the incoming root, reloads and
 * verifies the closed root, and only then calls C. The C dispatcher may alter
 * the saved RAX result and return the already-authorized subject root. The
 * existing closed-root return primitive performs the terminal root switch,
 * restores the complete bank, and executes IRETQ.
 *
 * Exception stubs never resume. They independently reload the closed root and
 * halt. Their entry can interrupt any point after subject-root installation;
 * no STAC/CLAC instruction is reachable in this object.
 */
.section .text.qotom_entry,"ax",@progbits
.code64

.extern leanos_closed_root_return
.extern qotom_entry_closed_root
.extern qotom_entry_subject_root
.extern qotom_entry_observed_root
.extern qotom_entry_dispatch

.macro QOTOM_SAVE
    push %rax; push %rbx; push %rcx; push %rdx; push %rbp; push %rsi; push %rdi
    push %r8; push %r9; push %r10; push %r11; push %r12; push %r13; push %r14; push %r15
.endm

.macro QOTOM_CLOSE_OR_HALT failure
    mov qotom_entry_closed_root(%rip), %r10
    test %r10, %r10
    jz \failure
    test $0xfff, %r10d
    jnz \failure
    mov %r10, %cr3
    mov %cr3, %r11
    cmp %r10, %r11
    jne \failure
.endm

.global qotom_entry_start
.type qotom_entry_start,@function
qotom_entry_start:
    cli
    cld
    /* RDI=subject root, RSI=closed root, RDX=user RIP, RCX=user RSP. */
    mov %rdi, qotom_entry_subject_root(%rip)
    mov %rsi, qotom_entry_closed_root(%rip)
    pushq $0x1b
    push %rcx
    pushq $0x202
    pushq $0x23
    push %rdx
    xor %eax, %eax
    .rept 15
    push %rax
    .endr
    mov qotom_entry_subject_root(%rip), %rdi
    mov qotom_entry_closed_root(%rip), %rsi
    jmp leanos_closed_root_return
.size qotom_entry_start, .-qotom_entry_start

.global qotom_entry_isr80
.type qotom_entry_isr80,@function
qotom_entry_isr80:
    cld
    QOTOM_SAVE
    mov %cr3, %rax
    mov %rax, qotom_entry_observed_root(%rip)
    QOTOM_CLOSE_OR_HALT qotom_entry_entry_terminal
    mov %rsp, %rdi
    call qotom_entry_dispatch
    mov %rax, %rdi
    mov qotom_entry_closed_root(%rip), %rsi
    jmp leanos_closed_root_return
.size qotom_entry_isr80, .-qotom_entry_isr80

/* These terminal stubs deliberately share one instruction shape. Hardware
 * error-code words remain untouched because no path returns or calls C. */
.macro QOTOM_EXCEPTION name
    .global \name
    .type \name,@function
\name:
    cli
    cld
    QOTOM_CLOSE_OR_HALT qotom_entry_exception_unclosed
    jmp qotom_entry_exception_closed
    .size \name, .-\name
.endm

QOTOM_EXCEPTION qotom_entry_isr2
QOTOM_EXCEPTION qotom_entry_isr6
QOTOM_EXCEPTION qotom_entry_isr8
QOTOM_EXCEPTION qotom_entry_isr13
QOTOM_EXCEPTION qotom_entry_isr14

.global qotom_entry_exception_closed
.type qotom_entry_exception_closed,@function
qotom_entry_exception_closed:
    cli
1:  hlt
    jmp 1b
.size qotom_entry_exception_closed, .-qotom_entry_exception_closed

.global qotom_entry_exception_unclosed
.type qotom_entry_exception_unclosed,@function
qotom_entry_exception_unclosed:
    cli
2:  hlt
    jmp 2b
.size qotom_entry_exception_unclosed, .-qotom_entry_exception_unclosed

.global qotom_entry_entry_terminal
.type qotom_entry_entry_terminal,@function
qotom_entry_entry_terminal:
    cli
3:  hlt
    jmp 3b
.size qotom_entry_entry_terminal, .-qotom_entry_entry_terminal

.section .user.a.text,"ax",@progbits
.global qotom_entry_user
.type qotom_entry_user,@function
qotom_entry_user:
    mov $0x2222, %rbx
    mov $0x3333, %rcx
    mov $0x4444, %rdx
    mov $0x5555, %rbp
    mov $0x6666, %rsi
    mov $0x7777, %rdi
    mov $0x8888, %r8
    mov $0x9999, %r9
    mov $0xaaaa, %r10
    mov $0xbbbb, %r11
    movabs $0xc0dec0dec0dec0de, %r12
    movabs $0x51a7e51a7e51a7e5, %r13
    mov $0xeeee, %r14
    mov $0xffff, %r15
    mov $0x51, %rax
    int $0x80
.global qotom_entry_user_after_first
qotom_entry_user_after_first:
    cmp $0x51525354, %rax
    jne qotom_entry_user_failure
    cmp $0x2222, %rbx
    jne qotom_entry_user_failure
    cmp $0x3333, %rcx
    jne qotom_entry_user_failure
    cmp $0x4444, %rdx
    jne qotom_entry_user_failure
    cmp $0x5555, %rbp
    jne qotom_entry_user_failure
    cmp $0x6666, %rsi
    jne qotom_entry_user_failure
    cmp $0x7777, %rdi
    jne qotom_entry_user_failure
    cmp $0x8888, %r8
    jne qotom_entry_user_failure
    cmp $0x9999, %r9
    jne qotom_entry_user_failure
    cmp $0xaaaa, %r10
    jne qotom_entry_user_failure
    cmp $0xbbbb, %r11
    jne qotom_entry_user_failure
    movabs $0xc0dec0dec0dec0de, %rax
    cmp %rax, %r12
    jne qotom_entry_user_failure
    movabs $0x51a7e51a7e51a7e5, %rax
    cmp %rax, %r13
    jne qotom_entry_user_failure
    cmp $0xeeee, %r14
    jne qotom_entry_user_failure
    cmp $0xffff, %r15
    jne qotom_entry_user_failure
    mov $0x52, %rax
    int $0x80
.global qotom_entry_user_after_second
qotom_entry_user_after_second:
qotom_entry_user_failure:
    ud2
.size qotom_entry_user, .-qotom_entry_user

.section .note.GNU-stack,"",@progbits
