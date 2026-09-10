/* Isolated transfer prototype, not linked into production.
 * uint64_t leanos_copy_root_transfer(uint64_t closed_root, uint64_t copy_root,
 *     const struct { uint64_t source, destination; } *trusted_operands,
 *     uint64_t count);
 *
 * The caller must supply the admitted UserCopyOperands sequence (at most
 * sixteen byte pairs), held in immutable kernel-owned memory. This is NOT
 * an interface for unvalidated user pointers. All roots map code, stack,
 * operands and exception-entry data; the copy root provides exactly the
 * admitted aliases. The closed root omits every protected-frame alias.
 *
 * IF, PCID and PGE constraints and unconditional reload/readback are enforced
 * by the existing helper. NMI/fault entry must independently restore the
 * closed root before any C code; those handlers are not implemented here.
 * A fault may leave a completed destination prefix and never implies rollback.
 * Normal return occurs only after reloading/verifying the closed root.
 */
.section .text.copy_root_transfer,"ax",@progbits
.code64
.global leanos_copy_root_transfer
.type leanos_copy_root_transfer,@function
leanos_copy_root_transfer:
    push %rbx
    push %r12
    push %r13
    push %r14
    push %r15
    mov %rdi, %r12
    mov %rsi, %r13
    mov %rdx, %r14
    mov %rcx, %r15
    /* Establish closure even for a rejected length or a zero-byte request. */
    call leanos_copy_root_reload
    cmp $16, %r15
    ja leanos_copy_root_terminal
    xor %ebx, %ebx
    test %r15, %r15
    jz .Ltransfer_return
    mov %r13, %rdi
    call leanos_copy_root_reload
.Ltransfer_byte:
    mov (%r14), %r10
    mov 8(%r14), %r11
 .global leanos_copy_transfer_load
leanos_copy_transfer_load:
    movb (%r10), %al
 .global leanos_copy_transfer_store
leanos_copy_transfer_store:
    movb %al, (%r11)
    inc %rbx
    add $16, %r14
    cmp %r15, %rbx
    jb .Ltransfer_byte
    mov %r12, %rdi
    call leanos_copy_root_reload
.Ltransfer_return:
    mov %rbx, %rax
    pop %r15
    pop %r14
    pop %r13
    pop %r12
    pop %rbx
    ret
.size leanos_copy_root_transfer, .-leanos_copy_root_transfer
.section .note.GNU-stack,"",@progbits
