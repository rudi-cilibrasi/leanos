#if TRANSFER_NMI
    lea transfer_nmi_entry(%rip), %rax
    lea idt64+2*16(%rip), %rdi
    movw %ax, (%rdi)
    movw $8, 2(%rdi)
    movb $0, 4(%rdi)
    movb $0x8e, 5(%rdi)
    shr $16, %rax
    movw %ax, 6(%rdi)
#endif
/* Included after the shared fixture establishes long mode and the PF gate.
 * FIXTURE=7 makes root_b omit both protected physical frames and first alias.
 * root_a is the copy root; no production kernel or user code is executed. */
    mov $value_b, %eax
    or $3, %rax
    mov %rax, leaves_a+0x3808
    movl $0x80000000, leaves_a+0x3804
    movl $0x80000000, leaves_a+0x380c
    movq $0, leaves_b+0x3808
#if TRANSFER_FAULT
    /* Remove the second copy alias: exactly eight byte operands precede it. */
    movq $0, leaves_a+0x3808
#endif
    xor %ecx, %ecx
.Luser_sentinels:
    movb $0xa5, value_a+4080(%rcx)
    inc %ecx
    cmp $32, %ecx
    jne .Luser_sentinels
#if !COPY_OUT
    /* Initialize a cross-page source and an independent expected byte pattern. */
    xor %ecx, %ecx
.Ltransfer_source:
    lea 0x10(%rcx), %eax
    movb %al, value_a+4088(%rcx)
    inc %ecx
    cmp $16, %ecx
    jne .Ltransfer_source
#endif
    /* The copy root exposes these frames only through the two admitted
     * aliases, not their bootstrap identity addresses. The helper flushes
     * stale translations before opening the window. */
    mov $value_a, %eax
    shr $9, %eax
    movq $0, leaves_a(%rax)
    mov $value_b, %eax
    shr $9, %eax
    movq $0, leaves_a(%rax)
    xor %ecx, %ecx
.Ltransfer_sentinels:
    movb $0xa5, transfer_buffer(%rcx)
    inc %ecx
    cmp $32, %ecx
    jne .Ltransfer_sentinels
#if COPY_OUT
    xor %ecx, %ecx
.Lkernel_source:
    lea 0x10(%rcx), %eax
    movb %al, transfer_buffer+8(%rcx)
    inc %ecx
    cmp $16, %ecx
    jne .Lkernel_source
#endif
    xor %ecx, %ecx
.Ltransfer_operands:
    mov %rcx, %rax
    shl $4, %rax
#if COPY_OUT
    lea transfer_buffer+8(%rcx), %rdx
    mov %rdx, transfer_operands(%rax)
    lea 0x700ff8(%rcx), %rdx
    mov %rdx, transfer_operands+8(%rax)
#else
    lea 0x700ff8(%rcx), %rdx
    mov %rdx, transfer_operands(%rax)
    lea transfer_buffer+8(%rcx), %rdx
    mov %rdx, transfer_operands+8(%rax)
#endif
    inc %ecx
    cmp $16, %ecx
    jne .Ltransfer_operands
    mov $'R', %al
    out %al, $0xe9
    mov $root_b, %edi
    mov $root_a, %esi
    mov $transfer_operands, %edx
    mov $TRANSFER_COUNT, %ecx
    call leanos_copy_root_transfer
    cmp $TRANSFER_COUNT, %rax
    jne failed
    mov %cr3, %rax
    cmp $root_b, %rax
    jne failed
#if COPY_OUT
    /* Closure was checked before reopening solely to inspect destination
     * memory. This fixture inspection is not part of the transfer helper. */
    mov $root_a, %edi
    call leanos_copy_root_reload
    mov $0x700ff0, %esi
#else
    mov $transfer_buffer, %esi
#endif
    xor %ecx, %ecx
.Ltransfer_verify:
    mov $0xa5, %eax
    cmp $8, %ecx
    jb .Ltransfer_compare
    cmp $(8+TRANSFER_COUNT), %ecx
    jae .Ltransfer_compare
    lea 8(%rcx), %eax
.Ltransfer_compare:
    cmpb %al, (%rsi,%rcx)
    jne failed
    inc %ecx
    cmp $32, %ecx
    jne .Ltransfer_verify
#if COPY_OUT
    /* Copy-out must also preserve all kernel source bytes and sentinels. */
    xor %ecx, %ecx
.Lsource_verify:
    mov $0xa5, %eax
    cmp $8, %ecx
    jb .Lsource_compare
    cmp $24, %ecx
    jae .Lsource_compare
    lea 8(%rcx), %eax
.Lsource_compare:
    cmpb %al, transfer_buffer(%rcx)
    jne failed
    inc %ecx
    cmp $32, %ecx
    jne .Lsource_verify
    mov $root_b, %edi
    call leanos_copy_root_reload
#endif
    mov $'T', %al
    out %al, $0xe9
transfer_denied:
    mov 0x700ff8, %rax
    jmp failed
page_fault:
#if TRANSFER_FAULT
    /* First action establishes closure from a fixed trusted operand. No C,
     * resume or rollback occurs; the completed prefix stays in memory. */
    mov $root_b, %edi
    call leanos_copy_root_reload
#if COPY_OUT
    cmpq $2, (%rsp)
    jne failed
    cmpq $leanos_copy_transfer_store, 8(%rsp)
#else
    cmpq $0, (%rsp)
    jne failed
    cmpq $leanos_copy_transfer_load, 8(%rsp)
#endif
    jne failed
    cmp $8, %rbx
    jne failed
    mov %cr2, %rax
    cmp $0x701000, %rax
    jne failed
    mov %cr3, %rax
    cmp $root_b, %rax
    jne failed
    mov $'X', %al
    out %al, $0xe9
    jmp leanos_copy_root_terminal
#else
    /* Observe an already closed root: this probe must not repair it. */
    cmpq $0, (%rsp)
    jne failed
    cmpq $transfer_denied, 8(%rsp)
    jne failed
    mov %cr2, %rax
    cmp $0x700ff8, %rax
    jne failed
    mov %cr3, %rax
    cmp $root_b, %rax
    jne failed
    mov $'P', %al
    out %al, $0xe9
    mov $0x10, %eax
    out %eax, $0xf4
    jmp failed
#endif /* TRANSFER_FAULT */

#if TRANSFER_NMI
transfer_nmi_entry:
    mov $root_b, %edi
    call leanos_copy_root_reload
    cmp $8, %rbx
    jne failed
    mov (%rsp), %rax
    cmp $leanos_copy_transfer_nmi_wait, %rax
    jb failed
    cmp $leanos_copy_transfer_nmi_wait_end, %rax
    jae failed
    mov %cr3, %rax
    cmp $root_b, %rax
    jne failed
    mov $'N', %al
    out %al, $0xe9
    jmp leanos_copy_root_terminal
#endif
