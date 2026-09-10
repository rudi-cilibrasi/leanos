/* Included after the shared fixture establishes long mode and the PF gate.
 * FIXTURE=7 makes root_b omit both protected physical frames and first alias.
 * root_a is the copy root; no production kernel or user code is executed. */
    mov $value_b, %eax
    or $3, %rax
    mov %rax, leaves_a+0x3808
    movl $0x80000000, leaves_a+0x3804
    movl $0x80000000, leaves_a+0x380c
    movq $0, leaves_b+0x3808
    /* Initialize a cross-page source and an independent expected byte pattern. */
    xor %ecx, %ecx
.Ltransfer_source:
    lea 0x10(%rcx), %eax
    movb %al, value_a+4088(%rcx)
    inc %ecx
    cmp $16, %ecx
    jne .Ltransfer_source
    xor %ecx, %ecx
.Ltransfer_sentinels:
    movb $0xa5, transfer_buffer(%rcx)
    inc %ecx
    cmp $32, %ecx
    jne .Ltransfer_sentinels
    xor %ecx, %ecx
.Ltransfer_operands:
    mov %rcx, %rax
    shl $4, %rax
    lea 0x700ff8(%rcx), %rdx
    mov %rdx, transfer_operands(%rax)
    lea transfer_buffer+8(%rcx), %rdx
    mov %rdx, transfer_operands+8(%rax)
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
    xor %ecx, %ecx
.Ltransfer_verify:
    mov $0xa5, %eax
    cmp $8, %ecx
    jb .Ltransfer_compare
    cmp $(8+TRANSFER_COUNT), %ecx
    jae .Ltransfer_compare
    lea 8(%rcx), %eax
.Ltransfer_compare:
    cmpb %al, transfer_buffer(%rcx)
    jne failed
    inc %ecx
    cmp $32, %ecx
    jne .Ltransfer_verify
    mov $'T', %al
    out %al, $0xe9
transfer_denied:
    mov 0x700ff8, %rax
    jmp failed
page_fault:
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
