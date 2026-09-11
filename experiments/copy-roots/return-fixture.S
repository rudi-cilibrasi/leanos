/* Isolated no-SMAP CPL3 return execution fixture. */
.section .multiboot,"a"
.balign 8
header:
.long 0xe85250d6, 0, header_end-header
.long -(0xe85250d6 + (header_end-header))
.short 0, 0
.long 8
header_end:

.section .text,"ax"
.code32
.global _start
_start:
    cli
    mov $stack_top, %esp
    /* Mask PIC interrupts so the IF-rejection fixture reaches the helper. */
    mov $0xff, %al
    out %al, $0x21
    out %al, $0xa1
    xor %ecx, %ecx
1:  mov %ecx, %eax
    shl $12, %eax
    or $3, %eax
    mov %eax, leaves_a(,%ecx,8)
    mov %eax, leaves_b(,%ecx,8)
    inc %ecx
    cmp $4096, %ecx
    jne 1b
    xor %ecx, %ecx
2:  mov %ecx, %eax
    shl $12, %eax
    lea leaves_a(%eax), %edx
    or $3, %edx
    mov %edx, directory_a(,%ecx,8)
    lea leaves_b(%eax), %edx
    or $3, %edx
    mov %edx, directory_b(,%ecx,8)
    inc %ecx
    cmp $8, %ecx
    jne 2b
    mov $directory_a, %eax
    or $3, %eax
    mov %eax, pdpt_a
    mov $directory_b, %eax
    or $3, %eax
    mov %eax, pdpt_b
    mov $pdpt_a, %eax
    or $3, %eax
    mov %eax, root_a
    mov $pdpt_b, %eax
    or $3, %eax
    mov %eax, root_b
    mov $0x20, %eax
    mov %eax, %cr4
    mov $root_a, %eax
    mov %eax, %cr3
    mov $0xc0000080, %ecx
    rdmsr
    or $0x900, %eax
    wrmsr
    lgdt gdt_pointer
    mov %cr0, %eax
    or $0x80000001, %eax
    mov %eax, %cr0
    ljmp $8, $long_mode

.code64
long_mode:
    mov $16, %eax
    mov %ax, %ds
    mov %ax, %es
    mov %ax, %ss
    mov $stack_top, %rsp
    /* Subject-only code and stack; the closed root omits their frames. */
    orq $4, root_b
    orq $4, pdpt_b
    orq $4, directory_b
    mov $user_code, %eax
    shr $9, %eax
    movq $0, leaves_a(%rax)
    orq $4, leaves_b(%rax)
    mov $user_stack, %eax
    shr $9, %eax
    movq $0, leaves_a(%rax)
    orq $4, leaves_b(%rax)
    /* Refresh the closed root after removing the two mappings. */
    mov $root_a, %eax
    mov %rax, %cr3
    mov $tss, %rax
    movw %ax, gdt+42(%rip)
    shr $16, %rax
    movb %al, gdt+44(%rip)
    movb %ah, gdt+47(%rip)
    movq $stack_top, tss+4(%rip)
    movq $nmi_stack_top, tss+36(%rip)
    movq $fault_stack_top, tss+44(%rip)
    movq $df_stack_top, tss+52(%rip)
#if FIXTURE == 14
    movq $nmi_stack_top, tss+44(%rip) /* wrong fault IST negative */
#endif
    movw $104, tss+102(%rip)
    mov $0x28, %eax
    ltr %ax
    lea entered(%rip), %rax
    lea idt64+128*16(%rip), %rdi
    movw %ax, (%rdi)
    movw $8, 2(%rdi)
    movb $0, 4(%rdi)
    movb $0xee, 5(%rdi)
    shr $16, %rax
    movw %ax, 6(%rdi)
    lea nmi_entry(%rip), %rax
    lea idt64+2*16(%rip), %rdi
    movw %ax, (%rdi)
    movw $8, 2(%rdi)
    movb $1, 4(%rdi)
    movb $0x8e, 5(%rdi)
    shr $16, %rax
    movw %ax, 6(%rdi)
    /* Separate ISTs for return faults and failed contributory-fault delivery. */
.macro fault_gate vector, handler, ist
    lea \handler(%rip), %rax
    lea idt64+\vector*16(%rip), %rdi
    movw %ax, (%rdi)
    movw $8, 2(%rdi)
    movb $\ist, 4(%rdi)
    movb $0x8e, 5(%rdi)
    shr $16, %rax
    movw %ax, 6(%rdi)
.endm
    fault_gate 13, gp_entry, 2
    fault_gate 11, np_entry, 2
    fault_gate 12, ss_entry, 2
    fault_gate 8, df_entry, 3
#if FIXTURE == 9 || FIXTURE == 12 || FIXTURE == 13 || FIXTURE == 14
    /* Deliberately violate caller frame validation to exercise terminal entry. */
    movq $0x73, context+128(%rip)
#elif FIXTURE == 10
    andb $0x7f, gdt+37(%rip) /* user code descriptor not present */
#elif FIXTURE == 11
    andb $0x7f, gdt+29(%rip) /* user stack descriptor not present */
#endif
#if FIXTURE == 12
    /* #GP delivery to an absent gate raises #NP, producing #DF. */
    movb $0x0e, idt64+13*16+5(%rip)
#endif
    lidt idt_pointer(%rip)
    mov $'R', %al
    out %al, $0xe9
    mov $context, %rsp
    mov $root_b, %edi
    mov $root_a, %esi
#if FIXTURE == 1
    xor %edi, %edi
#elif FIXTURE == 2
    inc %edi
#elif FIXTURE == 3
    mov $0x1000000, %edi
#elif FIXTURE == 4
    mov %cr4, %rax
    or $0x80, %rax
    mov %rax, %cr4
#elif FIXTURE == 5
    mov %cr4, %rax
    or $0x20000, %rax
    mov %rax, %cr4
#elif FIXTURE == 6
    sti
#elif FIXTURE == 7
    mov $root_b, %esi
#elif FIXTURE == 8
    mov $root_a, %edi
#endif
    jmp leanos_closed_root_return

gp_entry:
    mov $13, %ebx
    jmp fault_entry
np_entry:
    mov $11, %ebx
    jmp fault_entry
ss_entry:
    mov $12, %ebx
    jmp fault_entry
df_entry:
    mov $8, %ebx
fault_entry:
    cli
    mov %cr3, %rdx
    mov $root_a, %eax
#if FIXTURE != 13
    mov %rax, %cr3
#endif
    mov %cr3, %rcx
    cmp %rax, %rcx
    jne failed
    cmp $root_b, %rdx
    jne failed
#if FIXTURE == 12
    cmp $8, %ebx
    jne failed
    cmp $df_stack_top-48, %rsp
    jne failed
    cmpq $0, (%rsp)
#else
    cmp $fault_stack_top-48, %rsp
    jne failed
#if FIXTURE == 9 || FIXTURE == 13 || FIXTURE == 14
    cmp $13, %ebx
    jne failed
    cmpq $0x70, (%rsp)
#elif FIXTURE == 10
    cmp $11, %ebx
    jne failed
    cmpq $0x20, (%rsp)
#elif FIXTURE == 11
    /* QEMU TCG versions report #NP here; Intel specifies #SS. Record which
     * vector arrived, while requiring the same closure for either entry. */
    cmp $11, %ebx
    je 1f
    cmp $12, %ebx
    jne failed
1:  cmpq $0x18, (%rsp)
#else
    jmp failed
#endif
#endif
    jne failed
    /* #DF is an abort: its saved instruction pointer is not restart evidence. */
#if FIXTURE != 12
    /* Audited return.S ends with the two-byte IRETQ, then its terminal. */
    cmpq $leanos_closed_root_return_terminal-2, 8(%rsp)
    jne failed
#endif
    cmpq $8, 16(%rsp)
    jne failed
    cmpq $context+120, 32(%rsp)
    jne failed
    cmpq $0x10, 40(%rsp)
    jne failed
    mov $'E', %al
    out %al, $0xe9
    lea 65(%rbx), %eax
    out %al, $0xe9
    mov $0x10, %eax
    out %eax, $0xf4
    jmp failed

nmi_entry:
    cli
    mov %cr3, %rdx
    mov $root_a, %eax
    mov %rax, %cr3
    mov %cr3, %rcx
    cmp %rax, %rcx
    jne failed
    cmp $root_b, %rdx
    jne failed
    cmp $nmi_stack_top-40, %rsp
    jne failed
    cmpq $8, 8(%rsp)
    jne failed
    cmpq $0x10, 32(%rsp)
    jne failed
    mov $'N', %al
    out %al, $0xe9
    mov $0x10, %eax
    out %eax, $0xf4
    jmp failed

entered:
    /* Record the complete restored GPR bank before any scratch use. */
    push %rax; push %rbx; push %rcx; push %rdx; push %rbp; push %rsi; push %rdi
    push %r8; push %r9; push %r10; push %r11; push %r12; push %r13; push %r14; push %r15
    mov %cr3, %rdx
    mov $root_a, %eax
    mov %rax, %cr3
    mov %cr3, %rcx
    cmp %rax, %rcx
    jne failed
    cmp $root_b, %rdx
    jne failed
    xor %ecx, %ecx
1:  lea 0x100(%rcx), %rax
    cmp %rax, (%rsp,%rcx,8)
    jne failed
    inc %ecx
    cmp $15, %ecx
    jne 1b
    cmpq $user_after_int, 120(%rsp)
    jne failed
    cmpq $0x23, 128(%rsp)
    jne failed
    cmpq $0x202, 136(%rsp)
    jne failed
    cmpq $user_stack_top, 144(%rsp)
    jne failed
    cmpq $0x1b, 152(%rsp)
    jne failed
    mov $'P', %al
    out %al, $0xe9
    mov $0x10, %eax
    out %eax, $0xf4
failed:
    mov $'F', %al
    out %al, $0xe9
    mov $0x11, %eax
    out %eax, $0xf4
    cli
1:  hlt
    jmp 1b

.balign 4096
user_code:
    int $0x80
user_after_int:
    ud2
.balign 4096

.section .data,"aw"
.balign 16
gdt:
.quad 0, 0x00af9a000000ffff, 0x00cf92000000ffff
.quad 0x00cff2000000ffff, 0x00affa000000ffff
.quad 0x0000890000000067, 0
gdt_end:
gdt_pointer:
.word gdt_end-gdt-1
.long gdt
idt_pointer:
.word 4095
.quad idt64
.balign 16
.quad 0, 0
context:
.set regvalue, 0x100
.rept 15
.quad regvalue
.set regvalue, regvalue+1
.endr
.quad user_code, 0x23, 0x202, user_stack_top, 0x1b

.section .bss,"aw",@nobits
.balign 4096
idt64: .skip 4096
root_a: .skip 4096
root_b: .skip 4096
pdpt_a: .skip 4096
pdpt_b: .skip 4096
directory_a: .skip 4096
directory_b: .skip 4096
leaves_a: .skip 32768
leaves_b: .skip 32768
stack: .skip 16384
stack_top:
tss: .skip 104
.balign 4096
nmi_stack: .skip 4096
nmi_stack_top:
.balign 4096
fault_stack: .skip 4096
fault_stack_top:
.balign 4096
df_stack: .skip 4096
df_stack_top:
.balign 4096
user_stack: .skip 4096
user_stack_top:
.section .note.GNU-stack,"",@progbits
