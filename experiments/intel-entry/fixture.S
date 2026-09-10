/* Isolated CPL3 instruction fixture, not platform or user-return admission. */
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
    mov $0xff, %al
    out %al, $0x21
    out %al, $0xa1
    xor %ecx, %ecx
1:  mov %ecx, %eax
    shl $12, %eax
    or $3, %eax
    mov %eax, leaves(,%ecx,8)
    inc %ecx
    cmp $4096, %ecx
    jne 1b
    xor %ecx, %ecx
2:  mov %ecx, %eax
    shl $12, %eax
    lea leaves(%eax), %edx
    or $7, %edx
    mov %edx, directory(,%ecx,8)
    inc %ecx
    cmp $8, %ecx
    jne 2b
    mov $directory, %eax
    or $7, %eax
    mov %eax, pdpt
    mov $pdpt, %eax
    or $7, %eax
    mov %eax, root
    mov $user_probe, %eax
    shr $9, %eax
    orl $4, leaves(%eax)
    andl $~2, leaves(%eax)
    mov $user_stack, %eax
    shr $9, %eax
    orl $4, leaves(%eax)
    mov $0x20, %eax
    mov %eax, %cr4
    mov $root, %eax
    mov %eax, %cr3
    /* Extracted verbatim from boot/boot.S by the runner. */
#include "normalization.inc"
    lgdt gdt_pointer
    mov %cr0, %eax
    or $0x80010001, %eax
    mov %eax, %cr0
    ljmp $8, $long_mode

.code64
.macro CHECK_MSR index, expected
    mov $\index, %ecx
    rdmsr
    test %edx, %edx
    jne failed
    cmp $\expected, %eax
    jne failed
.endm
.macro GATE vector, target
    lea \target(%rip), %rax
    lea idt+\vector*16(%rip), %rdi
    movw %ax, (%rdi)
    movw $8, 2(%rdi)
    movb $0x8e, 5(%rdi)
    shr $16, %rax
    movw %ax, 6(%rdi)
.endm
long_mode:
    mov $16, %eax
    mov %ax, %ds
    mov %ax, %es
    mov %ax, %ss
    mov $stack_top, %rsp
    /* Bind the execution fixture to Intel's instruction behavior. */
    xor %eax, %eax
    cpuid
    cmp $0x756e6547, %ebx
    jne failed
    cmp $0x49656e69, %edx
    jne failed
    cmp $0x6c65746e, %ecx
    jne failed
    mov $1, %eax
    cpuid
    cmp $0x30678, %eax
    jne failed
    test $0x1c000000, %ecx
    jne failed
    mov $7, %eax
    xor %ecx, %ecx
    cpuid
    test $0x100000, %ebx
    jne failed
    CHECK_MSR 0xc0000080, 0xd00
    CHECK_MSR 0xc0000081, 0
    CHECK_MSR 0xc0000082, 0
    CHECK_MSR 0xc0000083, 0
    CHECK_MSR 0xc0000084, 0
    CHECK_MSR 0x174, 0
    CHECK_MSR 0x175, 0
    CHECK_MSR 0x176, 0
    mov $tss, %eax
    movw %ax, gdt_tss+2(%rip)
    shr $16, %eax
    movb %al, gdt_tss+4(%rip)
    movb %ah, gdt_tss+7(%rip)
    movq $stack_top, tss+4(%rip)
    movw $104, tss+102(%rip)
    mov $40, %eax
    ltr %ax
    GATE 6, invalid_opcode
    GATE 13, general_protection
    lidt idt_pointer(%rip)
    mov $'R', %al
    out %al, $0xe9
#ifdef WRONG_ORIGIN
    jmp user_probe
#else
    pushq $27
    pushq $user_stack_top
    pushq $2
    pushq $35
    pushq $user_probe
    iretq
#endif
invalid_opcode:
    pushq $0
    pushq $6
    jmp handler
general_protection:
    pushq $13
handler:
#ifndef EXPECTED_VECTOR
#if PROBE == 0
#define EXPECTED_VECTOR 6
#else
#define EXPECTED_VECTOR 13
#endif
#endif
    cmpq $EXPECTED_VECTOR, (%rsp)
    jne failed
    cmpq $0, 8(%rsp)
    jne failed
    cmpq $user_probe, 16(%rsp)
    jne failed
    cmpq $35, 24(%rsp)
    jne failed
#if PROBE == 0
    mov $'6', %al
#else
    mov $'G', %al
#endif
    out %al, $0xe9
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
3:  hlt
    jmp 3b
.section .user,"ax"
.balign 4096
user_probe:
#if PROBE == 0
    syscall
#else
    sysenter
#endif
    ud2
.section .data,"aw"
.balign 8
gdt:
.quad 0, 0x00af9a000000ffff, 0x00cf92000000ffff
.quad 0x00cff2000000ffff, 0x00affa000000ffff
gdt_tss:
.word 103, 0
.byte 0, 0x89, 0, 0
.long 0, 0
gdt_pointer:
.word 55
.quad gdt
idt_pointer:
.word 4095
.quad idt
.section .bss,"aw",@nobits
.balign 4096
root: .skip 4096
pdpt: .skip 4096
directory: .skip 4096
leaves: .skip 32768
idt: .skip 4096
tss: .skip 104
.balign 4096
stack: .skip 16384
stack_top:
.balign 4096
user_stack: .skip 4096
user_stack_top:
.section .note.GNU-stack,"",@progbits
