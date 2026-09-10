/* QEMU-only Multiboot2 fixture; no production entry/CPL3 admission. */
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
    mov $value_a, %eax
    or $3, %eax
    mov %eax, leaves_a+0x3800
    mov %eax, leaves_b+0x3800
#if FIXTURE == 7 || FIXTURE == 9 || FIXTURE == 10
    movl $0, leaves_b+0x3800
    /* Omit identity aliases of both protected backing frames as well. */
    mov $value_a, %eax
    shr $9, %eax
    movl $0, leaves_b(%eax)
    mov $value_b, %eax
    shr $9, %eax
    movl $0, leaves_b(%eax)
#endif
    mov $0x20, %eax
    mov %eax, %cr4
    mov $root_a, %eax
    mov %eax, %cr3
    mov $0xc0000080, %ecx
    rdmsr
#ifdef TRANSFER_FIXTURE
    or $0x900, %eax
#else
    or $0x100, %eax
#endif
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
#if FIXTURE == 7 || FIXTURE == 9 || FIXTURE == 10
    lea page_fault(%rip), %rax
    lea idt64+14*16(%rip), %rdi
    movw %ax, (%rdi)
    movw $8, 2(%rdi)
    movb $0, 4(%rdi)
    movb $0x8e, 5(%rdi)
    shr $16, %rax
    movw %ax, 6(%rdi)
#if FIXTURE == 9
    lea nmi_entry(%rip), %rax
    lea idt64+2*16(%rip), %rdi
    movw %ax, (%rdi)
    movw $8, 2(%rdi)
    movb $0, 4(%rdi)
    movb $0x8e, 5(%rdi)
    shr $16, %rax
    movw %ax, 6(%rdi)
#endif
    lidt idt_pointer(%rip)
#endif
#ifdef TRANSFER_FIXTURE
#include "transfer-fixture.inc"
#else
#if FIXTURE != 9
    mov $'R', %al
    out %al, $0xe9
#endif
    mov $root_a, %edi
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
#endif
#if FIXTURE == 7 || FIXTURE == 9 || FIXTURE == 10
    mov $0x700000, %esi
#if FIXTURE == 10
    mov $value_a, %esi
#endif
    cmpq $0x111, (%rsi)
    jne failed
#if FIXTURE == 9
    mov $'R', %al
    out %al, $0xe9
nmi_wait:
    hlt
    jmp nmi_wait
nmi_entry:
    /* First software action selects the fixed closed root; no C is called. */
#endif
    mov $root_b, %edi
    call leanos_copy_root_reload
#if FIXTURE == 9
    mov $'N', %al
#else
    mov $'D', %al
#endif
    out %al, $0xe9
faulting_read:
    mov (%rsi), %rax
    jmp failed
#elif FIXTURE != 0
    call leanos_copy_root_reload
    jmp failed
#else
    /* Prime a translation, mutate its PTE, then reload the same root. */
    mov $0x700000, %esi
    cmpq $0x111, (%rsi)
    jne failed
    mov $value_b, %eax
    or $3, %rax
    mov %rax, leaves_a+0x3800
    call leanos_copy_root_reload
    cmp $1, %eax
    jne failed
    cmpq $0x222, (%rsi)
    jne failed
    mov $'S', %al
    out %al, $0xe9
    /* A distinct root retains the first backing frame. */
    mov $root_b, %edi
    call leanos_copy_root_reload
    cmp $1, %eax
    jne failed
    cmpq $0x111, (%rsi)
    jne failed
    mov $'T', %al
    out %al, $0xe9
    mov $'P', %al
    out %al, $0xe9
    mov $0x10, %eax
    out %eax, $0xf4
#endif
#if FIXTURE == 7 || FIXTURE == 9 || FIXTURE == 10
page_fault:
    /* Require a not-present supervisor read at exactly the denied operand. */
    cmpq $0, (%rsp)
    jne failed
    cmpq $faulting_read, 8(%rsp)
    jne failed
    mov %cr2, %rax
#if FIXTURE == 10
    cmp $value_a, %rax
#else
    cmp $0x700000, %rax
#endif
    jne failed
    mov %cr3, %rax
    cmp $root_b, %rax
    jne failed
    mov $'P', %al
    out %al, $0xe9
    mov $0x10, %eax
    out %eax, $0xf4
    jmp failed
#endif
#endif /* TRANSFER_FIXTURE */
failed:
    mov $'F', %al
    out %al, $0xe9
    mov $0x11, %eax
    out %eax, $0xf4
    cli
3:  hlt
    jmp 3b

.section .rodata,"a"
.balign 8
gdt:
.quad 0, 0x00af9a000000ffff, 0x00cf92000000ffff
gdt_pointer:
.word 23
.long gdt
idt_pointer:
.word 4095
.quad idt64
.balign 4096
value_a: .quad 0x111
.balign 4096
value_b: .quad 0x222

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
#ifdef TRANSFER_FIXTURE
.balign 16
transfer_operands: .skip 256
transfer_buffer: .skip 32
#endif
.section .note.GNU-stack,"",@progbits
