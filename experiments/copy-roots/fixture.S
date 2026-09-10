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
    mov $0x20, %eax
    mov %eax, %cr4
    mov $root_a, %eax
    mov %eax, %cr3
    mov $0xc0000080, %ecx
    rdmsr
    or $0x100, %eax
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
    mov $'R', %al
    out %al, $0xe9
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
#if FIXTURE != 0
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
.balign 4096
value_a: .quad 0x111
.balign 4096
value_b: .quad 0x222

.section .bss,"aw",@nobits
.balign 4096
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
.section .note.GNU-stack,"",@progbits
