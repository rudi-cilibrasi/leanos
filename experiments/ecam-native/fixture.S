/* Isolated native ECAM primitive fixture; no PCI configuration access. */
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
    mov $pdpt, %eax
    or $3, %eax
    mov %eax, root
    mov $directory, %eax
    or $3, %eax
    mov %eax, pdpt
    xor %ecx, %ecx
1:  mov %ecx, %eax
    shl $21, %eax
    or $0x83, %eax
    mov %eax, directory(,%ecx,8)
    inc %ecx
    cmp $8, %ecx
    jne 1b
    mov $0x20, %eax
    mov %eax, %cr4
    mov $root, %eax
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
    cld
    call fixture_main
2:  cli
    hlt
    jmp 2b

.section .rodata,"a"
.balign 8
gdt:
.quad 0, 0x00af9a000000ffff, 0x00cf92000000ffff
gdt_pointer:
.word 23
.long gdt
.section .bss,"aw",@nobits
.balign 4096
.global root, directory
root: .skip 4096
pdpt: .skip 4096
directory: .skip 4096
stack: .skip 16384
stack_top:
.section .note.GNU-stack,"",@progbits
