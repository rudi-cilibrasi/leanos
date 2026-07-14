.set MB2_MAGIC, 0xe85250d6
.set MB2_ARCH, 0
.set MB2_LENGTH, mb2_end - mb2_start
.set MB2_CHECKSUM, -(MB2_MAGIC + MB2_ARCH + MB2_LENGTH)

.section .multiboot,"a",@progbits
.align 8
mb2_start:
    .long MB2_MAGIC
    .long MB2_ARCH
    .long MB2_LENGTH
    .long MB2_CHECKSUM
    .short 0
    .short 0
    .long 8
mb2_end:

.section .text.boot,"ax",@progbits
.code32
.global multiboot_entry
.type multiboot_entry, @function
multiboot_entry:
    cli
    mov $boot_stack_top, %esp

    /* Identity-map the first GiB with 2 MiB pages. */
    mov $page_directory, %edi
    mov $0x83, %eax
    mov $512, %ecx
1:
    mov %eax, (%edi)
    movl $0, 4(%edi)
    add $0x200000, %eax
    add $8, %edi
    loop 1b

    mov $page_directory, %eax
    or $3, %eax
    mov %eax, page_directory_pointer
    movl $0, page_directory_pointer + 4
    mov $page_directory_pointer, %eax
    or $3, %eax
    mov %eax, page_map_level_4
    movl $0, page_map_level_4 + 4

    mov %cr4, %eax
    or $(1 << 5), %eax
    mov %eax, %cr4
    mov $page_map_level_4, %eax
    mov %eax, %cr3
    mov $0xc0000080, %ecx
    rdmsr
    or $(1 << 8), %eax
    wrmsr
    mov %cr0, %eax
    or $(1 << 31), %eax
    mov %eax, %cr0
    lgdt gdt64_pointer
    ljmp $0x08, $long_mode_entry

.code64
long_mode_entry:
    mov $0x10, %ax
    mov %ax, %ds
    mov %ax, %es
    mov %ax, %ss
    xor %ax, %ax
    mov %ax, %fs
    mov %ax, %gs
    mov $boot_stack_top, %rsp
    xor %rbp, %rbp
    call kernel_main
2:
    cli
    hlt
    jmp 2b
.size multiboot_entry, . - multiboot_entry

.section .rodata.gdt,"a",@progbits
.align 8
gdt64:
    .quad 0
    .quad 0x00af9a000000ffff
    .quad 0x00af92000000ffff
gdt64_end:
gdt64_pointer:
    .word gdt64_end - gdt64 - 1
    .long gdt64

.section .bss,"aw",@nobits
.align 4096
page_map_level_4:
    .skip 4096
page_directory_pointer:
    .skip 4096
page_directory:
    .skip 4096
.align 16
boot_stack:
    .skip 16384
boot_stack_top:

.section .note.GNU-stack,"",@progbits
