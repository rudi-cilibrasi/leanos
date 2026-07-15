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

    /* Identity-map 16 MiB with 4 KiB leaves; only the two explicit user
       ranges receive U/S at the leaf.  Upper levels permit traversal. */
    mov $page_table, %edi
    mov $3, %eax
    mov $4096, %ecx
1:
    mov %eax, (%edi)
    movl $0x80000000, 4(%edi)
    add $0x1000, %eax
    add $8, %edi
    loop 1b

    mov $page_table, %eax
    or $7, %eax
    mov $4, %ecx
    mov $page_directory, %edi
2:
    mov %eax, (%edi)
    movl $0, 4(%edi)
    add $4096, %eax
    add $8, %edi
    loop 2b
    mov $page_directory, %eax
    or $7, %eax
    mov %eax, page_directory_pointer
    mov $page_directory_pointer, %eax
    or $7, %eax
    mov %eax, page_map_level_4
    movl $0, page_map_level_4 + 4

    /* Instruction pages are read-only and executable.  All other leaves
       retain NX; only these two explicit pages receive U/S. */
    mov $__kernel_text_start, %eax
    shr $9, %eax
    and $0x7ff8, %eax
    mov $__kernel_text_end, %ecx
    add $0xfff, %ecx
    shr $9, %ecx
    and $0x7ff8, %ecx
4:
    andl $~2, page_table(%eax)
    andl $0x7fffffff, page_table+4(%eax)
    add $8, %eax
    cmp %ecx, %eax
    jb 4b

    mov $__user_text_start, %eax
    shr $9, %eax
    and $0x7ff8, %eax
    orl $4, page_table(%eax)
    andl $~2, page_table(%eax)
    andl $0x7fffffff, page_table+4(%eax)
    mov $__user_stack_start, %eax
    shr $9, %eax
    and $0x7ff8, %eax
    orl $4, page_table(%eax)

    mov %cr4, %eax
    or $(1 << 5), %eax
    mov %eax, %cr4
    mov $page_map_level_4, %eax
    mov %eax, %cr3
    mov $0xc0000080, %ecx
    rdmsr
    or $((1 << 8) | (1 << 11)), %eax
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
3:
    cli
    hlt
    jmp 3b
.size multiboot_entry, . - multiboot_entry

.section .data.gdt,"aw",@progbits
.align 8
.global gdt64
gdt64:
    .quad 0
    .quad 0x00af9a000000ffff
    .quad 0x00af92000000ffff
    .quad 0x00aff2000000ffff
    .quad 0x00affa000000ffff
    .quad 0
    .quad 0
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
.align 4096
page_table:
    .skip 16384
.align 16
boot_stack:
    .skip 16384
boot_stack_top:

.section .text,"ax",@progbits
.global load_tss
load_tss:
    mov $0x28, %ax
    ltr %ax
    ret
.global enter_user
enter_user:
    pushq $0x1b
    push %rsi
    pushfq
    pop %rax
    or $0x200, %rax
    push %rax
    pushq $0x23
    push %rdi
    iretq

.macro SAVE
    push %rax; push %rbx; push %rcx; push %rdx; push %rbp; push %rsi; push %rdi
    push %r8; push %r9; push %r10; push %r11; push %r12; push %r13; push %r14; push %r15
.endm
.macro RESTORE
    pop %r15; pop %r14; pop %r13; pop %r12; pop %r11; pop %r10; pop %r9; pop %r8
    pop %rdi; pop %rsi; pop %rbp; pop %rdx; pop %rcx; pop %rbx; pop %rax
.endm
.global isr80
isr80:
    SAVE
    mov 112(%rsp), %rdi
    mov 104(%rsp), %rsi
    mov 96(%rsp), %rdx
    mov 88(%rsp), %rcx
    mov 128(%rsp), %r8
    call syscall_handler
    mov %rax, 112(%rsp)
    RESTORE
    iretq
.global isr14
isr14:
    SAVE
    mov 120(%rsp), %rdi
    mov 128(%rsp), %rsi
    mov 136(%rsp), %rdx
    call page_fault_handler
    mov %rax, 128(%rsp)
    RESTORE
    add $8, %rsp
    iretq

.section .user.text,"ax",@progbits
.global user_entry
user_entry:
    mov $0x1b, %ax
    mov %ax, %ds
    mov %ax, %es
    mov $0, %rax
    mov $0, %rbx
    mov $7, %rcx
    mov $1, %rdx
    int $0x80
    mov $99, %rax
    xor %rbx, %rbx
    xor %rcx, %rcx
    xor %rdx, %rdx
    int $0x80
    mov 0, %rax
.global user_fault_recovered
user_fault_recovered:
    mov $255, %rax
    int $0x80
1:  jmp 1b

.section .user.bss,"aw",@nobits
.align 4096
.global user_stack
user_stack:
    .skip 4096
.global user_stack_top
user_stack_top:

.section .note.GNU-stack,"",@progbits
