.set MB2_MAGIC, 0xe85250d6
.set MB2_ARCH, 0
.set MB2_LENGTH, mb2_end - mb2_start
.set MB2_CHECKSUM, -(MB2_MAGIC + MB2_ARCH + MB2_LENGTH)
.set PAGE_TABLE_COUNT, 8
.set PAGE_ENTRY_COUNT, 512 * PAGE_TABLE_COUNT

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
    mov $page_table_a, %edi
    mov $3, %eax
    mov $PAGE_ENTRY_COUNT, %ecx
1:
    mov %eax, (%edi)
    movl $0x80000000, 4(%edi)
    add $0x1000, %eax
    add $8, %edi
    loop 1b

    mov $page_table_a, %eax
    or $7, %eax
    mov $PAGE_TABLE_COUNT, %ecx
    mov $page_directory_a, %edi
2:
    mov %eax, (%edi)
    movl $0, 4(%edi)
    add $4096, %eax
    add $8, %edi
    loop 2b
    mov $page_directory_a, %eax
    or $7, %eax
    mov %eax, page_directory_pointer_a
    mov $page_directory_pointer_a, %eax
    or $7, %eax
    mov %eax, page_map_level_4_a
    movl $0, page_map_level_4_a + 4

    /* Address space B starts from the same supervisor-only identity map. */
    mov $page_table_b, %edi
    mov $3, %eax
    mov $PAGE_ENTRY_COUNT, %ecx
5:
    mov %eax, (%edi)
    movl $0x80000000, 4(%edi)
    add $0x1000, %eax
    add $8, %edi
    loop 5b
    mov $page_table_b, %eax
    or $7, %eax
    mov $PAGE_TABLE_COUNT, %ecx
    mov $page_directory_b, %edi
6:
    mov %eax, (%edi)
    movl $0, 4(%edi)
    add $4096, %eax
    add $8, %edi
    loop 6b
    mov $page_directory_b, %eax
    or $7, %eax
    mov %eax, page_directory_pointer_b
    mov $page_directory_pointer_b, %eax
    or $7, %eax
    mov %eax, page_map_level_4_b
    movl $0, page_map_level_4_b + 4

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
    andl $~2, page_table_a(%eax)
    andl $0x7fffffff, page_table_a+4(%eax)
    andl $~2, page_table_b(%eax)
    andl $0x7fffffff, page_table_b+4(%eax)
    add $8, %eax
    cmp %ecx, %eax
    jb 4b

    mov $__user_a_text_start, %eax
    shr $9, %eax
    and $0x7ff8, %eax
    orl $4, page_table_a(%eax)
    andl $~2, page_table_a(%eax)
    andl $0x7fffffff, page_table_a+4(%eax)
    mov $__user_a_stack_start, %eax
    shr $9, %eax
    and $0x7ff8, %eax
    orl $4, page_table_a(%eax)
    mov $__user_b_text_start, %eax
    shr $9, %eax
    and $0x7ff8, %eax
    orl $4, page_table_b(%eax)
    andl $~2, page_table_b(%eax)
    andl $0x7fffffff, page_table_b+4(%eax)
    mov $__user_b_stack_start, %eax
    shr $9, %eax
    and $0x7ff8, %eax
    orl $4, page_table_b(%eax)

    mov %cr4, %eax
    or $(1 << 5), %eax
    mov %eax, %cr4
    mov $page_map_level_4_a, %eax
    mov %eax, %cr3
    mov $0xc0000080, %ecx
    rdmsr
    or $((1 << 8) | (1 << 11)), %eax
    wrmsr
    /* Construction is complete before paging and supervisor write protection. */
    mov %cr0, %eax
    or $((1 << 31) | (1 << 16)), %eax
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
.global page_map_level_4_a
page_map_level_4_a:
    .skip 4096
page_directory_pointer_a:
    .skip 4096
page_directory_a:
    .skip 4096
.align 4096
page_table_a:
    .skip 4096 * PAGE_TABLE_COUNT
page_table_a_end:
.global page_map_level_4_b
page_map_level_4_b:
    .skip 4096
page_directory_pointer_b:
    .skip 4096
page_directory_b:
    .skip 4096
.align 4096
page_table_b:
    .skip 4096 * PAGE_TABLE_COUNT
page_table_b_end:
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
.global enable_smep
enable_smep:
    /* Called after the page-fault gate and TSS are installed. */
    mov %cr4, %rax
    bts $20, %rax
    mov %rax, %cr4
    ret
.global run_wp_probe
run_wp_probe:
.global wp_probe_instruction
wp_probe_instruction:
    movb $0, wp_probe_target(%rip)
.global wp_probe_recovered
wp_probe_recovered:
    ret
.global wp_probe_target
wp_probe_target:
    nop
.global run_smep_probe
run_smep_probe:
.global smep_probe_instruction
smep_probe_instruction:
    jmp user_a_entry
.global smep_probe_recovered
smep_probe_recovered:
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
    cmp $0xfeed, %rax
    jne 7f
    movq $user_b_entry, 120(%rsp)
    movq $user_b_stack_top, 144(%rsp)
    movq $page_map_level_4_b, %rax
    mov %rax, %cr3
    xor %rax, %rax
7:
    mov %rax, 112(%rsp)
    RESTORE
    iretq
.global isr14
isr14:
    SAVE
    sub $8, %rsp
    mov 128(%rsp), %rdi
    mov 136(%rsp), %rsi
    mov 144(%rsp), %rdx
    mov %cr2, %rcx
    call page_fault_handler
    mov %rax, 136(%rsp)
    add $8, %rsp
    RESTORE
    add $8, %rsp
    iretq
.global isr32
isr32:
    SAVE
    mov 128(%rsp), %rdi
    call timer_handler
    /* The modeled one-shot scheduler selected B.  Install its fresh frame
       before CR3 so no instruction is fetched with mismatched identity. */
    movq $user_b_entry, 120(%rsp)
    movq $user_b_stack_top, 144(%rsp)
    movabs $0xc0dec0dec0dec0de, %rax
    mov %rax, 24(%rsp)
    movabs $0x51a7e51a7e51a7e5, %rax
    mov %rax, 16(%rsp)
    movq $page_map_level_4_b, %rax
    mov %rax, %cr3
    call switch_complete
    RESTORE
    iretq

.section .user.a.text,"ax",@progbits
.global user_a_entry
user_a_entry:
    mov $0x1b, %ax
    mov %ax, %ds
    mov %ax, %es
    mov $1, %rax
    xor %rbx, %rbx
    xor %rcx, %rcx
    xor %rdx, %rdx
    int $0x80
1:  jmp 1b

.section .user.a.bss,"aw",@nobits
.align 4096
.global user_a_stack
user_a_stack:
    .skip 4096
.global user_a_stack_top
user_a_stack_top:

.section .user.b.text,"ax",@progbits
.global user_b_entry
user_b_entry:
    mov $0x1b, %ax
    mov %ax, %ds
    mov %ax, %es
    movabs $0xc0dec0dec0dec0de, %rax
    cmp %rax, %r12
    jne 2f
    movabs $0x51a7e51a7e51a7e5, %rax
    cmp %rax, %r13
    jne 2f
    mov $2, %rax
    xor %rbx, %rbx
    xor %rcx, %rcx
    xor %rdx, %rdx
    int $0x80
2:  mov $3, %rax
    int $0x80
3:  jmp 3b

.section .user.b.bss,"aw",@nobits
.align 4096
.global user_b_stack
user_b_stack:
    .skip 4096
.global user_b_stack_top
user_b_stack_top:

.section .note.GNU-stack,"",@progbits
