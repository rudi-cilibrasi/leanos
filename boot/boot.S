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
    /* Preserve the Multiboot2 handoff before either register is reused. */
    mov %eax, multiboot_magic
    mov %ebx, multiboot_info
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
    orl $4, page_table_a+8(%eax)
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

    /* The canonical plan omits the other subject's pages entirely rather than
       retaining supervisor aliases in that address space. */
    mov $__user_b_text_start, %eax
    shr $9, %eax
    and $0x7ff8, %eax
    mov $__user_b_stack_end, %ecx
    add $0xfff, %ecx
    shr $9, %ecx
    and $0x7ff8, %ecx
7:
    movl $0, page_table_a(%eax)
    movl $0, page_table_a+4(%eax)
    add $8, %eax
    cmp %ecx, %eax
    jb 7b

    mov $__user_a_text_start, %eax
    shr $9, %eax
    and $0x7ff8, %eax
    mov $__user_a_stack_end, %ecx
    add $0xfff, %ecx
    shr $9, %ecx
    and $0x7ff8, %ecx
8:
    movl $0, page_table_b(%eax)
    movl $0, page_table_b+4(%eax)
    add $8, %eax
    cmp %ecx, %eax
    jb 8b

    /* The page immediately below IST1 is absent in both address spaces. */
#ifndef LEANOS_DF_MAP_GUARD
    mov $__df_ist_guard_start, %eax
    shr $9, %eax
    and $0x7ff8, %eax
    movl $0, page_table_a(%eax)
    movl $0, page_table_a+4(%eax)
    movl $0, page_table_b(%eax)
    movl $0, page_table_b+4(%eax)
#endif

    /* The linker-owned page immediately below the ordinary CPL3 entry stack
       is absent in every live address space. */
    mov $__entry_stack_guard_start, %eax
    shr $9, %eax
    and $0x7ff8, %eax
    movl $0, page_table_a(%eax)
    movl $0, page_table_a+4(%eax)
    movl $0, page_table_b(%eax)
    movl $0, page_table_b+4(%eax)

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
    mov multiboot_magic(%rip), %edi
    mov multiboot_info(%rip), %esi
    call kernel_main
3:
    cli
    hlt
    jmp 3b
.size multiboot_entry, . - multiboot_entry

.section .data.gdt,"aw",@progbits
.align 8
.global multiboot_magic
multiboot_magic:
    .long 0
.global multiboot_info
multiboot_info:
    .long 0
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
.global page_directory_pointer_a
page_directory_pointer_a:
    .skip 4096
.global page_directory_a
page_directory_a:
    .skip 4096
.align 4096
.global page_table_a
page_table_a:
    .skip 4096 * PAGE_TABLE_COUNT
page_table_a_end:
.global page_map_level_4_b
page_map_level_4_b:
    .skip 4096
.global page_directory_pointer_b
page_directory_pointer_b:
    .skip 4096
.global page_directory_b
page_directory_b:
    .skip 4096
.align 4096
.global page_table_b
page_table_b:
    .skip 4096 * PAGE_TABLE_COUNT
page_table_b_end:
.align 16
.global boot_stack
boot_stack:
    .skip 16384
.global boot_stack_top
boot_stack_top:

.section .df_ist.guard,"aw",@nobits
.align 4096
.global df_ist_guard
df_ist_guard:
    .skip 4096

.section .df_ist.stack,"aw",@nobits
.align 4096
.global df_ist_stack
df_ist_stack:
    .skip 16384
.global df_ist_stack_top
df_ist_stack_top:

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
    bts $21, %rax
    mov %rax, %cr4
    ret
.global smap_copy_from
smap_copy_from:
    pushfq
    cli
.global smap_copy_from_cld
smap_copy_from_cld:
    cld
.global smap_copy_from_stac
smap_copy_from_stac:
    stac
    mov %rdx, %rcx
    rep movsb
.global smap_copy_from_clac
smap_copy_from_clac:
    clac
    popfq
    ret
.global smap_copy_to
smap_copy_to:
    pushfq
    cli
.global smap_copy_to_cld
smap_copy_to_cld:
    cld
.global smap_copy_to_stac
smap_copy_to_stac:
    stac
    mov %rdx, %rcx
    rep movsb
.global smap_copy_to_clac
smap_copy_to_clac:
    clac
    popfq
    ret
.global smap_omit_cleanup_probe
smap_omit_cleanup_probe:
.global smap_omit_cleanup_probe_stac
smap_omit_cleanup_probe_stac:
    stac
    ret
.global smap_force_clac
smap_force_clac:
    clac
    ret
.global run_smap_probe
run_smap_probe:
.global smap_probe_instruction
smap_probe_instruction:
    movb user_a_stack(%rip), %al
.global smap_probe_recovered
smap_probe_recovered:
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
#ifdef LEANOS_RETURN_INITIAL_INDIRECT_FIXTURE
    /* Negative final-ELF fixture: bypass validation from initial dispatch. */
    lea user_return_restore(%rip), %rax
    jmp *%rax
#endif
    /* This function is entered by a SysV call and never returns.  Discard the
       caller return address so the synthetic 160-byte frame leaves RSP
       16-byte aligned at the validator call site. */
    add $8, %rsp
    pushq $0x1b
    push %rsi
    pushfq
    pop %rax
    or $0x200, %rax
    push %rax
    pushq $0x23
    push %rdi
    /* Supply an all-zero initial register bank so every CPL3 transition uses
       the same reviewed validator/restore epilogue. */
    xor %eax, %eax
    .rept 15
    push %rax
    .endr
    mov $1, %esi
#ifdef LEANOS_RETURN_BRANCH_FIXTURE
    jmp user_return_restore
#else
    jmp user_return_epilogue
#endif

/* Raise a real #GP with RSP immediately above the unmapped guard.  Its present
   IST0 gate must push an exception frame into the guard, so the resulting #PF
   during contributory-exception delivery escalates to #DF. */
.global run_double_fault_probe
run_double_fault_probe:
    cli
    clac
    cld
    mov $__df_ist_guard_end, %rsp
    mov $0xffff, %eax
    mov %ax, %ds
1:  hlt
    jmp 1b

.macro DF_SERIAL label, length
    lea \label(%rip), %rsi
    mov $\length, %ecx
1:
    mov $0x3fd, %dx
2:  inb %dx, %al
    test $0x20, %al
    jz 2b
    movb (%rsi), %al
    mov $0x3f8, %dx
    outb %al, %dx
    inc %rsi
    dec %ecx
    jnz 1b
.endm

/* Reaching this present #GP gate means the ordinary-stack frame push worked.
   The guard-mapped negative image must take this path and must not claim #DF. */
.global isr13
isr13:
#ifdef LEANOS_ENTRY_ADVERSARIAL
    clac
    cld
    push %rax; push %rbx; push %rcx; push %rdx; push %rbp; push %rsi; push %rdi
    push %r8; push %r9; push %r10; push %r11; push %r12; push %r13; push %r14; push %r15
    sub $8, %rsp
    mov 128(%rsp), %rdi
    mov 136(%rsp), %rsi
    mov 144(%rsp), %rdx
    call entry_adversarial_gp_handler
    mov %rax, 136(%rsp)
    add $8, %rsp
    /* Discard the #GP error word by shifting the five-word user frame into
       the standard SAVE+iret layout consumed by the existing validator. */
    mov 128(%rsp), %rax
    mov %rax, 120(%rsp)
    mov 136(%rsp), %rax
    mov %rax, 128(%rsp)
    mov 144(%rsp), %rax
    mov %rax, 136(%rsp)
    mov 152(%rsp), %rax
    mov %rax, 144(%rsp)
    mov 160(%rsp), %rax
    mov %rax, 152(%rsp)
    mov $2, %esi
    jmp user_return_epilogue
#else
    cli
    clac
    cld
    DF_SERIAL df_guard_mapped_record, df_guard_mapped_record_end-df_guard_mapped_record
    mov $0x13, %al
    mov $0xf4, %dx
    outb %al, %dx
6:  hlt
    jmp 6b
#endif

/* Vector 8 has a hardware error-code word.  This terminal stub uses no C ABI,
   calls, pushes, allocation, formatting, recovery path, or iretq. */
.global isr8
.global isr8_clac
.global isr8_cld
isr8:
    cli
isr8_clac:
    clac
isr8_cld:
    cld
    mov %rsp, %rbx
    cmp $__df_ist_stack_start, %rbx
    jb 3f
    cmp $__df_ist_stack_end, %rbx
    jae 3f
    cmpq $0, 0(%rbx)
    jne 3f
    movabs $0xd0b1efa17badc0de, %rax
    cmp %rax, __df_ist_stack_start(%rip)
    jne 3f
    movabs $0x15a1c0decafef00d, %rax
    cmp %rax, __df_ist_stack_end-128(%rip)
    jne 3f
    DF_SERIAL df_success_record, df_success_record_end-df_success_record
    mov $0x12, %al
    mov $0xf4, %dx
    outb %al, %dx
4:  hlt
    jmp 4b
3:
    DF_SERIAL df_failure_record, df_failure_record_end-df_failure_record
    mov $0x13, %al
    mov $0xf4, %dx
    outb %al, %dx
5:  hlt
    jmp 5b

.section .rodata,"a",@progbits
df_success_record:
    .ascii "LEANOS/8 TERMINAL reason=double-fault vector=8 error=0 ist=1 rsp=in-range canaries=intact normal-stack=unmapped return=none\n"
df_success_record_end:
df_failure_record:
    .ascii "LEANOS/8 TERMINAL reason=double-fault evidence=invalid status=FAIL\n"
df_failure_record_end:
df_guard_mapped_record:
    .ascii "LEANOS/8 NEGATIVE reason=guard-mapped vector=13 double-fault=absent status=FAIL\n"
df_guard_mapped_record_end:

.section .text,"ax",@progbits

.macro SAVE
    push %rax; push %rbx; push %rcx; push %rdx; push %rbp; push %rsi; push %rdi
    push %r8; push %r9; push %r10; push %r11; push %r12; push %r13; push %r14; push %r15
.endm
.macro RESTORE
    pop %r15; pop %r14; pop %r13; pop %r12; pop %r11; pop %r10; pop %r9; pop %r8
    pop %rdi; pop %rsi; pop %rbp; pop %rdx; pop %rcx; pop %rbx; pop %rax
.endm
/* All ordinary gates execute this protocol after AC/DF cleanup and SAVE.
   No operation-specific handler reads the architectural frame until the
   kernel-owned manifest adapter has authorized its vector/stub/shape/context. */
.macro NORMALIZE_ENTRY vector, has_error, cs_offset
    /* No-error entries arrive 16-byte aligned after SAVE.  Reserve both an
       explicit dummy error slot and padding so the C call remains aligned. */
    sub $16, %rsp
    movq $0, (%rsp)
    movq $0, 8(%rsp)
    mov $\vector, %edi
    mov $\has_error, %esi
    mov %rsp, %rdx
    mov \cs_offset(%rsp), %rcx
    call authorize_interrupt_entry
    add $16, %rsp
.endm
.global isr80
isr80:
.global isr80_clac
isr80_clac:
    clac
.global isr80_cld
isr80_cld:
    cld
    SAVE
    NORMALIZE_ENTRY 128, 0, 144
    mov 112(%rsp), %rdi
    mov 104(%rsp), %rsi
    mov 96(%rsp), %rdx
    mov 88(%rsp), %rcx
    mov 128(%rsp), %r8
    mov 136(%rsp), %r9
    call syscall_handler
    cmp $0xbeef, %rax
    je 8f
    cmp $0xcafe, %rax
    je 9f
    cmp $0xfeed, %rax
    jne 7f
    movq $user_b_entry, 120(%rsp)
    movq $user_b_stack_top, 144(%rsp)
    movq $page_map_level_4_b, %rax
    mov %rax, %cr3
    xor %rax, %rax
7:
    mov %rax, 112(%rsp)
    mov $2, %esi
    jmp user_return_epilogue
8:  /* B blocked: preserve its exact continuation and dispatch fresh A. */
    mov %rsp, %rsi
    lea saved_context_b(%rip), %rdi
    mov $20, %ecx
    rep movsq
    mov saved_context_b+120(%rip), %rax
    mov %rax, saved_context_b_original_rip(%rip)
    mov saved_context_b+136(%rip), %rax
    mov %rax, saved_context_b_original_flags(%rip)
    mov saved_context_b+144(%rip), %rax
    mov %rax, saved_context_b_original_rsp(%rip)
    xor %eax, %eax
    mov %rsp, %rdi
    mov $15, %ecx
    rep stosq
    movq $user_a_entry, 120(%rsp)
    movq $0x23, 128(%rsp)
    movq $0x202, 136(%rsp)
    movq $user_a_stack_top, 144(%rsp)
    movq $0x1b, 152(%rsp)
    movq $page_map_level_4_a, %rax
    mov %rax, %cr3
    mov %rsp, %rdi
    mov saved_context_owner_a(%rip), %rsi
    mov saved_context_owner_b(%rip), %rdx
    call switch_complete
    mov $2, %esi
    jmp user_return_epilogue
9:  /* A's send woke B: preserve A and restore B's blocked continuation. */
    mov %rsp, %rsi
    lea saved_context_a(%rip), %rdi
    mov $20, %ecx
    rep movsq
    lea saved_context_b(%rip), %rsi
    mov %rsp, %rdi
    mov $20, %ecx
    rep movsq
    movq $0x4c45414e, 112(%rsp)
    movq $0x4f53, 104(%rsp)
    movq $1, 96(%rsp)
    movq $page_map_level_4_b, %rax
    mov %rax, %cr3
    mov %rsp, %rdi
    mov saved_context_owner_b(%rip), %rsi
    mov saved_context_owner_a(%rip), %rdx
    call switch_complete
    mov $2, %esi
    jmp user_return_epilogue
.global isr14
isr14:
.global isr14_clac
isr14_clac:
    clac
.global isr14_cld
isr14_cld:
    cld
    SAVE
    sub $8, %rsp
    movq $0, (%rsp)
    mov $14, %edi
    mov $1, %esi
    mov %rsp, %rdx
    mov 144(%rsp), %rcx
    call authorize_interrupt_entry
    mov 128(%rsp), %rdi
    mov 136(%rsp), %rsi
    mov 144(%rsp), %rdx
    mov %cr2, %rcx
    call page_fault_handler
    sub $16, %rsp
    mov %rax, 8(%rsp)
    call complete_interrupt_entry
    mov 8(%rsp), %rax
    add $16, %rsp
    mov %rax, 136(%rsp)
.global diagnostic_return_restore
diagnostic_return_restore:
    add $8, %rsp
    RESTORE
    add $8, %rsp
.global diagnostic_return_iretq
diagnostic_return_iretq:
    iretq
.global isr32
.section .bss,"aw",@nobits
.align 16
.global saved_context_a
saved_context_a:
    .skip 160
.global saved_context_b
saved_context_b:
    .skip 160
.global saved_context_a_original_rip
saved_context_a_original_rip:
    .skip 8
.global saved_context_a_original_flags
saved_context_a_original_flags:
    .skip 8
.global saved_context_a_original_rsp
saved_context_a_original_rsp:
    .skip 8
.global saved_context_b_original_rip
saved_context_b_original_rip:
    .skip 8
.global saved_context_b_original_flags
saved_context_b_original_flags:
    .skip 8
.global saved_context_b_original_rsp
saved_context_b_original_rsp:
    .skip 8
.section .rodata,"a",@progbits
.align 8
.global saved_context_owner_a
saved_context_owner_a:
    .quad 1
.global saved_context_owner_b
saved_context_owner_b:
    .quad 2
.set B_INITIAL_RAX, 0x010001
.set B_INITIAL_RBX, 0x020002
.set B_INITIAL_RCX, 0x030003
.set B_INITIAL_RDX, 0x040004
.set B_INITIAL_RBP, 0x050005
.set B_INITIAL_RSI, 0x060006
.set B_INITIAL_RDI, 0x070007
.set B_INITIAL_R8,  0x080008
.set B_INITIAL_R9,  0x090009
.set B_INITIAL_R10, 0x100010
.set B_INITIAL_R11, 0x110011
.set B_INITIAL_R12, 0xc0dec0dec0dec0de
.set B_INITIAL_R13, 0x51a7e51a7e51a7e5
.set B_INITIAL_R14, 0x140014
.set B_INITIAL_R15, 0x150015
.align 16
.global initial_context_b
initial_context_b:
    /* SAVE layout: r15..rax, then the five-word iretq frame. */
    .quad B_INITIAL_R15, B_INITIAL_R14, B_INITIAL_R13, B_INITIAL_R12
    .quad B_INITIAL_R11, B_INITIAL_R10, B_INITIAL_R9, B_INITIAL_R8
    .quad B_INITIAL_RDI, B_INITIAL_RSI, B_INITIAL_RBP, B_INITIAL_RDX
    .quad B_INITIAL_RCX, B_INITIAL_RBX, B_INITIAL_RAX
    .quad user_b_entry, 0x23, 0x202, user_b_stack_top, 0x1b
.section .text,"ax",@progbits
isr32:
.global isr32_clac
isr32_clac:
    clac
.global isr32_cld
isr32_cld:
    cld
    SAVE
    NORMALIZE_ENTRY 32, 0, 144
    mov 128(%rsp), %rdi
    call timer_handler
    cmp $2, %rax
    je 1f
    cmp $1, %rax
    je 2f
    ud2
1:  /* Save A's exact GPR/iret frame, then install B's fresh context. */
    mov %rsp, %rsi
    lea saved_context_a(%rip), %rdi
    mov $20, %ecx
    rep movsq
    mov saved_context_a+120(%rip), %rax
    mov %rax, saved_context_a_original_rip(%rip)
    mov saved_context_a+136(%rip), %rax
    mov %rax, saved_context_a_original_flags(%rip)
    mov saved_context_a+144(%rip), %rax
    mov %rax, saved_context_a_original_rsp(%rip)
    lea initial_context_b(%rip), %rsi
    mov %rsp, %rdi
    mov $20, %ecx
    rep movsq
    movq $page_map_level_4_b, %rax
    mov %rax, %cr3
    mov saved_context_owner_b(%rip), %rsi
    mov saved_context_owner_a(%rip), %rdx
    jmp 3f
2:  /* Preserve B separately and restore A byte-for-byte before CR3/iretq. */
    mov %rsp, %rsi
    lea saved_context_b(%rip), %rdi
    mov $20, %ecx
    rep movsq
    mov saved_context_b+120(%rip), %rax
    mov %rax, saved_context_b_original_rip(%rip)
    mov saved_context_b+136(%rip), %rax
    mov %rax, saved_context_b_original_flags(%rip)
    mov saved_context_b+144(%rip), %rax
    mov %rax, saved_context_b_original_rsp(%rip)
    lea saved_context_a(%rip), %rsi
    mov %rsp, %rdi
    mov $20, %ecx
    rep movsq
    movq $page_map_level_4_a, %rax
    mov %rax, %cr3
    mov saved_context_owner_a(%rip), %rsi
    mov saved_context_owner_b(%rip), %rdx
3:
    mov %rsp, %rdi
    call switch_complete
    mov $3, %esi
    jmp user_return_epilogue

/* The only boot-reachable CPL3 return. validate_user_return receives the exact
   immutable register/frame tuple at RSP; after acceptance this block performs
   no frame write, context change, or call before consuming that tuple. */
.global user_return_epilogue
.global user_return_iretq
user_return_epilogue:
    /* Normalize the two explicitly kernel-managed override bits in the exact
       outgoing frame before it is validated.  NT, VM, IOPL, selectors, and
       every address/context field remain reject-only. */
    andq $-263169, 136(%rsp) /* ~(RFLAGS.DF | RFLAGS.AC) */
    mov %rsp, %rdi
    call validate_user_return
#ifdef LEANOS_RETURN_POST_VALIDATE_QEMU_FIXTURE
    /* Negative machine-path fixture: mutate the attested RIP, then re-enter
       the production validator so the guest records a typed terminal result
       before the mutated tuple can reach RESTORE/iretq. */
    movabs $0x0000800000000000, %rax
    mov %rax, 120(%rsp)
    mov %rsp, %rdi
    mov $1, %esi
    call validate_user_return
#endif
#ifdef LEANOS_RETURN_INDIRECT_FIXTURE
    /* Negative final-ELF fixture: synthesize an indirect restore entrant. */
    lea user_return_restore(%rip), %rax
    push %rax
    ret
#endif
.global user_return_restore
user_return_restore:
#ifdef LEANOS_RETURN_RESTORE_FIXTURE
    /* Negative final-ELF fixture: consume one slot into the wrong register. */
    pop %r14
    pop %r14; pop %r13; pop %r12; pop %r11; pop %r10; pop %r9; pop %r8
    pop %rdi; pop %rsi; pop %rbp; pop %rdx; pop %rcx; pop %rbx; pop %rax
#else
    RESTORE
#endif
user_return_iretq:
    iretq

.section .user.a.text,"ax",@progbits
.global user_a_entry
user_a_entry:
    mov $0x1b, %ax
    mov %ax, %ds
    mov %ax, %es
#ifdef LEANOS_ENTRY_ADVERSARIAL
    int $14
    int $32
#endif
    movb $0x5a, user_a_stack+4094(%rip)
    movb $0xa5, user_a_stack+4095(%rip)
    movb $0x3c, user_a_stack+4096(%rip)
    movb $0xc3, user_a_stack+4097(%rip)
    mov $4, %rax
    xor %rbx, %rbx
    lea user_a_stack+4094(%rip), %rcx
    mov $4, %rdx
    std
    int $0x80
    cld
    mov $4, %rax
    mov $1, %rbx
    lea user_a_stack+4110(%rip), %rcx
    mov $4, %rdx
    std
    int $0x80
    cld
    cmpb $0x5a, user_a_stack+4110(%rip)
    jne user_copy_fail
    cmpb $0xa5, user_a_stack+4111(%rip)
    jne user_copy_fail
    cmpb $0x3c, user_a_stack+4112(%rip)
    jne user_copy_fail
    cmpb $0xc3, user_a_stack+4113(%rip)
    jne user_copy_fail
    /* Exercise the admitted CPL3 protection-fault frame before continuing the
       scenario.  Page zero is present supervisor-only in root A, so this read
       deterministically raises #PF with error code 5. */
.global user_a_fault_instruction
user_a_fault_instruction:
    mov 0, %rax
.global user_a_fault_recovered
user_a_fault_recovered:
#ifdef LEANOS_PREEMPTION_SCENARIO
    mov $1, %rax
    xor %rbx, %rbx
    xor %rcx, %rcx
    xor %rdx, %rdx
    movabs $0xa11ca11ca11ca11c, %r12
    movabs $0xa22da22da22da22d, %r13
    int $0x80
1:  mov $6, %rax
    int $0x80
    test %rax, %rax
    jz 1b
    movabs $0xa11ca11ca11ca11c, %rax
    cmp %rax, %r12
    jne user_copy_fail
    movabs $0xa22da22da22da22d, %rax
    cmp %rax, %r13
    jne user_copy_fail
    mov $5, %rax
#else
    mov $8, %rax
    mov $0x4c45414e, %rbx
    mov $0x4f53, %rcx
    xor %rdx, %rdx
#endif
    int $0x80
    ud2
user_copy_fail:
    mov $3, %rax
    int $0x80
    ud2

.section .user.a.bss,"aw",@nobits
.align 4096
.global user_a_stack
user_a_stack:
    .skip 8192
.global user_a_stack_top
user_a_stack_top:

.section .user.b.text,"ax",@progbits
.global user_b_entry
user_b_entry:
#ifdef LEANOS_PREEMPTION_SCENARIO
    cmp $B_INITIAL_RAX, %rax
    jne 2f
    cmp $B_INITIAL_RBX, %rbx
    jne 2f
    cmp $B_INITIAL_RCX, %rcx
    jne 2f
    cmp $B_INITIAL_RDX, %rdx
    jne 2f
    cmp $B_INITIAL_RBP, %rbp
    jne 2f
    cmp $B_INITIAL_RSI, %rsi
    jne 2f
    cmp $B_INITIAL_RDI, %rdi
    jne 2f
    cmp $B_INITIAL_R8, %r8
    jne 2f
    cmp $B_INITIAL_R9, %r9
    jne 2f
    cmp $B_INITIAL_R10, %r10
    jne 2f
    cmp $B_INITIAL_R11, %r11
    jne 2f
    cmp $B_INITIAL_R14, %r14
    jne 2f
    cmp $B_INITIAL_R15, %r15
    jne 2f
    movabs $B_INITIAL_R12, %rax
    cmp %rax, %r12
    jne 2f
    movabs $B_INITIAL_R13, %rax
    cmp %rax, %r13
    jne 2f
#endif
    mov $0x1b, %ax
    mov %ax, %ds
    mov %ax, %es
#ifdef LEANOS_PREEMPTION_SCENARIO
    mov $2, %rax
    xor %rbx, %rbx
    xor %rcx, %rcx
    xor %rdx, %rdx
#else
    mov $10, %rax
    mov $(2 * 65536), %rbx
    mov $0xcafe, %rcx
    mov $0xbeef, %rdx
    int $0x80
    mov %rax, %r14
    cmp $(3 * 65536), %r14
    jne 2f
    mov $11, %rax
    mov $(2 * 65536), %rbx
    mov $0xcafe, %rcx
    mov $0xbeef, %rdx
    int $0x80
    test %rax, %rax
    jne 2f
    mov $12, %rax
    mov %r14, %rbx
    mov $0xcafe, %rcx
    mov $0xbeef, %rdx
    int $0x80
    cmp $1, %rax
    jne 2f
    mov $7, %rax
    xor %rbx, %rbx
    xor %rcx, %rcx
    mov $B_INITIAL_RDX, %rdx
    mov $B_INITIAL_RBP, %rbp
    mov $B_INITIAL_RSI, %rsi
    mov $B_INITIAL_RDI, %rdi
    mov $B_INITIAL_R8, %r8
    mov $B_INITIAL_R9, %r9
    mov $B_INITIAL_R10, %r10
    mov $B_INITIAL_R11, %r11
    movabs $B_INITIAL_R12, %r12
    movabs $B_INITIAL_R13, %r13
    mov $B_INITIAL_R14, %r14
    mov $B_INITIAL_R15, %r15
#endif
    int $0x80
#ifndef LEANOS_PREEMPTION_SCENARIO
    cmp $0x4c45414e, %rax
    jne 2f
    cmp $0x4f53, %rbx
    jne 2f
    cmp $1, %rcx
    jne 2f
    cmp $B_INITIAL_RDX, %rdx
    jne 2f
    cmp $B_INITIAL_RBP, %rbp
    jne 2f
    cmp $B_INITIAL_RSI, %rsi
    jne 2f
    cmp $B_INITIAL_RDI, %rdi
    jne 2f
    cmp $B_INITIAL_R8, %r8
    jne 2f
    cmp $B_INITIAL_R9, %r9
    jne 2f
    cmp $B_INITIAL_R10, %r10
    jne 2f
    cmp $B_INITIAL_R11, %r11
    jne 2f
    cmp $B_INITIAL_R14, %r14
    jne 2f
    cmp $B_INITIAL_R15, %r15
    jne 2f
    movabs $B_INITIAL_R12, %rax
    cmp %rax, %r12
    jne 2f
    movabs $B_INITIAL_R13, %rax
    cmp %rax, %r13
    jne 2f
    mov $0x4c45414e, %rbx
    mov $1, %rdx
    mov $0x4f53, %rcx
    mov $9, %rax
    int $0x80
#else
1:  jmp 1b
#endif
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
