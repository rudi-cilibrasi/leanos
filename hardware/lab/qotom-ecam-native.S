.section .text
.global lab_ecam_native_load32
.type lab_ecam_native_load32, @function
/* SysV: opaque=%rdi, checked mapped VA=%rsi, private sample=%rdx. */
lab_ecam_native_load32:
    mov (%rsi), %eax
    mov %eax, (%rdx)
    mov $1, %eax
    ret
.size lab_ecam_native_load32, .-lab_ecam_native_load32

.global lab_ecam_native_invalidate
.type lab_ecam_native_invalidate, @function
lab_ecam_native_invalidate:
    invlpg (%rsi)
    ret
.size lab_ecam_native_invalidate, .-lab_ecam_native_invalidate

.global lab_ecam_native_controls
.type lab_ecam_native_controls, @function
/* SysV: opaque=%rdi, private lab_ecam_controls output=%rsi. MSR reads only
 * after CPUID reports MSR and PAT. No control/MSR writes and no port I/O. */
lab_ecam_native_controls:
    push %rbx
    mov %rsi, %r8
    pushfq
    pop %r9
    mov $1, %eax
    xor %ecx, %ecx
    cpuid
    and $0x10020, %edx
    cmp $0x10020, %edx
    jne .Lecam_unavailable
    mov $0x277, %ecx
    rdmsr
    mov %eax, %eax
    shl $32, %rdx
    or %rdx, %rax
    mov %rax, (%r8)
    mov %cr0, %rax
    mov %rax, 8(%r8)
    mov %cr3, %rax
    mov %rax, 16(%r8)
    mov %cr4, %rax
    mov %rax, 24(%r8)
    mov $0xc0000080, %ecx
    rdmsr
    mov %eax, %eax
    shl $32, %rdx
    or %rdx, %rax
    mov %rax, 32(%r8)
    mov %r9, 40(%r8)
    mov $1, %eax
    pop %rbx
    ret
.Lecam_unavailable:
    xor %eax, %eax
    pop %rbx
    ret
.size lab_ecam_native_controls, .-lab_ecam_native_controls
.section .note.GNU-stack,"",@progbits
