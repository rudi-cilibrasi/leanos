/* Mechanism-1 dword read. Caller admits hardware and address before entry.
 * Preserve caller flags, mask ordinary interrupts across the address/data
 * pair, and restore the original flags. No device configuration data write.
 * CF8 remains set to the selected address. NMI/SMM/other-CPU exclusion is a
 * separate caller obligation. A fault never promises restoration or return.
 */
.text
.code64
.global leanos_pci_config_read_dword
.type leanos_pci_config_read_dword,@function
leanos_pci_config_read_dword:
    pushfq
    cli
    mov %edi, %eax
    mov $0xcf8, %edx
    out %eax, %dx
    mov $0xcfc, %edx
    in %dx, %eax
    popfq
    ret
.size leanos_pci_config_read_dword, .-leanos_pci_config_read_dword
.section .note.GNU-stack,"",@progbits
