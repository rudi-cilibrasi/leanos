.text

.macro function name
.globl \name
.type \name, @function
\name:
.endm

function out16
    out %ax, (%dx)
    ret
.size out16, .-out16

function out32
    out %eax, (%dx)
    ret
.size out32, .-out32

function in32
    in (%dx), %eax
    ret
.size in32, .-in32

function pci_config_dword
    call out32
    call in32
    ret
.size pci_config_dword, .-pci_config_dword

function pci_config_command
    call out32
    call out16
    ret
.size pci_config_command, .-pci_config_command

function quarantine_q35_pci_dma
    call pci_config_dword
    call pci_config_command
    ret
.size quarantine_q35_pci_dma, .-quarantine_q35_pci_dma

function enter_user
    ret
.size enter_user, .-enter_user

function timer_handler
#ifdef LEANOS_RUNTIME_HANDLER_REUSE
    call pci_config_dword
#endif
    ret
.size timer_handler, .-timer_handler

#ifdef LEANOS_CONDITIONAL_PORT_SITE
function conditional_port_path
    out %al, (%dx)
    ret
.size conditional_port_path, .-conditional_port_path
#endif

function kernel_main
    call quarantine_q35_pci_dma
    call enter_user
    ret
.size kernel_main, .-kernel_main

.section .note.GNU-stack,"",@progbits
