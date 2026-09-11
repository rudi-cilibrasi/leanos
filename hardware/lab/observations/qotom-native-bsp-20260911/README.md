# Qotom native BSP boot capture

The protected Win7 Legacy USB boot consumed the root-selected 132-byte MADT
and bound its complete 0/2/4/6 processor inventory to a fresh executing-CPU
observation. The native BSP result was status 0, detail 0, offset 132, APIC 0, count 4,
IA32_APIC_BASE 0xfee00900. Strict hosted generated replay of the same captured
MADT and fresh sample agreed with all six result words. Native PCI inventory
also matched all sixteen functions. FINAL remained `qotom-platform-pending`.

The runner completed successfully and returned to FreeBSD SSH after a
34.31808857401484-second quiet interval. FreeBSD boot time changed from
1789141779 to 1789144499. The one-shot request was consumed. Independent
read-only SSH verification confirmed the installed ELF hash and request=none.
COM1 was 38400 baud, 8N1, no flow control,through FTDI/null modem; USB serial 11758C40.

ELF SHA256:
`d5e95500e224cc6e85665de6060f5912c21413ebb6693637c936213220521cce`.
The build manifest records 78c4c44 with dirty image-integration sources, as
observed at build time. Capture runner source was fb5e659. The manifest is not
relabelled as a later clean build. The guarded installer backed up the prior
boot files and verified staged/installed hashes and the filesystem. Recovery
files and the legacy boot area were preserved.

This evidence establishes a physical BSP/topology candidate binding and PCI
inventory match. It does not establish AP dormancy, interrupt routing safety,
DMA containment, allocation/publication or CPL3 admission. Those requirements
remain under issues #331, #330, #329, #291 and #332. No operator-visible screen result
was obtained in this run; framebuffer metadata does not satisfy issue #335.
