# Qotom lab MSR write-site audit

The captured BSP lab ELF contains eight WRMSR byte pairs in its four
executable sections. All eight occur in the 70-byte bootstrap normalization
block. On entry through the beginning of that block, their ECX selectors are
IA32_EFER, STAR, LSTAR, CSTAR, SFMASK and SYSENTER_CS/ESP/EIP. The
[retained audit](../hardware/lab/qotom-bsp-msr-write-audit.json) binds these
addresses and selectors to the physical capture's ELF SHA256.

`audit-qotom-msr-writes.py` checks the entire fixed block, including selector
loads and the intervening instructions, against reviewed relocation-free
bytes. It scans raw byte pairs in every executable section, including pairs
that a disassembler might consider unaligned or part of another instruction.
Extra pairs or a changed normalization block fail. The check rejects malformed
section tables and writable or unbacked executable sections. Its five tests
include an extra WRMSR site and a changed selector. The BSP lab builder
runs the audit after linking and retains its report/hash in the build manifest.

This is a restricted artifact check, not a proof of AP-start exclusion. The
selector statement assumes entry through the block's beginning and preservation
of its register state. An unchecked jump directly to a write site could violate
that premise. Execution from other memory, firmware/SMM actions and legacy APIC
MMIO writes are outside this check. Neither an AP-dormancy assumption nor a
whole-platform authorization is created here. The remaining control-flow,
mapping/write-authority and firmware contracts must be established separately
before runtime admission under issues #331 and #291.
