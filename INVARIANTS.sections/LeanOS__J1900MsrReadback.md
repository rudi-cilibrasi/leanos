# Exact Intel MSR readback

The readback check compares eight complete register values with the expected Intel state. It rejects reserved EFER bits and nonzero entry targets; it does not read registers or authorize an MSR instruction.

- `validate_denied_iff` — The check passes exactly for EFER 0xd00 and seven zero target or mask registers, with no ignored high bits.
