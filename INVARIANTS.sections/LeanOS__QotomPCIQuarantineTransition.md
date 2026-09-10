# Initial PCI inventory and command-trace binding

These proofs bind two supplied observations; they do not authenticate hardware execution or establish DMA containment.

- `check_preserves_inputs` — Successful combined checking preserves every initial raw header and every input trace step exactly, in their respective orders.
- `witnessed_registers_stable` — Every witnessed trace step matches its initial header outside the Command/Status dword.
- `witnessed_initial_count` — The initial validated inventory contains fifteen functions.
- `witnessed_trace_count` — The validated write/readback trace contains fifteen steps.
