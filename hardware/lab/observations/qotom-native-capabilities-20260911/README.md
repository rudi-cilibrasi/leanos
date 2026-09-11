# Native Qotom capability capture

A protected Win7 Legacy USB boot collected conventional PCI capability headers
for all 16 functions after native inventory and BSP checks matched. All lists
terminated successfully; strict decoding bound their initial pointers to the
same captured PCI headers. FINAL remained `qotom-platform-pending`.

FreeBSD recovered automatically after a 34.3124156119884-second quiet interval;
boot time changed from 1789144499 to 1789146758. The one-shot request was consumed.
Independent read-only SSH confirmed the installed ELF and `request=none`.
Serial used FTDI/null modem to COM1, 38400 baud, 8N1, no flow control.

ELF SHA256:
`27773506501f290f107cf80b860e8f9a92034496d05b86787240d543b4b3ec37`.
The build manifest truthfully records a959f17 with dirty integration sources;
runner revision was 69ee9cb. The installer checked USB serial 11758C40 and old
file hashes, backed up boot files, and verified the new hashes and filesystem.

These are header observations, not interpreted capability payloads or proof of
DMA shutdown, transaction drain, AP dormancy, or platform/CPL3 admission.
No operator-visible display result was obtained. Those hardware issues remain
open. Failed reads are not replayed; none occurred in this capture.
