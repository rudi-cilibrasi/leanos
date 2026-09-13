# Qotom J1900 CPU/control production checkpoint

This protected physical cycle ran the Qotom BSP production image built from
`14bc87624a05058100b2c9679c0aec86557980b4`. The exact ELF SHA-256 is
`9e7119f09cc133b72aa1cc0d3cd2ca033fd9ea847493f6b18435075cec852976`.
The linked image contains the composed `LeanOS.J1900CpuControlPolicy` boundary;
the final-image test requires eight checked calls for result words 0 through 7.

The board emitted the complete 22-word `j1900-cpu-v1` observation with selection
65536 and the complete eight-word control observation with readback 1. It then
passed the composed production checkpoint, published memory and the quarantined
four-processor topology, and stopped at the expected typed terminal
`qotom-platform-pending`. The boundary's CPL3-authority word is permanently zero,
so this run grants no CPL3 or whole-platform authority.

The watchdog-protected run retained 34.317 seconds of post-terminal quiet. The
one-shot request was consumed, GRUB chained to FreeBSD on `hd1`, and authenticated
SSH returned with boot time changing from 1789222511 to 1789232782. A separate
read-only mount after recovery verified the installed ELF, digest file, GRUB
configuration, cleared environment block and watchdog fragments. COM1 used
38400 baud, 8N1, no flow control through the FTDI/null-modem link.
