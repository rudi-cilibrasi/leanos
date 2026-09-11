# Native xHCI operational state — 2026-09-11

The protected Win7 Legacy boot completed ownership handoff and SMI disable,
then sampled USBSTS=`0x1`, USBCMD=`0`, USBSTS=`0x1`, with status 0. The controller
reported halted in both samples and Run/Stop and interrupt enables were clear.
Complete resource/list/ownership checks passed before and after sampling.
No operational write, stop request, reset or xHCI bus-master disable occurred.

These sequential samples establish the observed halted state; they are not an
atomic snapshot, continuing firmware exclusion, transaction-drain or DMA proof.
A later BME step must refresh this state immediately around its own operation.
The diagnostic terminal remains `qotom-platform-pending`.

FreeBSD recovered after 34.30548526099301 seconds of serial quiet, boot time
1789163919 to 1789165000, with the request consumed. Independent SSH verified
the installed image/configuration and request=none, then removed the read-only
mount. Serial was FTDI/null modem COM1 at 38400 baud, 8N1.

ELF SHA256:
`e04546479e316e4086a3005fdc55e95740b195309889d0286e956b064fc20721`.
Build and runner revision: 2d2a3509d069066362e7f0d45b8e22a4ff0b9357; sources were
clean. All 89 manifest hashes, the unchanged eight-site MSR-write audit and QEMU
foreign-firmware rejection passed. Guarded USB serial 11758C40, backup, old/new
hashes and filesystem checks passed before the protected boot.
