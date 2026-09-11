# Native Qotom EHCI operational capture

Protected Win7 Legacy boot sampled operational registers after cooperative EHCI
handoff and legacy SMI disable. Status 0 retained USBCMD `0x80000`, USBSTS `0x1000`,
USBINTR `0` and CONFIGFLAG `0`. Run/Stop was clear and HCHalted set when sampled.
No operational write, controller stop or reset was requested. Final ownership
and disabled-SMI binding refresh passed. These sequential samples do not prove
continuing firmware exclusion or system-wide DMA containment.

The protected capture passed generated inventory replay and returned to FreeBSD
after 34.29887664999114 seconds of serial quiet. Boot time changed from
1789153139 to 1789155039, with the request consumed. Independent read-only SSH
confirmed the installed image and request=none; the verification mount was removed.
Serial was FTDI/null modem COM1, 38400 baud, 8N1, no flow control.

ELF SHA256:
`c9b39bc70e68ee78ec6a7831b1315fe66230a0dd9e7810ded91e28b1a54bd814`.
Build provenance is 8516dcb with dirty native integration sources; the capture
runner was e42b6ea. The guarded installer checked USB serial 11758C40, previous
and staged hashes, retained a backup, and verified filesystem and installed hashes.
FINAL remains qotom-platform-pending. No platform or CPL3 admission is claimed.
