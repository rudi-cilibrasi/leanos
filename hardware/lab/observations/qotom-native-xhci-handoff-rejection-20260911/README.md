# Native Qotom xHCI handoff rejection

The protected Win7 Legacy boot issued one ownership request and observed
BIOS-clear/OS-owned support `0x01000801` after two polling delays. It then rejected
the final verification with status 10. The record is:

```text
status=10 attempted=1 polls=2 support=16779265 control=0
```

The zero control field is unreported final data, not a sample proving SMI-disable.
Status 10 combines final collection, complete-list comparison and semaphore
checks; this capture cannot distinguish which failed. No completed ownership
handoff, continuing firmware exclusion, controller shutdown or DMA quarantine
is established. The terminal reason is `qotom-xhci-handoff`.

The preceding xHCI capture returned the same seven capability values and six
extended headers as the prior observation, with legacy offset `0x8460`, support
`0x00010801` and control `0x00002001`. The only xHCI write requested was DWORD
`0x01010801` to `0xd0908460`. No forced BIOS clear, legacy control/status write,
operational write or reset was requested.

Protected replay accepted this failure record and FreeBSD recovered automatically
after 34.30788890799158 seconds of serial quiet. Boot time changed from 1789159496
to 1789160798, with the one-shot request consumed. Independent read-only SSH
confirmed the installed image/configuration and request=none; the mount was
removed. Serial was FTDI/null modem COM1, 38400 baud, 8N1, no flow control.

ELF SHA256:
`2d26ea6a71c542b2891bd01665ff73156c6d2c96b5ecc00fcd11ac1dec9391bf`.
Build provenance is 1eb65a8 with dirty integration sources; runner was cf0829c.
The guarded install checked USB serial 11758C40, old/new hashes, backup,
filesystem and read-only installed hashes. The next experiment needs additional
final-verification diagnostics while retaining the same acceptance checks.
