# Native Qotom blocking IPC capture — 2026-09-13

A protected Win7 Legacy boot completed the named `qotom-blocking-ipc-v1`
profile on the Qotom J1900. The physical path admitted the existing PCI trust
contract, enabled the no-SMAP copy-root controls, completed the entry
checkpoint, and then ran the fixed two-subject scenario. The exact semantic
suffix ended with:

```text
LEANOS/10 IPC event=block subject=2 endpoint=10 empty=1 runnable=0 result=PASS
LEANOS/8 PAGING root=A selected=1 resumed=1 result=PASS
LEANOS/10 IPC event=dispatch subject=1 address-space=1 blocked-subject=2 trusted=1
LEANOS/6 COPY direction=in length=4 cross-page=1 validated=1 user-df=1 kernel-df=cleared ac=cleared result=PASS
LEANOS/6 COPY direction=out length=4 cross-page=0 validated=1 user-df=1 kernel-df=cleared destination=verified-by-cpl3 ac=cleared result=PASS
LEANOS/11 USER-FAULT vector=14 error=5 origin=cpl3 address=zero contained=1 result=PASS
LEANOS/10 IPC event=send sender=1 endpoint=10 payload0=1279607118 payload1=20307 accepted=1
LEANOS/10 IPC event=wake subject=2 ready-insertions=1 reserved=1 result=PASS
LEANOS/8 PAGING root=B selected=1 result=PASS
LEANOS/10 IPC event=dispatch subject=2 address-space=2 reservation=owned trusted=1
LEANOS/10 IPC event=deliver receiver=2 endpoint=10 sender=1 payload0=1279607118 payload1=20307 exact=1 canaries=preserved
LEANOS/10 FINAL status=PASS blocks=1 wakes=1 deliveries=1
```

The run used subject roots `0x176000` and `0x181000`, closed root `0x1b1000`,
read-only copy root `0x1a6000`, and writable copy-out root `0x19a000`. The
decoder accepted eight semantic syscalls, one recoverable CPL3 page fault, two
context switches, two copy transfers, four blocking-model transitions, and
four capability-reuse transitions. Vector 32 was absent, both PIC masks were
`0xff`, and the profile did not program the PIT or enable interrupts.

The protected ELF SHA256 is
`61e5a57715f48fe2e80888381a2178ad49d2ea088d3effa1ce0202bd7c0b6638`.
Clean source revision `9734ed860141f45721d37c565ad8de84054735bc`
reproduced that exact ELF from prepared revision
`4b0a428174cb868cb792f0c3f08387a9597e00d2`; `build-manifest.json` records
the complete hashed input set.
The complete `serial.raw`, including recovery output, has SHA256
`05523b6791a4cabfd9fae346454cf5ede3bf81c303c4f62dae68db389027e437`.
The same canonical q35 blocking-IPC transcript passed QEMU 8.2.2 under both
the pinned TCG and KVM constructions; each emulator serial log has SHA256
`a3fc7d6dbece61c7e4b69c864b8e7ed91814675fe3ff14810c4d3dc3ca66c69e`.

After the final record, the kernel entered its absorbing `cli; hlt` loop. The
runner measured 92.4421041070018 seconds of serial quiet, then observed the
watchdog reset. FreeBSD boot time changed from 1789292980 to 1789293459,
authenticated SSH returned, and the one-shot request was consumed. Independent
inspection confirmed the installed ELF and GRUB hashes, `request=none`, and a
clean FAT filesystem. Serial used the FTDI USB-to-DB9 cable and null-modem
adapter on COM1 at 38400 baud, 8N1, with no flow control.

The first physical attempt used ELF
`7e3c9c0ccffb0fb94888d5c189d902dbec93094e98ede80468a4370dae52e4fa`.
It reached the switch back to B and then emitted
`FINAL status=FAIL reason=qotom-blocking-deliver-frame`. The frame guard had
required `RDX` to be both B's original `0x040004` canary and the delivery
argument `sender=1`. The corrected guard takes the exact expected `RDX` for
each entry: `0x040004` for the block syscall and `1` for delivery. All other
preserved registers remain checked. The failed full serial stream SHA256 was
`c6a91e02a84cd87f0ff3a8aca14e54183950f9df9668b0f347732f8c10de69a4`;
its one-shot request was also consumed and FreeBSD recovered from boot epoch
1789286918 to 1789292980. The accepted `cycle-1` directory contains only the
corrected run.

`capture.sh` records the protected runner invocation. `install.sh` records the
final digest-bound USB update. This observation establishes one bounded
physical execution of the named profile; the limitations in
`docs/qotom-blocking-ipc-integration.md` still apply.
