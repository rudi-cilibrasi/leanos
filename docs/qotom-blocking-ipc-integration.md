# Qotom blocking IPC integration

The opt-in `qotom-blocking-ipc-v1` image completes the fixed two-subject
blocking-IPC scenario on the Qotom J1900 profile. It runs only after the exact
PCI trust contract, no-SMAP controls, closed/copy-root publication, and two
validated CPL3 entry returns have succeeded. The profile uses synchronous
`INT 0x80` entries and one recoverable CPL3 page fault. It does not enable a
timer or any asynchronous interrupt source.

The generated `QotomBlockingIPCIntegration` boundary consumes the earlier
checkpoint results plus three distinct aligned roots, complete root scans, the
exact syscall and page-fault gates, an absent vector-32 gate, both legacy PIC
masks, two context banks, and the generated-model binding flag. Its eleven
result words identify the ABI, admission/error result, CPL3 authority, eight
semantic syscalls, one recoverable fault, two context switches, two copy
transfers, four blocking-IPC transitions, four capability-reuse transitions,
and the terminal policy. The hosted harness checks the accepted vector and one
isolated rejection for every input.

## Machine path

Subject B first exercises capability generation replacement: generation 2 is
accepted, cleared, and replaced by generation 3; replay of generation 2 is
rejected without an effect; generation 3 is accepted. B then blocks on the
empty endpoint. The dispatcher copies its complete 20-word saved frame into B's
private context bank, constructs A's initial frame, selects A's page-table root,
and returns through the audited closed-root return primitive.

Subject A performs four-byte copy-in and copy-out requests. The source crosses
a page boundary and is visible only through the read-only copy root. The
destination is visible only through the distinct writable copy-out root and is
verified again in CPL3. Each syscall enters under the subject root, reloads and
reads back the closed root before calling C, and returns through the existing
root-switch/restore/`IRETQ` primitive. No Qotom path executes `STAC` or `CLAC`.

A then reads virtual address zero. The identity page remains supervisor-present,
so the CPU must report CPL3 page-fault error code 5. The entry stub saves CR2 and
all fifteen GPRs, closes and reads back the root, and calls C. The dispatcher
requires the exact CR2, error, RIP, selectors, stack, flags, roots, and register
bank before advancing saved RIP to the one linked recovery label. A sends the
fixed payload and wakes B. B resumes with its canaries intact and validates the
exact delivery.

The success path emits:

```text
LEANOS/10 FINAL status=PASS blocks=1 wakes=1 deliveries=1
```

It then executes an absorbing `cli; hlt` loop. Port `0xf4` remains an emulator
exit mechanism and is not retained in this physical path. The already-established
USB watchdog resets the board, consumes the one-shot request, and chains back to
FreeBSD. A physical result is accepted only when the exact loaded ELF digest,
the semantic transcript, 30 to 100 seconds of post-terminal silence, a changed
FreeBSD boot epoch, restored SSH, and `request=none` all agree.

## Comparison with the q35 scenario

| Stage | q35 blocking IPC | `qotom-blocking-ipc-v1` |
| --- | --- | --- |
| DMA/platform gate | q35 VT-d and device snapshot | Exact Qotom PCI trust contract and bounded fixed-platform premises |
| User isolation | SMEP and SMAP with AC-controlled copies | SMEP with closed, read-only copy-in, and writable copy-out roots; no SMAP |
| Entry | Generated q35 entry controls | DPL3 `INT 0x80`, complete saved bank, immediate closed-root reload/readback |
| Interrupts | Canonical q35 scenario infrastructure | IF clear, vector 32 absent, PIC masks `0xff`, no PIT programming |
| Recoverable fault | One contained CPL3 page fault | One exact CPL3 read fault at zero, error 5, recovered at one linked label |
| Scheduling | Two subjects and generated blocking model | Two explicit 20-word context banks and the same four generated model calls |
| Semantic trace | `blocking-ipc.transcript` | Exact suffix of the same repository-owned template |
| Terminal | Structured PASS and emulator exit | Structured PASS, `cli; hlt`, watchdog reset, FreeBSD recovery |

This is a bounded hardware scenario rather than a general scheduler or syscall
surface. The scalar proof does not establish runtime observation fidelity. The
linked audit covers retained instructions and model-call multiplicity; q35
execution covers the emulator profile; the COM1 capture covers one named ELF on
one board. Firmware/SMM exclusion, compiler correctness, hardware semantics,
timing, liveness beyond the fixed trace, and final-binary refinement remain
outside the theorem.

## Build and checks

The complete Qotom lab builder selects the profile with
`--blocking-ipc-integration`; that option requires
`--exception-integration`, which in turn requires the entry and copy-root
stages. The build emits `blocking-ipc-integration-audit.json` beside the ELF.

The focused checks are:

```sh
lake build LeanOS.QotomBlockingIPCIntegration LeanOS.SecurityClaims
LEANOS_HOSTED_BOUNDARY_ID=qotom-blocking-ipc \
  scripts/check-boot-handoff-host.sh ordinary
python3 scripts/audit-qotom-blocking-ipc-integration.py --self-test
python3 scripts/audit-qotom-blocking-ipc-integration.py \
  build/qotom-blocking-ipc-integration-lab/leanos-qotom-lab.elf
python3 scripts/test-qotom-blocking-ipc-integration-capture.py
```

The protected runner records the distinct profile and decoder/template hashes
when invoked with `--blocking-ipc-integration`. Capture artifacts belong in a
new `qotom-native-blocking-ipc-YYYYMMDD` observation directory; earlier entry
and exception histories are never rewritten as blocking-IPC evidence.

## Physical result

The [2026-09-13 Qotom observation](../hardware/lab/observations/qotom-native-blocking-ipc-20260913/README.md)
accepted ELF SHA256
`61e5a57715f48fe2e80888381a2178ad49d2ea088d3effa1ce0202bd7c0b6638`.
It observed the exact semantic suffix and final record, 92.4421041070018
seconds of post-terminal silence, watchdog reset, a changed FreeBSD boot epoch,
restored SSH, and a consumed one-shot request. The complete serial stream has
SHA256 `05523b6791a4cabfd9fae346454cf5ede3bf81c303c4f62dae68db389027e437`.
