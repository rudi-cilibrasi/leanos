# Closed-root machine return

`return.S` implements the machine tail following the plan in
`LeanOS.KernelRootReturn`. It is entered by JMP, with the exact validated
20-word register/IRET bank at RSP, the authorized subject root in RDI and
the trusted closed root in RSI. It checks IF clear, PCID/PGE disabled,
the current closed-root identity, and a nonzero, aligned, distinct target
below 16 MiB. It unconditionally reloads CR3 and checks readback before
restoring all 15 GPRs and executing IRET. It does not write the outgoing bank
or call C. PUSHF temporarily uses the writable word immediately below the bank;
that space must also be mapped and owned by the caller.

Numeric root checks do not establish table provenance, protected-frame
exclusion or ownership stability. Frame validation and flag normalization must
finish before entry. The kernel controls and page tables needed by IRET,
exception entry and the return code must remain valid in both roots. Rejection
halts without a cleanup-success claim. Exceptional entry must independently
establish closure and terminate; a CR3 write is not an atomic return to user.

The linked instruction audit checks every instruction in the primitive and
its terminal block. Eighteen mutations cover missing guards/reload/readback,
extra calls, unsupported STAC, register changes, frame writes, wrong IRET,
terminal escape and undecodable bytes. This is a local instruction contract,
not a whole-image control-flow or ownership proof.

The isolated QEMU fixture uses `max,smap=off`, two fixture-owned roots and
two subject-only pages for code and stack. Its closed root omits those pages;
its subject root makes them user accessible. A real CPL3 INT 0x80 immediately
captures the returned GPR bank, closes the root, and compares every GPR and
all five IRET fields against independent expected values. The original cases cover
normal return, eight rejected preconditions, wrong-register restoration,
missing reload, readback mismatch, and injected NMI before register restoration
and immediately before IRET. NMI uses a separate TSS IST stack, checks its
hardware frame, reloads the closed root and terminates. Injected checkpoint
variants intentionally differ from the audited primitive; they are execution
experiments, not accepted production objects.

Six additional cases exercise terminal return-fault handling: an invalid CS
selector (#GP), a non-present CS (#NP), a non-present SS, failed #GP delivery
through a non-present gate (#DF), omitted fault-handler closure, and a wrong
fault IST. The first four must observe the subject root at entry, reload and
read back the closed root, verify the expected error code and separate IST
frame, and terminate. Ordinary faults also check that the saved RIP points to
the audited IRETQ. The double-fault case does not treat its saved RIP as valid
restart evidence. The two negative handlers must fail without a closure-success
marker. All twenty cases audit the linked primitive unless they intentionally
mutate it. Descriptor/frame corruption is deliberate violation of the caller's
preconditions to exercise terminal handling; it is not successful admission of
an invalid return frame.

The non-present-SS case records the actual exception vector in `results.json`.
Intel documents #SS for a non-present stack segment, but QEMU TCG's
`helper_ret_protected` raises #NP at its stack-descriptor presence check. The
fixture accepts only vector 11 or 12 with selector error 0x18 and the same
closure/stack checks. A recorded 11 is #NP execution evidence, not #SS coverage
or hardware conformance. References: [Intel system programming manual, exception
handling](https://www.intel.com/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-software-developer-vol-3a-part-1-manual.pdf)
and [QEMU segment return implementation](https://gitlab.com/qemu-project/qemu/-/blob/master/target/i386/tcg/seg_helper.c).

These fixtures do not exercise every NMI timing, IRET fault, nested exception,
or cleanup failure. They cover one deliberately induced double-fault sequence,
not arbitrary double-fault recovery or an unusable IST. The dedicated fixture
stacks have no guard pages. Fixture mappings are synthetic, not the production
root collector. Production entry/return dispatch, trusted frame ownership,
profile controls, terminal cleanup and final-object admission remain required
for issue #329. No production image links this primitive yet, and these results
do not admit Qotom or complete physical CPL3 acceptance.

Run the checks with each pinned compiler via `LEANOS_CC`:

```sh
python3 scripts/check-closed-root-return.py --self-test
python3 scripts/test-closed-root-return-qemu.py
```

Execution reports include compiler/QEMU versions, exact ELF and primitive
object hashes, captures and halted-register evidence under
`build/closed-root-return/qemu-COMPILER/`.
