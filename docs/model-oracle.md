# Model-oracle replay

`LeanOS.Oracle` is the version-one, bounded corpus for every currently exported
freestanding adapter: `KernelTransition.bootTransition` and
`Syscall.syscallDemo`, `IPCSyscall.ipcDemo`, and
`Preemption.preemptionDemo`, `Preemption.resumableDemo`, and
`BootAllocation.check`, `Interrupt.userReturnDemo`, and
`BlockingIPC.blockingIpcDemo`. Its stable 75-vector order covers accepted calls,
typed decoding failures, invalid state and permission encodings, boot-handoff
and publication-order failures, both bounded A/B preemption directions, and
maximum `UInt64` boundary words, plus accepted initial/syscall/scheduler returns
and adversarial return frames and contexts. The Lean
checks evaluate every expected result from
the adapter definition and connect the accepted and rejected examples to the
source models.

The resumable adapter executes both composite context-bank legs and packs the
restored owner/address-space, logical stack marker, and r12 marker together
with the outgoing saved owner/stack/r12 markers. Target and outgoing
descriptors combine kernel-owned bank metadata with each frame's actual saved
RSP; r12 markers also come from the two concrete buffers. The boot path thus
rejects a corrupted outgoing stack or exchanged bank before the success
transcript. B is restored from a kernel-owned complete initial image and checks
all fifteen distinct GPR values before its first authorized syscall, so the
boot protocol also fails if any A register is inherited. The kernel validates
the exact initial RIP/CS/RFLAGS/RSP/SS before restore, and a live-image negative
mutates RFLAGS to a different valid user value and requires rejection. Exact kernel-owned
RIP/RSP/RFLAGS snapshots additionally guard the
full saved return-frame words that are intentionally too large for the compact
oracle descriptor, so exchanging A and B is rejected by the same generated-code
witness rather than only by a
serial symptom check. `./scripts/generate-oracle.sh` emits `corpus.tsv` and a C header from that one
Lean executable. The file records its schema and source revision. The complete
proof gate replays it against hosted Lean-generated C. Image construction embeds
the same generated header; QEMU must report an ordered result for every vector
before its guest success signal. The runner constructs its expected transcript
from `corpus.tsv`, so a summary PASS cannot replace a missing, changed, or
reordered vector. The corpus is finite, deterministic, contains only scalar
words, and performs no allocation at the freestanding entry points.

These comparisons test encoders, exported entry points, result decoding, ABI
glue, and the bounded emulator path for the listed cases. They are reproducible
integration evidence, not exhaustive exploration, semantic refinement,
verified compilation, or proof about the final binary. Corpus extraction, Lean
code generation, the C compiler, ABI, C/assembly glue, linker, serial checker,
QEMU, firmware, and hardware semantics remain trusted. New boot-reachable
adapters must extend the versioned corpus and its model-agreement checks. The
blocking-IPC vectors are also consumed by the guest's block, send/wake,
dispatch, and delivery gates, so payload words cannot select the trusted caller
or active address space.

The return adapter uses one bounded synthetic subject/address-space fixture.
Its five scalar words encode a kernel-owned purpose/context mode, RIP, RSP,
packed CS/SS selectors, and RFLAGS. The negative matrix covers noncanonical and
out-of-region addresses, wrong selectors and origin, IOPL/NT/VM/AC/DF/IF,
stale subject/address-space/CR3 bindings, fatal and diagnostic modes, and a
validate-then-mutate attempt. The exported scalar path remains allocation-free;
the richer Lean transition still returns the complete accepted request as its
attestation.

Run the complete local evidence path with:

```sh
./scripts/check.sh
./scripts/check-markdown.sh
./scripts/build-image.sh
./scripts/run-image.sh
```
