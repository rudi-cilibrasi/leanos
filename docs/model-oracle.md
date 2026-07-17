# Model-oracle replay

`LeanOS.Oracle` is the version-one, bounded corpus for every currently exported
freestanding adapter: `KernelTransition.bootTransition` and
`Syscall.syscallDemo`, `IPCSyscall.ipcDemo`, and
`Preemption.preemptionDemo`, and `BootAllocation.check`. Its stable
twenty-six-vector
order covers accepted calls,
typed decoding failures, invalid state and permission encodings, boot-handoff
and publication-order failures, both bounded A/B preemption directions, and
maximum `UInt64` boundary words. The Lean
checks evaluate every expected result from
the adapter definition and connect the accepted and rejected examples to the
source models.

`./scripts/generate-oracle.sh` emits `corpus.tsv` and a C header from that one
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
adapters must extend the versioned corpus and its model-agreement checks.

Run the complete local evidence path with:

```sh
./scripts/check.sh
./scripts/check-markdown.sh
./scripts/build-image.sh
./scripts/run-image.sh
```
