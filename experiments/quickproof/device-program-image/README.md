# QuickProof project 10: the device-program image parser and policy admission (#638)

This experiment proves that the C which reads a device-program image accepts
exactly the images of the format `LeanOS.Wifi.Bytecode.Program.image` writes,
returns exactly the target, policy, code and blob those images encode, and
starts the executor from a zero scratch; and that the kernel's policy
admission returns exactly the subset test it states, for every image and
every pair of targets and policies. It uses
[QuickProof](https://github.com/genproof/quickproof-public) v0.1.0 (Coq 8.20.1,
VST 2.15, CompCert 3.15) on
[`hardware/wifi/wifi-exec.h`](../../../hardware/wifi/wifi-exec.h).

Every kernel that runs a Lean device program (the `device-service` image and
its fixtures, `keyboard-echo`, and the Qotom lab kernel) binds it in the same
order:

- `wifi_image_header` reads the image's target and declared policy;
- the kernel admits that policy against its own profile for the device
  (`device_service_admitted`, `network_source_admitted`,
  `dhcp_source_admitted`, or the lab's `lab_dev_policy_admitted`);
- `wifi_start` fills the executor state from the image and zeroes the 256 KiB
  scratch, and the generated executor (ADR 0020) runs the program.

The Lean theorems are about what happens after this. `ExecRefinement.step_eq`
holds for every program "the C image parser accepts" (`WF`: a blob, sink
table and descriptor map that fit 32 bits, and descriptor regions inside
scratch), and the confinement theorems say what an admitted policy permits.
Until now, that the parser accepts only such programs and copies their
fields faithfully rested on differential fuzzing. This theorem is about that
C, under CompCert's semantics for x86-64, for every input the law allows.
The decision record is ADR 0030, with the amendment of issue #638.

Most of the code was provable as written: the parser and `wifi_start` take
the image, its length and caller objects, and return a status. The policy
admission was not in the header. Its checks were written out in each caller:
the subset test in `boot/kernel.c`'s device service and again in the lab
kernel, and the frame-source shape twice, for the network and the DHCP
source. Commit 8f328b08 moved them into the header as three functions:

- `wifi_policy_within(p, max)`, the subset test the lab kernel calls for each
  of its device profiles;
- `wifi_service_admitted(t, p, want, max)`, the device-service shape: the
  exact target, a present policy, and the subset test;
- `wifi_source_admitted(t, p, max)`, the frame-source shape of the network
  and DHCP sources: no device, a present policy within the window, and no
  sink, descriptor, DMA or configuration right.

The kernel's three admission functions keep their names and call these. For
GCC, 63 of the 73 kernel and lab objects are identical before and after the
move, and the other 10 have identical stack usage.

## The law

The law is a C program in [`project/harness/`](project/harness/). Its first
comment states the claim, and that comment, not this summary, is what a reader
must review.

**`image_exact`: the parser, the start and the admission, for any image.**
The image has any 32-bit length and any bytes. The target, policy, header
length, executor state and scratch may hold any prior values, and the
admission compares any targets and any policies of at most 8 sinks and 16
descriptors. `main` calls one entry point. The law states:

- that the header returns 0 exactly when the image has a supported version
  (1, 2 or 3), the length each part needs, and fields the format allows: a
  well-formed bus/device/function, a BAR offset from 0x10 to 0x24, a window
  that is a nonzero multiple of 512 of at most 64 KiB, at most 8 sinks, at
  most 16 descriptors, and each descriptor of a known kind, a count from 1
  to 4096 and a limit, computed without overflow, inside the scratch;
- the exact target, header length and policy it writes, and that the
  policy's sink and descriptor entries past its counts keep their values;
- that `wifi_start` returns 0 exactly when the header does and the
  instruction count and blob length fit the rest of the image exactly; then
  the code and the blob are exactly the bytes after the header, every
  register, the stack pointer, pc and step count are 0, the stack entries
  are unchanged, and every scratch byte is 0;
- that on failure `wifi_start` leaves the scratch and every executor field
  but the target and policy unchanged;
- the exact result of each admission function: the sink, descriptor, window,
  DMA, bitmap and mask subset test, and each shape's target and presence
  conditions;
- that no function writes the image.

The law's reference decoder `read_image` reads the image word by word in the
order of the comment, independently of the header's code. `main` compares
the status and every byte of every object with it, so one law gives both
directions: each image the header accepts is one the format allows, and each
image the format allows is accepted with exactly its fields.

Not claimed (`project/DEVIATIONS.md`):

- what a policy permits (`LeanOS.DeviceProgramConfinement`) and what the
  executor does after the start (`ExecRefinement`);
- that each kernel profile is the Lean policy its comment names, which
  `scripts/check-device-policies.py` checks mechanically (#642), and that
  the format the law states is the one `Program.image` writes, checked by
  reading;
- a NULL or overlapping argument, or a policy of more than 8 sinks or 16
  descriptors passed to an admission (the kernel passes its program array
  and static objects, and the parser never builds such a policy);
- the scratch's `volatile` qualifier, which the proof defines away;
- termination, though every loop is bounded;
- anything about the compiled kernel (CompCert's C is not GCC's).

The header also accepts two encodings `Program.image` never writes, an
explicit BAR offset of 0x10 and an empty descriptor map under flags bit 1,
with the same meaning as the encoder's. The law states them.

## The proof's shape

`Defs.v` models the image as a list of bytes:

- `le32 bs k` is word@k, and `decode bs` follows the law comment step by
  step, giving the target, the policy and the header length, or `None`;
- `store P P0` lays a decoded policy over the prior object, which is the
  "entries past the counts keep their values" clause;
- `start bs` adds the instruction count and blob checks, and `started` is
  the executor state after a successful start;
- `within`, `service` and `source` are the admission booleans. Their bit
  tests are the same `Int` and `Int64` expression `(x & ~y) == 0` the C and
  the law compute.

Each function's specification (`Specs.v`) returns the model's status and
gives every object it writes as a model value. The header's specification
writes `store (decoded policy) P0` into the policy object; `wifi_start`'s
gives the whole executor state and a zero scratch, or the prior state and
scratch.

The law's `read_image` is proved to compute the same `decode` and `start`
from its own reading of the image, and its `check_policy` to compare every
field of the policy object, including the entries past the counts, with
`store`. `start_case` fills, copies and compares the whole scratch, and
its proof follows the header's specification through `dp_start` into both
branches.

Three steps needed care:

- The scratch is 262,144 bytes. Unfolding it overflowed Coq's stack in
  `entailer!`. The zeroing loop's invariant is stated as
  `Zrepeat 0 i ++ sublist i SCRATCH sc`, with the scratch and `Zrepeat` made
  opaque locally, and the law's loops over the scratch the same way.
- A lemma binder that appeared only inside a `data_at` of the law's state
  got the fully expanded representation type of the policy struct as its
  type. `subst`, `entailer!` and `abbreviate_semax` then took minutes or
  hung, one run reaching 5.4 GB. Writing the type (`pv : policy_t`) brought
  the same steps under a second. The first proof of `start_case`'s success
  branch still took 846 s, so it is split into three files.
- The header's one dead branch, `image_len >= 68 ? word@64 : 0xffffffff`,
  is unreachable because the version-3 length test precedes it. The proof
  closes it by contradiction, and the model has `word@64` only. The proof
  also shows that `16u * n` cannot wrap after the `n <= (len - H) / 16`
  test.

## Results

`qp verify` on a fresh clone: **PASS** ([`VERIFY.md`](VERIFY.md)).

| Theorem | Result | Axioms |
| --- | --- | --- |
| `image_exact` | PROVED | 13: standard + VST malloc |

The statement and `whole_prog` are identical to the frozen contract, and the
regenerated Clight is identical to the committed Clight. The proof sources
contain no `Admitted`, `admit`, `Axiom`, `Parameter` or `Conjecture`.

`qp check` ([`CHECK.md`](CHECK.md)) covers all 282 mutation sites:

- 3,000 native ASan/UBSan runs and 20 CompCert-interpreter runs, all clean;
- the VST lint is clean;
- 255 of the 259 live mutants killed. The other 23 sites are dead code (21)
  or do not compile (2). The 4 survivors are equivalent:
  - `hdr = 0` becomes `hdr = 1` in `wifi_start`: the header overwrites it
    before any read;
  - `return 1` becomes `return 2` in `wifi_is_sink` and `wifi_has_desc`:
    every caller tests the result for zero only;
  - `image_len >= 68` becomes `>= 67` in the header's dead branch above.

What it took (development machine, 12 CPUs):

| Item | Measure |
| --- | --- |
| C under test | the 304-line header (9 functions), 6 wrappers; 1 law, 411 lines and a 31-line header |
| Coq written | 7,089 lines in 51 files (the contract included), by component below |
| Shared model and specs | `Defs.v`, `Specs.v`, `SpecTypes.v`, `Bodies.v`: 845 lines |
| The header's nine functions and their wrappers | `Body*.v`, `Hd*.v`: 2,227 lines in 18 files |
| The law's `main`, callees and helpers | `Law*.v` and its contract: 3,881 lines in 28 files + 136 lines |
| Who wrote it | AI agents (Claude Opus 5.5 in Claude Code). The main session wrote the refactor and the law, and an agent the model and the specifications. Two more agents then proved the bodies and the law in parallel. The bodies took 3.4 hours; the header parser alone is 1,068 lines in 8 files. The law took about 11.5 hours, of which `read_image` and `start_case` took most. |

`qp verify` checks all of it in 33 minutes with 6 build jobs. Every file
compiles alone in under 6 minutes and 1.7 GB: the slowest is the law's
`LawCheckPol.v` (359 s), and the largest `LawStartGood.v` (1.68 GB).

## Reproducing

```sh
scripts/check-quickproof.sh --check device-program-image
```

[`check.conf`](check.conf) makes `qp check` run all 282 mutation sites
rather than a sample of 40, with 1,000 native runs per mutant, so the kill
count the gate compares covers the whole header. It gives each interpreter
seed 90 s, because a `wifi_start` seed fills, copies and compares the whole
scratch. `scripts/check-quickproof-pins.sh`, part of `scripts/check.sh`,
fails when `hardware/wifi/wifi-exec.h`, `LeanOS/Wifi/Bytecode.lean` (the
encoder whose format the law states) or any file of `project/` or `proof/`
differs from [`pins.tsv`](pins.tsv).

## Files

- `project/`: the QuickProof project. It holds `project.conf` (the pins),
  `quickproof.conf`, the law, `env/` (input distributions for the native and
  interpreter runs only), `patch/` (the wrapper unit and its header) and
  `DEVIATIONS.md`.
- `proof/src/`: the Coq proof sources; everything else in the proof
  repository is regenerated by `qp assemble`.
- `CHECK.md`, `VERIFY.md`, `check.conf`, `pins.tsv`.

QuickProof is under the PolyForm Noncommercial License 1.0.0, and its
toolchain includes CompCert under the INRIA Non-Commercial License. The files
here were written for LeanOS and are under its license. Running them uses
QuickProof under its own.
