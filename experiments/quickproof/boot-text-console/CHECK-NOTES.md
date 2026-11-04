# Reading `CHECK.md` (the checks before the proof)

`CHECK.md` is `qp check`'s report for the final laws: the VST lint, 3,000 native
runs per law under ASan/UBSan, 20 CompCert-interpreter runs per law, and 40 live
mutants. Each mutant runs against both laws for up to 300 seeds. None of this is
proof. It shows that the laws are not vacuous and finds spec mistakes before
proof work starts.

## How the laws got here

| Step | Mutants killed | What changed |
| --- | --- | --- |
| First law, uniform random bytes | 0 / 22 | Header mutations were invisible: `qp mutants` recompiles library units only, and the header was included by the harness. Random bytes never form a Multiboot2 chain, so the writer was never reached. |
| Shaped `env.c` (well-formed chains, boundary geometries) | 7 / 22 | Only the model was mutated: the header still lived in the harness. |
| Header moved into a library unit (`patch/console_unit.c`), window sized exactly to the surface, completeness law added | 19 / 40 | The weakest survivors made the console reject everything or never enable. A safety law alone accepts that. |
| Law 1 also checks the displayed cell and the cursor after CR/LF; `env.c` adds truncated chains, wrapped and overlong tag sizes | 26 / 40 | The final laws. |

Native runs and the interpreter never failed on the unmutated code. The one
interpreter stop on the way was a name clash between `env.c` and a harness
helper in the interpreter's single translation unit, a known QuickProof
limitation (`docs/KNOWN-ISSUES.md`), fixed by renaming.

## The 14 survivors

| Kind | Mutants | Why they survive |
| --- | --- | --- |
| Equivalent under these laws | `available < 16` → `< 15`, `<= 16`; `total < 16` → `< 17`, `<= 16`; `total & 7` → `& 6`; `busy = 1` → `= 2`; `return 0` → `return 1` on enable's rejection path | The smallest acceptable chain is 48 bytes, totals must be multiples of 8 to be accepted, any nonzero `busy` blocks, and law 1 calls enable only on accepted geometries. |
| Behaviour the laws do not claim | the scroll copy loop bound `x < width` → `x < 1`; the zeroing of `out->bits` on rejection; the end tag accepted when not last (`||` → `&&`, 2 sites) | Scrolled cell contents, outputs after a rejection, and rejection of malformed chains after the framebuffer tag are not stated. |
| The model of the Lean export (2) | `pitch <= 512` → `< 512`; `pitch % 2 != 0` → `== 0` | The model defines "valid" for both laws, so mutating it moves the spec with the code. Its own check is the Lean refinement theorem of the export and the model's VST proof against the same conjunction (DEVIATIONS.md D3). |
| Distribution gap | `size < 8 || size > total - offset` → `&&` | Needs a framebuffer tag within 30 bytes of the end with an oversized size field. Random inputs rarely build it; the proof covers it (an out-of-bounds read there would make the theorem false). |
