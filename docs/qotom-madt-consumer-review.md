# Qotom MADT stream consumer review

The two scalar exports are suitable as a processor-topology/BSP candidate
interface. Their successful result does not authorize allocation, device
ownership, interrupt delivery, or CPL3 entry by itself. This review covers the
interface added by PR #385; production integration remains under #331 and the
whole platform admission issue #291.

| Caller obligation | Evidence and integration requirement |
| --- | --- |
| Select the authoritative MADT and validate its immutable copy | `boot/kernel.c:boot_allocate` already selects the root, copies advertised tables, rejects duplicate addresses, selects a unique MADT, and calls `validate_generated_madt_envelope`. The Qotom consumer must retain this path. `validated_terminal_finish_binding` explicitly assumes successful envelope validation and a complete fixed header; it does not establish physical-copy provenance. |
| Initialize and consume the actual bytes | Start with `[44,0,0,0,0,0,0,256,0,0,0,0]`; consume entries through the validated table length. `QotomMadtStreamRun.run` and the C replay carry actual returned projections. |
| Keep projection inputs stable | All projections for one transition use one old-state snapshot and one byte. Stage words 3–14 before replacing state. Both the existing production singleton loop and the new hosted replay follow this pattern. Updating a state field between calls invalidates the model correspondence. |
| Fail on rejection or inconsistent ABI/status | Check version 1, zero error, active status on intermediate bytes, terminal status on the final byte, exact next offset and consumed-byte echo. Rejected state cannot be reused. The C replay checks these conditions, including unsupported projections. |
| Preserve the terminal result into BSP binding | Pass actual status/error and all twelve final words to finish. The theorem derives count, offset, cleared partial state, admitted ID and all bitset limbs; C must not replace them with expected constants. The harness copies `result+3` into the finish input. |
| Supply a physical BSP observation | Use the observed CPUID EDX, MSR-read availability, IA32_APIC_BASE and sampled executing ID from the same executing CPU. The scalar interface checks widths and binding predicates; it does not make an unsafe MSR read safe or prove that supplied observations were obtained from hardware. The captured observation is manifest-hash pinned in replay. |
| Preserve profile separation | `boot/kernel.c:validate_generated_madt_entries` currently calls the existing singleton export and requires count one. The new Qotom exports have separate generated ABI rows; no runtime profile switch or kernel call was introduced. Integrating them requires an explicit Qotom platform path, rather than weakening the singleton policy. |
| Retain freestanding closure | The object probe retains both new exports and checks the exact symbol set with no unresolved Lean-runtime dependencies. Hosted ordinary and pinned ASan/UBSan builds check generated ABI use and function-entry coverage. Production must repeat closure checks on the actual linked kernel. |
| Treat candidate success as one part of platform admission | The stream checks non-processor record widths, not routing fields. Captured malformed NMI fields, AP dormancy, DMA quarantine, no-SMAP isolation and the bounded CPL3 scenario remain unresolved physical obligations. No topology success may bypass those checks. |

The formal result is soundness of successful initialized traversal and exact
finish equivalence with the typed BSP binder. It is not a completeness proof
that every reference-admitted byte stream succeeds. The complete-table theorem
constructs the topology witness from the authoritative decoded snapshot, so
its finish result does not depend on a caller-invented parsed inventory.

The hosted replay composes every table result, including rejected parses,
with all standalone observation cases that retain the valid terminal shape.
This covers native BSP values, unavailable reads, missing features, wrong ID,
wrong APIC state and scalar-width violations on actual parser outputs. The
standalone terminal-field mutation probes remain independent negative checks.

No production source or hardware state was changed by this review. Kernel
integration needs its own profile, final-object, emulator and physical evidence;
it is not a reason to describe this candidate interface as full Qotom admission.
