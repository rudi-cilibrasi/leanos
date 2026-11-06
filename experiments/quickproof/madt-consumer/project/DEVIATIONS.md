# Deviations of the madt-consumer project

The theorem is about the program below, not about the kernel image byte for
byte. Every difference from the C the kernel compiles is listed here; quote a
result together with this file (QuickProof `docs/GUARANTEES.md`).

## D1. A wrapper unit (`patch/madt_unit.c`)

`qotom_bind_validated_madt_entries` and `qotom_bsp_publish` are `static
inline`. The unit includes `include/qotom_bsp_consumer.h` unchanged and gives
the consumer the external name `madt_bind`. The wrapper only forwards its
arguments, and its body is proved like every other function.

## D2. A shim for the generated `boundary-abi.h` (`patch/boundary-abi.h`)

The generated header declares every Lean export. The shim declares only the
three the consumer calls, with the generated prototypes:

- `leanos_qotom_madt_stream_byte_step_query`;
- `leanos_qotom_madt_nmi_policy_query`;
- `leanos_qotom_madt_stream_finish_query`.

## D3. The Lean exports are the law's

The kernel links the consumer with the C that Lean compiles from
`LeanOS/QotomMadtStream.lean`. The law links it with its own three functions
of the same names and prototypes instead: an adversarial Lean that may answer
any value, a different one on every call. Each function checks its call
against the obligations of `docs/qotom-madt-consumer-review.md`.

The consumer's proof does not depend on those functions. It holds for every
implementation that answers each call with a 64-bit value. The law
instantiates it with its own, and its specification asks each export only for
the consumer's next call (`MadtSpecs`).

What the answers of the real exports mean is what the Lean theorems state
(`LeanOS.QotomMadtStream`). The step that stays trusted is reading the law's
protocol, the review table and the Lean statements as the same. So does the
calling convention: the Lean-compiled functions take and return `uint64_t` as
declared (ADR 0029).

## Not deviations, but limits of the law

- The span is an object of exactly `length` bytes, as the kernel passes
  (`madt->bytes + 44`, `madt->length - 44` of a validated copy). That the copy
  is the authoritative, envelope-validated MADT and stays immutable is the
  caller's obligation, outside the theorem.
- That the observation was read safely on the executing CPU is outside it too.
- Partial correctness: termination is not claimed, though every loop is
  bounded.
