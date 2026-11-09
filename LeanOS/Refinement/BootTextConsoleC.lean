import LeanOS.Refinement.CSymbolic
import LeanOS.BootTextConsole

/-!
# Rung 3 for `leanos_boot_text_surface` (issue #597)

`bootTextSurfaceC` is the C function the pinned Lean toolchain emits for the
`@[export leanos_boot_text_surface]` selector `BootTextConsole.checkRaw`, with
the `@[inline]` predicate `valid` inlined into it, extracted from the generated
`BootTextConsole.c` by `scripts/extract-generated-c.py`. The build re-runs the
extractor and fails if the emitted C no longer matches this AST.

Under the C-subset semantics of `LeanOS.Refinement.CSubset` it calls nothing,
and on every six words it returns exactly `checkRaw`. `bootTextSurfaceC_spec`
states the answer over the naturals, conjunct by conjunct; that statement is
the predicate the QuickProof model of the export assumes
(`experiments/quickproof/boot-text-console`, `valid_geo_iff` in its Coq proof),
so the model is the emitted C's meaning, not only a reading of the Lean source.
The theorems do not cover the calling convention, the compiler, the linker, the
boot path or QEMU (ADR 0029).
-/
namespace LeanOS.Refinement.BootTextConsoleC

open LeanOS.Refinement.CSubset LeanOS.Refinement.CSymbolic LeanOS.BootTextConsole

-- BEGIN GENERATED AST leanos_boot_text_surface
def bootTextSurfaceC : Func :=
  { params := [("v_kind_207_", .u64), ("v_bits_208_", .u64), ("v_address_209_", .u64), ("v_pitch_210_", .u64), ("v_width_211_", .u64), ("v_height_212_", .u64)]
    result := .u64
    body := [
      (.decl .u8 "v___y_214_"),
      (.decl .u8 "v___y_218_"),
      (.decl .u64 "v___x_237_"),
      (.decl .u8 "v___x_238_"),
      (.assign "v___x_237_" (.lit 2)),
      (.assign "v___x_238_" (.bin .decEq (.var "v_kind_207_") (.var "v___x_237_"))),
      (.ifZero "v___x_238_" [(.assign "v___y_218_" (.var "v___x_238_")), (.goto "v___jp_217_")] [(.decl .u64 "v___x_239_"), (.decl .u8 "v___x_240_"), (.assign "v___x_239_" (.lit 16)), (.assign "v___x_240_" (.bin .decEq (.var "v_bits_208_") (.var "v___x_239_"))), (.assign "v___y_218_" (.var "v___x_240_")), (.goto "v___jp_217_")]),
      (.block "v___jp_213_" [(.ifZero "v___y_214_" [(.decl .u64 "v___x_215_"), (.assign "v___x_215_" (.lit 0)), (.ret (.var "v___x_215_"))] [(.decl .u64 "v___x_216_"), (.assign "v___x_216_" (.lit 1)), (.ret (.var "v___x_216_"))])]),
      (.block "v___jp_217_" [(.ifZero "v___y_218_" [(.decl .u64 "v___x_219_"), (.assign "v___x_219_" (.lit 0)), (.ret (.var "v___x_219_"))] [(.decl .u64 "v___x_220_"), (.decl .u8 "v___x_221_"), (.assign "v___x_220_" (.lit 753664)), (.assign "v___x_221_" (.bin .decEq (.var "v_address_209_") (.var "v___x_220_"))), (.ifZero "v___x_221_" [(.assign "v___y_214_" (.var "v___x_221_")), (.goto "v___jp_213_")] [(.decl .u64 "v___x_222_"), (.decl .u8 "v___x_223_"), (.assign "v___x_222_" (.lit 0)), (.assign "v___x_223_" (.bin .decLt (.var "v___x_222_") (.var "v_width_211_"))), (.ifZero "v___x_223_" [(.assign "v___y_214_" (.var "v___x_223_")), (.goto "v___jp_213_")] [(.decl .u64 "v___x_224_"), (.decl .u8 "v___x_225_"), (.assign "v___x_224_" (.lit 160)), (.assign "v___x_225_" (.bin .decLe (.var "v_width_211_") (.var "v___x_224_"))), (.ifZero "v___x_225_" [(.assign "v___y_214_" (.var "v___x_225_")), (.goto "v___jp_213_")] [(.decl .u8 "v___x_226_"), (.assign "v___x_226_" (.bin .decLt (.var "v___x_222_") (.var "v_height_212_"))), (.ifZero "v___x_226_" [(.assign "v___y_214_" (.var "v___x_226_")), (.goto "v___jp_213_")] [(.decl .u64 "v___x_227_"), (.decl .u8 "v___x_228_"), (.assign "v___x_227_" (.lit 64)), (.assign "v___x_228_" (.bin .decLe (.var "v_height_212_") (.var "v___x_227_"))), (.ifZero "v___x_228_" [(.assign "v___y_214_" (.var "v___x_228_")), (.goto "v___jp_213_")] [(.decl .u64 "v___x_229_"), (.decl .u64 "v___x_230_"), (.decl .u8 "v___x_231_"), (.assign "v___x_229_" (.lit 2)), (.assign "v___x_230_" (.bin .mod (.var "v_pitch_210_") (.var "v___x_229_"))), (.assign "v___x_231_" (.bin .decEq (.var "v___x_230_") (.var "v___x_222_"))), (.ifZero "v___x_231_" [(.assign "v___y_214_" (.var "v___x_231_")), (.goto "v___jp_213_")] [(.decl .u64 "v___x_232_"), (.decl .u64 "v___x_233_"), (.decl .u8 "v___x_234_"), (.assign "v___x_232_" (.lit 1)), (.assign "v___x_233_" (.bin .shiftLeft (.var "v_width_211_") (.var "v___x_232_"))), (.assign "v___x_234_" (.bin .decLe (.var "v___x_233_") (.var "v_pitch_210_"))), (.ifZero "v___x_234_" [(.assign "v___y_214_" (.var "v___x_234_")), (.goto "v___jp_213_")] [(.decl .u64 "v___x_235_"), (.decl .u8 "v___x_236_"), (.assign "v___x_235_" (.lit 512)), (.assign "v___x_236_" (.bin .decLe (.var "v_pitch_210_") (.var "v___x_235_"))), (.assign "v___y_214_" (.var "v___x_236_")), (.goto "v___jp_213_")])])])])])])])])])] }
-- END GENERATED AST

/-- The emitter writes `2 * width` as a shift. -/
theorem shiftLeft_one (w : UInt64) : w <<< 1 = 2 * w := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_mul]
  simp only [UInt64.toNat_ofNat, Nat.shiftLeft_eq, Nat.reducePow, Nat.reduceMod]
  omega

/-- Rung 3: the emitted C of `leanos_boot_text_surface` computes the Lean
selector on every six words. -/
theorem bootTextSurfaceC_refines (kind bits address pitch width height : UInt64) :
    call bootTextSurfaceC [kind, bits, address, pitch, width, height] =
      some (checkRaw kind bits address pitch width height) := by
  apply callWith_of_tree noCalls _ bootTextSurfaceC rfl
  csym_refine [checkRaw, valid, shiftLeft_one]

/-- `valid` over the naturals, conjunct by conjunct. -/
theorem valid_iff_toNat (s : Surface) : valid s = true ↔
    s.kind.toNat = 2 ∧ s.bits.toNat = 16 ∧ s.address.toNat = 753664 ∧
      0 < s.width.toNat ∧ s.width.toNat ≤ 160 ∧ 0 < s.height.toNat ∧ s.height.toNat ≤ 64 ∧
      s.pitch.toNat % 2 = 0 ∧ 2 * s.width.toNat ≤ s.pitch.toNat ∧ s.pitch.toNat ≤ 512 := by
  simp only [valid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, ← UInt64.toNat_inj,
    UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, UInt64.toNat_mul, UInt64.toNat_mod,
    UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

/-- The emitted C's answer, stated over the naturals: 1 exactly on the
geometries of `valid`, else 0. This is the predicate the QuickProof model of
the export assumes (`valid_geo_iff` there), conjunct by conjunct. -/
theorem bootTextSurfaceC_spec (kind bits address pitch width height : UInt64) :
    call bootTextSurfaceC [kind, bits, address, pitch, width, height] =
      some (if kind.toNat = 2 ∧ bits.toNat = 16 ∧ address.toNat = 753664 ∧
               0 < width.toNat ∧ width.toNat ≤ 160 ∧ 0 < height.toNat ∧ height.toNat ≤ 64 ∧
               pitch.toNat % 2 = 0 ∧ 2 * width.toNat ≤ pitch.toNat ∧ pitch.toNat ≤ 512
            then 1 else 0) := by
  rw [bootTextSurfaceC_refines, checkRaw]
  by_cases h : valid ⟨kind, bits, address, pitch, width, height⟩ = true
  · have h' := (valid_iff_toNat _).mp h
    dsimp only at h'
    simp only [h, h', and_self, ↓reduceIte]
  · have h' := fun h' => h ((valid_iff_toNat _).mpr h')
    dsimp only at h'
    simp only [h, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i hp; exact absurd hp h'
    · rfl

/-- For a geometry the emitted C accepts, every cell with `row < height` and
`column < width` lies in the 32 KiB aperture
(`BootTextConsole.cell_inside_aperture`, read through the emitted C). -/
theorem bootTextSurfaceC_cell_inside_aperture (kind bits address pitch width height : UInt64)
    (row column : Nat)
    (h : call bootTextSurfaceC [kind, bits, address, pitch, width, height] = some 1)
    (hr : row < height.toNat) (hc : column < width.toNat) :
    row * pitch.toNat + 2 * column + 2 ≤ 32768 := by
  rw [bootTextSurfaceC_refines, Option.some_inj, checkRaw] at h
  have hv : valid ⟨kind, bits, address, pitch, width, height⟩ = true := by
    by_cases hv : valid ⟨kind, bits, address, pitch, width, height⟩ = true
    · exact hv
    · simp [hv] at h
  exact cell_inside_aperture _ row column hv hr hc

end LeanOS.Refinement.BootTextConsoleC
