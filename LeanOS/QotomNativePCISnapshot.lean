import LeanOS.QotomNativePCIFields

/-! Proof model for a complete immutable snapshot checked by the scalar bridge.
The records and lists here are not an exported freestanding transport. -/
namespace LeanOS.QotomNativePCISnapshot
open PCIHeaderObservation QotomNativePCIFields

/-- Exactly sixteen physical word slots, independently of any declared count. -/
structure Input where
  bdf : DMAQuarantine.BDF
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  w4 : UInt64
  w5 : UInt64
  w6 : UInt64
  w7 : UInt64
  w8 : UInt64
  w9 : UInt64
  w10 : UInt64
  w11 : UInt64
  w12 : UInt64
  w13 : UInt64
  w14 : UInt64
  w15 : UInt64

def Input.raw (input : Input) : RawHeader :=
  ⟨input.bdf, [input.w0, input.w1, input.w2, input.w3, input.w4, input.w5, input.w6, input.w7, input.w8, input.w9, input.w10, input.w11, input.w12, input.w13, input.w14, input.w15]⟩

def Input.check (input : Input) (index : UInt64) : Bool :=
  checkHeader index input.bdf.bus input.bdf.device input.bdf.function input.w0 input.w1 input.w2 input.w3 input.w4 input.w5 input.w6 input.w7 input.w8 input.w9 input.w10 input.w11 input.w12 input.w13 input.w14 input.w15

theorem Input.check_binds (input : Input) (index : UInt64)
    (checked : input.check index = true) :
    ∃ header, decode input.raw = .ok header ∧
      some (QotomPCIInventory.project header) =
        QotomNativePCIInventory.baseline[index.toNat]? :=
  checkHeader_binds_raw index input.bdf.bus input.bdf.device input.bdf.function input.w0 input.w1 input.w2 input.w3 input.w4 input.w5 input.w6 input.w7 input.w8 input.w9 input.w10 input.w11 input.w12 input.w13 input.w14 input.w15 checked

/-- Success of the exact sixteen-iteration loop establishes a native inventory
witness whose raw headers are precisely the complete supplied snapshot. -/
theorem complete_snapshot (inputs : List Input) (count : inputs.length = 16)
    (checked : ∀ i : Fin inputs.length, (inputs[i]).check (UInt64.ofNat i.val) = true) :
    ∃ witness : QotomNativePCIInventory.Witness,
      witness.headers.map (·.raw) = inputs.map Input.raw := by
  classical
  let chosen (i : Fin inputs.length) : Header :=
    Classical.choose (Input.check_binds inputs[i] (UInt64.ofNat i.val) (checked i))
  have properties (i : Fin inputs.length) :=
    Classical.choose_spec (Input.check_binds inputs[i] (UInt64.ofNat i.val) (checked i))
  have preserved (i : Fin inputs.length) : (chosen i).raw = (inputs[i]).raw :=
    decode_preserves_raw _ _ (properties i).1
  let headers := List.ofFn chosen
  have raw : headers.map (·.raw) = inputs.map Input.raw := by
    apply List.ext_getElem
    · simp [headers]
    · intro i hi hj
      simpa [headers] using preserved ⟨i, by simpa using hj⟩
  have inventory : headers.map QotomPCIInventory.project = QotomNativePCIInventory.baseline := by
    apply List.ext_getElem
    · simp [headers, count, QotomNativePCIInventory.baseline, QotomPCIInventory.baseline]
    · intro i hi hj
      have bounded : i < inputs.length := by simpa [headers] using hi
      have native := (properties ⟨i, bounded⟩).2
      have narrow : (UInt64.ofNat i).toNat = i := by
        have small : i < 16 := by omega
        simp [Nat.mod_eq_of_lt (show i < 2^64 by omega)]
      change some (QotomPCIInventory.project (chosen ⟨i, bounded⟩)) =
        QotomNativePCIInventory.baseline[(UInt64.ofNat i).toNat]? at native
      rw [narrow] at native
      rw [List.getElem?_eq_getElem hj] at native
      have equal := Option.some.inj native
      simpa [headers, chosen] using equal
  exact ⟨⟨headers, inventory⟩, raw⟩

end LeanOS.QotomNativePCISnapshot
