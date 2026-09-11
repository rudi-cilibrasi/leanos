import LeanOS.QotomPCIInventory

/-! Closed candidate for the native ECAM capture. This distinct type cannot
satisfy the historical fifteen-function inventory witness. It preserves raw
register observations and grants no quarantine, DMA or CPL3 authority. -/
namespace LeanOS.QotomNativePCIInventory
open DMAQuarantine PCIHeaderObservation
abbrev Entry := QotomPCIInventory.Entry
abbrev Error := QotomPCIInventory.Error
abbrev project := QotomPCIInventory.project

/-- The shared identity/routing projection matches the historical snapshot;
only the native EHCI function at 00:1d.0 is added, in canonical BDF order. -/
def baseline : List Entry :=
  QotomPCIInventory.baseline.take 10 ++
    [⟨⟨0, 29, 0⟩, ⟨0x8086, 0x0f34, 0x0c0320⟩, false, .endpoint⟩] ++
  QotomPCIInventory.baseline.drop 10

private def compareEntries : Nat → List Entry → List Entry → Except Error Unit
  | _, [], [] => .ok ()
  | i, actual :: rest, expected :: tail =>
    if actual.bdf != expected.bdf then .error (.address i)
    else if actual.identity != expected.identity then .error (.identity i)
    else if actual.multifunction != expected.multifunction then .error (.multifunction i)
    else if actual.routing != expected.routing then .error (.routing i)
    else compareEntries (i + 1) rest tail
  | _, _, _ => .error .count

private def decodeAll : Nat → List RawHeader → Except Error (List Header)
  | _, [] => .ok []
  | index, raw :: rest => do
    let h ← (decode raw).mapError (.header index)
    let tail ← decodeAll (index + 1) rest
    pure (h :: tail)

private theorem decodeAll_preserves_raw (raw : List RawHeader) (index : Nat)
    (headers : List Header) (accepted : decodeAll index raw = .ok headers) :
    headers.map (·.raw) = raw := by
  induction raw generalizing index headers with
  | nil =>
    simp [decodeAll] at accepted
    subst headers
    rfl
  | cons first rest ih =>
    cases decoded : decode first with
    | error reason => simp [Bind.bind, Except.bind, Except.mapError, decodeAll, decoded] at accepted
    | ok header =>
      cases tailDecoded : decodeAll (index + 1) rest with
      | error reason => simp [Bind.bind, Except.bind, Except.mapError, decodeAll, decoded, tailDecoded] at accepted
      | ok tail =>
        simp [Pure.pure, Except.pure, Bind.bind, Except.bind, Except.mapError, decodeAll, decoded, tailDecoded] at accepted
        subst headers
        simp only [List.map_cons]
        rw [decode_preserves_raw first header decoded,
          ih (index + 1) tail tailDecoded]

/-- Retains every raw register, including windows and command bits. The proof
binds the entire observed inventory to one baseline; it confers no permission
to enter CPL3 or to access q35 remapping registers. -/
structure Witness where
  headers : List Header
  inventory : headers.map project = baseline

def check (raw : List RawHeader) : Except Error Witness := do
  if raw.length != baseline.length then throw .count
  let headers ← decodeAll 0 raw
  compareEntries 0 (headers.map project) baseline
  if same : headers.map project = baseline then
    pure ⟨headers, same⟩
  else throw .count

theorem check_preserves_raw (raw : List RawHeader) (w : Witness)
    (accepted : check raw = .ok w) : w.headers.map (·.raw) = raw := by
  unfold check at accepted
  cases decoded : decodeAll 0 raw with
  | error reason =>
    simp [decoded, Bind.bind, Except.bind] at accepted
    split at accepted <;> contradiction
  | ok headers =>
    cases compared : compareEntries 0 (headers.map project) baseline with
    | error reason =>
      simp [decoded, compared, Bind.bind, Except.bind] at accepted
      split at accepted <;> contradiction
    | ok result =>
      by_cases same : headers.map project = baseline
      · have comparedBaseline : compareEntries 0 baseline baseline = .ok result := by
          simpa only [same] using compared
        simp [decoded, same, comparedBaseline, Bind.bind, Except.bind,
          Pure.pure, Except.pure] at accepted
        split at accepted
        · cases accepted
          exact decodeAll_preserves_raw raw 0 headers decoded
        · contradiction
      · simp [decoded, compared, same, Bind.bind, Except.bind] at accepted
        split at accepted <;> contradiction

theorem witness_has_complete_inventory (w : Witness) :
    w.headers.map project = baseline := w.inventory

theorem witness_has_sixteen_functions (w : Witness) : w.headers.length = 16 := by
  have h := congrArg List.length w.inventory
  simpa [baseline, QotomPCIInventory.baseline] using h


/-- The native witness cannot be substituted for the historical inventory. -/
theorem distinct_from_historical (native : Witness)
    (historical : QotomPCIInventory.Witness) : native.headers ≠ historical.headers := by
  intro same
  have impossible : (16 : Nat) = 15 := by
    calc
      16 = native.headers.length := (witness_has_sixteen_functions native).symm
      _ = historical.headers.length := congrArg List.length same
      _ = 15 := QotomPCIInventory.witness_has_fifteen_functions historical
  cases impossible

/-- Complete immutable snapshot transport: sixteen slots of BDF plus sixteen
raw dwords. Both the declared count and physical array size are checked before
reading any slot. This hosted boundary allocates Lean objects; it is not yet
a freestanding or hardware enumeration adapter. Success is inventory match
only, not quarantine. The array argument is consumed by the generated C ABI. -/
@[export leanos_qotom_native_pci_inventory_check]
def checkWords (count : UInt64) (words : Array UInt64) : UInt64 :=
  if count != 16 then QotomPCIInventory.Error.count.code
  else if words.size != 304 then 0x10001
  else
    let raw := (List.range 16).map fun index =>
      let offset := index * 19
      let bdf : BDF := ⟨words.getD offset 0, words.getD (offset + 1) 0,
        words.getD (offset + 2) 0⟩
      let dwords := (List.range 16).map fun i => words.getD (offset + 3 + i) 0
      ({ bdf := bdf, words := dwords } : RawHeader)
    match check raw with
    | .ok _ => 1
    | .error reason => QotomPCIInventory.Error.code reason

end LeanOS.QotomNativePCIInventory
