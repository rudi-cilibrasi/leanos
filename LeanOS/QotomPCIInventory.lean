import LeanOS.PCIHeaderObservation

/-!
Closed inventory candidate for the retained 2026-09-10 Qotom AHCI capture.
This is not the older IDE observation and is not a selected boot profile.
The caller must supply a complete, canonically ordered enumeration; this model
cannot prove that hardware enumeration found every function. Command/status,
BARs and forwarding windows are preserved for subsequent quarantine policy,
not accepted as safe by this inventory comparison.
-/
namespace LeanOS.QotomPCIInventory

open DMAQuarantine PCIHeaderObservation

inductive Routing where
  | endpoint
  | bridge (primary secondary subordinate control : UInt64)
  deriving BEq, DecidableEq, Repr

structure Entry where
  bdf : BDF
  identity : Identity
  multifunction : Bool
  routing : Routing
  deriving BEq, DecidableEq, Repr

def project (header : Header) : Entry :=
  { bdf := header.raw.bdf
    identity := header.identity
    multifunction := header.multifunction
    routing := match header.layout with
      | .endpoint => .endpoint
      | .bridge r => .bridge r.primary r.secondary r.subordinate r.control }

/-- Captured AHCI identity and routing, not a union of firmware profiles. -/
def baseline : List Entry :=
  [ ⟨⟨0, 0, 0⟩, ⟨0x8086, 0x0f00, 0x060000⟩, false, .endpoint⟩,
    ⟨⟨0, 2, 0⟩, ⟨0x8086, 0x0f31, 0x030000⟩, false, .endpoint⟩,
    ⟨⟨0, 19, 0⟩, ⟨0x8086, 0x0f23, 0x010601⟩, false, .endpoint⟩,
    ⟨⟨0, 20, 0⟩, ⟨0x8086, 0x0f35, 0x0c0330⟩, false, .endpoint⟩,
    ⟨⟨0, 26, 0⟩, ⟨0x8086, 0x0f18, 0x108000⟩, false, .endpoint⟩,
    ⟨⟨0, 27, 0⟩, ⟨0x8086, 0x0f04, 0x040300⟩, false, .endpoint⟩,
    ⟨⟨0, 28, 0⟩, ⟨0x8086, 0x0f48, 0x060400⟩, true, .bridge 0 1 1 0x10⟩,
    ⟨⟨0, 28, 1⟩, ⟨0x8086, 0x0f4a, 0x060400⟩, true, .bridge 0 2 2 0x10⟩,
    ⟨⟨0, 28, 2⟩, ⟨0x8086, 0x0f4c, 0x060400⟩, true, .bridge 0 3 3 0x10⟩,
    ⟨⟨0, 28, 3⟩, ⟨0x8086, 0x0f4e, 0x060400⟩, true, .bridge 0 4 4 0x10⟩,
    ⟨⟨0, 31, 0⟩, ⟨0x8086, 0x0f1c, 0x060100⟩, true, .endpoint⟩,
    ⟨⟨0, 31, 3⟩, ⟨0x8086, 0x0f12, 0x0c0500⟩, false, .endpoint⟩,
    ⟨⟨1, 0, 0⟩, ⟨0x10ec, 0x8168, 0x020000⟩, false, .endpoint⟩,
    ⟨⟨2, 0, 0⟩, ⟨0x14e4, 0x4353, 0x028000⟩, false, .endpoint⟩,
    ⟨⟨3, 0, 0⟩, ⟨0x10ec, 0x8168, 0x020000⟩, false, .endpoint⟩ ]

inductive Error where
  | count
  | header (index : Nat) (reason : PCIHeaderObservation.Error)
  | address (index : Nat)
  | identity (index : Nat)
  | multifunction (index : Nat)
  | routing (index : Nat)
  deriving BEq, DecidableEq, Repr

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

theorem witness_has_fifteen_functions (w : Witness) : w.headers.length = 15 := by
  have h := congrArg List.length w.inventory
  simpa [baseline] using h

end LeanOS.QotomPCIInventory
