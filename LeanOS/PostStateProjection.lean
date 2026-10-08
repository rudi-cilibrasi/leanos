import LeanOS.CompositeDispatcher

/-!
# Hosted post-state projections (issue #476)

The model oracle compares reply words. A reply word says that an allocation
was accepted, but not which bytes the published frame holds. Likewise a copy
or revoke vector checks the reply, not the capability table it leaves behind.

These exports project the post-state itself, from the same canonical states
the scenario and dispatcher vectors use:

* `leanos_frame_scrub_projection` digests a frame's bytes after a
  frame-budget scenario state, with an explicit any-nonzero bit;
* `leanos_frame_budget_capability_row` encodes one capability row of that
  scenario's scrub state; and
* `leanos_mixed_capability_row` encodes one capability row of the complete
  authoritative state behind a composite mixed edge.

They are hosted-only. They materialize model states, which allocates, so they
are linked with the Lean runtime by `scripts/check-poststate-host.sh` and are
not part of any boot image. This module adds no proof: it measures more of
the trusted boundary between Lean and its generated C.
-/
namespace LeanOS.PostStateProjection

open LeanOS

/-- Answer for an undecodable state word. No valid projection has all bits
set: a capability row never sets bits 30-39, and a digest never sets bits
33-63. -/
def invalid : UInt64 := 0xffffffffffffffff

/-! ## Frame contents -/

/-- FNV-1a over all `FrameScrub.frameBytes` bytes of `frame` in the low 32
bits, and bit 32 set exactly when some byte is not zero. A projection below
`2^32` therefore states that the whole frame is zero. -/
def frameDigest (bytes : FrameScrub.FrameBytes) (frame : FrameScrub.FrameId) : UInt64 :=
  Nat.fold FrameScrub.frameBytes (fun offset _ acc =>
    let byte := (bytes frame offset).toUInt64
    let hash := ((acc &&& 0xffffffff) ^^^ byte) * 16777619 &&& 0xffffffff
    let nonzero := (acc >>> 32) ||| (if byte = 0 then 0 else 1)
    (nonzero <<< 32) ||| hash) 2166136261

def frameBudgetStates : List FrameBudgetScenario.StateId :=
  [.initial, .aAllocated, .aExhausted, .bSelected, .bAllocated, .aTerminated,
   .bFresh, .staleDenied, .complete, .aReleased, .releaseDenied, .releaseComplete]

def decodeFrameBudgetState (word : UInt64) : Option FrameBudgetScenario.StateId :=
  frameBudgetStates.find? fun id => FrameBudgetScenario.encodeState id = word

@[export leanos_frame_scrub_projection]
def frameScrubProjection (stateWord frame : UInt64) : UInt64 :=
  match decodeFrameBudgetState stateWord with
  | some id => frameDigest (FrameBudgetScenario.materialize id).scrub.bytes frame.toNat
  | none => invalid

/-! ## Capability rows -/

def rightsBits (rights : Capability.Rights) : UInt64 :=
  (if rights.read then 1 else 0) ||| (if rights.write then 2 else 0) |||
    (if rights.send then 4 else 0) ||| (if rights.receive then 8 else 0) |||
    (if rights.grant then 16 else 0) ||| (if rights.revoke then 32 else 0)

def kindBits : Capability.ObjectKind → UInt64
  | .memory => 1
  | .addressSpace => 2
  | .endpoint => 3

/-- One capability-table row: bit 63 present, bits 40-55 identity (the
generation a stale handle is checked against), bits 24-29 rights, bits
20-21 kind, bits 0-19 object. An empty slot is zero. -/
def rowWord : Option Capability.Capability → UInt64
  | none => 0
  | some capability =>
    (0x8000000000000000 : UInt64) |||
      ((capability.identity.toUInt64 &&& 0xffff) <<< 40) |||
      (rightsBits capability.rights <<< 24) |||
      (kindBits capability.kind <<< 20) |||
      (capability.object.toUInt64 &&& 0xfffff)

@[export leanos_frame_budget_capability_row]
def frameBudgetCapabilityRow (stateWord subject slot : UInt64) : UInt64 :=
  match decodeFrameBudgetState stateWord with
  | some id =>
    rowWord ((FrameBudgetScenario.materialize id).scrub.memory.capabilities.slots
      subject.toNat slot.toNat)
  | none => invalid

@[export leanos_mixed_capability_row]
def mixedCapabilityRow (stateWord subject slot : UInt64) : UInt64 :=
  match CompositeDispatcher.decodeMixedState stateWord with
  | .ok id =>
    match CompositeDispatcher.mixedMaterialize id with
    | .ok state => rowWord (state.capabilities.slots subject.toNat slot.toNat)
    | .error _ => invalid
  | .error _ => invalid

/-! ## The post-state corpus -/

structure Vector where
  id : String
  adapter : Nat
  words : List UInt64
  expected : UInt64

/-- Adapter numbering of the post-state corpus: 0 frame digest (arity 2),
1 frame-budget capability row (arity 3), 2 mixed capability row (arity 3). -/
def adapters : List (Nat × String × Nat) :=
  [(0, "leanos_frame_scrub_projection", 2),
   (1, "leanos_frame_budget_capability_row", 3),
   (2, "leanos_mixed_capability_row", 3)]

private def scrub (id : String) (state : FrameBudgetScenario.StateId) (frame : UInt64) :
    Vector :=
  let word := FrameBudgetScenario.encodeState state
  { id, adapter := 0, words := [word, frame], expected := frameScrubProjection word frame }

private def budgetRow (id : String) (state : FrameBudgetScenario.StateId)
    (subject slot : UInt64) : Vector :=
  let word := FrameBudgetScenario.encodeState state
  { id, adapter := 1, words := [word, subject, slot]
    expected := frameBudgetCapabilityRow word subject slot }

private def mixedRow (id : String) (state : CompositeDispatcher.MixedStateId)
    (subject slot : UInt64) : Vector :=
  let word := CompositeDispatcher.encodeMixedState state
  { id, adapter := 2, words := [word, subject, slot]
    expected := mixedCapabilityRow word subject slot }

/-- Frame 100 is allocated to A, written dirty (0xa5 at offset 0), released
dirty when A terminates, and republished to B: the reallocation must read as
all zero. Frame 101 starts with 0xcc boot bytes and is scrubbed when B
allocates it. -/
def frameVectors : List Vector := [
  scrub "frame-scrub.initial.frame-100-boot-bytes" .initial 100,
  scrub "frame-scrub.a-allocated.frame-100-written" .aAllocated 100,
  scrub "frame-scrub.b-allocated.frame-101-scrubbed" .bAllocated 101,
  scrub "frame-scrub.a-terminated.frame-100-released-dirty" .aTerminated 100,
  scrub "frame-scrub.b-fresh.frame-100-republished-zero" .bFresh 100,
  scrub "frame-scrub.a-released.frame-100-released-dirty" .aReleased 100,
  { id := "frame-scrub.invalid-state", adapter := 0, words := [0x4c01, 100]
    expected := frameScrubProjection 0x4c01 100 }]

/-- Allocation and release rows: A's slot 0 after allocation and after
termination, and B's fresh slot 1 with its new identity. -/
def budgetRowVectors : List Vector := [
  budgetRow "frame-budget-row.a-allocated.a-slot-0" .aAllocated 0 0,
  budgetRow "frame-budget-row.a-terminated.a-slot-0-retired" .aTerminated 0 0,
  budgetRow "frame-budget-row.b-allocated.b-slot-0" .bAllocated 1 0,
  budgetRow "frame-budget-row.b-fresh.b-slot-1-new-identity" .bFresh 1 1,
  budgetRow "frame-budget-row.a-released.a-slot-0-retired" .aReleased 0 0]

/-- Copy and revoke rows of the composite mixed scenario: the transferred
capability before and after revocation, the destination slot before and
after the fresh copy (whose identity is new), and the current subject's slot
0, the revoke authority and copy source, which must not change. -/
def mixedRowVectors : List Vector := [
  mixedRow "mixed-row.transfer-accepted.subject-2-slot-3" .transferAccepted 2 3,
  mixedRow "mixed-row.capability-revoked.subject-2-slot-3-empty"
    .transferredCapabilityRevoked 2 3,
  mixedRow "mixed-row.capability-revoked.subject-2-slot-0-authority"
    .transferredCapabilityRevoked 2 0,
  mixedRow "mixed-row.stale-rejected.subject-2-slot-3-empty" .staleHandleRejected 2 3,
  mixedRow "mixed-row.capability-copied.subject-2-slot-3" .freshCapabilityCopied 2 3,
  mixedRow "mixed-row.capability-copied.subject-2-slot-0-source" .freshCapabilityCopied 2 0]

def vectors : List Vector := frameVectors ++ budgetRowVectors ++ mixedRowVectors

theorem poststate_shape : vectors.length = 18 := by decide

private def wordsText : List UInt64 → String
  | [] => ""
  | [word] => toString word
  | word :: rest => toString word ++ "," ++ wordsText rest

/-- Rendered by `scripts/render-poststate-header.awk` into `poststate.h`. -/
def emit : IO Unit := do
  IO.println "leanos-poststate\t1"
  for (id, symbol, arity) in adapters do
    IO.println s!"adapter\t{id}\t{symbol}\t{arity}"
  for entry in vectors.zipIdx do
    let v := entry.1
    IO.println s!"{entry.2}\t{v.id}\t{v.adapter}\t{wordsText v.words}\t{v.expected}"

end LeanOS.PostStateProjection
