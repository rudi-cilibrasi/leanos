import LeanOS.DMAQuarantine

/-!
Bounded decoding of a conventional PCI configuration header. This describes
observations, not enumeration completeness, DMA containment, or admission.
Offsets follow include/uapi/linux/pci_regs.h in the Linux source tree.
All sixteen raw dwords are retained, including reserved and device-specific
bits; no register is written and no BAR sizing probe is performed.
-/
namespace LeanOS.PCIHeaderObservation

open DMAQuarantine

structure RawHeader where
  bdf : BDF
  words : List UInt64
  deriving BEq, DecidableEq, Repr

/-- Window fields remain raw register pairs. Decoding does not establish that
they describe enabled, nonoverlapping, or safe forwarding ranges. -/
structure BridgeRegisters where
  primary : UInt64
  secondary : UInt64
  subordinate : UInt64
  control : UInt64
  ioBaseLimit : UInt64
  secondaryStatus : UInt64
  memoryBaseLimit : UInt64
  prefetchBaseLimit : UInt64
  prefetchBaseUpper : UInt64
  prefetchLimitUpper : UInt64
  ioBaseLimitUpper : UInt64
  deriving BEq, DecidableEq, Repr

inductive Layout where
  | endpoint
  | bridge (registers : BridgeRegisters)
  deriving BEq, DecidableEq, Repr

structure Header where
  raw : RawHeader
  identity : Identity
  command : UInt64
  status : UInt64
  revision : UInt64
  multifunction : Bool
  layout : Layout
  deriving BEq, DecidableEq, Repr

inductive Error where
  | invalidBDF | wrongWordCount | nonDword | absent | unsupportedLayout
  deriving BEq, DecidableEq, Repr

private def word (r : RawHeader) (index : Nat) : UInt64 := r.words.getD index 0

private def bridgeRegisters (r : RawHeader) : BridgeRegisters :=
  { primary := word r 6 &&& 0xff
    secondary := (word r 6 >>> 8) &&& 0xff
    subordinate := (word r 6 >>> 16) &&& 0xff
    control := word r 15 >>> 16
    ioBaseLimit := word r 7 &&& 0xffff
    secondaryStatus := word r 7 >>> 16
    memoryBaseLimit := word r 8
    prefetchBaseLimit := word r 9
    prefetchBaseUpper := word r 10
    prefetchLimitUpper := word r 11
    ioBaseLimitUpper := word r 12 }

private def project (r : RawHeader) (layout : Layout) : Header :=
  { raw := r
    identity := ⟨word r 0 &&& 0xffff, word r 0 >>> 16, word r 2 >>> 8⟩
    command := word r 1 &&& 0xffff
    status := word r 1 >>> 16
    revision := word r 2 &&& 0xff
    multifunction := ((word r 3 >>> 16) &&& 0x80) != 0
    layout := layout }

def decode (r : RawHeader) : Except Error Header :=
  if !bdfValid r.bdf then .error .invalidBDF
  else if r.words.length != 16 then .error .wrongWordCount
  else if !(r.words.all (· < 0x100000000)) then .error .nonDword
  else if (word r 0 &&& 0xffff) == 0xffff then .error .absent
  else if ((word r 3 >>> 16) &&& 0x7f) == 0 then .ok (project r .endpoint)
  else if ((word r 3 >>> 16) &&& 0x7f) == 1 then .ok (project r (.bridge (bridgeRegisters r)))
  else .error .unsupportedLayout

theorem decode_preserves_raw r h (accepted : decode r = .ok h) : h.raw = r := by
  unfold decode at accepted
  repeat' (split at accepted <;> try contradiction)
  all_goals cases accepted; rfl

theorem decode_transport_bounds r h (accepted : decode r = .ok h) :
    bdfValid r.bdf = true ∧ r.words.length = 16 ∧
      r.words.all (· < 0x100000000) = true := by
  unfold decode at accepted
  split at accepted
  · contradiction
  rename_i address
  split at accepted
  · contradiction
  rename_i width
  split at accepted
  · contradiction
  rename_i dwords
  exact ⟨by simpa using address, by simpa using width, by simpa using dwords⟩

def Error.code : Error → UInt64
  | .invalidBDF => 0x100
  | .wrongWordCount => 0x101
  | .nonDword => 0x102
  | .absent => 0x103
  | .unsupportedLayout => 0x104

/-- Twenty observation words: success tag, identity, command/status, revision,
multifunction, layout tag, then eleven bridge fields. Endpoint bridge fields
are canonical zeros. These words carry no admission or quiescence authority. -/
def observationWords (h : Header) : List UInt64 :=
  [1, h.identity.vendor, h.identity.device, h.identity.classCode,
   h.command, h.status, h.revision, if h.multifunction then 1 else 0,
   match h.layout with | .endpoint => 0 | .bridge _ => 1] ++
    match h.layout with
    | .endpoint => List.replicate 11 0
    | .bridge r => [r.primary, r.secondary, r.subordinate, r.control,
        r.ioBaseLimit, r.secondaryStatus, r.memoryBaseLimit, r.prefetchBaseLimit,
        r.prefetchBaseUpper, r.prefetchLimitUpper, r.ioBaseLimitUpper]

theorem observationWords_width h : (observationWords h).length = 20 := by
  cases layout : h.layout <;> simp [observationWords, layout]

/-- Read a field from one immutable supplied observation. Field zero must be
checked before consuming data fields, whose values can equal an error code.
An out-of-range selector returns 0x105. -/
def observe (r : RawHeader) (field : UInt64) : UInt64 :=
  if field ≥ 20 then 0x105
  else match decode r with
    | .error e => e.code
    | .ok h => (observationWords h).getD field.toNat 0

theorem observe_success_tag r h (accepted : decode r = .ok h) : observe r 0 = 1 := by
  simp [observe, accepted, observationWords]

/-- Fixed scalar transport for generated-C replay and a future boot adapter.
The caller supplies sixteen dwords and an explicit declared count. This export
does not access PCI configuration space or assert enumeration completeness. -/
@[export leanos_pci_header_observe]
def checkRaw (field count bus device fn
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : UInt64) : UInt64 :=
  if field ≥ 20 then 0x105
  else if !bdfValid ⟨bus, device, fn⟩ then Error.invalidBDF.code
  else if count != 16 then Error.wrongWordCount.code
  else observe ⟨⟨bus, device, fn⟩,
    [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15]⟩ field

namespace Scalar
open DMAQuarantine PCIHeaderObservation

/-- Fixed-width status path intended for a freestanding inventory bridge.
The sixteen argument slots are physical; count is the declared logical width. -/
def status (count bus device fn
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : UInt64) : UInt64 :=
  if !(bus < 256 && device < 32 && fn < 8) then 0x100
  else if count != 16 then 0x101
  else if !(w0 < 0x100000000 &&
      w1 < 0x100000000 &&
      w2 < 0x100000000 &&
      w3 < 0x100000000 &&
      w4 < 0x100000000 &&
      w5 < 0x100000000 &&
      w6 < 0x100000000 &&
      w7 < 0x100000000 &&
      w8 < 0x100000000 &&
      w9 < 0x100000000 &&
      w10 < 0x100000000 &&
      w11 < 0x100000000 &&
      w12 < 0x100000000 &&
      w13 < 0x100000000 &&
      w14 < 0x100000000 &&
      w15 < 0x100000000) then 0x102
  else if (w0 &&& 0xffff) == 0xffff then 0x103
  else if ((w3 >>> 16) &&& 0x7f) == 0 then 1
  else if ((w3 >>> 16) &&& 0x7f) == 1 then 1
  else 0x104

/-- For an actual sixteen-word transport, scalar validation returns exactly
its reference decoder status, including all rejection classes. -/
theorem status_eq_decode (bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : UInt64) :
    status 16 bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 =
      match decode ⟨⟨bus, device, fn⟩, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15]⟩ with
      | .ok _ => 1
      | .error reason => reason.code := by
  by_cases absent : (w0 &&& 0xffff) = 0xffff <;>
    by_cases endpoint : ((w3 >>> 16) &&& 0x7f) = 0 <;>
    by_cases bridge : ((w3 >>> 16) &&& 0x7f) = 1 <;>
    simp [status, decode, bdfValid, PCIHeaderObservation.word,
      List.all_cons, List.all_nil, Error.code, or_assoc, absent, endpoint, bridge] <;>
    repeat' (split <;> simp_all)

/-- Scalar observation projection. Status is checked before any data field;
endpoint-only queries return canonical zero for bridge register fields. -/
def query (field count bus device fn
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : UInt64) : UInt64 :=
  if field ≥ 20 then 0x105
  else
    let checked := status count bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
    if checked != 1 then checked
    else if field == 0 then 1
    else if field == 1 then w0 &&& 0xffff
    else if field == 2 then w0 >>> 16
    else if field == 3 then w2 >>> 8
    else if field == 4 then w1 &&& 0xffff
    else if field == 5 then w1 >>> 16
    else if field == 6 then w2 &&& 0xff
    else if field == 7 then if ((w3 >>> 16) &&& 0x80) != 0 then 1 else 0
    else if field == 8 then (w3 >>> 16) &&& 0x7f
    else if ((w3 >>> 16) &&& 0x7f) == 0 then 0
    else if field == 9 then w6 &&& 0xff
    else if field == 10 then (w6 >>> 8) &&& 0xff
    else if field == 11 then (w6 >>> 16) &&& 0xff
    else if field == 12 then w15 >>> 16
    else if field == 13 then w7 &&& 0xffff
    else if field == 14 then w7 >>> 16
    else if field == 15 then w8
    else if field == 16 then w9
    else if field == 17 then w10
    else if field == 18 then w11
    else w12

set_option maxHeartbeats 2000000 in
/-- Exact reference observation equivalence for every field and sixteen-word
input. Invalid selectors reject before validating header contents. -/
theorem query_eq_observe (field bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : UInt64) :
    query field 16 bus device fn w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 =
      observe ⟨⟨bus, device, fn⟩, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15]⟩ field := by
  by_cases outside : field ≥ 20
  · simp [query, observe, outside]
  by_cases address : bus < 256 ∧ device < 32 ∧ fn < 8
  case neg =>
    have bad : 256 ≤ bus ∨ 32 ≤ device ∨ 8 ≤ fn := by
      simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at *
      omega
    simp [query, status, observe, decode, bdfValid, Error.code, or_assoc, outside, bad]
  by_cases dwords : w0 < 0x100000000 ∧ w1 < 0x100000000 ∧ w2 < 0x100000000 ∧ w3 < 0x100000000 ∧ w4 < 0x100000000 ∧ w5 < 0x100000000 ∧ w6 < 0x100000000 ∧ w7 < 0x100000000 ∧ w8 < 0x100000000 ∧ w9 < 0x100000000 ∧ w10 < 0x100000000 ∧ w11 < 0x100000000 ∧ w12 < 0x100000000 ∧ w13 < 0x100000000 ∧ w14 < 0x100000000 ∧ w15 < 0x100000000
  case neg =>
    have bad : 0x100000000 ≤ w0 ∨ 0x100000000 ≤ w1 ∨ 0x100000000 ≤ w2 ∨ 0x100000000 ≤ w3 ∨ 0x100000000 ≤ w4 ∨ 0x100000000 ≤ w5 ∨ 0x100000000 ≤ w6 ∨ 0x100000000 ≤ w7 ∨ 0x100000000 ≤ w8 ∨ 0x100000000 ≤ w9 ∨ 0x100000000 ≤ w10 ∨ 0x100000000 ≤ w11 ∨ 0x100000000 ≤ w12 ∨ 0x100000000 ≤ w13 ∨ 0x100000000 ≤ w14 ∨ 0x100000000 ≤ w15 := by
      simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at *
      omega
    simp [query, status, observe, decode, bdfValid, Error.code, or_assoc, outside, address, bad]
  by_cases absent : (w0 &&& 0xffff) = 0xffff
  · simp [query, status, observe, decode, bdfValid, word, Error.code, outside, address, dwords, absent]
  have selectors : field = 0 ∨ field = 1 ∨ field = 2 ∨ field = 3 ∨ field = 4 ∨ field = 5 ∨ field = 6 ∨ field = 7 ∨ field = 8 ∨ field = 9 ∨ field = 10 ∨ field = 11 ∨ field = 12 ∨ field = 13 ∨ field = 14 ∨ field = 15 ∨ field = 16 ∨ field = 17 ∨ field = 18 ∨ field = 19 := by
    simp only [UInt64.le_iff_toNat_le, ← UInt64.toNat_inj] at *
    simp at *
    omega
  rcases selectors with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 <;> subst field <;>
    by_cases endpoint : ((w3 >>> 16) &&& 0x7f) = 0 <;>
    by_cases bridge : ((w3 >>> 16) &&& 0x7f) = 1 <;>
    simp_all [query, status, observe, decode, bdfValid, word, project, bridgeRegisters, observationWords, Error.code]

end Scalar

end LeanOS.PCIHeaderObservation
