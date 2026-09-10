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

end LeanOS.PCIHeaderObservation
