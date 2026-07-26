import LeanOS.BootMemoryMap

/-!
# Allocation-free bounded handoff stream codec

This module is the scalar transport boundary for feeding an immutable bounded
Multiboot2 copy to generated code.  The rich byte decoder remains the
authoritative parser.  This codec does not claim to replace it yet: it binds a
stream to one buffer identity and extent, accepts canonical one-to-eight-byte
chunks at exactly one next offset, and exposes the chunk only when that state
transition succeeds.

Every exported argument and result is `UInt64`.  In particular, the exported
path constructs no `List`, `Array`, `ByteArray`, structure, exception, closure,
or arbitrary-precision `Nat`.  A caller obtains each next-state word by
replaying the same pure transition with a different query selector, then
commits all returned words together.
-/
namespace LeanOS.BootMemoryMapStreaming

def abiVersion : UInt64 := 2

def statusActive : UInt64 := 0
def statusComplete : UInt64 := 1
def statusRejected : UInt64 := 2

def errorNone : UInt64 := 0
def errorBadMagic : UInt64 := 1
def errorUnalignedInfo : UInt64 := 2
def errorBufferTooSmall : UInt64 := 3
def errorBufferTooLarge : UInt64 := 4
def errorIdentityMismatch : UInt64 := 5
def errorStaleVersion : UInt64 := 6
def errorStaleState : UInt64 := 7
def errorStreamMismatch : UInt64 := 8
def errorOffsetMismatch : UInt64 := 9
def errorBadChunkCount : UInt64 := 10
def errorExtentOverflow : UInt64 := 11
def errorBadTerminal : UInt64 := 12
def errorNoncanonicalChunk : UInt64 := 13
def errorAddressOverflow : UInt64 := 14

def initialChain : UInt64 := 0xcbf29ce484222325
def chainPrime : UInt64 := 0x100000001b3

private def initError (magic infoAddress totalBytes streamIdentity : UInt64) : UInt64 :=
  if magic != 0x36d76289 then errorBadMagic
  else if infoAddress % 8 != 0 then errorUnalignedInfo
  else if totalBytes < 16 then errorBufferTooSmall
  else if totalBytes > 65536 || totalBytes % 8 != 0 then errorBufferTooLarge
  else if totalBytes > 0xffffffffffffffff - infoAddress then errorAddressOverflow
  else if streamIdentity != infoAddress then errorIdentityMismatch
  else errorNone

/-- Version-two reset projection.

Queries are: version, status, error, bound stream identity, bound extent, next
offset, and continuity chain.  Out-of-range queries are zero.  A rejected reset
does not expose a bound identity or extent.
-/
@[export leanos_boot_handoff_stream_init]
def initWord (magic infoAddress totalBytes streamIdentity query : UInt64) : UInt64 :=
  let reason := initError magic infoAddress totalBytes streamIdentity
  if query == 0 then abiVersion
  else if query == 1 then if reason == errorNone then statusActive else statusRejected
  else if query == 2 then reason
  else if reason != errorNone then 0
  else if query == 3 then streamIdentity
  else if query == 4 then totalBytes
  else if query == 5 then 0
  else if query == 6 then initialChain
  else 0

private def canonicalChunk (count chunk : UInt64) : Bool :=
  if count == 1 then chunk < 0x100
  else if count == 2 then chunk < 0x10000
  else if count == 3 then chunk < 0x1000000
  else if count == 4 then chunk < 0x100000000
  else if count == 5 then chunk < 0x10000000000
  else if count == 6 then chunk < 0x1000000000000
  else if count == 7 then chunk < 0x100000000000000
  else count == 8

def stepError (version status error boundIdentity boundExtent nextOffset
    streamIdentity offset count chunk terminal : UInt64) : UInt64 :=
  if version != abiVersion then errorStaleVersion
  else if status != statusActive || error != errorNone ||
      boundExtent < 16 || boundExtent > 65536 || boundExtent % 8 != 0 ||
      boundIdentity % 8 != 0 ||
      boundExtent > 0xffffffffffffffff - boundIdentity ||
      nextOffset >= boundExtent then errorStaleState
  else if streamIdentity != boundIdentity then errorStreamMismatch
  else if offset != nextOffset then errorOffsetMismatch
  else if count == 0 || count > 8 then errorBadChunkCount
  else if count > boundExtent - nextOffset then errorExtentOverflow
  else if terminal > 1 ||
      ((nextOffset + count == boundExtent) != (terminal == 1)) then errorBadTerminal
  else if !canonicalChunk count chunk then errorNoncanonicalChunk
  else errorNone

private def nextChain (chain count chunk : UInt64) : UInt64 :=
  ((chain ^^^ chunk) * chainPrime) ^^^ count

/-- One allocation-free stream transition.

State queries 0..6 have the same layout as `initWord`.  Queries 7 and 8 expose
the canonical chunk and its byte count for this transition only.  Rejection
zeros every projection other than version, rejected status, and typed error.
-/
@[export leanos_boot_handoff_stream_step]
def stepWord (version status error boundIdentity boundExtent nextOffset chain
    streamIdentity offset count chunk terminal query : UInt64) : UInt64 :=
  let reason := stepError version status error boundIdentity boundExtent nextOffset
    streamIdentity offset count chunk terminal
  let advanced := nextOffset + count
  if query == 0 then abiVersion
  else if query == 1 then
    if reason != errorNone then statusRejected
    else if advanced == boundExtent then statusComplete
    else statusActive
  else if query == 2 then reason
  else if reason != errorNone then 0
  else if query == 3 then boundIdentity
  else if query == 4 then boundExtent
  else if query == 5 then advanced
  else if query == 6 then nextChain chain count chunk
  else if query == 7 then chunk
  else if query == 8 then count
  else 0

theorem init_deterministic magic infoAddress totalBytes streamIdentity query first second
    (hfirst : initWord magic infoAddress totalBytes streamIdentity query = first)
    (hsecond : initWord magic infoAddress totalBytes streamIdentity query = second) :
    first = second := by
  rw [hfirst] at hsecond
  exact hsecond

theorem step_deterministic version status error boundIdentity boundExtent nextOffset
    chain streamIdentity offset count chunk terminal query first second
    (hfirst : stepWord version status error boundIdentity boundExtent nextOffset chain
      streamIdentity offset count chunk terminal query = first)
    (hsecond : stepWord version status error boundIdentity boundExtent nextOffset chain
      streamIdentity offset count chunk terminal query = second) :
    first = second := by
  rw [hfirst] at hsecond
  exact hsecond

theorem accepted_step_advances_exactly version status error boundIdentity boundExtent
    nextOffset chain streamIdentity offset count chunk terminal
    (h : stepError version status error boundIdentity boundExtent nextOffset
      streamIdentity offset count chunk terminal = errorNone) :
    stepWord version status error boundIdentity boundExtent nextOffset chain
      streamIdentity offset count chunk terminal 5 = nextOffset + count := by
  simp [stepWord, h]

theorem accepted_step_preserves_stream version status error boundIdentity boundExtent
    nextOffset chain streamIdentity offset count chunk terminal
    (h : stepError version status error boundIdentity boundExtent nextOffset
      streamIdentity offset count chunk terminal = errorNone) :
    stepWord version status error boundIdentity boundExtent nextOffset chain
      streamIdentity offset count chunk terminal 3 = boundIdentity ∧
    stepWord version status error boundIdentity boundExtent nextOffset chain
      streamIdentity offset count chunk terminal 4 = boundExtent := by
  simp [stepWord, h]

theorem accepted_step_exposes_exact_chunk version status error boundIdentity boundExtent
    nextOffset chain streamIdentity offset count chunk terminal
    (h : stepError version status error boundIdentity boundExtent nextOffset
      streamIdentity offset count chunk terminal = errorNone) :
    stepWord version status error boundIdentity boundExtent nextOffset chain
      streamIdentity offset count chunk terminal 7 = chunk ∧
    stepWord version status error boundIdentity boundExtent nextOffset chain
      streamIdentity offset count chunk terminal 8 = count := by
  simp [stepWord, h]

theorem accepted_step_terminal_iff_extent version status error boundIdentity boundExtent
    nextOffset chain streamIdentity offset count chunk terminal
    (h : stepError version status error boundIdentity boundExtent nextOffset
      streamIdentity offset count chunk terminal = errorNone) :
    (stepWord version status error boundIdentity boundExtent nextOffset chain
      streamIdentity offset count chunk terminal 1 = statusComplete) =
    (nextOffset + count == boundExtent) := by
  simp [stepWord, h, statusComplete, statusActive]

theorem rejected_step_has_rejected_status version status error boundIdentity boundExtent
    nextOffset chain streamIdentity offset count chunk terminal
    (h : stepError version status error boundIdentity boundExtent nextOffset
      streamIdentity offset count chunk terminal != errorNone) :
    stepWord version status error boundIdentity boundExtent nextOffset chain
      streamIdentity offset count chunk terminal 1 = statusRejected := by
  simp [stepWord, h, statusRejected]

theorem completed_replay_rejects version error boundIdentity boundExtent nextOffset chain
    streamIdentity offset count chunk terminal :
    stepWord version statusComplete error boundIdentity boundExtent nextOffset chain
      streamIdentity offset count chunk terminal 1 = statusRejected := by
  apply rejected_step_has_rejected_status
  by_cases hversion : version = abiVersion
  · simp [stepError, hversion, statusComplete, statusActive, errorStaleState, errorNone]
  · simp [stepError, hversion, errorStaleVersion, errorNone]

theorem rejection_exposes_no_chunk version status error boundIdentity boundExtent
    nextOffset chain streamIdentity offset count chunk terminal
    (h : stepError version status error boundIdentity boundExtent nextOffset
      streamIdentity offset count chunk terminal != errorNone) :
    stepWord version status error boundIdentity boundExtent nextOffset chain
      streamIdentity offset count chunk terminal 7 = 0 := by
  simp [stepWord, h]

/-- Proof-side exact state.  This rich value is not used by either exported
function; it records the byte sequence property that the scalar protocol is
designed to preserve. -/
structure ModelState where
  identity : UInt64
  extent : Nat
  offset : Nat
  complete : Bool

structure ModelChunk where
  identity : UInt64
  offset : Nat
  bytes : List UInt8
  terminal : Bool

def modelStep (state : ModelState) (chunk : ModelChunk) : Option ModelState :=
  if state.complete ||
      chunk.identity != state.identity ||
      chunk.offset != state.offset ||
      chunk.bytes.isEmpty ||
      chunk.bytes.length > 8 ||
      state.offset + chunk.bytes.length > state.extent ||
      ((state.offset + chunk.bytes.length == state.extent) != chunk.terminal) then
    none
  else
    some
      { identity := state.identity
        extent := state.extent
        offset := state.offset + chunk.bytes.length
        complete := chunk.terminal }

theorem modelStep_continuity state chunk next
    (h : modelStep state chunk = some next) :
    next.identity = state.identity ∧
    next.extent = state.extent ∧
    next.offset = state.offset + chunk.bytes.length := by
  unfold modelStep at h
  split at h
  · contradiction
  · injection h with hnext
    subst next
    exact ⟨rfl, rfl, rfl⟩

def replay : ModelState → List ModelChunk → Option ModelState
  | state, [] => some state
  | state, chunk :: rest =>
      match modelStep state chunk with
      | none => none
      | some next => replay next rest

/-- Any successful multi-chunk replay retains one buffer binding and advances
by exactly the sum of the accepted byte counts. -/
theorem replay_continuity state chunks final
    (h : replay state chunks = some final) :
    final.identity = state.identity ∧
    final.extent = state.extent ∧
    final.offset = state.offset + (chunks.map (·.bytes.length)).sum := by
  induction chunks generalizing state with
  | nil =>
      simp [replay] at h
      subst final
      simp
  | cons chunk rest ih =>
      unfold replay at h
      cases hstep : modelStep state chunk with
      | none =>
          simp [hstep] at h
      | some next =>
          simp only [hstep] at h
          have hsingle := modelStep_continuity state chunk next hstep
          have hrest := ih next h
          rcases hsingle with ⟨hidentity, hextent, hoffset⟩
          rcases hrest with ⟨hfinalIdentity, hfinalExtent, hfinalOffset⟩
          constructor
          · exact hfinalIdentity.trans hidentity
          constructor
          · exact hfinalExtent.trans hextent
          · simp only [List.map_cons, List.sum_cons]
            omega

namespace Fixtures

def magic : UInt64 := 0x36d76289

example : initWord magic 0x1000 96 0x1000 0 = abiVersion := by decide
example : initWord magic 0x1000 96 0x1000 1 = statusActive := by decide
example : initWord magic 0x1000 95 0x1000 1 = statusRejected := by decide
example : initWord magic 0x1000 96 0x2000 2 = errorIdentityMismatch := by decide
example : initWord magic 0xfffffffffffffff8 16 0xfffffffffffffff8 2 =
    errorAddressOverflow := by decide

example : stepWord abiVersion statusActive errorNone 0x1000 96 0 initialChain
    0x1000 0 8 96 0 5 = 8 := by decide
example : stepWord abiVersion statusActive errorNone 0x1000 96 0 initialChain
    0x2000 0 8 96 0 1 = statusRejected := by decide
example : stepWord abiVersion statusActive errorNone 0x1000 96 0 initialChain
    0x1000 8 8 96 0 1 = statusRejected := by decide
example : stepWord abiVersion statusActive errorNone 0x1000 96 88 initialChain
    0x1000 88 8 8 1 1 = statusComplete := by decide
example : stepWord abiVersion statusComplete errorNone 0x1000 96 96 initialChain
    0x1000 96 1 0 0 1 = statusRejected := by decide
example : stepWord abiVersion statusActive errorNone 0x1000 96 0 initialChain
    0x1000 0 1 0x100 0 2 = errorNoncanonicalChunk := by decide

end Fixtures

end LeanOS.BootMemoryMapStreaming
