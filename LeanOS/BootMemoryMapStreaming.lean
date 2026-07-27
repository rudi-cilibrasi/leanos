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

/-- Proof-side canonical decomposition into exactly `count` eight-byte chunks.
The scalar production decoder consumes this fixed chunk width.  The explicit
count makes the construction structurally recursive; the public theorem below
binds it to an arbitrary aligned byte buffer. -/
def canonicalChunksAux (identity : UInt64) :
    (offset count : Nat) → List UInt8 → List ModelChunk
  | _, 0, _ => []
  | offset, count + 1, bytes =>
      let part := bytes.take 8
      { identity
        offset
        bytes := part
        terminal := count == 0 } ::
        canonicalChunksAux identity (offset + 8) count (bytes.drop 8)

/-- The unique proof-side chunking used to compare a complete immutable byte
buffer with the allocation-free scalar stream decoder. -/
def canonicalChunks (identity : UInt64) (bytes : List UInt8) : List ModelChunk :=
  canonicalChunksAux identity 0 (bytes.length / 8) bytes

/-- The canonical decomposition has exactly one chunk for every complete
eight-byte source word. -/
theorem canonicalChunks_length (identity : UInt64) (bytes : List UInt8) :
    (canonicalChunks identity bytes).length = bytes.length / 8 := by
  have aux :
      ∀ count offset (tail : List UInt8),
        (canonicalChunksAux identity offset count tail).length = count := by
    intro count
    induction count with
    | zero =>
        intro offset tail
        rfl
    | succ count ih =>
        intro offset tail
        simp only [canonicalChunksAux, List.length_cons]
        exact congrArg Nat.succ (ih (offset + 8) (tail.drop 8))
  exact aux (bytes.length / 8) 0 bytes

/-- Every position in the canonical decomposition is the exact eight-byte
slice at the corresponding source offset.  The offset and terminal flag are
derived from the list index, so later decoder/scalar refinements cannot pair a
rich source read with a different scalar chunk. -/
theorem canonicalChunksAux_get?_source
    (identity : UInt64) (offset count : Nat) (bytes : List UInt8)
    (hbytes : bytes.length = count * 8) (index : Nat) (hindex : index < count) :
    (canonicalChunksAux identity offset count bytes)[index]? =
      some
        { identity
          offset := offset + index * 8
          bytes := (bytes.drop (index * 8)).take 8
          terminal := index + 1 == count } := by
  induction count generalizing offset bytes index with
  | zero =>
      omega
  | succ count ih =>
      cases index with
      | zero =>
          simp only [canonicalChunksAux, List.getElem?_cons_zero, Nat.zero_mul,
            List.drop_zero, Nat.zero_add]
          cases count <;> rfl
      | succ index =>
          simp only [canonicalChunksAux, List.getElem?_cons_succ]
          have hdrop : (bytes.drop 8).length = count * 8 := by
            simp only [List.length_drop]
            omega
          rw [ih (offset := offset + 8) (bytes := bytes.drop 8)
            hdrop index (by omega)]
          congr 2
          · omega
          · rw [List.drop_drop]
            congr 2
            omega
          · rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
            omega

/-- Public specialization of `canonicalChunksAux_get?_source`: every aligned
source offset names exactly one canonical chunk with the source bytes, stream
identity, scalar offset, and final-chunk bit fixed by the immutable input. -/
theorem canonicalChunks_get?_source
    (identity : UInt64) (bytes : List UInt8)
    (haligned : bytes.length % 8 = 0)
    (index : Nat) (hindex : index < bytes.length / 8) :
    (canonicalChunks identity bytes)[index]? =
      some
        { identity
          offset := index * 8
          bytes := (bytes.drop (index * 8)).take 8
          terminal := index + 1 == bytes.length / 8 } := by
  unfold canonicalChunks
  simpa only [Nat.zero_add] using
    canonicalChunksAux_get?_source identity 0 (bytes.length / 8) bytes
      (by omega) index hindex

/-- Canonical chunks reconstruct every aligned byte buffer exactly, not merely
the finite regression corpus. -/
theorem canonicalChunks_reconstruct (identity : UInt64) (bytes : List UInt8)
    (haligned : bytes.length % 8 = 0) :
    (canonicalChunks identity bytes).flatMap (·.bytes) = bytes := by
  have aux :
      ∀ count offset (tail : List UInt8),
        tail.length = count * 8 →
        (canonicalChunksAux identity offset count tail).flatMap (·.bytes) = tail := by
    intro count
    induction count with
    | zero =>
        intro offset tail hlength
        simp_all [canonicalChunksAux]
    | succ count ih =>
        intro offset tail hlength
        simp only [canonicalChunksAux, List.flatMap_cons]
        rw [ih]
        · exact List.take_append_drop 8 tail
        · simp only [List.length_drop]
          omega
  unfold canonicalChunks
  apply aux
  omega

/-- Replaying the canonical chunks for any nonempty aligned buffer preserves
one identity and extent, consumes every byte exactly once, and reaches the
complete state. -/
theorem canonicalChunks_replay (identity : UInt64) (bytes : List UInt8)
    (hnonempty : 0 < bytes.length) (haligned : bytes.length % 8 = 0) :
    replay
        { identity, extent := bytes.length, offset := 0, complete := false }
        (canonicalChunks identity bytes) =
      some
        { identity, extent := bytes.length, offset := bytes.length,
          complete := true } := by
  have aux :
      ∀ count offset extent (tail : List UInt8),
        0 < count →
        tail.length = count * 8 →
        offset + tail.length = extent →
        replay
            { identity, extent, offset, complete := false }
            (canonicalChunksAux identity offset count tail) =
          some { identity, extent, offset := extent, complete := true } := by
    intro count
    induction count with
    | zero =>
        intro offset extent tail hpositive
        omega
    | succ count ih =>
        intro offset extent tail _ hlength hextent
        simp only [canonicalChunksAux, replay]
        have hpart : (tail.take 8).length = 8 := by
          simp [List.length_take]
          omega
        have htail : tail ≠ [] := by
          intro hempty
          simp_all
        cases count with
        | zero =>
            have hextent' : offset + 8 = extent := by omega
            have hstep :
                modelStep
                    { identity, extent, offset, complete := false }
                    { identity, offset, bytes := tail.take 8, terminal := true } =
                  some
                    { identity, extent, offset := offset + 8, complete := true } := by
              simp [modelStep, hpart, hextent', htail]
            simp only [beq_self_eq_true]
            rw [hstep]
            simp [canonicalChunksAux, replay, hextent']
        | succ count =>
            have hbefore : offset + 8 < extent := by omega
            have hstep :
                modelStep
                    { identity, extent, offset, complete := false }
                    { identity, offset, bytes := tail.take 8, terminal := false } =
                  some
                    { identity, extent, offset := offset + 8, complete := false } := by
              simp [modelStep, hpart, htail]
              omega
            have hterminal : (count + 1 == 0) = false := by simp
            rw [hterminal]
            rw [hstep]
            have hdrop : (tail.drop 8).length = (count + 1) * 8 := by
              simp only [List.length_drop]
              omega
            apply ih (offset + 8) extent (tail.drop 8) (by omega) hdrop
            omega
  unfold canonicalChunks
  apply aux (bytes.length / 8) 0 bytes.length bytes
  · omega
  · omega
  · omega

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
