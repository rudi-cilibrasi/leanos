import LeanOS.SpawnAllocatorTheorems

/-!
# The spawn allocator in thirteen words, decided by fixed-width code (#575)

The reviewed bounded representation of `LeanOS.SpawnAllocator.State` is
thirteen 64-bit words:

| Word | Field | Encoding |
| --- | --- | --- |
| 0 | `subjectNext` | the counter |
| 1 | `objectNext` | the counter |
| 2 | `capabilityNext` | the counter |
| 3 | `controlNext` | the counter |
| 4 | `authorityNext` | the counter, nonzero |
| 5 | `authority` | the generation, `0` for none |
| 6..9 | `children[0..3]` | `0` for an empty slot, else `generation << 16 \| charge`, generation in `1 .. 2^48 - 2` |
| 10, 11 | `memory[0..1]` (parent slots 2, 3) | `0` for an empty slot, else the capability identity |
| 12 | `budget`, `parentFrames` | `budget \| parentFrames << 16`, budget at most 4, bits 32..63 zero |

and the frames of the parent and its children are fewer than `2^16`.
`Canonical` decides exactly these rules, and `decode` and `encode` are
inverse on them (`decode_bounded`, `encode_decode`, `decode_encode`).

The command is the dispatcher's five command words (`CommandWords`): a tag of
the spawn family and four arguments, decoded by `decodeCommand` with the
hosted oracles' canonical rules.

## The generated functions

`stepNextWord`, `stepReply` and `stepValue` take the thirteen state words and
the five command words as `UInt64` scalars and are allocation-free and
non-recursive: no `Nat`, no structure, no list.  The reply is

* the status byte of a decided command: `0x01` accepted, `0x80 + code`
  rejected, with the hosted oracles' codes;
* `0xff02`, `0xff04`, `0xff05`: the command words do not decode
  (`CompositeDispatcher.errorWord`);
* `0xff03`: the state words are not canonical;
* `0xff07`: the command lies outside the bounded representation (only a
  kernel grant of spawn authority can, `SpawnAllocator.grantAuthorityStep`).

`stepNextWord index` is word `index` of the successor, and every word is
unchanged unless the reply is `0x01`.

`words_refine` proves, for **every** input, that the three functions compute
`specStep`: decode the words and the command, run `SpawnAllocator.step`, and
encode the successor.
-/
namespace LeanOS.SpawnAllocatorWords

open LeanOS
open LeanOS.FailStop
open LeanOS.SpawnAllocator
open LeanOS.CompositeDispatcher (CommandWords DecodeError)

set_option linter.unusedSimpArgs false

/-! ## Command words -/

def spawnTag : UInt64 := 0x7001
def grantTag : UInt64 := 0x7101
def terminateTag : UInt64 := 0x7201
def allocateTag : UInt64 := 0x7301
def releaseTag : UInt64 := 0x7401
def grantAuthorityTag : UInt64 := 0x7501
def revokeAuthorityTag : UInt64 := 0x7601

/-- Decode the spawn family's command words, with the canonical rules of
`SpawnOracle.decodeSpawn`, `SpawnAccountingOracle.decodeChild` and
`SpawnBoundary.decodeFamily`. -/
def decodeCommand (words : CommandWords) : Except DecodeError Command :=
  if words.tag = spawnTag ∨ words.tag = grantTag ∨ words.tag = terminateTag then
    match SpawnAccountingOracle.decodeChild words with
    | .error reason => .error reason
    | .ok operation => .ok (.child operation)
  else if words.tag = allocateTag then
    if words.arg1 ≠ 0 ∨ words.arg2 ≠ 0 ∨ words.arg3 ≠ 0 then .error .reservedBits
    else .ok (.memory (.allocate words.arg0.toNat))
  else if words.tag = releaseTag then
    if words.arg1 ≠ 0 ∨ words.arg2 ≠ 0 ∨ words.arg3 ≠ 0 then .error .reservedBits
    else .ok (.memory (.release words.arg0.toNat))
  else if words.tag = grantAuthorityTag then
    if words.arg2 ≠ 0 ∨ words.arg3 ≠ 0 then .error .reservedBits
    else .ok (.child (.grantAuthority words.arg0.toNat words.arg1.toNat))
  else if words.tag = revokeAuthorityTag then
    if words.arg1 ≠ 0 ∨ words.arg2 ≠ 0 ∨ words.arg3 ≠ 0 then .error .reservedBits
    else .ok (.child (.revokeAuthority words.arg0.toNat))
  else .error .unknownCommand

/-! ## State words -/

/-- The thirteen state words. -/
@[ext] structure Words where
  subjectNext : UInt64
  objectNext : UInt64
  capabilityNext : UInt64
  controlNext : UInt64
  authorityNext : UInt64
  authority : UInt64
  child0 : UInt64
  child1 : UInt64
  child2 : UInt64
  child3 : UInt64
  memory2 : UInt64
  memory3 : UInt64
  frames : UInt64
  deriving DecidableEq, Repr

def Words.toList (words : Words) : List UInt64 :=
  [words.subjectNext, words.objectNext, words.capabilityNext, words.controlNext,
    words.authorityNext, words.authority, words.child0, words.child1, words.child2, words.child3,
    words.memory2, words.memory3, words.frames]

def Words.ofList : List UInt64 → Option Words
  | [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12] =>
      some ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12⟩
  | _ => none

theorem Words.ofList_toList (words : Words) : Words.ofList words.toList = some words := rfl

def encodeChild : Option ChildRecord → UInt64
  | none => 0
  | some entry => UInt64.ofNat (entry.generation * 65536 + entry.charge)

def decodeChild (word : UInt64) : Option ChildRecord :=
  if word = 0 then none
  else some { generation := word.toNat / 65536, charge := word.toNat % 65536 }

def encodeMemory : Option Nat → UInt64
  | none => 0
  | some identity => UInt64.ofNat identity

def decodeMemory (word : UInt64) : Option Nat := if word = 0 then none else some word.toNat

def encodeAuthority : Option Nat → UInt64
  | none => 0
  | some generation => UInt64.ofNat generation

def decodeAuthority (word : UInt64) : Option Nat := if word = 0 then none else some word.toNat

/-- Encode a record.  On bounded records with at most four children and two
memory slots this is exact (`decode_encode`). -/
def encode (state : SpawnAllocator.State) : Words :=
  { subjectNext := UInt64.ofNat state.subjectNext
    objectNext := UInt64.ofNat state.objectNext
    capabilityNext := UInt64.ofNat state.capabilityNext
    controlNext := UInt64.ofNat state.controlNext
    authorityNext := UInt64.ofNat state.authorityNext
    authority := encodeAuthority state.authority
    child0 := encodeChild (state.childAt 0)
    child1 := encodeChild (state.childAt 1)
    child2 := encodeChild (state.childAt 2)
    child3 := encodeChild (state.childAt 3)
    memory2 := encodeMemory (state.memoryAt 2)
    memory3 := encodeMemory (state.memoryAt 3)
    frames := UInt64.ofNat (state.budget + state.parentFrames * 65536) }

def decode (words : Words) : SpawnAllocator.State :=
  { subjectNext := words.subjectNext.toNat
    objectNext := words.objectNext.toNat
    capabilityNext := words.capabilityNext.toNat
    controlNext := words.controlNext.toNat
    authorityNext := words.authorityNext.toNat
    authority := decodeAuthority words.authority
    budget := words.frames.toNat % 65536
    children := [decodeChild words.child0, decodeChild words.child1, decodeChild words.child2,
      decodeChild words.child3]
    memory := [decodeMemory words.memory2, decodeMemory words.memory3]
    parentFrames := words.frames.toNat / 65536 }

/-! ## The generated functions

Every function below takes and returns `UInt64` only. -/

def maxWord : UInt64 := 0xffffffffffffffff
def generationLimit : UInt64 := 0xffffffffffff

/-- A child word is canonical: empty, or a generation in `1 .. 2^48 - 2`. -/
def childCanonical (word : UInt64) : Bool :=
  word == 0 || (word >>> 16 != 0 && word >>> 16 < generationLimit)

def occupied (word : UInt64) : UInt64 := if word == 0 then 0 else 1

def chargeOf (word : UInt64) : UInt64 := word &&& 0xffff

def generationOf (word : UInt64) : UInt64 := word >>> 16

/-- The state words are canonical. -/
def canonical (w4 c0 c1 c2 c3 f : UInt64) : Bool :=
  w4 != 0 && childCanonical c0 && childCanonical c1 && childCanonical c2 && childCanonical c3 &&
    f >>> 32 == 0 && f &&& 0xffff ≤ 4 &&
    (f >>> 16) + chargeOf c0 + chargeOf c1 + chargeOf c2 + chargeOf c3 < 0x10000

def identityExhaustedW (next : UInt64) : Bool := next == 0 || next == maxWord

def capabilityExhaustedW (next : UInt64) : Bool := next == 0 || generationLimit ≤ next

def controlAvailableW (next : UInt64) : Bool := next != 0 && next < generationLimit

def childCountW (c0 c1 c2 c3 : UInt64) : UInt64 :=
  occupied c0 + occupied c1 + occupied c2 + occupied c3

/-- The first free child slot, `4` for none. -/
def freeSlotW (c0 c1 c2 c3 : UInt64) : UInt64 :=
  if c0 == 0 then 0 else if c1 == 0 then 1 else if c2 == 0 then 2 else if c3 == 0 then 3 else 4

def childWordAt (slot c0 c1 c2 c3 : UInt64) : UInt64 :=
  if slot == 0 then c0 else if slot == 1 then c1 else if slot == 2 then c2
  else if slot == 3 then c3 else 0

def memoryWordAt (slot m2 m3 : UInt64) : UInt64 :=
  if slot == 2 then m2 else if slot == 3 then m3 else 0

def budgetW (f : UInt64) : UInt64 := f &&& 0xffff

def parentFramesW (f : UInt64) : UInt64 := f >>> 16

def availableW (f m2 m3 : UInt64) : UInt64 :=
  if occupied m2 + occupied m3 ≤ parentFramesW f then parentFramesW f - (occupied m2 + occupied m3)
  else 0

/-- Endpoint resolution: `0` when the word names the parent's endpoint, else
the `SpawnOracle.handleErrorCode` of the denial. -/
def resolveEndpointW (m2 m3 word : UInt64) : UInt64 :=
  let slot := word &&& 0xffff
  let identity := word >>> 16
  if slot == 0xffff then 0x20
  else if identity == 0 || identity == generationLimit then 0x21
  else if 4 ≤ slot then 0x23
  else if slot == 0 then (if identity == 3 then 0 else 0x24)
  else if slot == 1 then (if identity == 4 then 0x25 else 0x24)
  else if memoryWordAt slot m2 m3 == 0 then 0x24
  else if identity == memoryWordAt slot m2 m3 then 0x25 else 0x24

/-- Control-word resolution: `0` when the word names a live entry, else the
`SpawnAccountingOracle.controlDenialCode` of the denial. -/
def resolveControlW (c0 c1 c2 c3 word : UInt64) : UInt64 :=
  let slot := word &&& 0xffff
  let identity := word >>> 16
  if slot == 0xffff then 0x41
  else if identity == 0 || identity == generationLimit then 0x42
  else if childWordAt slot c0 c1 c2 c3 == 0 then 0x43
  else if generationOf (childWordAt slot c0 c1 c2 c3) == identity then 0 else 0x43

/-- Endpoint rights: no read or write, and one of send, receive, grant,
revoke (`Capability.rightsValid .endpoint`). -/
def rightsValidW (rights : UInt64) : Bool := rights &&& 3 == 0 && rights &&& 60 != 0

/-- The command words decode (`decodeCommand`): `0` when they do, else the
dispatcher's error word. -/
def commandErrorW (tag a0 a1 a2 a3 : UInt64) : UInt64 :=
  if tag == 0x7001 then
    if a3 != 0 then 0xff02 else if a0 == 0 then 0xff05 else if 64 ≤ a2 then 0xff02 else 0
  else if tag == 0x7101 then
    if a2 != 0 || a3 != 0 then 0xff02 else if a1 == 0 then 0xff05 else 0
  else if tag == 0x7201 || tag == 0x7301 || tag == 0x7401 || tag == 0x7601 then
    if a1 != 0 || a2 != 0 || a3 != 0 then 0xff02 else 0
  else if tag == 0x7501 then
    if a2 != 0 || a3 != 0 then 0xff02 else 0
  else 0xff04

def uncoveredWord : UInt64 := 0xff07
def stateErrorWord : UInt64 := 0xff03

/-- The status of a decodable command on canonical words. -/
def decideW (w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2 : UInt64) : UInt64 :=
  if tag == 0x7001 then
    if w5 == 0 then 0x81
    else if w5 != a0 then 0x82
    else if budgetW f ≤ childCountW c0 c1 c2 c3 then 0x8c
    else if freeSlotW c0 c1 c2 c3 == 4 then 0x8c
    else if !controlAvailableW w3 then 0x8d
    else if identityExhaustedW w0 then 0x83
    else if identityExhaustedW w1 then 0x87
    else if capabilityExhaustedW w2 then 0x92
    else if resolveEndpointW m2 m3 a1 != 0 then 0x80 + resolveEndpointW m2 m3 a1
    else if !rightsValidW a2 then 0x8a
    else 0x01
  else if tag == 0x7101 then
    if resolveControlW c0 c1 c2 c3 a0 != 0 then 0x80 + resolveControlW c0 c1 c2 c3 a0
    else if availableW f m2 m3 < a1 then 0xc5
    else 0x01
  else if tag == 0x7201 then
    if resolveControlW c0 c1 c2 c3 a0 != 0 then 0x80 + resolveControlW c0 c1 c2 c3 a0
    else 0x01
  else if tag == 0x7301 then
    if 0xffff ≤ a0 || 4 ≤ a0 then 0x82
    else if capabilityExhaustedW w2 then 0x83
    else if a0 < 2 || memoryWordAt a0 m2 m3 != 0 then 0x84
    else if identityExhaustedW w1 then 0x85
    else if availableW f m2 m3 == 0 then 0x87
    else 0x01
  else if tag == 0x7401 then
    if 4 ≤ a0 then 0x89
    else if a0 < 2 then 0x8a
    else if memoryWordAt a0 m2 m3 == 0 then 0x89
    else 0x01
  else if tag == 0x7501 then
    if a0 == 2 then
      if a1 ≤ 64 && childCountW c0 c1 c2 c3 ≤ a1 then
        if 4 < a1 || w4 == maxWord then uncoveredWord else 0x01
      else 0x80
    else if a0 == 1 then
      if a1 ≤ 64 then uncoveredWord else 0x80
    else 0x80
  else 0x01

/-- **The reply word.** -/
def stepReply (w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2 a3 : UInt64) : UInt64 :=
  if !canonical w4 c0 c1 c2 c3 f then stateErrorWord
  else if commandErrorW tag a0 a1 a2 a3 != 0 then commandErrorW tag a0 a1 a2 a3
  else decideW w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2

/-- **The value word** of an accepted command: the control word of a spawn,
the frames a grant moved or a termination returned, the generation of a
kernel grant; zero otherwise. -/
def stepValue (w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2 a3 : UInt64) : UInt64 :=
  if stepReply w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2 a3 != 0x01 then 0
  else if tag == 0x7001 then freeSlotW c0 c1 c2 c3 + (w3 <<< 16)
  else if tag == 0x7101 then a1
  else if tag == 0x7201 then chargeOf (childWordAt (a0 &&& 0xffff) c0 c1 c2 c3)
  else if tag == 0x7501 then w4
  else 0

/-- The child word of slot `index` after an accepted command. -/
def nextChild (index w3 c0 c1 c2 c3 tag a0 a1 : UInt64) (current : UInt64) : UInt64 :=
  if tag == 0x7001 then
    if freeSlotW c0 c1 c2 c3 == index then w3 <<< 16 else current
  else if tag == 0x7101 then
    if a0 &&& 0xffff == index then current + a1 else current
  else if tag == 0x7201 then
    if a0 &&& 0xffff == index then 0 else current
  else current

/-- The memory word of parent slot `slot` after an accepted command. -/
def nextMemory (slot w2 tag a0 : UInt64) (current : UInt64) : UInt64 :=
  if tag == 0x7301 && a0 == slot then w2
  else if tag == 0x7401 && a0 == slot then 0
  else current

/-- The frames word after an accepted command. -/
def nextFrames (c0 c1 c2 c3 f tag a0 a1 : UInt64) : UInt64 :=
  if tag == 0x7101 then budgetW f + ((parentFramesW f - a1) <<< 16)
  else if tag == 0x7201 then
    budgetW f + ((parentFramesW f + chargeOf (childWordAt (a0 &&& 0xffff) c0 c1 c2 c3)) <<< 16)
  else if tag == 0x7501 then a1 + (parentFramesW f <<< 16)
  else if tag == 0x7601 && a0 == 2 then parentFramesW f <<< 16
  else f

/-- **Word `index` of the successor.** -/
def stepNextWord (index w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2 a3 : UInt64) :
    UInt64 :=
  let accepted := stepReply w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2 a3 == 0x01
  if index == 0 then (if accepted && tag == 0x7001 then w0 + 1 else w0)
  else if index == 1 then (if accepted && (tag == 0x7001 || tag == 0x7301) then w1 + 1 else w1)
  else if index == 2 then
    (if accepted && tag == 0x7001 then w2 + 2
     else if accepted && tag == 0x7301 then w2 + 1 else w2)
  else if index == 3 then (if accepted && tag == 0x7001 then w3 + 1 else w3)
  else if index == 4 then (if accepted && tag == 0x7501 then w4 + 1 else w4)
  else if index == 5 then
    (if accepted && tag == 0x7501 then w4
     else if accepted && tag == 0x7601 && a0 == 2 then 0 else w5)
  else if index == 6 then
    (if accepted then nextChild 0 w3 c0 c1 c2 c3 tag a0 a1 c0 else c0)
  else if index == 7 then
    (if accepted then nextChild 1 w3 c0 c1 c2 c3 tag a0 a1 c1 else c1)
  else if index == 8 then
    (if accepted then nextChild 2 w3 c0 c1 c2 c3 tag a0 a1 c2 else c2)
  else if index == 9 then
    (if accepted then nextChild 3 w3 c0 c1 c2 c3 tag a0 a1 c3 else c3)
  else if index == 10 then (if accepted then nextMemory 2 w2 tag a0 m2 else m2)
  else if index == 11 then (if accepted then nextMemory 3 w2 tag a0 m3 else m3)
  else if index == 12 then (if accepted then nextFrames c0 c1 c2 c3 f tag a0 a1 else f)
  else 0

/-! ## The specification of the words -/

/-- Canonical words: the rules of the module documentation. -/
def Canonical (words : Words) : Bool :=
  canonical words.authorityNext words.child0 words.child1 words.child2 words.child3 words.frames

/-- What the words should compute: decode, run the allocator, encode. -/
def specStep (words : Words) (command : CommandWords) : Words × UInt64 × UInt64 :=
  if Canonical words = false then (words, stateErrorWord, 0)
  else match decodeCommand command with
    | .error reason => (words, CompositeDispatcher.errorWord reason, 0)
    | .ok operation =>
        match step (decode words) operation with
        | none => (words, uncoveredWord, 0)
        | some result => (encode result.next, result.status, result.value)

/-- The generated functions on a `Words` record. -/
def codeReply (words : Words) (command : CommandWords) : UInt64 :=
  stepReply words.subjectNext words.objectNext words.capabilityNext words.controlNext
    words.authorityNext words.authority words.child0 words.child1 words.child2 words.child3
    words.memory2 words.memory3 words.frames command.tag command.arg0 command.arg1 command.arg2
    command.arg3

def codeValue (words : Words) (command : CommandWords) : UInt64 :=
  stepValue words.subjectNext words.objectNext words.capabilityNext words.controlNext
    words.authorityNext words.authority words.child0 words.child1 words.child2 words.child3
    words.memory2 words.memory3 words.frames command.tag command.arg0 command.arg1 command.arg2
    command.arg3

def codeNext (words : Words) (command : CommandWords) : Words :=
  let wordAt := fun (index : UInt64) =>
    stepNextWord index words.subjectNext words.objectNext words.capabilityNext words.controlNext
      words.authorityNext words.authority words.child0 words.child1 words.child2 words.child3
      words.memory2 words.memory3 words.frames command.tag command.arg0 command.arg1 command.arg2
      command.arg3
  ⟨wordAt 0, wordAt 1, wordAt 2, wordAt 3, wordAt 4, wordAt 5, wordAt 6, wordAt 7, wordAt 8, wordAt 9,
    wordAt 10, wordAt 11, wordAt 12⟩

end LeanOS.SpawnAllocatorWords
