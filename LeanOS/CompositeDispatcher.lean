import LeanOS.FailStop
import LeanOS.InvalidationPublication
import LeanOS.StaleTranslation
import LeanOS.FrameBudgetScenario

/-!
# Canonical bounded composite dispatcher

This module introduces the first stateful generated boundary for
`FailStop.authoritativeGate`.  The ABI is intentionally finite: it describes
one versioned mixed trace, and every accepted state word denotes the complete
`FailStop.CompositeState` reached by replaying the preceding exact gate steps.
It does not define a smaller semantic transition.

All words are little logical scalar fields, not byte buffers.  Version one
uses six input words:

1. canonical state token;
2. command tag;
3. command argument 0;
4. command argument 1;
5. command argument 2;
6. command argument 3.

Every reserved field must be zero.  Result word zero records the ABI version,
exact next-state token, and typed-reply token.  Result word one is zero except
when an accepted attached receipt returns its exact generation-bound handle.
Unsupported state / command pairs reject before `authoritativeGate` is
evaluated.  This finite slice is the seed for later bounded snapshot families;
generated C, its scalar calling convention, and the compiler remain trusted
hosted-test boundaries.
-/
namespace LeanOS.CompositeDispatcher

open LeanOS
open LeanOS.FailStop
set_option maxRecDepth 16384

def abiVersion : UInt64 := 1

inductive DecodeError where
  | wrongVersion
  | reservedBits
  | unknownState
  | unknownCommand
  | noncanonicalArguments
  | invalidSequence
  deriving DecidableEq, Repr

/-- The observable states of the version-one mixed trace.  Each successor is
defined below by the exact authoritative gate, including rejection stutters. -/
inductive StateId where
  | initial
  | subjectCreated
  | unknownSyscallRejected
  | malformedMapRejected
  | schedulerObserved
  | subjectTerminated
  | fatalEntered
  | postFatalRejected
  deriving DecidableEq, Repr

def encodeStateId : StateId → UInt64
  | .initial => 0x0001
  | .subjectCreated => 0x0101
  | .unknownSyscallRejected => 0x0201
  | .malformedMapRejected => 0x0301
  | .schedulerObserved => 0x0401
  | .subjectTerminated => 0x0501
  | .fatalEntered => 0x0601
  | .postFatalRejected => 0x0701

def decodeStateId (word : UInt64) : Except DecodeError StateId :=
  if word = 0x0001 then .ok .initial
  else if word = 0x0101 then .ok .subjectCreated
  else if word = 0x0201 then .ok .unknownSyscallRejected
  else if word = 0x0301 then .ok .malformedMapRejected
  else if word = 0x0401 then .ok .schedulerObserved
  else if word = 0x0501 then .ok .subjectTerminated
  else if word = 0x0601 then .ok .fatalEntered
  else if word = 0x0701 then .ok .postFatalRejected
  else if word % 256 != abiVersion then .error .wrongVersion
  else if 0x0801 ≤ word then .error .reservedBits
  else .error .unknownState

theorem decode_encode_state (id : StateId) :
    decodeStateId (encodeStateId id) = .ok id := by
  cases id <;> rfl

theorem state_encoding_injective (first second : StateId)
    (h : encodeStateId first = encodeStateId second) : first = second := by
  cases first <;> cases second <;> simp_all [encodeStateId]

inductive CommandId where
  | createSubjectOne
  | rejectStaleMapHandle
  | rejectNonblockingReceiveHandle
  | rejectCapabilityCopy
  | rejectBlockingCancel
  | rejectDeferredDrain
  | rejectUnknownSyscall
  | rejectMalformedMap
  | observeScheduler
  | terminateSubjectOne
  | enterFatalKernelFault
  | attemptPostFatalSchedule
  deriving DecidableEq, Repr

structure CommandWords where
  tag : UInt64
  arg0 : UInt64
  arg1 : UInt64
  arg2 : UInt64
  arg3 : UInt64
  deriving DecidableEq, Repr

def encodeCommand : CommandId → CommandWords
  | .createSubjectOne => { tag := 0x0101, arg0 := 1, arg1 := 0, arg2 := 0, arg3 := 0 }
  | .rejectStaleMapHandle =>
      { tag := 0x0801, arg0 := 0x10000, arg1 := 7, arg2 := 1, arg3 := 0 }
  | .rejectNonblockingReceiveHandle =>
      { tag := 0x0901, arg0 := 0x10000, arg1 := 0, arg2 := 0, arg3 := 0 }
  | .rejectCapabilityCopy =>
      { tag := 0x0a01, arg0 := 0, arg1 := 0, arg2 := 1, arg3 := 0 }
  | .rejectBlockingCancel =>
      { tag := 0x0b01, arg0 := 0, arg1 := 0, arg2 := 0, arg3 := 0 }
  | .rejectDeferredDrain =>
      { tag := 0x0c01, arg0 := 0, arg1 := 0, arg2 := 0, arg3 := 0 }
  | .rejectUnknownSyscall =>
      { tag := 0x0201, arg0 := 99, arg1 := 0, arg2 := 0, arg3 := 0 }
  | .rejectMalformedMap =>
      { tag := 0x0301, arg0 := 0, arg1 := 0, arg2 := 0, arg3 := 0 }
  | .observeScheduler =>
      { tag := 0x0401, arg0 := 0, arg1 := 0, arg2 := 0, arg3 := 0 }
  | .terminateSubjectOne =>
      { tag := 0x0501, arg0 := 1, arg1 := 0, arg2 := 0, arg3 := 0 }
  | .enterFatalKernelFault =>
      { tag := 0x0601, arg0 := 0, arg1 := 0, arg2 := 0, arg3 := 0 }
  | .attemptPostFatalSchedule =>
      { tag := 0x0701, arg0 := 0, arg1 := 0, arg2 := 0, arg3 := 0 }

def decodeCommand (words : CommandWords) : Except DecodeError CommandId :=
  if words.tag = 0x0101 then
    if words.arg0 = 1 && words.arg1 = 0 && words.arg2 = 0 && words.arg3 = 0 then
      .ok .createSubjectOne
    else .error .noncanonicalArguments
  else if words.tag = 0x0801 then
    if words.arg0 = 0x10000 && words.arg1 = 7 && words.arg2 = 1 && words.arg3 = 0 then
      .ok .rejectStaleMapHandle
    else .error .noncanonicalArguments
  else if words.tag = 0x0901 then
    if words.arg0 = 0x10000 && words.arg1 = 0 && words.arg2 = 0 && words.arg3 = 0 then
      .ok .rejectNonblockingReceiveHandle
    else .error .noncanonicalArguments
  else if words.tag = 0x0a01 then
    if words.arg0 = 0 && words.arg1 = 0 && words.arg2 = 1 && words.arg3 = 0 then
      .ok .rejectCapabilityCopy
    else .error .noncanonicalArguments
  else if words.tag = 0x0b01 then
    if words.arg0 = 0 && words.arg1 = 0 && words.arg2 = 0 && words.arg3 = 0 then
      .ok .rejectBlockingCancel
    else .error .noncanonicalArguments
  else if words.tag = 0x0c01 then
    if words.arg0 = 0 && words.arg1 = 0 && words.arg2 = 0 && words.arg3 = 0 then
      .ok .rejectDeferredDrain
    else .error .noncanonicalArguments
  else if words.tag = 0x0201 then
    if words.arg0 = 99 && words.arg1 = 0 && words.arg2 = 0 && words.arg3 = 0 then
      .ok .rejectUnknownSyscall
    else .error .noncanonicalArguments
  else if words.tag = 0x0301 then
    if words.arg0 = 0 && words.arg1 = 0 && words.arg2 = 0 && words.arg3 = 0 then
      .ok .rejectMalformedMap
    else .error .noncanonicalArguments
  else if words.tag = 0x0401 then
    if words.arg0 = 0 && words.arg1 = 0 && words.arg2 = 0 && words.arg3 = 0 then
      .ok .observeScheduler
    else .error .noncanonicalArguments
  else if words.tag = 0x0501 then
    if words.arg0 = 1 && words.arg1 = 0 && words.arg2 = 0 && words.arg3 = 0 then
      .ok .terminateSubjectOne
    else .error .noncanonicalArguments
  else if words.tag = 0x0601 then
    if words.arg0 = 0 && words.arg1 = 0 && words.arg2 = 0 && words.arg3 = 0 then
      .ok .enterFatalKernelFault
    else .error .noncanonicalArguments
  else if words.tag = 0x0701 then
    if words.arg0 = 0 && words.arg1 = 0 && words.arg2 = 0 && words.arg3 = 0 then
      .ok .attemptPostFatalSchedule
    else .error .noncanonicalArguments
  else if words.tag % 256 != abiVersion then .error .wrongVersion
  else if 0x0d01 ≤ words.tag then .error .reservedBits
  else .error .unknownCommand

theorem decode_encode_command (id : CommandId) :
    decodeCommand (encodeCommand id) = .ok id := by
  cases id <;> rfl

theorem command_encoding_injective (first second : CommandId)
    (h : encodeCommand first = encodeCommand second) : first = second := by
  cases first <;> cases second <;> simp_all [encodeCommand]

/-- The normalized public commands carry only raw syscall words or a bounded
subject selector.  Caller and address-space identity remain absent. -/
def fatalKernelFrame : Interrupt.HardwareFrame :=
  { vector := 14
    errorCode := 0
    savedPrivilege := .kernel
    instructionPointer := 0x400000
    stackPointer := 0x500000
    codeSelector := 0x23
    stackSelector := 0x1b
    flags := 2
    canonicalInstructionPointer := true
    canonicalStackPointer := true
    flagsAllowed := true }

def commandOperation : CommandId → AuthoritativeOperation
  | .createSubjectOne => .ordinary (.createSubject 1)
  | .rejectStaleMapHandle =>
      .ordinary (.syscall { number := 0, arg0 := 0x10000, arg1 := 7, arg2 := 1 })
  | .rejectNonblockingReceiveHandle => .ordinary (.ipc (.receive 0x10000))
  | .rejectCapabilityCopy => .ordinary (.capabilityCopy 0 0 1 {})
  | .rejectBlockingCancel => .blocking (.cancel 0)
  | .rejectDeferredDrain => .drainDeferred 0
  | .rejectUnknownSyscall =>
      .ordinary (.syscall { number := 99, arg0 := 0, arg1 := 0, arg2 := 0 })
  | .rejectMalformedMap =>
      .ordinary (.syscall { number := 0, arg0 := 0, arg1 := 0, arg2 := 0 })
  | .observeScheduler => .ordinary .scheduleNext
  | .terminateSubjectOne => .ordinary (.terminateSubject 1)
  | .enterFatalKernelFault => .ordinary (.interrupt fatalKernelFrame)
  | .attemptPostFatalSchedule => .ordinary .scheduleNext

def nextState : StateId → CommandId → Option StateId
  | .initial, .createSubjectOne => some .subjectCreated
  | .subjectCreated, .rejectUnknownSyscall => some .unknownSyscallRejected
  | .unknownSyscallRejected, .rejectMalformedMap => some .malformedMapRejected
  | .malformedMapRejected, .observeScheduler => some .schedulerObserved
  | .schedulerObserved, .terminateSubjectOne => some .subjectTerminated
  | .subjectTerminated, .enterFatalKernelFault => some .fatalEntered
  | .fatalEntered, .attemptPostFatalSchedule => some .postFatalRejected
  | _, _ => none

structure ReplyToken where
  next : StateId
  reply : UInt64
  deriving DecidableEq, Repr

def replyToken : StateId → CommandId → Option ReplyToken
  | .initial, .createSubjectOne => some { next := .subjectCreated, reply := 1 }
  | .subjectCreated, .rejectStaleMapHandle =>
      some { next := .subjectCreated, reply := 8 }
  | .subjectCreated, .rejectNonblockingReceiveHandle =>
      some { next := .subjectCreated, reply := 9 }
  | .subjectCreated, .rejectCapabilityCopy =>
      some { next := .subjectCreated, reply := 10 }
  | .subjectCreated, .rejectBlockingCancel =>
      some { next := .subjectCreated, reply := 11 }
  | .subjectCreated, .rejectDeferredDrain =>
      some { next := .subjectCreated, reply := 12 }
  | .subjectCreated, .rejectUnknownSyscall =>
      some { next := .unknownSyscallRejected, reply := 2 }
  | .unknownSyscallRejected, .rejectMalformedMap =>
      some { next := .malformedMapRejected, reply := 3 }
  | .malformedMapRejected, .observeScheduler =>
      some { next := .schedulerObserved, reply := 4 }
  | .schedulerObserved, .terminateSubjectOne =>
      some { next := .subjectTerminated, reply := 5 }
  | .subjectTerminated, .enterFatalKernelFault =>
      some { next := .fatalEntered, reply := 6 }
  | .fatalEntered, .attemptPostFatalSchedule =>
      some { next := .postFatalRejected, reply := 7 }
  | _, _ => none

/-- Version byte, next-state byte, and reply byte; all upper bits are reserved. -/
def encodeReply (token : ReplyToken) : UInt64 :=
  abiVersion + ((encodeStateId token.next / 256) * 256) + token.reply * 65536

def decodeReply (word : UInt64) : Except DecodeError ReplyToken :=
  if word = 0x010101 then .ok { next := .subjectCreated, reply := 1 }
  else if word = 0x080101 then .ok { next := .subjectCreated, reply := 8 }
  else if word = 0x090101 then .ok { next := .subjectCreated, reply := 9 }
  else if word = 0x0a0101 then .ok { next := .subjectCreated, reply := 10 }
  else if word = 0x0b0101 then .ok { next := .subjectCreated, reply := 11 }
  else if word = 0x0c0101 then .ok { next := .subjectCreated, reply := 12 }
  else if word = 0x020201 then .ok { next := .unknownSyscallRejected, reply := 2 }
  else if word = 0x030301 then .ok { next := .malformedMapRejected, reply := 3 }
  else if word = 0x040401 then .ok { next := .schedulerObserved, reply := 4 }
  else if word = 0x050501 then .ok { next := .subjectTerminated, reply := 5 }
  else if word = 0x060601 then .ok { next := .fatalEntered, reply := 6 }
  else if word = 0x070701 then .ok { next := .postFatalRejected, reply := 7 }
  else if word % 256 != abiVersion then .error .wrongVersion
  else if 0x0d0801 ≤ word then .error .reservedBits
  else .error .unknownCommand

theorem decode_encode_reply_for_trace state command token
    (htoken : replyToken state command = some token) :
    decodeReply (encodeReply token) = .ok token := by
  cases state <;> cases command <;> simp [replyToken] at htoken
  all_goals subst token <;> rfl

theorem reply_encoding_injective first second
    (hfirst : ∃ state command, replyToken state command = some first)
    (hsecond : ∃ state command, replyToken state command = some second)
    (hequal : encodeReply first = encodeReply second) :
    first = second := by
  obtain ⟨firstState, firstCommand, hfirst⟩ := hfirst
  obtain ⟨secondState, secondCommand, hsecond⟩ := hsecond
  have hdecodeFirst := decode_encode_reply_for_trace firstState firstCommand first hfirst
  have hdecodeSecond :=
    decode_encode_reply_for_trace secondState secondCommand second hsecond
  rw [hequal, hdecodeSecond] at hdecodeFirst
  exact Except.ok.inj hdecodeFirst.symm

def expectedReplyWord (state : StateId) (command : CommandId) : Option UInt64 :=
  (replyToken state command).map encodeReply

def errorWord : DecodeError → UInt64
  | .wrongVersion => 0xff01
  | .reservedBits => 0xff02
  | .unknownState => 0xff03
  | .unknownCommand => 0xff04
  | .noncanonicalArguments => 0xff05
  | .invalidSequence => 0xff06

/-- Allocation-free scalar table for the accepted hosted mixed trace.  The
logical `MixedCommandId` table below proves that these exact edges invoke the
same `authoritativeGate` operations; this raw table keeps the generated ABI
free of heap-allocated decoded values. -/
def mixedDispatchRaw (stateWord tag arg0 arg1 arg2 arg3 : UInt64) : UInt64 :=
  if tag = 0x2001 then
    if arg0 != 0x30000 || arg1 != 0x30000 ||
        arg2 != 0xCAFE || arg3 != 0xBEEF then 0xff05
    else if stateWord = 0x0801 then 0x200901 else 0xff06
  else if tag = 0x2101 then
    if arg0 != 0x30000 || arg1 != 3 || arg2 != 0 || arg3 != 0 then 0xff05
    else if stateWord = 0x0901 then 0x210a01 else 0xff06
  else if tag = 0x2201 then
    if arg0 != 0 || arg1 != 2 || arg2 != 3 || arg3 != 0 then 0xff05
    else if stateWord = 0x0a01 then 0x220b01 else 0xff06
  else if tag = 0x2301 then
    if arg0 != 0x60003 || arg1 != 0xAAAA ||
        arg2 != 0xBBBB || arg3 != 0 then 0xff05
    else if stateWord = 0x0b01 then 0x230c01 else 0xff06
  else if tag = 0x2401 then
    if arg0 != 0 || arg1 != 2 || arg2 != 3 || arg3 != 4 then 0xff05
    else if stateWord = 0x0c01 then 0x240d01 else 0xff06
  else if tag = 0x2501 then
    if arg0 != 0x50002 || arg1 != 7 || arg2 != 1 || arg3 != 0 then 0xff05
    else if stateWord = 0x0d01 then 0x250e01 else 0xff06
  else if tag = 0x2601 then
    if arg0 != 2 || arg1 != 8 || arg2 != 3 || arg3 != 0 then 0xff05
    else if stateWord = 0x0e01 then 0x260f01 else 0xff06
  else if tag = 0x2701 then
    if arg0 != 99 || arg1 != 0 || arg2 != 0 || arg3 != 0 then 0xff05
    else if stateWord = 0x0f01 then 0x271001 else 0xff06
  else if tag = 0x2801 then
    if arg0 != 0x70003 || arg1 != 0x1111 ||
        arg2 != 0x2222 || arg3 != 0 then 0xff05
    else if stateWord = 0x1001 then 0x281101 else 0xff06
  else if tag = 0x2901 then
    if arg0 != 0x30000 || arg1 != 0 || arg2 != 0 || arg3 != 0 then 0xff05
    else if stateWord = 0x1101 then 0x291201 else 0xff06
  else if tag = 0x2a01 then
    if arg0 != 0x30000 || arg1 != 0 || arg2 != 0 || arg3 != 0 then 0xff05
    else if stateWord = 0x1201 then 0x2a1301 else 0xff06
  else if tag = 0x2b01 then
    if arg0 != 0x20001 || arg1 != 0x3333 ||
        arg2 != 0x4444 || arg3 != 0 then 0xff05
    else if stateWord = 0x1301 then 0x2b1401 else 0xff06
  else if tag = 0x2c01 then
    if arg0 != 0 || arg1 != 0 || arg2 != 0 || arg3 != 0 then 0xff05
    else if stateWord = 0x1401 then 0x2c1501 else 0xff06
  else if tag = 0x2d01 then
    if arg0 != 0 || arg1 != 0 || arg2 != 0 || arg3 != 0 then 0xff05
    else if stateWord = 0x1501 then 0x2d1601 else 0xff06
  else if tag = 0x2e01 then
    if arg0 != 0 || arg1 != 0 || arg2 != 0 || arg3 != 0 then 0xff05
    else if stateWord = 0x1601 then 0x2e1701 else 0xff06
  else if tag = 0x2f01 then
    if arg0 != 0 || arg1 != 0 || arg2 != 0 || arg3 != 0 then 0xff05
    else if stateWord = 0x1701 then 0x2f1801 else 0xff06
  else if tag = 0x3001 then
    if arg0 != 7 || arg1 != 0 || arg2 != 0 || arg3 != 0 then 0xff05
    else if stateWord = 0x0f01 then 0x301901 else 0xff06
  else if tag = 0x3101 then
    if arg0 != 9 || arg1 != 0 || arg2 != 0 || arg3 != 0 then 0xff05
    else if stateWord = 0x0f01 then 0x310f01 else 0xff06
  else if tag = 0x4501 then
    if arg0 != 8 || arg1 != 1 || arg2 != 0 || arg3 != 0 then 0xff05
    else if stateWord = 0x0f01 then 0x452e01 else 0xff06
  else if tag = 0x4601 then
    if arg0 != 8 || arg1 != 1 || arg2 != 1 || arg3 != 0 then 0xff05
    else if stateWord = 0x2e01 then 0x462e01 else 0xff06
  else if tag = 0x4701 then
    if arg0 != 0x60003 || arg1 != 0xCAFE ||
        arg2 != 0xBEEF || arg3 != 0 then 0xff05
    else if stateWord = 0x0901 then 0x470901 else 0xff06
  else if tag = 0x4801 then
    if arg0 != 0x60003 || arg1 != 0xA174 ||
        arg2 != 0xB174 || arg3 != 0 then 0xff05
    else if stateWord = 0x0a01 then 0x482f01 else 0xff06
  else if tag = 0x4901 then
    if arg0 != 0x60003 || arg1 != 0 || arg2 != 0 || arg3 != 0 then 0xff05
    else if stateWord = 0x2f01 then 0x492f01 else 0xff06
  else if tag % 256 != abiVersion then 0xff01
  else if 0x4a01 ≤ tag then 0xff02
  else 0xff04

/-- Allocation-free scalar table for the in-flight revocation trace (#175).
Subject 1 seals a send-only child of its endpoint authority and then revokes
that whole lineage before subject 2 can receive; the receipt, the canceled
handle, and the same-slot replacement are all decided by the exact
authoritative gate replay named by each state token. -/
def inFlightRevocationDispatchRaw (stateWord tag arg0 arg1 arg2 arg3 : UInt64) : UInt64 :=
  if tag = 0x2001 then
    if arg0 != 0x20001 || arg1 != 0x20001 ||
        arg2 != 0xCAFE || arg3 != 0xBEEF then 0xff05
    else if stateWord = 0x6001 then 0x206101 else 0xff06
  else if tag = 0x5001 then
    if arg0 != 1 || arg1 != 1 || arg2 != 1 || arg3 != 0 then 0xff05
    else if stateWord = 0x6101 then 0x506101 else 0xff06
  else if tag = 0x5101 then
    if arg0 != 2 || arg1 != 1 || arg2 != 0 || arg3 != 0 then 0xff05
    else if stateWord = 0x6101 then 0x516101 else 0xff06
  else if tag = 0x5201 then
    if arg0 != 2 || arg1 != 1 || arg2 != 1 || arg3 != 0 then 0xff05
    else if stateWord = 0x6101 then 0x526201 else 0xff06
  else if tag = 0x5301 then
    if arg0 != 2 || arg1 != 1 || arg2 != 1 || arg3 != 0 then 0xff05
    else if stateWord = 0x6201 then 0x536201 else 0xff06
  else if tag = 0x5401 then
    if arg0 != 0x20001 || arg1 != 0x20001 ||
        arg2 != 0xCAFE || arg3 != 0xBEEF then 0xff05
    else if stateWord = 0x6201 then 0x546201 else 0xff06
  else if tag = 0x5501 then
    if arg0 != 0 || arg1 != 0 || arg2 != 0 || arg3 != 0 then 0xff05
    else if stateWord = 0x6201 then 0x556301 else 0xff06
  else if tag = 0x2101 then
    if arg0 != 0x30000 || arg1 != 3 || arg2 != 0 || arg3 != 0 then 0xff05
    else if stateWord = 0x6301 then 0x216301 else 0xff06
  else if tag = 0x2401 then
    if arg0 != 0 || arg1 != 2 || arg2 != 3 || arg3 != 4 then 0xff05
    else if stateWord = 0x6301 then 0x246401 else 0xff06
  else if tag = 0x5601 then
    if arg0 != 0x70003 || arg1 != 0xAAAA ||
        arg2 != 0xBBBB || arg3 != 0 then 0xff05
    else if stateWord = 0x6401 then 0x566401 else 0xff06
  else if tag = 0x5701 then
    if arg0 != 0x80003 || arg1 != 0x1111 ||
        arg2 != 0x2222 || arg3 != 0 then 0xff05
    else if stateWord = 0x6401 then 0x576501 else 0xff06
  else if tag % 256 != abiVersion then 0xff01
  else if 0x5801 ≤ tag then 0xff02
  else 0xff04

/-- Allocation-free scalar table for the canonical invalidation publication
protocol.  Pending state tokens retain the complete published pre-state; only
an exact acknowledgement advances to the logical successor. -/
def invalidationDispatchRaw (stateWord tag arg0 arg1 arg2 arg3 : UInt64) : UInt64 :=
  if tag = 0x3201 then
    if arg0 != 1 || arg1 != 1 || arg2 != 7 || arg3 != 1 then 0xff05
    else if stateWord = 0x1a01 then 0x321b01 else 0xff06
  else if tag = 0x3301 then
    if arg0 != 0 || arg1 != 1 || arg2 != 7 || arg3 != 1 then 0xff05
    else if stateWord = 0x1b01 then 0x331c01 else 0xff06
  else if tag = 0x3401 then
    if arg0 != 2 || arg1 != 1 || arg2 != 0 || arg3 != 0 then 0xff05
    else if stateWord = 0x1c01 then 0x341d01 else 0xff06
  else if tag = 0x3501 then
    if arg0 != 1 || arg1 != 1 || arg2 != 7 || arg3 != 0 then 0xff05
    else if stateWord = 0x1d01 then 0x351e01 else 0xff06
  else if tag = 0x3601 then
    if arg0 != 0 || arg1 != 0 || arg2 != 0 || arg3 != 0 then 0xff05
    else if stateWord = 0x1e01 then 0x361f01 else 0xff06
  else if tag = 0x3701 then
    if arg0 != 1 || arg1 != 1 || arg2 != 7 || arg3 != 1 then 0xff05
    else if stateWord = 0x1f01 then 0x372001 else 0xff06
  else if tag = 0x3801 then
    if arg0 != 3 || arg1 != 0 || arg2 != 0 || arg3 != 1 then 0xff05
    else if stateWord = 0x2001 then 0x382101 else 0xff06
  else if tag = 0x3901 then
    if arg0 != 0 || arg1 != 0 || arg2 != 0 || arg3 != 0 then 0xff05
    else if stateWord = 0x2101 then 0x392201 else 0xff06
  else if tag = 0x3a01 then
    if arg0 != 0 || arg1 != 1 || arg2 != 0 || arg3 != 0 then 0xff05
    else if stateWord = 0x2201 then 0x3a2301 else 0xff06
  else if tag = 0x3b01 then
    if arg0 != 2 || arg1 != 1 || arg2 != 0 || arg3 != 2 then 0xff05
    else if stateWord = 0x2301 then 0x3b2401 else 0xff06
  else if tag = 0x3c01 then
    if arg0 != 2 || arg1 != 0 || arg2 != 0 || arg3 != 0 then 0xff05
    else if stateWord = 0x2401 then 0x3c2501 else 0xff06
  else if tag = 0x3d01 then
    if arg0 != 3 || arg1 != 0 || arg2 != 0 || arg3 != 3 then 0xff05
    else if stateWord = 0x2501 then 0x3d2601 else 0xff06
  else if tag = 0x3e01 then
    if arg0 != 11 || arg1 != 0 || arg2 != 0 || arg3 != 0 then 0xff05
    else if stateWord = 0x2601 then 0x3e2701 else 0xff06
  else if tag = 0x3f01 then
    if arg0 != 0 || arg1 != 1 || arg2 != 7 || arg3 != 0 then 0xff05
    else if stateWord = 0x1a01 then 0x3f2801 else 0xff06
  else if tag = 0x4001 then
    if arg0 != 1 || arg1 != 1 || arg2 != 7 || arg3 != 0 then 0xff05
    else if stateWord = 0x2801 then 0x402901 else 0xff06
  else if tag = 0x4101 then
    if arg0 != 2 || arg1 != 0 || arg2 != 0 || arg3 != 0 then 0xff05
    else if stateWord = 0x1a01 then 0x412a01 else 0xff06
  else if tag = 0x4201 then
    if arg0 != 3 || arg1 != 0 || arg2 != 0 || arg3 != 0 then 0xff05
    else if stateWord = 0x2a01 then 0x422b01 else 0xff06
  else if tag = 0x4301 then
    if arg0 != 1 || arg1 != 0 || arg2 != 0 || arg3 != 0 then 0xff05
    else if stateWord = 0x2b01 then 0x432c01 else 0xff06
  else if tag = 0x4401 then
    if arg0 != 3 || arg1 != 0 || arg2 != 0 || arg3 != 1 then 0xff05
    else if stateWord = 0x2c01 then 0x442d01 else 0xff06
  else if tag % 256 != abiVersion then 0xff01
  else if 0x4501 ≤ tag then 0xff02
  else 0xff04

/-- Allocation-free generated entry point.  It validates every scalar before
selecting one exact trace edge.  The proof below connects each success word to
the full authoritative gate; this executable definition intentionally contains
no shadow kernel state. -/
@[export leanos_composite_dispatch]
def dispatch (stateWord tag arg0 arg1 arg2 arg3 : UInt64) : UInt64 :=
  if 0x1a01 ≤ stateWord && stateWord ≤ 0x2d01 then
    if stateWord % 256 != abiVersion then 0xff01
    else invalidationDispatchRaw stateWord tag arg0 arg1 arg2 arg3
  else if 0x4001 ≤ stateWord && stateWord ≤ 0x4b01 then
    if stateWord % 256 != abiVersion then 0xff01
    else FrameBudgetScenario.dispatch stateWord tag arg0 arg1 arg2 arg3
  else if 0x6001 ≤ stateWord && stateWord ≤ 0x6501 then
    if stateWord % 256 != abiVersion then 0xff01
    else inFlightRevocationDispatchRaw stateWord tag arg0 arg1 arg2 arg3
  else if stateWord = 0x0801 || stateWord = 0x0901 || stateWord = 0x0a01 ||
      stateWord = 0x0b01 || stateWord = 0x0c01 || stateWord = 0x0d01 ||
      stateWord = 0x0e01 || stateWord = 0x0f01 || stateWord = 0x1001 ||
      stateWord = 0x1101 || stateWord = 0x1201 || stateWord = 0x1301 ||
      stateWord = 0x1401 || stateWord = 0x1501 || stateWord = 0x1601 ||
      stateWord = 0x1701 || stateWord = 0x1801 || stateWord = 0x1901 ||
      stateWord = 0x2e01 || stateWord = 0x2f01 then
    mixedDispatchRaw stateWord tag arg0 arg1 arg2 arg3
  else if stateWord != 0x0001 && stateWord != 0x0101 && stateWord != 0x0201 &&
      stateWord != 0x0301 && stateWord != 0x0401 && stateWord != 0x0501 &&
      stateWord != 0x0601 && stateWord != 0x0701 then
    if stateWord % 256 != abiVersion then 0xff01
    else if 0x0801 ≤ stateWord then 0xff02
    else 0xff03
  else if tag = 0x0101 then
    if arg0 != 1 || arg1 != 0 || arg2 != 0 || arg3 != 0 then
      0xff05
    else if stateWord = 0x0001 then 0x010101
    else 0xff06
  else if tag = 0x0201 then
    if arg0 != 99 || arg1 != 0 || arg2 != 0 || arg3 != 0 then
      0xff05
    else if stateWord = 0x0101 then
      0x020201
    else 0xff06
  else if tag = 0x0301 then
    if arg0 != 0 || arg1 != 0 || arg2 != 0 || arg3 != 0 then
      0xff05
    else if stateWord = 0x0201 then
      0x030301
    else 0xff06
  else if tag = 0x0401 then
    if arg0 != 0 || arg1 != 0 || arg2 != 0 || arg3 != 0 then
      0xff05
    else if stateWord = 0x0301 then
      0x040401
    else 0xff06
  else if tag = 0x0501 then
    if arg0 != 1 || arg1 != 0 || arg2 != 0 || arg3 != 0 then
      0xff05
    else if stateWord = 0x0401 then
      0x050501
    else 0xff06
  else if tag = 0x0601 then
    if arg0 != 0 || arg1 != 0 || arg2 != 0 || arg3 != 0 then
      0xff05
    else if stateWord = 0x0501 then
      0x060601
    else 0xff06
  else if tag = 0x0701 then
    if arg0 != 0 || arg1 != 0 || arg2 != 0 || arg3 != 0 then
      0xff05
    else if stateWord = 0x0601 then
      0x070701
    else 0xff06
  else if tag = 0x0801 then
    if arg0 != 0x10000 || arg1 != 7 || arg2 != 1 || arg3 != 0 then
      0xff05
    else if stateWord = 0x0101 then 0x080101
    else 0xff06
  else if tag = 0x0901 then
    if arg0 != 0x10000 || arg1 != 0 || arg2 != 0 || arg3 != 0 then
      0xff05
    else if stateWord = 0x0101 then 0x090101
    else 0xff06
  else if tag = 0x0a01 then
    if arg0 != 0 || arg1 != 0 || arg2 != 1 || arg3 != 0 then
      0xff05
    else if stateWord = 0x0101 then 0x0a0101
    else 0xff06
  else if tag = 0x0b01 then
    if arg0 != 0 || arg1 != 0 || arg2 != 0 || arg3 != 0 then
      0xff05
    else if stateWord = 0x0101 then 0x0b0101
    else 0xff06
  else if tag = 0x0c01 then
    if arg0 != 0 || arg1 != 0 || arg2 != 0 || arg3 != 0 then
      0xff05
    else if stateWord = 0x0101 then 0x0c0101
    else 0xff06
  else if tag % 256 != abiVersion then 0xff01
  else if 0x0d01 ≤ tag then 0xff02
  else 0xff04

/-- The logical two-word version-one result. `control` remains the original
status ABI. `value = 0` means that no handle was returned; zero cannot encode a
capability handle because generation zero is reserved. -/
structure DispatchResult where
  control : UInt64
  value : UInt64
  deriving DecidableEq, Repr

/-- Select the optional value word solely from the fully validated control
word. The accepted attached-receipt selector is the only result allowed to
publish a handle. -/
def resultValue (control : UInt64) : UInt64 :=
  if control = 0x210a01 then 0x60003 else 0

def dispatchResult (stateWord tag arg0 arg1 arg2 arg3 : UInt64) : DispatchResult :=
  let control := dispatch stateWord tag arg0 arg1 arg2 arg3
  { control, value := resultValue control }

/-- Compatibility-preserving scalar accessor for result word one. Callers use
the same six immutable inputs as `leanos_composite_dispatch`; no caller-owned
result buffer or generated state cell is introduced. -/
@[export leanos_composite_dispatch_value]
def dispatchValue (stateWord tag arg0 arg1 arg2 arg3 : UInt64) : UInt64 :=
  resultValue (dispatch stateWord tag arg0 arg1 arg2 arg3)

theorem dispatchResult_control_eq_dispatch stateWord tag arg0 arg1 arg2 arg3 :
    (dispatchResult stateWord tag arg0 arg1 arg2 arg3).control =
      dispatch stateWord tag arg0 arg1 arg2 arg3 := by
  rfl

theorem dispatchResult_value_eq_dispatchValue stateWord tag arg0 arg1 arg2 arg3 :
    (dispatchResult stateWord tag arg0 arg1 arg2 arg3).value =
      dispatchValue stateWord tag arg0 arg1 arg2 arg3 := by
  rfl

/-- A returned handle is present exactly for the accepted receipt control
word. This excludes every rejection, data-only success, and malformed input. -/
theorem dispatchValue_eq_delivered_handle_iff stateWord tag arg0 arg1 arg2 arg3 :
    dispatchValue stateWord tag arg0 arg1 arg2 arg3 = 0x60003 ↔
      dispatch stateWord tag arg0 arg1 arg2 arg3 = 0x210a01 := by
  simp [dispatchValue, resultValue]

/-- All non-receipt controls expose the canonical no-value word. -/
theorem dispatchValue_eq_zero_iff stateWord tag arg0 arg1 arg2 arg3 :
    dispatchValue stateWord tag arg0 arg1 arg2 arg3 = 0 ↔
      dispatch stateWord tag arg0 arg1 arg2 arg3 ≠ 0x210a01 := by
  simp [dispatchValue, resultValue]

/-- The published receipt value is a canonical slot-3, generation-6 handle,
not a raw slot number or a reserved no-value encoding. -/
theorem delivered_handle_decodes :
    CapabilityHandle.decode 0x60003 =
      .ok { slot := 3, identity := 6 } := by
  rfl

/-!
The boot boundary uses two allocation-free words per manifest slot. The first
is the exact canonical identity (`vendor | device << 16 | class << 32`). The
second is the exact canonical control projection (`status | command << 2 |
assignmentTag << 13 | bridge << 14 | multifunction << 15 |
assignmentOwner << 16`). This compact transport contains every field of the
fixed q35 snapshot; BDF and slot order are fixed by `q35Manifest`.
-/

def q35IdentityWord (function : DMAQuarantine.FunctionState) : UInt64 :=
  function.identity.vendor |||
    function.identity.device <<< 16 |||
    function.identity.classCode <<< 32

def q35ControlWord (function : DMAQuarantine.FunctionState) : UInt64 :=
  DMAQuarantine.statusTag function.status |||
    function.command <<< 2 |||
    DMAQuarantine.assignmentTag function.assignment <<< 13 |||
    (if function.bridge then (1 : UInt64) else 0) <<< 14 |||
    (if function.multifunction then (1 : UInt64) else 0) <<< 15 |||
    DMAQuarantine.assignmentOwner function.assignment <<< 16

/-- Checked source of the scalar export's literal table. This binds all
identity/control words and the otherwise implicit BDF slot order to the
canonical rich snapshot rather than treating the generated boundary and
`DMAQuarantine.validate` as independent policies. -/
theorem q35_scalar_projection_matches_canonical_snapshot :
    DMAQuarantine.q35Snapshot.functions.map
        (fun function => (function.bdf, q35IdentityWord function, q35ControlWord function)) =
      [ (⟨0, 0, 0⟩, 0x0006000029c08086, 0x0001),
        (⟨0, 1, 0⟩, 0x0003000011111234, 0x0001),
        (⟨0, 3, 0⟩, 0, 0),
        (⟨0, 31, 0⟩, 0x0006010029188086, 0xc001),
        (⟨0, 31, 2⟩, 0x0001060129228086, 0x8001),
        (⟨0, 31, 3⟩, 0x000c050029308086, 0x8001) ] := by
  native_decide

/-- Generated, allocation-free validation of the exact production
`DMAQuarantine.q35Snapshot`. Stable nonzero results reuse
`DMAQuarantine.rejectReasonTag`. -/
@[export leanos_validate_q35_dma_snapshot]
def validateQ35DMASnapshot
    (version topology
      identity0 control0 identity1 control1 identity2 control2
      identity3 control3 identity4 control4 identity5 control5 : UInt64) : UInt64 :=
  if version != DMAQuarantine.snapshotVersion then
    1
  else if topology != DMAQuarantine.q35TopologyVersion then
    2
  else if identity0 != 0x0006000029c08086 ||
      identity1 != 0x0003000011111234 ||
      identity2 != 0 ||
      identity3 != 0x0006010029188086 ||
      identity4 != 0x0001060129228086 ||
      identity5 != 0x000c050029308086 then
    5
  else if control0 = 0x0011 || control1 = 0x0011 ||
      control2 = 0x0010 || control3 = 0xc011 ||
      control4 = 0x8011 || control5 = 0x8011 then
    8
  else if control0 != 0x0001 || control1 != 0x0001 ||
      control2 != 0 || control3 != 0xc001 ||
      control4 != 0x8001 || control5 != 0x8001 then
    4
  else
    0

/-- The generated scalar boundary and the canonical rich validator agree on
the production snapshot selected by the checked projection table above. -/
theorem validate_q35_dma_snapshot_canonical_correspondence :
    validateQ35DMASnapshot
        DMAQuarantine.snapshotVersion DMAQuarantine.q35TopologyVersion
        0x0006000029c08086 0x0001
        0x0003000011111234 0x0001
        0 0
        0x0006010029188086 0xc001
        0x0001060129228086 0x8001
        0x000c050029308086 0x8001 =
      (DMAQuarantine.encodeValidationResult
        (DMAQuarantine.validate DMAQuarantine.q35Snapshot)).head! := by
  native_decide

/-- The scalar fast rejection for a live bus-master bit is the canonical
validator's rejection for the corresponding rich q35 snapshot. -/
theorem validate_q35_dma_snapshot_bus_master_correspondence :
    validateQ35DMASnapshot
        DMAQuarantine.snapshotVersion DMAQuarantine.q35TopologyVersion
        0x0006000029c08086 0x0001
        0x0003000011111234 0x0011
        0 0
        0x0006010029188086 0xc001
        0x0001060129228086 0x8001
        0x000c050029308086 0x8001 =
      (DMAQuarantine.encodeValidationResult
        (DMAQuarantine.validate DMAQuarantine.q35BusMasterBitFlipSnapshot)).head! := by
  native_decide

/-- The scalar export and the logical adapter use one canonical edge table. -/
theorem dispatch_canonical state command :
    let words := encodeCommand command
    dispatch (encodeStateId state) words.tag words.arg0 words.arg1 words.arg2 words.arg3 =
      (expectedReplyWord state command).getD (errorWord .invalidSequence) := by
  cases state <;> cases command <;> native_decide

def initialState : Except DecodeError CompositeState :=
  match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
  | .ok plan => .ok (bootRuntime plan)
  | .error _ => .error .reservedBits

/-- Materialization is replay, not a second transition: every successor is the
literal post-state returned by `authoritativeGate`. -/
def subjectCreatedState : Except DecodeError CompositeState := do
  let state ← initialState
  pure (authoritativeGate state (commandOperation .createSubjectOne)).state

def unknownSyscallRejectedState : Except DecodeError CompositeState := do
  let state ← subjectCreatedState
  pure (authoritativeGate state (commandOperation .rejectUnknownSyscall)).state

def malformedMapRejectedState : Except DecodeError CompositeState := do
  let state ← unknownSyscallRejectedState
  pure (authoritativeGate state (commandOperation .rejectMalformedMap)).state

def schedulerObservedState : Except DecodeError CompositeState := do
  let state ← malformedMapRejectedState
  pure (authoritativeGate state (commandOperation .observeScheduler)).state

def subjectTerminatedState : Except DecodeError CompositeState := do
  let state ← schedulerObservedState
  pure (authoritativeGate state (commandOperation .terminateSubjectOne)).state

def fatalEnteredState : Except DecodeError CompositeState := do
  let state ← subjectTerminatedState
  pure (authoritativeGate state (commandOperation .enterFatalKernelFault)).state

def postFatalRejectedState : Except DecodeError CompositeState := do
  let state ← fatalEnteredState
  pure (authoritativeGate state (commandOperation .attemptPostFatalSchedule)).state

def materialize : StateId → Except DecodeError CompositeState
  | .initial => initialState
  | .subjectCreated => subjectCreatedState
  | .unknownSyscallRejected => unknownSyscallRejectedState
  | .malformedMapRejected => malformedMapRejectedState
  | .schedulerObserved => schedulerObservedState
  | .subjectTerminated => subjectTerminatedState
  | .fatalEntered => fatalEnteredState
  | .postFatalRejected => postFatalRejectedState

structure LogicalStep where
  pre : CompositeState
  operation : AuthoritativeOperation
  outcome : AuthoritativeGateOutcome

def logicalStep (state : StateId) (command : CommandId) :
    Except DecodeError LogicalStep := do
  let pre ← materialize state
  match nextState state command with
  | none => .error .invalidSequence
  | some _ =>
      pure {
        pre := pre
        operation := commandOperation command
        outcome := authoritativeGate pre (commandOperation command)
      }

/-- Every accepted logical adapter step invokes the exact global gate and
returns its exact state and typed result. -/
theorem logicalStep_refines_authoritativeGate state command step
    (hstep : logicalStep state command = .ok step) :
    step.outcome = authoritativeGate step.pre step.operation := by
  unfold logicalStep at hstep
  cases hmaterialize : materialize state with
  | error reason =>
      rw [hmaterialize] at hstep
      change Except.error reason = Except.ok step at hstep
      contradiction
  | ok pre =>
      rw [hmaterialize] at hstep
      cases hnext : nextState state command with
      | none =>
          rw [hnext] at hstep
          change Except.error DecodeError.invalidSequence = Except.ok step at hstep
          contradiction
      | some next =>
          rw [hnext] at hstep
          change Except.ok {
            pre := pre
            operation := commandOperation command
            outcome := authoritativeGate pre (commandOperation command)
          } = Except.ok step at hstep
          injection hstep with heq
          subst step
          rfl

/-- A command can advance only from its canonical predecessor token.  This is
the finite state-continuity law used by the hosted sequence corpus. -/
theorem state_continuity state command next
    (hnext : nextState state command = some next) :
    next = state ∨
    (state = .initial ∧ command = .createSubjectOne ∧ next = .subjectCreated) ∨
    (state = .subjectCreated ∧ command = .rejectUnknownSyscall ∧
      next = .unknownSyscallRejected) ∨
    (state = .unknownSyscallRejected ∧ command = .rejectMalformedMap ∧
      next = .malformedMapRejected) ∨
    (state = .malformedMapRejected ∧ command = .observeScheduler ∧
      next = .schedulerObserved) ∨
    (state = .schedulerObserved ∧ command = .terminateSubjectOne ∧
      next = .subjectTerminated) ∨
    (state = .subjectTerminated ∧ command = .enterFatalKernelFault ∧
      next = .fatalEntered) ∨
    (state = .fatalEntered ∧ command = .attemptPostFatalSchedule ∧
      next = .postFatalRejected) := by
  cases state <;> cases command <;> simp_all [nextState]

/-- The encoded successor materializes to the exact post-state returned by the
same authoritative gate step. -/
theorem materialize_next_exact state command next pre
    (hnext : nextState state command = some next)
    (hpre : materialize state = .ok pre) :
    materialize next =
      .ok (authoritativeGate pre (commandOperation command)).state := by
  cases state <;> cases command <;> simp [nextState] at hnext
  all_goals subst next
  all_goals
    simp only [materialize, subjectCreatedState, unknownSyscallRejectedState,
      malformedMapRejectedState, schedulerObservedState, subjectTerminatedState,
      fatalEnteredState, postFatalRejectedState] at hpre ⊢
    rw [hpre]
    rfl

/-- Execute any finite command list through the canonical state-token graph.
Unlike `runAuthoritativeOperations`, this function can reject: rejection means
that some command was not paired with the unique state token produced by its
predecessor. -/
def runCommands : StateId → List CommandId → Except DecodeError StateId
  | state, [] => .ok state
  | state, command :: rest =>
      match nextState state command with
      | none => .error .invalidSequence
      | some next => runCommands next rest

/-- An accepted nonempty list exposes the exact first successor and continues
only from that successor.  Thus no stale or cross-trace state can be inserted
between adjacent commands. -/
theorem runCommands_cons_continuity state command rest finish
    (hrun : runCommands state (command :: rest) = .ok finish) :
    ∃ next, nextState state command = some next ∧
      runCommands next rest = .ok finish := by
  unfold runCommands at hrun
  cases hnext : nextState state command with
  | none =>
      rw [hnext] at hrun
      contradiction
  | some next =>
      rw [hnext] at hrun
      refine ⟨next, ?_, hrun⟩
      rfl

/-- The canonical intermediate token of an accepted command prefix is unique. -/
theorem runCommands_result_unique start commands first second
    (hfirst : runCommands start commands = .ok first)
    (hsecond : runCommands start commands = .ok second) :
    first = second := by
  have hequal : Except.ok first = Except.ok second := hfirst.symm.trans hsecond
  exact Except.ok.inj hequal

/-- Every split of an accepted list has one canonical intermediate token.  A
suffix cannot be spliced onto a different trace state while retaining
acceptance. -/
theorem runCommands_append_continuity start firstCommands remainingCommands finish
    (hrun : runCommands start (firstCommands ++ remainingCommands) = .ok finish) :
    ∃ middle, runCommands start firstCommands = .ok middle ∧
      runCommands middle remainingCommands = .ok finish := by
  induction firstCommands generalizing start with
  | nil =>
      exact ⟨start, rfl, hrun⟩
  | cons command rest ih =>
      rw [List.cons_append] at hrun
      obtain ⟨next, hnext, hrest⟩ :=
        runCommands_cons_continuity start command (rest ++ remainingCommands) finish hrun
      obtain ⟨middle, hfirst, hremaining⟩ := ih next hrest
      refine ⟨middle, ?_, hremaining⟩
      simp only [runCommands, hnext]
      exact hfirst

/-- General finite-list refinement: every accepted encoded command sequence
materializes to exactly the state obtained by running the same normalized
operations through the authoritative composite gate.  The result applies to
all lists accepted by the version-one graph, not only the repository corpus. -/
theorem runCommands_refines_authoritativeOperations start commands finish pre
    (hrun : runCommands start commands = .ok finish)
    (hpre : materialize start = .ok pre) :
    materialize finish =
      .ok (runAuthoritativeOperations pre (commands.map commandOperation)) := by
  induction commands generalizing start finish pre with
  | nil =>
      simp only [runCommands, Except.ok.injEq] at hrun
      subst finish
      simpa [runAuthoritativeOperations] using hpre
  | cons command rest ih =>
      obtain ⟨next, hnext, hrest⟩ :=
        runCommands_cons_continuity start command rest finish hrun
      have hmaterialized :=
        materialize_next_exact start command next pre hnext hpre
      have hrefined := ih next finish
        (authoritativeGate pre (commandOperation command)).state hrest hmaterialized
      simpa [runAuthoritativeOperations] using hrefined

/-- Finite-list refinement for the complete version-one corpus. -/
def canonicalTrace : List (StateId × CommandId) :=
  [(.initial, .createSubjectOne),
   (.subjectCreated, .rejectUnknownSyscall),
   (.unknownSyscallRejected, .rejectMalformedMap),
   (.malformedMapRejected, .observeScheduler),
   (.schedulerObserved, .terminateSubjectOne),
   (.subjectTerminated, .enterFatalKernelFault),
   (.fatalEntered, .attemptPostFatalSchedule)]

def canonicalCommands : List CommandId :=
  [.createSubjectOne, .rejectUnknownSyscall, .rejectMalformedMap, .observeScheduler,
   .terminateSubjectOne, .enterFatalKernelFault, .attemptPostFatalSchedule]

theorem canonicalTrace_all_exact :
    canonicalTrace.all (fun edge =>
      (nextState edge.1 edge.2).isSome) = true := by
  native_decide

theorem canonicalCommands_complete :
    runCommands .initial canonicalCommands = .ok .postFatalRejected := by
  rfl

theorem canonicalCommands_refine start :
    materialize .initial = .ok start →
    materialize .postFatalRejected =
      .ok (runAuthoritativeOperations start
        (canonicalCommands.map commandOperation)) :=
  runCommands_refines_authoritativeOperations .initial canonicalCommands
    .postFatalRejected start canonicalCommands_complete

/-- The added lifecycle/fatal suffix selects subject termination, fatal entry,
and an attempted post-fatal scheduler operation.  `logicalStep_refines_authoritativeGate`
then retains each operation's exact typed result and successor. -/
theorem canonical_lifecycle_fatal_operations :
    commandOperation .terminateSubjectOne = .ordinary (.terminateSubject 1) ∧
    commandOperation .enterFatalKernelFault = .ordinary (.interrupt fatalKernelFrame) ∧
    commandOperation .attemptPostFatalSchedule = .ordinary .scheduleNext := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Complete bounded codecs

`StateId` is not itself the decoded state.  The public decoder below returns
the complete `CompositeState` reconstructed by exact authoritative replay,
together with the equality that makes the reconstruction canonical.  Thus no
caller-supplied projection, post-state fragment, or pointer identity can enter
the logical adapter. -/

structure CanonicalCompositeState where
  id : StateId
  state : CompositeState
  canonical : materialize id = .ok state

def encodeCompositeState (state : CanonicalCompositeState) : UInt64 :=
  encodeStateId state.id

def decodeCompositeState (word : UInt64) :
    Except DecodeError CanonicalCompositeState :=
  match decodeStateId word with
  | .error reason => .error reason
  | .ok id =>
      match hstate : materialize id with
      | .error reason => .error reason
      | .ok state => .ok { id, state, canonical := hstate }

theorem CanonicalCompositeState.eq_of_id_eq
    (first second : CanonicalCompositeState)
    (hid : first.id = second.id) :
    first = second := by
  cases first with
  | mk firstId firstState firstCanonical =>
      cases second with
      | mk secondId secondState secondCanonical =>
          dsimp at hid
          subst secondId
          have hstate : firstState = secondState :=
            Except.ok.inj (firstCanonical.symm.trans secondCanonical)
          subst secondState
          rfl

theorem decodeCompositeState_sound word decoded
    (_hdecode : decodeCompositeState word = .ok decoded) :
    materialize decoded.id = .ok decoded.state :=
  decoded.canonical

theorem decode_encode_composite_state (state : CanonicalCompositeState) :
    decodeCompositeState (encodeCompositeState state) = .ok state := by
  unfold decodeCompositeState encodeCompositeState
  rw [decode_encode_state]
  simp only
  split
  · rename_i reason hmaterialize
    have hfalse : Except.error reason = Except.ok state.state :=
      hmaterialize.symm.trans state.canonical
    contradiction
  · congr 1
    exact CanonicalCompositeState.eq_of_id_eq _ _ rfl

theorem composite_state_encoding_injective
    (first second : CanonicalCompositeState)
    (hequal : encodeCompositeState first = encodeCompositeState second) :
    first = second := by
  apply CanonicalCompositeState.eq_of_id_eq
  apply state_encoding_injective
  exact hequal

/-- A normalized operation is the exact `AuthoritativeOperation` selected by
its canonical command words. -/
structure CanonicalOperation where
  command : CommandId
  operation : AuthoritativeOperation
  exact : operation = commandOperation command

def canonicalOperation (command : CommandId) : CanonicalOperation :=
  { command, operation := commandOperation command, exact := rfl }

def encodeOperation (operation : CanonicalOperation) : CommandWords :=
  encodeCommand operation.command

def decodeOperation (words : CommandWords) :
    Except DecodeError CanonicalOperation := do
  pure (canonicalOperation (← decodeCommand words))

theorem CanonicalOperation.eq_of_command_eq
    (first second : CanonicalOperation)
    (hcommand : first.command = second.command) :
    first = second := by
  cases first with
  | mk firstCommand firstOperation firstExact =>
      cases second with
      | mk secondCommand secondOperation secondExact =>
          dsimp at hcommand
          subst secondCommand
          cases firstExact
          cases secondExact
          rfl

theorem decode_encode_operation (operation : CanonicalOperation) :
    decodeOperation (encodeOperation operation) = .ok operation := by
  unfold decodeOperation encodeOperation
  rw [decode_encode_command]
  change Except.ok (canonicalOperation operation.command) = Except.ok operation
  congr 1
  exact CanonicalOperation.eq_of_command_eq _ _ rfl

theorem operation_encoding_injective
    (first second : CanonicalOperation)
    (hequal : encodeOperation first = encodeOperation second) :
    first = second := by
  apply CanonicalOperation.eq_of_command_eq
  apply command_encoding_injective
  exact hequal

/-- The typed logical result contains the literal post-state and result of the
one authoritative gate invocation.  This is the object denoted by an accepted
reply word; the small word is only its bounded canonical name. -/
structure CanonicalTypedStep where
  pre : CanonicalCompositeState
  command : CommandId
  operation : AuthoritativeOperation
  post : CompositeState
  result : AuthoritativeGateResult
  operation_exact : operation = commandOperation command
  outcome_exact :
    authoritativeGate pre.state operation = { state := post, result := result }

def canonicalTypedStep (state : CanonicalCompositeState) (command : CommandId) :
    CanonicalTypedStep :=
  let operation := commandOperation command
  let outcome := authoritativeGate state.state operation
  { pre := state
    command
    operation
    post := outcome.state
    result := outcome.result
    operation_exact := rfl
    outcome_exact := rfl }

theorem canonicalTypedStep_refines_authoritativeGate state command :
    let step := canonicalTypedStep state command
    authoritativeGate step.pre.state step.operation =
      { state := step.post, result := step.result } := by
  exact (canonicalTypedStep state command).outcome_exact

def decodeTypedReply (stateWord : UInt64) (command : CommandId)
    (replyWord : UInt64) : Except DecodeError CanonicalTypedStep := do
  let state ← decodeCompositeState stateWord
  let token ← decodeReply replyWord
  match replyToken state.id command with
  | some expected =>
      if token = expected then .ok (canonicalTypedStep state command)
      else .error .invalidSequence
  | none => .error .invalidSequence

theorem decode_encode_typed_reply state command token
    (hstate :
      decodeCompositeState (encodeCompositeState state) = .ok state)
    (htoken : replyToken state.id command = some token) :
    decodeTypedReply (encodeCompositeState state) command (encodeReply token) =
      .ok (canonicalTypedStep state command) := by
  unfold decodeTypedReply
  rw [hstate]
  rw [decode_encode_reply_for_trace state.id command token htoken]
  change (match replyToken state.id command with
    | some expected =>
        if token = expected then
          Except.ok (ε := DecodeError) (canonicalTypedStep state command)
        else Except.error (α := CanonicalTypedStep) .invalidSequence
    | none => Except.error (α := CanonicalTypedStep) .invalidSequence) =
      Except.ok (ε := DecodeError) (canonicalTypedStep state command)
  rw [htoken]
  simp

/-- Every successful scalar export result decodes to the literal typed result
and post-state of the same authoritative gate invocation. -/
theorem decode_dispatch_success
    (state : CanonicalCompositeState) command token
    (htoken : replyToken state.id command = some token) :
    let words := encodeCommand command
    decodeTypedReply (encodeCompositeState state) command
      (dispatch (encodeCompositeState state)
        words.tag words.arg0 words.arg1 words.arg2 words.arg3) =
      .ok (canonicalTypedStep state command) := by
  dsimp
  unfold encodeCompositeState
  rw [dispatch_canonical]
  simp only [expectedReplyWord, htoken, Option.map_some, Option.getD_some]
  exact decode_encode_typed_reply state command token
    (decode_encode_composite_state state) htoken

theorem capabilityHandle_command_uses_canonical_codec :
    CapabilityHandle.decode 0x10000 =
        .ok { slot := 0, identity := 1 } ∧
      CapabilityHandle.encode { slot := 0, identity := 1 } = some 0x10000 ∧
      commandOperation .rejectStaleMapHandle =
        .ordinary (.syscall
          { number := 0, arg0 := 0x10000, arg1 := 7, arg2 := 1 }) := by
  constructor
  · rfl
  constructor
  · rfl
  · rfl

def mixedPhaseTwoCommands : List CommandId :=
  [.rejectStaleMapHandle, .rejectNonblockingReceiveHandle,
   .rejectCapabilityCopy, .rejectBlockingCancel, .rejectDeferredDrain]

theorem mixedPhaseTwoCommands_cover_authoritative_families :
    mixedPhaseTwoCommands.map commandOperation =
      [.ordinary (.syscall { number := 0, arg0 := 0x10000, arg1 := 7, arg2 := 1 }),
       .ordinary (.ipc (.receive 0x10000)),
       .ordinary (.capabilityCopy 0 0 1 {}),
       .blocking (.cancel 0),
       .drainDeferred 0] := by
  rfl

/-! ## Accepted hosted mixed trace

The seed trace above keeps useful denial probes.  The version-one hosted
integration trace below is the positive end-to-end corpus required by the
stateful ABI: its canonical pre-state is kernel-owned, and every successor is
reconstructed by replaying the exact authoritative gate. -/

inductive MixedStateId where
  | initial
  | transferOffered
  | transferAccepted
  | delegatedSendAccepted
  | transferredCapabilityRevoked
  | staleHandleRejected
  | freshCapabilityCopied
  | syscallMapped
  | directMapped
  | unknownSyscallRejected
  | nonblockingSent
  | nonblockingReceived
  | blockingReceiverBlocked
  | blockingReceiverWoken
  | timerSwitched
  | userFaultCleaned
  | fatalEntered
  | postFatalRejected
  | pageUnmapped
  | pageProtected
  deriving DecidableEq, Repr

def encodeMixedState : MixedStateId → UInt64
  | .initial => 0x0801
  | .transferOffered => 0x0901
  | .transferAccepted => 0x0a01
  | .delegatedSendAccepted => 0x2f01
  | .transferredCapabilityRevoked => 0x0b01
  | .staleHandleRejected => 0x0c01
  | .freshCapabilityCopied => 0x0d01
  | .syscallMapped => 0x0e01
  | .directMapped => 0x0f01
  | .unknownSyscallRejected => 0x1001
  | .nonblockingSent => 0x1101
  | .nonblockingReceived => 0x1201
  | .blockingReceiverBlocked => 0x1301
  | .blockingReceiverWoken => 0x1401
  | .timerSwitched => 0x1501
  | .userFaultCleaned => 0x1601
  | .fatalEntered => 0x1701
  | .postFatalRejected => 0x1801
  | .pageUnmapped => 0x1901
  | .pageProtected => 0x2e01

def decodeMixedState (word : UInt64) : Except DecodeError MixedStateId :=
  if word = 0x0801 then .ok .initial
  else if word = 0x0901 then .ok .transferOffered
  else if word = 0x0a01 then .ok .transferAccepted
  else if word = 0x2f01 then .ok .delegatedSendAccepted
  else if word = 0x0b01 then .ok .transferredCapabilityRevoked
  else if word = 0x0c01 then .ok .staleHandleRejected
  else if word = 0x0d01 then .ok .freshCapabilityCopied
  else if word = 0x0e01 then .ok .syscallMapped
  else if word = 0x0f01 then .ok .directMapped
  else if word = 0x1001 then .ok .unknownSyscallRejected
  else if word = 0x1101 then .ok .nonblockingSent
  else if word = 0x1201 then .ok .nonblockingReceived
  else if word = 0x1301 then .ok .blockingReceiverBlocked
  else if word = 0x1401 then .ok .blockingReceiverWoken
  else if word = 0x1501 then .ok .timerSwitched
  else if word = 0x1601 then .ok .userFaultCleaned
  else if word = 0x1701 then .ok .fatalEntered
  else if word = 0x1801 then .ok .postFatalRejected
  else if word = 0x1901 then .ok .pageUnmapped
  else if word = 0x2e01 then .ok .pageProtected
  else if word % 256 != abiVersion then .error .wrongVersion
  else if 0x1a01 ≤ word then .error .reservedBits
  else .error .unknownState

theorem decode_encode_mixed_state state :
    decodeMixedState (encodeMixedState state) = .ok state := by
  cases state <;> rfl

theorem mixed_state_encoding_injective first second
    (hequal : encodeMixedState first = encodeMixedState second) :
    first = second := by
  cases first <;> cases second <;> simp_all [encodeMixedState]

inductive MixedCommandId where
  | offerTransfer
  | acceptTransfer
  | rejectSealedHandleBeforeReceipt
  | useDelegatedSend
  | rejectDelegatedReceive
  | revokeTransferredCapability
  | rejectStaleReusedHandle
  | copyFreshCapability
  | acceptedSyscallMap
  | acceptedDirectMap
  | rejectUnknownSyscall
  | nonblockingSend
  | nonblockingReceive
  | blockingReceive
  | blockingSend
  | timerSwitch
  | cleanupUserFault
  | enterFatalKernelFault
  | attemptPostFatalSchedule
  | acceptedSyscallUnmap
  | rejectUnmappedPageUnmap
  | acceptedProtect
  | rejectProtectAmplification
  deriving DecidableEq, Repr

def encodeMixedCommand : MixedCommandId → CommandWords
  | .offerTransfer =>
      { tag := 0x2001, arg0 := 0x30000, arg1 := 0x30000,
        arg2 := 0xCAFE, arg3 := 0xBEEF }
  | .acceptTransfer =>
      { tag := 0x2101, arg0 := 0x30000, arg1 := 3, arg2 := 0, arg3 := 0 }
  | .rejectSealedHandleBeforeReceipt =>
      { tag := 0x4701, arg0 := 0x60003, arg1 := 0xCAFE,
        arg2 := 0xBEEF, arg3 := 0 }
  | .useDelegatedSend =>
      { tag := 0x4801, arg0 := 0x60003, arg1 := 0xA174,
        arg2 := 0xB174, arg3 := 0 }
  | .rejectDelegatedReceive =>
      { tag := 0x4901, arg0 := 0x60003, arg1 := 0, arg2 := 0, arg3 := 0 }
  | .revokeTransferredCapability =>
      { tag := 0x2201, arg0 := 0, arg1 := 2, arg2 := 3, arg3 := 0 }
  | .rejectStaleReusedHandle =>
      { tag := 0x2301, arg0 := 0x60003, arg1 := 0xAAAA,
        arg2 := 0xBBBB, arg3 := 0 }
  | .copyFreshCapability =>
      { tag := 0x2401, arg0 := 0, arg1 := 2, arg2 := 3, arg3 := 4 }
  | .acceptedSyscallMap =>
      { tag := 0x2501, arg0 := 0x50002, arg1 := 7, arg2 := 1, arg3 := 0 }
  | .acceptedDirectMap =>
      { tag := 0x2601, arg0 := 2, arg1 := 8, arg2 := 3, arg3 := 0 }
  | .rejectUnknownSyscall =>
      { tag := 0x2701, arg0 := 99, arg1 := 0, arg2 := 0, arg3 := 0 }
  | .nonblockingSend =>
      { tag := 0x2801, arg0 := 0x70003, arg1 := 0x1111,
        arg2 := 0x2222, arg3 := 0 }
  | .nonblockingReceive =>
      { tag := 0x2901, arg0 := 0x30000, arg1 := 0, arg2 := 0, arg3 := 0 }
  | .blockingReceive =>
      { tag := 0x2a01, arg0 := 0x30000, arg1 := 0, arg2 := 0, arg3 := 0 }
  | .blockingSend =>
      { tag := 0x2b01, arg0 := 0x20001, arg1 := 0x3333,
        arg2 := 0x4444, arg3 := 0 }
  | .timerSwitch =>
      { tag := 0x2c01, arg0 := 0, arg1 := 0, arg2 := 0, arg3 := 0 }
  | .cleanupUserFault =>
      { tag := 0x2d01, arg0 := 0, arg1 := 0, arg2 := 0, arg3 := 0 }
  | .enterFatalKernelFault =>
      { tag := 0x2e01, arg0 := 0, arg1 := 0, arg2 := 0, arg3 := 0 }
  | .attemptPostFatalSchedule =>
      { tag := 0x2f01, arg0 := 0, arg1 := 0, arg2 := 0, arg3 := 0 }
  | .acceptedSyscallUnmap =>
      { tag := 0x3001, arg0 := 7, arg1 := 0, arg2 := 0, arg3 := 0 }
  | .rejectUnmappedPageUnmap =>
      { tag := 0x3101, arg0 := 9, arg1 := 0, arg2 := 0, arg3 := 0 }
  | .acceptedProtect =>
      { tag := 0x4501, arg0 := 8, arg1 := 1, arg2 := 0, arg3 := 0 }
  | .rejectProtectAmplification =>
      { tag := 0x4601, arg0 := 8, arg1 := 1, arg2 := 1, arg3 := 0 }

def decodeMixedCommand (words : CommandWords) :
    Except DecodeError MixedCommandId :=
  if words = encodeMixedCommand .offerTransfer then .ok .offerTransfer
  else if words = encodeMixedCommand .acceptTransfer then .ok .acceptTransfer
  else if words = encodeMixedCommand .rejectSealedHandleBeforeReceipt then
    .ok .rejectSealedHandleBeforeReceipt
  else if words = encodeMixedCommand .useDelegatedSend then
    .ok .useDelegatedSend
  else if words = encodeMixedCommand .rejectDelegatedReceive then
    .ok .rejectDelegatedReceive
  else if words = encodeMixedCommand .revokeTransferredCapability then
    .ok .revokeTransferredCapability
  else if words = encodeMixedCommand .rejectStaleReusedHandle then
    .ok .rejectStaleReusedHandle
  else if words = encodeMixedCommand .copyFreshCapability then .ok .copyFreshCapability
  else if words = encodeMixedCommand .acceptedSyscallMap then .ok .acceptedSyscallMap
  else if words = encodeMixedCommand .acceptedDirectMap then .ok .acceptedDirectMap
  else if words = encodeMixedCommand .rejectUnknownSyscall then .ok .rejectUnknownSyscall
  else if words = encodeMixedCommand .nonblockingSend then .ok .nonblockingSend
  else if words = encodeMixedCommand .nonblockingReceive then .ok .nonblockingReceive
  else if words = encodeMixedCommand .blockingReceive then .ok .blockingReceive
  else if words = encodeMixedCommand .blockingSend then .ok .blockingSend
  else if words = encodeMixedCommand .timerSwitch then .ok .timerSwitch
  else if words = encodeMixedCommand .cleanupUserFault then .ok .cleanupUserFault
  else if words = encodeMixedCommand .enterFatalKernelFault then .ok .enterFatalKernelFault
  else if words = encodeMixedCommand .attemptPostFatalSchedule then
    .ok .attemptPostFatalSchedule
  else if words = encodeMixedCommand .acceptedSyscallUnmap then
    .ok .acceptedSyscallUnmap
  else if words = encodeMixedCommand .rejectUnmappedPageUnmap then
    .ok .rejectUnmappedPageUnmap
  else if words = encodeMixedCommand .acceptedProtect then
    .ok .acceptedProtect
  else if words = encodeMixedCommand .rejectProtectAmplification then
    .ok .rejectProtectAmplification
  else if words.tag % 256 != abiVersion then .error .wrongVersion
  else if 0x4a01 ≤ words.tag then .error .reservedBits
  else .error .noncanonicalArguments

theorem decode_encode_mixed_command command :
    decodeMixedCommand (encodeMixedCommand command) = .ok command := by
  cases command <;> rfl

theorem mixed_command_encoding_injective first second
    (hequal : encodeMixedCommand first = encodeMixedCommand second) :
    first = second := by
  cases first <;> cases second <;> simp_all [encodeMixedCommand]

def mixedCommandOperation : MixedCommandId → AuthoritativeOperation
  | .offerTransfer =>
      .ordinary (.transferOffer 0x30000 0x30000 .endpoint
        { word0 := 0xCAFE, word1 := 0xBEEF } { send := true })
  | .acceptTransfer => .ordinary (.transferAccept 0x30000 3)
  | .rejectSealedHandleBeforeReceipt =>
      .ordinary (.ipc (.send 0x60003 0xCAFE 0xBEEF))
  | .useDelegatedSend =>
      .ordinary (.ipc (.send 0x60003 0xA174 0xB174))
  | .rejectDelegatedReceive => .ordinary (.ipc (.receive 0x60003))
  | .revokeTransferredCapability => .ordinary (.capabilityRevoke 0 2 3)
  | .rejectStaleReusedHandle =>
      .ordinary (.ipc (.send 0x60003 0xAAAA 0xBBBB))
  | .copyFreshCapability =>
      .ordinary (.capabilityCopy 0 2 3 { send := true })
  | .acceptedSyscallMap =>
      .ordinary (.syscall { number := 0, arg0 := 0x50002, arg1 := 7, arg2 := 1 })
  | .acceptedDirectMap =>
      .ordinary (.map 2 8 { read := true, write := true })
  | .rejectUnknownSyscall =>
      .ordinary (.syscall { number := 99, arg0 := 0, arg1 := 0, arg2 := 0 })
  | .nonblockingSend => .ordinary (.ipc (.send 0x70003 0x1111 0x2222))
  | .nonblockingReceive => .ordinary (.ipc (.receive 0x30000))
  | .blockingReceive =>
      .blocking (.receive 0x30000 compositeDispatcherBlockingFrame
        compositeDispatcherBlockingRegisters)
  | .blockingSend => .blocking (.send 0x20001 0x3333 0x4444)
  | .timerSwitch =>
      .ordinary (.resumePreempt compositeDispatcherTimerFrame
        compositeDispatcherTimerRegisters)
  | .cleanupUserFault => .ordinary (.interrupt compositeDispatcherUserFaultFrame)
  | .enterFatalKernelFault => .ordinary (.interrupt compositeDispatcherKernelFaultFrame)
  | .attemptPostFatalSchedule => .ordinary .scheduleNext
  | .acceptedSyscallUnmap =>
      .ordinary (.syscall { number := 1, arg0 := 7, arg1 := 0, arg2 := 0 })
  | .rejectUnmappedPageUnmap =>
      .ordinary (.syscall { number := 1, arg0 := 9, arg1 := 0, arg2 := 0 })
  | .acceptedProtect =>
      .ordinary (.protect 8 { read := true })
  | .rejectProtectAmplification =>
      .ordinary (.protect 8 { read := true, write := true })

def mixedNextState : MixedStateId → MixedCommandId → Option MixedStateId
  | .initial, .offerTransfer => some .transferOffered
  | .transferOffered, .acceptTransfer => some .transferAccepted
  | .transferOffered, .rejectSealedHandleBeforeReceipt =>
      some .transferOffered
  | .transferAccepted, .useDelegatedSend => some .delegatedSendAccepted
  | .delegatedSendAccepted, .rejectDelegatedReceive =>
      some .delegatedSendAccepted
  | .transferAccepted, .revokeTransferredCapability =>
      some .transferredCapabilityRevoked
  | .transferredCapabilityRevoked, .rejectStaleReusedHandle =>
      some .staleHandleRejected
  | .staleHandleRejected, .copyFreshCapability => some .freshCapabilityCopied
  | .freshCapabilityCopied, .acceptedSyscallMap => some .syscallMapped
  | .syscallMapped, .acceptedDirectMap => some .directMapped
  | .directMapped, .rejectUnknownSyscall => some .unknownSyscallRejected
  | .unknownSyscallRejected, .nonblockingSend => some .nonblockingSent
  | .nonblockingSent, .nonblockingReceive => some .nonblockingReceived
  | .nonblockingReceived, .blockingReceive => some .blockingReceiverBlocked
  | .blockingReceiverBlocked, .blockingSend => some .blockingReceiverWoken
  | .blockingReceiverWoken, .timerSwitch => some .timerSwitched
  | .timerSwitched, .cleanupUserFault => some .userFaultCleaned
  | .userFaultCleaned, .enterFatalKernelFault => some .fatalEntered
  | .fatalEntered, .attemptPostFatalSchedule => some .postFatalRejected
  | .directMapped, .acceptedSyscallUnmap => some .pageUnmapped
  | .directMapped, .rejectUnmappedPageUnmap => some .directMapped
  | .directMapped, .acceptedProtect => some .pageProtected
  | .pageProtected, .rejectProtectAmplification => some .pageProtected
  | _, _ => none

def mixedExpectedReply : MixedStateId → MixedCommandId → Option UInt64
  | .initial, .offerTransfer => some 0x200901
  | .transferOffered, .acceptTransfer => some 0x210a01
  | .transferOffered, .rejectSealedHandleBeforeReceipt => some 0x470901
  | .transferAccepted, .useDelegatedSend => some 0x482f01
  | .delegatedSendAccepted, .rejectDelegatedReceive => some 0x492f01
  | .transferAccepted, .revokeTransferredCapability => some 0x220b01
  | .transferredCapabilityRevoked, .rejectStaleReusedHandle => some 0x230c01
  | .staleHandleRejected, .copyFreshCapability => some 0x240d01
  | .freshCapabilityCopied, .acceptedSyscallMap => some 0x250e01
  | .syscallMapped, .acceptedDirectMap => some 0x260f01
  | .directMapped, .rejectUnknownSyscall => some 0x271001
  | .unknownSyscallRejected, .nonblockingSend => some 0x281101
  | .nonblockingSent, .nonblockingReceive => some 0x291201
  | .nonblockingReceived, .blockingReceive => some 0x2a1301
  | .blockingReceiverBlocked, .blockingSend => some 0x2b1401
  | .blockingReceiverWoken, .timerSwitch => some 0x2c1501
  | .timerSwitched, .cleanupUserFault => some 0x2d1601
  | .userFaultCleaned, .enterFatalKernelFault => some 0x2e1701
  | .fatalEntered, .attemptPostFatalSchedule => some 0x2f1801
  | .directMapped, .acceptedSyscallUnmap => some 0x301901
  | .directMapped, .rejectUnmappedPageUnmap => some 0x310f01
  | .directMapped, .acceptedProtect => some 0x452e01
  | .pageProtected, .rejectProtectAmplification => some 0x462e01
  | _, _ => none

inductive MixedReplyId where
  | transferOffered
  | transferAccepted
  | sealedHandleRejected
  | delegatedSendAccepted
  | delegatedReceiveRejected
  | transferredCapabilityRevoked
  | staleHandleRejected
  | freshCapabilityCopied
  | syscallMapped
  | directMapped
  | unknownSyscallRejected
  | nonblockingSent
  | nonblockingReceived
  | blockingReceiverBlocked
  | blockingReceiverWoken
  | timerSwitched
  | userFaultCleaned
  | fatalEntered
  | postFatalRejected
  | pageUnmapped
  | unmappedPageRejected
  | pageProtected
  | protectAmplificationRejected
  deriving DecidableEq, Repr

def encodeMixedReply : MixedReplyId → UInt64
  | .transferOffered => 0x200901
  | .transferAccepted => 0x210a01
  | .sealedHandleRejected => 0x470901
  | .delegatedSendAccepted => 0x482f01
  | .delegatedReceiveRejected => 0x492f01
  | .transferredCapabilityRevoked => 0x220b01
  | .staleHandleRejected => 0x230c01
  | .freshCapabilityCopied => 0x240d01
  | .syscallMapped => 0x250e01
  | .directMapped => 0x260f01
  | .unknownSyscallRejected => 0x271001
  | .nonblockingSent => 0x281101
  | .nonblockingReceived => 0x291201
  | .blockingReceiverBlocked => 0x2a1301
  | .blockingReceiverWoken => 0x2b1401
  | .timerSwitched => 0x2c1501
  | .userFaultCleaned => 0x2d1601
  | .fatalEntered => 0x2e1701
  | .postFatalRejected => 0x2f1801
  | .pageUnmapped => 0x301901
  | .unmappedPageRejected => 0x310f01
  | .pageProtected => 0x452e01
  | .protectAmplificationRejected => 0x462e01

def decodeMixedReply (word : UInt64) : Except DecodeError MixedReplyId :=
  if word = 0x200901 then .ok .transferOffered
  else if word = 0x210a01 then .ok .transferAccepted
  else if word = 0x470901 then .ok .sealedHandleRejected
  else if word = 0x482f01 then .ok .delegatedSendAccepted
  else if word = 0x492f01 then .ok .delegatedReceiveRejected
  else if word = 0x220b01 then .ok .transferredCapabilityRevoked
  else if word = 0x230c01 then .ok .staleHandleRejected
  else if word = 0x240d01 then .ok .freshCapabilityCopied
  else if word = 0x250e01 then .ok .syscallMapped
  else if word = 0x260f01 then .ok .directMapped
  else if word = 0x271001 then .ok .unknownSyscallRejected
  else if word = 0x281101 then .ok .nonblockingSent
  else if word = 0x291201 then .ok .nonblockingReceived
  else if word = 0x2a1301 then .ok .blockingReceiverBlocked
  else if word = 0x2b1401 then .ok .blockingReceiverWoken
  else if word = 0x2c1501 then .ok .timerSwitched
  else if word = 0x2d1601 then .ok .userFaultCleaned
  else if word = 0x2e1701 then .ok .fatalEntered
  else if word = 0x2f1801 then .ok .postFatalRejected
  else if word = 0x301901 then .ok .pageUnmapped
  else if word = 0x310f01 then .ok .unmappedPageRejected
  else if word = 0x452e01 then .ok .pageProtected
  else if word = 0x462e01 then .ok .protectAmplificationRejected
  else if word % 256 != abiVersion then .error .wrongVersion
  else if 0x4a0001 ≤ word then .error .reservedBits
  else .error .unknownCommand

theorem decode_encode_mixed_reply reply :
    decodeMixedReply (encodeMixedReply reply) = .ok reply := by
  cases reply <;> rfl

theorem mixed_reply_encoding_injective first second
    (hequal : encodeMixedReply first = encodeMixedReply second) :
    first = second := by
  cases first <;> cases second <;> simp_all [encodeMixedReply]

def mixedReplyId : MixedStateId → MixedCommandId → Option MixedReplyId
  | .initial, .offerTransfer => some .transferOffered
  | .transferOffered, .acceptTransfer => some .transferAccepted
  | .transferOffered, .rejectSealedHandleBeforeReceipt =>
      some .sealedHandleRejected
  | .transferAccepted, .useDelegatedSend => some .delegatedSendAccepted
  | .delegatedSendAccepted, .rejectDelegatedReceive =>
      some .delegatedReceiveRejected
  | .transferAccepted, .revokeTransferredCapability =>
      some .transferredCapabilityRevoked
  | .transferredCapabilityRevoked, .rejectStaleReusedHandle =>
      some .staleHandleRejected
  | .staleHandleRejected, .copyFreshCapability => some .freshCapabilityCopied
  | .freshCapabilityCopied, .acceptedSyscallMap => some .syscallMapped
  | .syscallMapped, .acceptedDirectMap => some .directMapped
  | .directMapped, .rejectUnknownSyscall => some .unknownSyscallRejected
  | .unknownSyscallRejected, .nonblockingSend => some .nonblockingSent
  | .nonblockingSent, .nonblockingReceive => some .nonblockingReceived
  | .nonblockingReceived, .blockingReceive => some .blockingReceiverBlocked
  | .blockingReceiverBlocked, .blockingSend => some .blockingReceiverWoken
  | .blockingReceiverWoken, .timerSwitch => some .timerSwitched
  | .timerSwitched, .cleanupUserFault => some .userFaultCleaned
  | .userFaultCleaned, .enterFatalKernelFault => some .fatalEntered
  | .fatalEntered, .attemptPostFatalSchedule => some .postFatalRejected
  | .directMapped, .acceptedSyscallUnmap => some .pageUnmapped
  | .directMapped, .rejectUnmappedPageUnmap => some .unmappedPageRejected
  | .directMapped, .acceptedProtect => some .pageProtected
  | .pageProtected, .rejectProtectAmplification => some .protectAmplificationRejected
  | _, _ => none

/-- The full typed meaning of each mixed reply selector.  This table is
independent of `dispatch` and `authoritativeGate`: a scalar selector can only
claim one exact authoritative result. -/
def mixedReplyResult : MixedReplyId → AuthoritativeGateResult
  | .transferOffered =>
      .completed (.ordinary (.transferOffer .accepted))
  | .transferAccepted =>
      .completed (.ordinary (.transferAccept
        (.delivered
          { endpoint := 10, sender := 2,
            payload := { word0 := 0xCAFE, word1 := 0xBEEF } })
        (some 0x60003)))
  | .sealedHandleRejected =>
      .completed (.ordinary (.ipc (.syscall
        (.sendHandleRejected (.denied .staleHandle)))))
  | .delegatedSendAccepted =>
      .completed (.ordinary (.ipc (.syscall .sent)))
  | .delegatedReceiveRejected =>
      .completed (.ordinary (.ipc (.syscall
        (.receiveRejected .missingReceive))))
  | .transferredCapabilityRevoked =>
      .completed (.ordinary (.capability .accepted))
  | .staleHandleRejected =>
      .completed (.ordinary (.ipc (.syscall
        (.sendHandleRejected (.denied .staleHandle)))))
  | .freshCapabilityCopied =>
      .completed (.ordinary (.capability .accepted))
  | .syscallMapped =>
      .completed (.ordinary (.syscall .accepted))
  | .directMapped =>
      .completed (.ordinary (.map .accepted))
  | .unknownSyscallRejected =>
      .completed (.ordinary (.syscall (.rejected (.decode .unknownSyscall))))
  | .nonblockingSent =>
      .completed (.ordinary (.ipc (.syscall .sent)))
  | .nonblockingReceived =>
      .completed (.ordinary (.ipc (.syscall (.delivered 2 0x1111 0x2222))))
  | .blockingReceiverBlocked =>
      .completed (.blocking (.receive .blocked))
  | .blockingReceiverWoken =>
      .completed (.blocking (.send (.woke
        { owner := 2, addressSpace := 2
          frame := compositeDispatcherBlockingFrame
          registers := compositeDispatcherBlockingRegisters
          kind := .suspended })))
  | .timerSwitched =>
      .completed (.ordinary (.resume
        (some
          { owner := 2, addressSpace := 2
            frame := compositeDispatcherBlockingFrame
            registers := compositeDispatcherBlockingRegisters
            kind := .suspended })
        none))
  | .userFaultCleaned =>
      .completed (.ordinary (.interrupt (.contained 2)))
  | .fatalEntered =>
      .completed (.ordinary (.interrupt (.fatal .kernelFault)))
  | .postFatalRejected =>
      .rejectedHalted
        { reason := .kernelFault
          active := some
            { vector := 14, origin := .kernel,
              frame := compositeDispatcherKernelFaultFrame }
          incomingVector := 14
          incomingOrigin := .kernel }
  | .pageUnmapped =>
      .completed (.ordinary (.syscall .accepted))
  | .unmappedPageRejected =>
      .completed (.ordinary (.syscall (.rejected (.unmap .unmappedPage))))
  | .pageProtected =>
      .completed (.ordinary (.protect .accepted))
  | .protectAmplificationRejected =>
      .completed (.ordinary (.protect (.rejected .notOwner)))

/-- Machine effects are meanings of canonical typed replies, not a second
caller-maintained state channel.  The accepted unmap reply requires one exact
page invalidation; every other reply in this bounded slice requests none. -/
def mixedReplyEffect : MixedReplyId → StaleTranslation.Effect
  | .pageUnmapped => .page 2 7
  | .pageProtected => .page 2 8
  | _ => .none

theorem mixedExpectedReply_uses_canonical_codec state command :
    mixedExpectedReply state command =
      (mixedReplyId state command).map encodeMixedReply := by
  cases state <;> cases command <;> rfl

theorem mixed_dispatch_canonical state command :
    let words := encodeMixedCommand command
    dispatch (encodeMixedState state)
      words.tag words.arg0 words.arg1 words.arg2 words.arg3 =
      (mixedExpectedReply state command).getD (errorWord .invalidSequence) := by
  cases state <;> cases command <;> native_decide

/-- The accepted unmap effect cannot be spliced onto a stale state token or a
different canonical command.  Its address-space/page target is consequently
confined to the kernel-derived address space 2 and decoded page 7. -/
theorem mixed_unmap_effect_confined state command
    (hdispatch :
      let words := encodeMixedCommand command
      dispatch (encodeMixedState state)
        words.tag words.arg0 words.arg1 words.arg2 words.arg3 =
        encodeMixedReply .pageUnmapped) :
    state = .directMapped ∧ command = .acceptedSyscallUnmap ∧
      mixedReplyEffect .pageUnmapped = .page 2 7 := by
  cases state <;> cases command
  all_goals
    simp [encodeMixedCommand, encodeMixedState, encodeMixedReply, dispatch,
      mixedDispatchRaw, mixedReplyEffect] at hdispatch ⊢

/-- The accepted protection effect is available only on the canonical
full-state edge and is confined to kernel-derived address space 2/page 8. -/
theorem mixed_protect_effect_confined state command
    (hdispatch :
      let words := encodeMixedCommand command
      dispatch (encodeMixedState state)
        words.tag words.arg0 words.arg1 words.arg2 words.arg3 =
        encodeMixedReply .pageProtected) :
    state = .directMapped ∧ command = .acceptedProtect ∧
      mixedReplyEffect .pageProtected = .page 2 8 := by
  cases state <;> cases command
  all_goals
    simp [encodeMixedCommand, encodeMixedState, encodeMixedReply, dispatch,
      mixedDispatchRaw, mixedReplyEffect] at hdispatch ⊢

def mixedCanonicalCommands : List MixedCommandId :=
  [.offerTransfer, .acceptTransfer, .revokeTransferredCapability,
   .rejectStaleReusedHandle, .copyFreshCapability, .acceptedSyscallMap,
   .acceptedDirectMap, .rejectUnknownSyscall, .nonblockingSend,
   .nonblockingReceive, .blockingReceive, .blockingSend, .timerSwitch,
   .cleanupUserFault, .enterFatalKernelFault, .attemptPostFatalSchedule]

def mixedPrefix : MixedStateId → List MixedCommandId
  | .initial => []
  | .transferOffered => mixedCanonicalCommands.take 1
  | .transferAccepted => mixedCanonicalCommands.take 2
  | .delegatedSendAccepted =>
      mixedCanonicalCommands.take 2 ++ [.useDelegatedSend]
  | .transferredCapabilityRevoked => mixedCanonicalCommands.take 3
  | .staleHandleRejected => mixedCanonicalCommands.take 4
  | .freshCapabilityCopied => mixedCanonicalCommands.take 5
  | .syscallMapped => mixedCanonicalCommands.take 6
  | .directMapped => mixedCanonicalCommands.take 7
  | .unknownSyscallRejected => mixedCanonicalCommands.take 8
  | .nonblockingSent => mixedCanonicalCommands.take 9
  | .nonblockingReceived => mixedCanonicalCommands.take 10
  | .blockingReceiverBlocked => mixedCanonicalCommands.take 11
  | .blockingReceiverWoken => mixedCanonicalCommands.take 12
  | .timerSwitched => mixedCanonicalCommands.take 13
  | .userFaultCleaned => mixedCanonicalCommands.take 14
  | .fatalEntered => mixedCanonicalCommands.take 15
  | .postFatalRejected => mixedCanonicalCommands
  | .pageUnmapped =>
      mixedCanonicalCommands.take 7 ++ [.acceptedSyscallUnmap]
  | .pageProtected =>
      mixedCanonicalCommands.take 7 ++ [.acceptedProtect]

def mixedInitialState : Except DecodeError CompositeState :=
  match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
  | .ok plan => .ok (compositeDispatcherInitial plan)
  | .error _ => .error .reservedBits

def mixedMaterialize (id : MixedStateId) : Except DecodeError CompositeState := do
  let initial ← mixedInitialState
  pure (runAuthoritativeOperations initial
    ((mixedPrefix id).map mixedCommandOperation))

/-- Reconstruct the canonical invalidation step from the same complete
authoritative pre-state used by the composite dispatcher.  Actor and active
address space are kernel projections; only the page is the decoded syscall
argument. -/
def mixedUnmapStepAt (state : MixedStateId) (page : VirtualMapping.VirtualPage) :
    Except DecodeError StaleTranslation.Step := do
  let pre ← mixedMaterialize state
  pure (StaleTranslation.step pre.resumable.translations
    (.unmap pre.execution.core.context.currentSubject
      pre.execution.core.context.activeAddressSpace page))

/-- Reconstruct a protection reduction from the same complete authoritative
pre-state used by the generated composite edge.  Neither actor nor root is
present in the untrusted command words. -/
def mixedProtectStepAt (state : MixedStateId) (page : VirtualMapping.VirtualPage)
    (permissions : VirtualMapping.Permissions) :
    Except DecodeError StaleTranslation.Step := do
  let pre ← mixedMaterialize state
  pure (StaleTranslation.step pre.resumable.translations
    (.protect pre.execution.core.context.currentSubject
      pre.execution.core.context.activeAddressSpace page permissions))

structure CanonicalMixedState where
  id : MixedStateId
  state : CompositeState
  canonical : mixedMaterialize id = .ok state

def encodeMixedCompositeState (state : CanonicalMixedState) : UInt64 :=
  encodeMixedState state.id

theorem CanonicalMixedState.eq_of_id_eq
    (first second : CanonicalMixedState) (hid : first.id = second.id) :
    first = second := by
  cases first with
  | mk firstId firstState firstCanonical =>
      cases second with
      | mk secondId secondState secondCanonical =>
          dsimp at hid
          subst secondId
          have hstate : firstState = secondState :=
            Except.ok.inj (firstCanonical.symm.trans secondCanonical)
          subst secondState
          rfl

def decodeMixedCompositeState (word : UInt64) :
    Except DecodeError CanonicalMixedState :=
  match decodeMixedState word with
  | .error reason => .error reason
  | .ok id =>
      match hstate : mixedMaterialize id with
      | .ok state =>
          .ok ({ id, state, canonical := hstate } : CanonicalMixedState)
      | .error reason => .error reason

theorem decode_encode_mixed_composite_state (state : CanonicalMixedState) :
    decodeMixedCompositeState (encodeMixedCompositeState state) = .ok state := by
  unfold decodeMixedCompositeState encodeMixedCompositeState
  rw [decode_encode_mixed_state]
  change (match hstate : mixedMaterialize state.id with
    | .ok decoded =>
        Except.ok (ε := DecodeError)
          ({ id := state.id, state := decoded, canonical := hstate } :
            CanonicalMixedState)
    | .error reason =>
        Except.error (α := CanonicalMixedState) reason) = .ok state
  split
  next decoded hmaterialize =>
    have hdecoded : decoded = state.state :=
      Except.ok.inj (hmaterialize.symm.trans state.canonical)
    subst decoded
    congr 1
  next reason hmaterialize =>
    have himpossible :
        Except.error reason = Except.ok state.state :=
      hmaterialize.symm.trans state.canonical
    contradiction

theorem mixed_composite_state_encoding_injective
    (first second : CanonicalMixedState)
    (hequal : encodeMixedCompositeState first = encodeMixedCompositeState second) :
    first = second := by
  apply CanonicalMixedState.eq_of_id_eq
  apply mixed_state_encoding_injective
  exact hequal

/-- Every accepted scalar mixed edge decodes to an independently specified
reply meaning and the exact next authoritative state.  Unlike
`mixedLogicalStep`, this bridge starts from the exported scalar `dispatch`
result and relates both decoded fields back to `authoritativeGate`. -/
theorem mixed_dispatch_decodes_authoritative_edge
    (state : MixedStateId) (command : MixedCommandId)
    (next : MixedStateId) (reply : MixedReplyId)
    (hnext : mixedNextState state command = some next)
    (hreply : mixedReplyId state command = some reply) :
    let words := encodeMixedCommand command
    ∃ pre post,
      mixedMaterialize state = .ok pre ∧
      mixedMaterialize next = .ok post ∧
      decodeMixedReply
          (dispatch (encodeMixedState state)
            words.tag words.arg0 words.arg1 words.arg2 words.arg3) =
        .ok reply ∧
      authoritativeGate pre (mixedCommandOperation command) =
        { state := post, result := mixedReplyResult reply } := by
  cases state <;> cases command <;> simp [mixedNextState] at hnext
  all_goals subst next
  all_goals simp [mixedReplyId] at hreply
  all_goals subst reply
  all_goals refine ⟨_, _, rfl, rfl, ?_, ?_⟩
  all_goals rfl

/-- One accepted corpus edge carries only the canonical scalar selectors and
their table membership proofs.  Its semantic refinement is supplied by
`mixed_dispatch_decodes_authoritative_edge`, not stored in this record. -/
structure CanonicalMixedEdge where
  state : MixedStateId
  command : MixedCommandId
  next : MixedStateId
  reply : MixedReplyId
  next_exact : mixedNextState state command = some next
  reply_exact : mixedReplyId state command = some reply

def mixedCanonicalEdges : List CanonicalMixedEdge :=
  [{ state := .initial, command := .offerTransfer,
     next := .transferOffered, reply := .transferOffered,
     next_exact := rfl, reply_exact := rfl },
   { state := .transferOffered,
     command := .rejectSealedHandleBeforeReceipt,
     next := .transferOffered, reply := .sealedHandleRejected,
     next_exact := rfl, reply_exact := rfl },
   { state := .transferOffered, command := .acceptTransfer,
     next := .transferAccepted, reply := .transferAccepted,
     next_exact := rfl, reply_exact := rfl },
   { state := .transferAccepted, command := .useDelegatedSend,
     next := .delegatedSendAccepted, reply := .delegatedSendAccepted,
     next_exact := rfl, reply_exact := rfl },
   { state := .delegatedSendAccepted, command := .rejectDelegatedReceive,
     next := .delegatedSendAccepted, reply := .delegatedReceiveRejected,
     next_exact := rfl, reply_exact := rfl },
   { state := .transferAccepted, command := .revokeTransferredCapability,
     next := .transferredCapabilityRevoked,
     reply := .transferredCapabilityRevoked,
     next_exact := rfl, reply_exact := rfl },
   { state := .transferredCapabilityRevoked,
     command := .rejectStaleReusedHandle,
     next := .staleHandleRejected, reply := .staleHandleRejected,
     next_exact := rfl, reply_exact := rfl },
   { state := .staleHandleRejected, command := .copyFreshCapability,
     next := .freshCapabilityCopied, reply := .freshCapabilityCopied,
     next_exact := rfl, reply_exact := rfl },
   { state := .freshCapabilityCopied, command := .acceptedSyscallMap,
     next := .syscallMapped, reply := .syscallMapped,
     next_exact := rfl, reply_exact := rfl },
   { state := .syscallMapped, command := .acceptedDirectMap,
     next := .directMapped, reply := .directMapped,
     next_exact := rfl, reply_exact := rfl },
   { state := .directMapped, command := .rejectUnknownSyscall,
     next := .unknownSyscallRejected, reply := .unknownSyscallRejected,
     next_exact := rfl, reply_exact := rfl },
   { state := .unknownSyscallRejected, command := .nonblockingSend,
     next := .nonblockingSent, reply := .nonblockingSent,
     next_exact := rfl, reply_exact := rfl },
   { state := .nonblockingSent, command := .nonblockingReceive,
     next := .nonblockingReceived, reply := .nonblockingReceived,
     next_exact := rfl, reply_exact := rfl },
   { state := .nonblockingReceived, command := .blockingReceive,
     next := .blockingReceiverBlocked, reply := .blockingReceiverBlocked,
     next_exact := rfl, reply_exact := rfl },
   { state := .blockingReceiverBlocked, command := .blockingSend,
     next := .blockingReceiverWoken, reply := .blockingReceiverWoken,
     next_exact := rfl, reply_exact := rfl },
   { state := .blockingReceiverWoken, command := .timerSwitch,
     next := .timerSwitched, reply := .timerSwitched,
     next_exact := rfl, reply_exact := rfl },
   { state := .timerSwitched, command := .cleanupUserFault,
     next := .userFaultCleaned, reply := .userFaultCleaned,
     next_exact := rfl, reply_exact := rfl },
   { state := .userFaultCleaned, command := .enterFatalKernelFault,
     next := .fatalEntered, reply := .fatalEntered,
     next_exact := rfl, reply_exact := rfl },
   { state := .fatalEntered, command := .attemptPostFatalSchedule,
     next := .postFatalRejected, reply := .postFatalRejected,
     next_exact := rfl, reply_exact := rfl },
   { state := .directMapped, command := .acceptedSyscallUnmap,
     next := .pageUnmapped, reply := .pageUnmapped,
     next_exact := rfl, reply_exact := rfl },
   { state := .directMapped, command := .rejectUnmappedPageUnmap,
     next := .directMapped, reply := .unmappedPageRejected,
     next_exact := rfl, reply_exact := rfl },
   { state := .directMapped, command := .acceptedProtect,
     next := .pageProtected, reply := .pageProtected,
     next_exact := rfl, reply_exact := rfl },
   { state := .pageProtected, command := .rejectProtectAmplification,
     next := .pageProtected, reply := .protectAmplificationRejected,
     next_exact := rfl, reply_exact := rfl }]

def CanonicalMixedEdge.Refines (edge : CanonicalMixedEdge) : Prop :=
  let words := encodeMixedCommand edge.command
  ∃ pre post,
    mixedMaterialize edge.state = .ok pre ∧
    mixedMaterialize edge.next = .ok post ∧
    decodeMixedReply
        (dispatch (encodeMixedState edge.state)
          words.tag words.arg0 words.arg1 words.arg2 words.arg3) =
      .ok edge.reply ∧
    authoritativeGate pre (mixedCommandOperation edge.command) =
      { state := post, result := mixedReplyResult edge.reply }

theorem canonicalMixedEdge_refines (edge : CanonicalMixedEdge) :
    edge.Refines := by
  exact mixed_dispatch_decodes_authoritative_edge
    edge.state edge.command edge.next edge.reply
    edge.next_exact edge.reply_exact

/-- The hosted 23-edge corpus inherits its state/result meaning solely from
the scalar-to-authoritative bridge above. -/
theorem mixedCanonicalEdges_refine :
    ∀ edge ∈ mixedCanonicalEdges, edge.Refines := by
  intro edge _hmembership
  exact canonicalMixedEdge_refines edge

theorem decodeMixedCompositeState_sound word state
    (_hdecode : decodeMixedCompositeState word = .ok state) :
    mixedMaterialize state.id = .ok state.state := by
  exact state.canonical

structure MixedLogicalStep where
  pre : CompositeState
  operation : AuthoritativeOperation
  outcome : AuthoritativeGateOutcome

def mixedLogicalStep (state : MixedStateId) (command : MixedCommandId) :
    Except DecodeError MixedLogicalStep := do
  let pre ← mixedMaterialize state
  match mixedNextState state command with
  | none => .error .invalidSequence
  | some _ =>
      .ok { pre
            operation := mixedCommandOperation command
            outcome := authoritativeGate pre (mixedCommandOperation command) }

theorem mixedLogicalStep_refines_authoritativeGate state command step
    (hstep : mixedLogicalStep state command = .ok step) :
    step.outcome = authoritativeGate step.pre step.operation := by
  unfold mixedLogicalStep at hstep
  cases hmaterialize : mixedMaterialize state with
  | error reason =>
      rw [hmaterialize] at hstep
      contradiction
  | ok pre =>
      rw [hmaterialize] at hstep
      cases hnext : mixedNextState state command with
      | none =>
          rw [hnext] at hstep
          contradiction
      | some next =>
          rw [hnext] at hstep
          injection hstep with heq
          subst step
          rfl

theorem mixed_state_continuity state command next
    (hnext : mixedNextState state command = some next) :
    encodeMixedState next = encodeMixedState state ∨
      encodeMixedState next = encodeMixedState state + 0x100 ∨
      (state = .transferAccepted ∧ command = .useDelegatedSend ∧
        next = .delegatedSendAccepted) ∨
      (state = .directMapped ∧ command = .acceptedSyscallUnmap ∧
        next = .pageUnmapped) ∨
      (state = .directMapped ∧ command = .acceptedProtect ∧
        next = .pageProtected) := by
  cases state <;> cases command <;> simp [mixedNextState] at hnext
  all_goals subst next <;> simp [encodeMixedState]

/-- Finite-list refinement for the complete accepted mixed corpus.  Every
intermediate state used by the hosted harness is the corresponding prefix of
this exact authoritative execution. -/
theorem mixedCanonicalCommands_refine initial
    (hinitial : mixedInitialState = .ok initial) :
    mixedMaterialize .postFatalRejected =
      .ok (runAuthoritativeOperations initial
        (mixedCanonicalCommands.map mixedCommandOperation)) := by
  unfold mixedMaterialize
  rw [hinitial]
  rfl

/-- Exact typed-result coverage prevents the scalar ABI from labeling a
rejection as an accepted transition (or vice versa). -/
def authoritativeResultCompleted : AuthoritativeGateResult → Bool
  | .completed _ => true
  | .rejectedBusy | .rejectedHalted _ => false

def mixedOutcomeAt (state : MixedStateId) (command : MixedCommandId) :
    Except DecodeError AuthoritativeGateOutcome := do
  let pre ← mixedMaterialize state
  pure (authoritativeGate pre (mixedCommandOperation command))

theorem mixedCanonical_typed_results :
    (mixedOutcomeAt .initial .offerTransfer).toOption.map (·.result) =
        some (.completed (.ordinary (.transferOffer .accepted))) ∧
    (mixedOutcomeAt .transferAccepted .revokeTransferredCapability).toOption.map
        (·.result) = some (.completed (.ordinary (.capability .accepted))) ∧
    (mixedOutcomeAt .freshCapabilityCopied .acceptedSyscallMap).toOption.map
        (·.result) = some (.completed (.ordinary (.syscall .accepted))) ∧
    (mixedOutcomeAt .syscallMapped .acceptedDirectMap).toOption.map
        (·.result) = some (.completed (.ordinary (.map .accepted))) ∧
    (mixedOutcomeAt .unknownSyscallRejected .nonblockingSend).toOption.map
        (·.result) = some (.completed (.ordinary (.ipc (.syscall .sent)))) ∧
    (mixedOutcomeAt .nonblockingReceived .blockingReceive).toOption.map
        (·.result) = some (.completed (.blocking (.receive .blocked))) ∧
    (mixedOutcomeAt .blockingReceiverWoken .timerSwitch).toOption.map
        (fun outcome => authoritativeResultCompleted outcome.result) = some true ∧
    (mixedOutcomeAt .blockingReceiverWoken .timerSwitch).toOption.map
        (·.state.scheduler.lifecycle.current) = some (some 2) ∧
    (mixedOutcomeAt .timerSwitched .cleanupUserFault).toOption.map
        (·.result) = some (.completed (.ordinary (.interrupt (.contained 2)))) ∧
    (mixedOutcomeAt .timerSwitched .cleanupUserFault).toOption.map
        (fun outcome => outcome.state.lifecycle.capabilities.subjects 2) = some false ∧
    (mixedOutcomeAt .fatalEntered .attemptPostFatalSchedule).toOption.map
        (fun outcome => authoritativeResultCompleted outcome.result) = some false := by
  native_decide

/-- The offered descendant is present only in the authoritative sealed store.
Its future generation-bound handle cannot resolve through ordinary IPC until
the exact receipt transition installs it; that receipt then returns and binds
the same identity in subject 2's reviewed destination slot. -/
theorem mixed_pre_receipt_sealed_handle_rejection_inert :
    (mixedOutcomeAt .transferOffered
        .rejectSealedHandleBeforeReceipt).toOption.map (·.state) =
      (mixedMaterialize .transferOffered).toOption := by
  rfl

theorem mixed_pre_receipt_sealed_authority_denied :
    (mixedOutcomeAt .transferOffered
        .rejectSealedHandleBeforeReceipt).toOption.map (·.result) =
      some (mixedReplyResult .sealedHandleRejected) ∧
    (mixedMaterialize .transferOffered).toOption.map
        (fun state => (state.transfers.pending 10).isSome) = some true ∧
    (mixedMaterialize .transferOffered).toOption.map
        (fun state => state.transfers.capabilities.slots 2 3) = some none ∧
    (mixedOutcomeAt .transferOffered .acceptTransfer).toOption.map (·.result) =
      some (mixedReplyResult .transferAccepted) ∧
    (mixedOutcomeAt .transferOffered .acceptTransfer).toOption.map
        (fun outcome =>
          (outcome.state.transfers.capabilities.slots 2 3).map
            (fun capability => capability.identity)) = some (some 6) := by
  native_decide

/-- The generation-bound handle returned by receipt names the installed
send-only descendant.  Subject 2 can use that delegated send right, while a
receive through the same handle is rejected for missing authority and leaves
the complete authoritative state unchanged. -/
theorem mixed_delegated_send_only_authority_enforced :
    (mixedOutcomeAt .transferOffered .acceptTransfer).toOption.map (·.result) =
      some (mixedReplyResult .transferAccepted) ∧
    (mixedMaterialize .transferAccepted).toOption.map
        (fun state =>
          (state.capabilities.slots 2 3).map
            (fun capability =>
              (capability.identity, capability.rights.send,
                capability.rights.receive))) =
      some (some (6, true, false)) ∧
    (mixedOutcomeAt .transferAccepted .useDelegatedSend).toOption.map
        (·.result) = some (mixedReplyResult .delegatedSendAccepted) ∧
    (mixedOutcomeAt .delegatedSendAccepted
        .rejectDelegatedReceive).toOption.map (·.result) =
      some (mixedReplyResult .delegatedReceiveRejected) := by
  native_decide

theorem mixed_delegated_excess_right_rejection_inert :
    (mixedOutcomeAt .delegatedSendAccepted
        .rejectDelegatedReceive).toOption.map (·.state) =
      (mixedMaterialize .delegatedSendAccepted).toOption := by
  rfl

/-- Publication-order meaning for the accepted slice: the authoritative gate
publishes exactly the state produced by the canonical TLB unmap step, and the
typed reply exposes the required page effect only with that successor.  Thus
the modeled PTE removal/cache invalidation precedes publication of the reply;
the x86 instruction remains a trusted implementation boundary. -/
theorem mixed_accepted_unmap_publication_order :
    (mixedUnmapStepAt .directMapped 7).toOption.map
        (fun step => (step.accepted, step.effect)) =
      some (true, .page 2 7) ∧
    (mixedUnmapStepAt .directMapped 7).toOption.map (·.state) =
      (mixedOutcomeAt .directMapped .acceptedSyscallUnmap).toOption.map
        (·.state.resumable.translations) ∧
    (mixedOutcomeAt .directMapped .acceptedSyscallUnmap).toOption.map
        (fun outcome => outcome.state.virtualMemory.mappings 2 7) =
      some none := by
  constructor
  · native_decide
  constructor
  · rfl
  · native_decide

/-- A logical unmap rejection is a complete-state stutter and requests no
machine mutation.  This is the canonical rejection-preservation witness paired
with the accepted effect edge above. -/
theorem mixed_rejected_unmap_inert :
    (mixedUnmapStepAt .directMapped 9).toOption.map
        (fun step => (step.accepted, step.effect)) =
      some (false, .none) ∧
    (mixedOutcomeAt .directMapped .rejectUnmappedPageUnmap).toOption.map
        (·.state) =
      (mixedMaterialize .directMapped).toOption := by
  constructor
  · native_decide
  · rfl

/-- The canonical full-state protection edge is an accepted writable-to-read
only reduction.  Its exact `.page 2 8` effect suffices for target-entry
absence, and the same `TLB.State` is installed in the authoritative composite
successor. -/
theorem mixed_accepted_protect_publication_order :
    (mixedProtectStepAt .directMapped 8 { read := true }).toOption.map
        (fun step => (step.accepted, step.effect)) =
      some (true, .page 2 8) ∧
    (mixedProtectStepAt .directMapped 8 { read := true }).toOption.map (·.state) =
      (mixedOutcomeAt .directMapped .acceptedProtect).toOption.map
        (·.state.resumable.translations) ∧
    (mixedOutcomeAt .directMapped .acceptedProtect).toOption.map
        (fun outcome => outcome.state.virtualMemory.mappings 2 8) =
      some (some { object := 20, permissions := { read := true } }) ∧
    (mixedOutcomeAt .directMapped .acceptedProtect).toOption.map
        (fun outcome => TLB.lookup outcome.state.resumable.translations.entries
          { addressSpace := 2, page := 8 } StaleTranslation.ctx) =
      some none := by
  constructor
  · native_decide
  constructor
  · rfl
  constructor <;> native_decide

/-- From any globally well-formed materialized pre-state, the exact canonical
protection edge preserves the complete folded authoritative invariant. -/
theorem mixed_accepted_protect_preserves_global_invariant pre
    (_hmaterialize : mixedMaterialize .directMapped = .ok pre)
    (hstate : AuthoritativeRuntimeWellFormed pre) :
    AuthoritativeRuntimeWellFormed
      (authoritativeGate pre
        (mixedCommandOperation .acceptedProtect)).state := by
  simpa [mixedCommandOperation] using
    authoritativeGate_protect_preserves_authoritativeRuntimeWellFormed
      pre 8 { read := true } hstate

/-- Attempted write amplification after the canonical reduction is a typed,
effect-free full-composite stutter. -/
theorem mixed_rejected_protect_amplification_inert :
    (mixedProtectStepAt .pageProtected 8 { read := true, write := true }).toOption.map
        (fun step => (step.accepted, step.effect)) =
      some (false, .none) ∧
    (mixedOutcomeAt .pageProtected .rejectProtectAmplification).toOption.map
        (·.state) =
      (mixedMaterialize .pageProtected).toOption := by
  constructor
  · native_decide
  · rfl

/-! ## In-flight revocation before receipt

The mixed corpus above revokes a delegated generation only after receipt.  The
family below is the #175 trace: subject 1 holds a delegated revoke-only
authority on endpoint 10 (`FailStop.inFlightRevocationInitial`), seals a
send-only child of its own endpoint capability, and then revokes that whole
lineage before subject 2 can receive.  Every successor is exact
`authoritativeGate` replay: the accepted revocation cancels the sealed child
together with its envelope, subject 2's receipt is the typed empty rejection
with no handle, the reused destination slot receives a strictly newer
generation, and the canceled generation-bound handle is denied.  Probes at
each state cover missing revoke authority, a wrong lineage root, repeated
revocation, and an offer through the revoked capability. -/

inductive InFlightRevocationStateId where
  | subjectOneArmed
  | childOffered
  | lineageRevoked
  | subjectTwoRestored
  | destinationReplaced
  | replacementUsed
  deriving DecidableEq, Repr

def encodeInFlightRevocationState : InFlightRevocationStateId → UInt64
  | .subjectOneArmed => 0x6001
  | .childOffered => 0x6101
  | .lineageRevoked => 0x6201
  | .subjectTwoRestored => 0x6301
  | .destinationReplaced => 0x6401
  | .replacementUsed => 0x6501

def decodeInFlightRevocationState (word : UInt64) :
    Except DecodeError InFlightRevocationStateId :=
  if word = 0x6001 then .ok .subjectOneArmed
  else if word = 0x6101 then .ok .childOffered
  else if word = 0x6201 then .ok .lineageRevoked
  else if word = 0x6301 then .ok .subjectTwoRestored
  else if word = 0x6401 then .ok .destinationReplaced
  else if word = 0x6501 then .ok .replacementUsed
  else if word % 256 != abiVersion then .error .wrongVersion
  else if 0x6601 ≤ word then .error .reservedBits
  else .error .unknownState

theorem decode_encode_inFlightRevocation_state state :
    decodeInFlightRevocationState (encodeInFlightRevocationState state) = .ok state := by
  cases state <;> rfl

theorem inFlightRevocation_state_encoding_injective first second
    (hequal : encodeInFlightRevocationState first = encodeInFlightRevocationState second) :
    first = second := by
  cases first <;> cases second <;> simp_all [encodeInFlightRevocationState]

inductive InFlightRevocationCommandId where
  | offerChild
  | rejectRevocationWithoutAuthority
  | rejectWrongLineageRoot
  | revokeLineage
  | rejectRepeatedRevocation
  | rejectOfferAfterRevocation
  | switchToSubjectTwo
  | rejectCanceledReceipt
  | replaceDestinationSlot
  | rejectCanceledHandleReplay
  | useReplacementHandle
  deriving DecidableEq, Repr

def encodeInFlightRevocationCommand : InFlightRevocationCommandId → CommandWords
  | .offerChild =>
      { tag := 0x2001, arg0 := 0x20001, arg1 := 0x20001,
        arg2 := 0xCAFE, arg3 := 0xBEEF }
  | .rejectRevocationWithoutAuthority =>
      { tag := 0x5001, arg0 := 1, arg1 := 1, arg2 := 1, arg3 := 0 }
  | .rejectWrongLineageRoot =>
      { tag := 0x5101, arg0 := 2, arg1 := 1, arg2 := 0, arg3 := 0 }
  | .revokeLineage =>
      { tag := 0x5201, arg0 := 2, arg1 := 1, arg2 := 1, arg3 := 0 }
  | .rejectRepeatedRevocation =>
      { tag := 0x5301, arg0 := 2, arg1 := 1, arg2 := 1, arg3 := 0 }
  | .rejectOfferAfterRevocation =>
      { tag := 0x5401, arg0 := 0x20001, arg1 := 0x20001,
        arg2 := 0xCAFE, arg3 := 0xBEEF }
  | .switchToSubjectTwo =>
      { tag := 0x5501, arg0 := 0, arg1 := 0, arg2 := 0, arg3 := 0 }
  | .rejectCanceledReceipt =>
      { tag := 0x2101, arg0 := 0x30000, arg1 := 3, arg2 := 0, arg3 := 0 }
  | .replaceDestinationSlot =>
      { tag := 0x2401, arg0 := 0, arg1 := 2, arg2 := 3, arg3 := 4 }
  | .rejectCanceledHandleReplay =>
      { tag := 0x5601, arg0 := 0x70003, arg1 := 0xAAAA,
        arg2 := 0xBBBB, arg3 := 0 }
  | .useReplacementHandle =>
      { tag := 0x5701, arg0 := 0x80003, arg1 := 0x1111,
        arg2 := 0x2222, arg3 := 0 }

def decodeInFlightRevocationCommand (words : CommandWords) :
    Except DecodeError InFlightRevocationCommandId :=
  if words = encodeInFlightRevocationCommand .offerChild then .ok .offerChild
  else if words = encodeInFlightRevocationCommand .rejectRevocationWithoutAuthority then
    .ok .rejectRevocationWithoutAuthority
  else if words = encodeInFlightRevocationCommand .rejectWrongLineageRoot then
    .ok .rejectWrongLineageRoot
  else if words = encodeInFlightRevocationCommand .revokeLineage then .ok .revokeLineage
  else if words = encodeInFlightRevocationCommand .rejectRepeatedRevocation then
    .ok .rejectRepeatedRevocation
  else if words = encodeInFlightRevocationCommand .rejectOfferAfterRevocation then
    .ok .rejectOfferAfterRevocation
  else if words = encodeInFlightRevocationCommand .switchToSubjectTwo then
    .ok .switchToSubjectTwo
  else if words = encodeInFlightRevocationCommand .rejectCanceledReceipt then
    .ok .rejectCanceledReceipt
  else if words = encodeInFlightRevocationCommand .replaceDestinationSlot then
    .ok .replaceDestinationSlot
  else if words = encodeInFlightRevocationCommand .rejectCanceledHandleReplay then
    .ok .rejectCanceledHandleReplay
  else if words = encodeInFlightRevocationCommand .useReplacementHandle then
    .ok .useReplacementHandle
  else if words.tag % 256 != abiVersion then .error .wrongVersion
  else if 0x5801 ≤ words.tag then .error .reservedBits
  else .error .noncanonicalArguments

theorem decode_encode_inFlightRevocation_command command :
    decodeInFlightRevocationCommand (encodeInFlightRevocationCommand command) =
      .ok command := by
  cases command <;> rfl

theorem inFlightRevocation_command_encoding_injective first second
    (hequal : encodeInFlightRevocationCommand first =
      encodeInFlightRevocationCommand second) :
    first = second := by
  cases first <;> cases second <;> simp_all [encodeInFlightRevocationCommand]

/-- Every command is a public raw-slot or generation-bound word operation.  The
revoking actor, the receiving subject, the lineage root's identity, and the
replacement generation all come from the reconstructed composite state. -/
def inFlightRevocationOperation : InFlightRevocationCommandId → AuthoritativeOperation
  | .offerChild =>
      .ordinary (.transferOffer 0x20001 0x20001 .endpoint
        { word0 := 0xCAFE, word1 := 0xBEEF } { send := true })
  | .rejectRevocationWithoutAuthority => .ordinary (.capabilityRevokeSubtree 1 1 1)
  | .rejectWrongLineageRoot => .ordinary (.capabilityRevokeSubtree 2 1 0)
  | .revokeLineage => .ordinary (.capabilityRevokeSubtree 2 1 1)
  | .rejectRepeatedRevocation => .ordinary (.capabilityRevokeSubtree 2 1 1)
  | .rejectOfferAfterRevocation =>
      .ordinary (.transferOffer 0x20001 0x20001 .endpoint
        { word0 := 0xCAFE, word1 := 0xBEEF } { send := true })
  | .switchToSubjectTwo =>
      .ordinary (.resumePreempt compositeDispatcherTimerFrame
        compositeDispatcherTimerRegisters)
  | .rejectCanceledReceipt => .ordinary (.transferAccept 0x30000 3)
  | .replaceDestinationSlot => .ordinary (.capabilityCopy 0 2 3 { send := true })
  | .rejectCanceledHandleReplay => .ordinary (.ipc (.send 0x70003 0xAAAA 0xBBBB))
  | .useReplacementHandle => .ordinary (.ipc (.send 0x80003 0x1111 0x2222))

def inFlightRevocationNextState :
    InFlightRevocationStateId → InFlightRevocationCommandId →
      Option InFlightRevocationStateId
  | .subjectOneArmed, .offerChild => some .childOffered
  | .childOffered, .rejectRevocationWithoutAuthority => some .childOffered
  | .childOffered, .rejectWrongLineageRoot => some .childOffered
  | .childOffered, .revokeLineage => some .lineageRevoked
  | .lineageRevoked, .rejectRepeatedRevocation => some .lineageRevoked
  | .lineageRevoked, .rejectOfferAfterRevocation => some .lineageRevoked
  | .lineageRevoked, .switchToSubjectTwo => some .subjectTwoRestored
  | .subjectTwoRestored, .rejectCanceledReceipt => some .subjectTwoRestored
  | .subjectTwoRestored, .replaceDestinationSlot => some .destinationReplaced
  | .destinationReplaced, .rejectCanceledHandleReplay => some .destinationReplaced
  | .destinationReplaced, .useReplacementHandle => some .replacementUsed
  | _, _ => none

def inFlightRevocationExpectedReply :
    InFlightRevocationStateId → InFlightRevocationCommandId → Option UInt64
  | .subjectOneArmed, .offerChild => some 0x206101
  | .childOffered, .rejectRevocationWithoutAuthority => some 0x506101
  | .childOffered, .rejectWrongLineageRoot => some 0x516101
  | .childOffered, .revokeLineage => some 0x526201
  | .lineageRevoked, .rejectRepeatedRevocation => some 0x536201
  | .lineageRevoked, .rejectOfferAfterRevocation => some 0x546201
  | .lineageRevoked, .switchToSubjectTwo => some 0x556301
  | .subjectTwoRestored, .rejectCanceledReceipt => some 0x216301
  | .subjectTwoRestored, .replaceDestinationSlot => some 0x246401
  | .destinationReplaced, .rejectCanceledHandleReplay => some 0x566401
  | .destinationReplaced, .useReplacementHandle => some 0x576501
  | _, _ => none

inductive InFlightRevocationReplyId where
  | childOffered
  | revocationWithoutAuthorityRejected
  | wrongLineageRootRejected
  | lineageRevoked
  | repeatedRevocationRejected
  | offerAfterRevocationRejected
  | subjectTwoRestored
  | canceledReceiptRejected
  | destinationReplaced
  | canceledHandleReplayRejected
  | replacementUsed
  deriving DecidableEq, Repr

def encodeInFlightRevocationReply : InFlightRevocationReplyId → UInt64
  | .childOffered => 0x206101
  | .revocationWithoutAuthorityRejected => 0x506101
  | .wrongLineageRootRejected => 0x516101
  | .lineageRevoked => 0x526201
  | .repeatedRevocationRejected => 0x536201
  | .offerAfterRevocationRejected => 0x546201
  | .subjectTwoRestored => 0x556301
  | .canceledReceiptRejected => 0x216301
  | .destinationReplaced => 0x246401
  | .canceledHandleReplayRejected => 0x566401
  | .replacementUsed => 0x576501

def decodeInFlightRevocationReply (word : UInt64) :
    Except DecodeError InFlightRevocationReplyId :=
  if word = 0x206101 then .ok .childOffered
  else if word = 0x506101 then .ok .revocationWithoutAuthorityRejected
  else if word = 0x516101 then .ok .wrongLineageRootRejected
  else if word = 0x526201 then .ok .lineageRevoked
  else if word = 0x536201 then .ok .repeatedRevocationRejected
  else if word = 0x546201 then .ok .offerAfterRevocationRejected
  else if word = 0x556301 then .ok .subjectTwoRestored
  else if word = 0x216301 then .ok .canceledReceiptRejected
  else if word = 0x246401 then .ok .destinationReplaced
  else if word = 0x566401 then .ok .canceledHandleReplayRejected
  else if word = 0x576501 then .ok .replacementUsed
  else if word % 256 != abiVersion then .error .wrongVersion
  else if 0x580001 ≤ word then .error .reservedBits
  else .error .unknownCommand

theorem decode_encode_inFlightRevocation_reply reply :
    decodeInFlightRevocationReply (encodeInFlightRevocationReply reply) = .ok reply := by
  cases reply <;> rfl

theorem inFlightRevocation_reply_encoding_injective first second
    (hequal : encodeInFlightRevocationReply first = encodeInFlightRevocationReply second) :
    first = second := by
  cases first <;> cases second <;> simp_all [encodeInFlightRevocationReply]

def inFlightRevocationReplyId :
    InFlightRevocationStateId → InFlightRevocationCommandId →
      Option InFlightRevocationReplyId
  | .subjectOneArmed, .offerChild => some .childOffered
  | .childOffered, .rejectRevocationWithoutAuthority =>
      some .revocationWithoutAuthorityRejected
  | .childOffered, .rejectWrongLineageRoot => some .wrongLineageRootRejected
  | .childOffered, .revokeLineage => some .lineageRevoked
  | .lineageRevoked, .rejectRepeatedRevocation => some .repeatedRevocationRejected
  | .lineageRevoked, .rejectOfferAfterRevocation => some .offerAfterRevocationRejected
  | .lineageRevoked, .switchToSubjectTwo => some .subjectTwoRestored
  | .subjectTwoRestored, .rejectCanceledReceipt => some .canceledReceiptRejected
  | .subjectTwoRestored, .replaceDestinationSlot => some .destinationReplaced
  | .destinationReplaced, .rejectCanceledHandleReplay =>
      some .canceledHandleReplayRejected
  | .destinationReplaced, .useReplacementHandle => some .replacementUsed
  | _, _ => none

/-- The full typed meaning of each reply selector, independent of `dispatch`
and `authoritativeGate`.  The canceled receipt is the typed empty rejection
with no delivered word; no reply in this family publishes a handle. -/
def inFlightRevocationReplyResult : InFlightRevocationReplyId → AuthoritativeGateResult
  | .childOffered => .completed (.ordinary (.transferOffer .accepted))
  | .revocationWithoutAuthorityRejected =>
      .completed (.ordinary (.capability (.rejected .missingRevoke)))
  | .wrongLineageRootRejected =>
      .completed (.ordinary (.capability (.rejected .objectMismatch)))
  | .lineageRevoked => .completed (.ordinary (.capability .accepted))
  | .repeatedRevocationRejected =>
      .completed (.ordinary (.capability (.rejected .staleSlot)))
  | .offerAfterRevocationRejected =>
      .completed (.ordinary (.transferOffer (.rejected .staleEndpoint)))
  | .subjectTwoRestored =>
      .completed (.ordinary (.resume
        (some
          { owner := 2, addressSpace := 2
            frame := compositeDispatcherTimerFrame
            registers := compositeDispatcherBlockingRegisters
            kind := .suspended })
        none))
  | .canceledReceiptRejected =>
      .completed (.ordinary (.transferAccept (.rejected .empty) none))
  | .destinationReplaced => .completed (.ordinary (.capability .accepted))
  | .canceledHandleReplayRejected =>
      .completed (.ordinary (.ipc (.syscall
        (.sendHandleRejected (.denied .staleHandle)))))
  | .replacementUsed => .completed (.ordinary (.ipc (.syscall .sent)))

theorem inFlightRevocationExpectedReply_uses_canonical_codec state command :
    inFlightRevocationExpectedReply state command =
      (inFlightRevocationReplyId state command).map encodeInFlightRevocationReply := by
  cases state <;> cases command <;> rfl

theorem inFlightRevocation_dispatch_canonical state command :
    let words := encodeInFlightRevocationCommand command
    dispatch (encodeInFlightRevocationState state)
      words.tag words.arg0 words.arg1 words.arg2 words.arg3 =
      (inFlightRevocationExpectedReply state command).getD (errorWord .invalidSequence) := by
  cases state <;> cases command <;> native_decide

def inFlightRevocationCanonicalCommands : List InFlightRevocationCommandId :=
  [.offerChild, .revokeLineage, .switchToSubjectTwo, .replaceDestinationSlot,
   .useReplacementHandle]

def inFlightRevocationPrefix :
    InFlightRevocationStateId → List InFlightRevocationCommandId
  | .subjectOneArmed => []
  | .childOffered => inFlightRevocationCanonicalCommands.take 1
  | .lineageRevoked => inFlightRevocationCanonicalCommands.take 2
  | .subjectTwoRestored => inFlightRevocationCanonicalCommands.take 3
  | .destinationReplaced => inFlightRevocationCanonicalCommands.take 4
  | .replacementUsed => inFlightRevocationCanonicalCommands

def inFlightRevocationInitialState : Except DecodeError CompositeState :=
  match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
  | .ok plan => .ok (inFlightRevocationInitial plan)
  | .error _ => .error .reservedBits

/-- Materialization is exact authoritative replay from the kernel-owned seed. -/
def inFlightRevocationMaterialize (id : InFlightRevocationStateId) :
    Except DecodeError CompositeState := do
  let initial ← inFlightRevocationInitialState
  pure (runAuthoritativeOperations initial
    ((inFlightRevocationPrefix id).map inFlightRevocationOperation))

/-- Every accepted scalar edge decodes to an independently specified reply
meaning and the exact next authoritative state. -/
theorem inFlightRevocation_dispatch_decodes_authoritative_edge
    (state : InFlightRevocationStateId) (command : InFlightRevocationCommandId)
    (next : InFlightRevocationStateId) (reply : InFlightRevocationReplyId)
    (hnext : inFlightRevocationNextState state command = some next)
    (hreply : inFlightRevocationReplyId state command = some reply) :
    let words := encodeInFlightRevocationCommand command
    ∃ pre post,
      inFlightRevocationMaterialize state = .ok pre ∧
      inFlightRevocationMaterialize next = .ok post ∧
      decodeInFlightRevocationReply
          (dispatch (encodeInFlightRevocationState state)
            words.tag words.arg0 words.arg1 words.arg2 words.arg3) =
        .ok reply ∧
      authoritativeGate pre (inFlightRevocationOperation command) =
        { state := post, result := inFlightRevocationReplyResult reply } := by
  cases state <;> cases command <;> simp [inFlightRevocationNextState] at hnext
  all_goals subst next
  all_goals simp [inFlightRevocationReplyId] at hreply
  all_goals subst reply
  all_goals refine ⟨_, _, rfl, rfl, ?_, ?_⟩
  all_goals rfl

structure CanonicalInFlightRevocationEdge where
  state : InFlightRevocationStateId
  command : InFlightRevocationCommandId
  next : InFlightRevocationStateId
  reply : InFlightRevocationReplyId
  next_exact : inFlightRevocationNextState state command = some next
  reply_exact : inFlightRevocationReplyId state command = some reply

def inFlightRevocationCanonicalEdges : List CanonicalInFlightRevocationEdge :=
  [{ state := .subjectOneArmed, command := .offerChild,
     next := .childOffered, reply := .childOffered,
     next_exact := rfl, reply_exact := rfl },
   { state := .childOffered, command := .rejectRevocationWithoutAuthority,
     next := .childOffered, reply := .revocationWithoutAuthorityRejected,
     next_exact := rfl, reply_exact := rfl },
   { state := .childOffered, command := .rejectWrongLineageRoot,
     next := .childOffered, reply := .wrongLineageRootRejected,
     next_exact := rfl, reply_exact := rfl },
   { state := .childOffered, command := .revokeLineage,
     next := .lineageRevoked, reply := .lineageRevoked,
     next_exact := rfl, reply_exact := rfl },
   { state := .lineageRevoked, command := .rejectRepeatedRevocation,
     next := .lineageRevoked, reply := .repeatedRevocationRejected,
     next_exact := rfl, reply_exact := rfl },
   { state := .lineageRevoked, command := .rejectOfferAfterRevocation,
     next := .lineageRevoked, reply := .offerAfterRevocationRejected,
     next_exact := rfl, reply_exact := rfl },
   { state := .lineageRevoked, command := .switchToSubjectTwo,
     next := .subjectTwoRestored, reply := .subjectTwoRestored,
     next_exact := rfl, reply_exact := rfl },
   { state := .subjectTwoRestored, command := .rejectCanceledReceipt,
     next := .subjectTwoRestored, reply := .canceledReceiptRejected,
     next_exact := rfl, reply_exact := rfl },
   { state := .subjectTwoRestored, command := .replaceDestinationSlot,
     next := .destinationReplaced, reply := .destinationReplaced,
     next_exact := rfl, reply_exact := rfl },
   { state := .destinationReplaced, command := .rejectCanceledHandleReplay,
     next := .destinationReplaced, reply := .canceledHandleReplayRejected,
     next_exact := rfl, reply_exact := rfl },
   { state := .destinationReplaced, command := .useReplacementHandle,
     next := .replacementUsed, reply := .replacementUsed,
     next_exact := rfl, reply_exact := rfl }]

def CanonicalInFlightRevocationEdge.Refines (edge : CanonicalInFlightRevocationEdge) : Prop :=
  let words := encodeInFlightRevocationCommand edge.command
  ∃ pre post,
    inFlightRevocationMaterialize edge.state = .ok pre ∧
    inFlightRevocationMaterialize edge.next = .ok post ∧
    decodeInFlightRevocationReply
        (dispatch (encodeInFlightRevocationState edge.state)
          words.tag words.arg0 words.arg1 words.arg2 words.arg3) =
      .ok edge.reply ∧
    authoritativeGate pre (inFlightRevocationOperation edge.command) =
      { state := post, result := inFlightRevocationReplyResult edge.reply }

theorem canonicalInFlightRevocationEdge_refines (edge : CanonicalInFlightRevocationEdge) :
    edge.Refines :=
  inFlightRevocation_dispatch_decodes_authoritative_edge
    edge.state edge.command edge.next edge.reply edge.next_exact edge.reply_exact

/-- The eleven-edge corpus inherits its state/result meaning solely from the
scalar-to-authoritative bridge above. -/
theorem inFlightRevocationCanonicalEdges_refine :
    ∀ edge ∈ inFlightRevocationCanonicalEdges, edge.Refines := by
  intro edge _hmembership
  exact canonicalInFlightRevocationEdge_refines edge

def inFlightRevocationOutcomeAt (state : InFlightRevocationStateId)
    (command : InFlightRevocationCommandId) :
    Except DecodeError AuthoritativeGateOutcome := do
  let pre ← inFlightRevocationMaterialize state
  pure (authoritativeGate pre (inFlightRevocationOperation command))

/-- The seed is kernel-owned: subject 1 is current, its slot 2 holds the
delegated revoke-only authority on endpoint 10 as identity 6, and the next
identity is 7, so the sealed child below is generation 7. -/
theorem inFlightRevocation_seed_shape :
    (inFlightRevocationMaterialize .subjectOneArmed).toOption.map
        (fun state => state.execution.core.context.currentSubject) = some 1 ∧
    (inFlightRevocationMaterialize .subjectOneArmed).toOption.map
        (fun state =>
          (state.capabilities.slots 1 2).map
            (fun capability =>
              (capability.identity, capability.object, capability.rights.revoke))) =
      some (some (6, 10, true)) ∧
    (inFlightRevocationMaterialize .subjectOneArmed).toOption.map
        (fun state => state.capabilities.nextIdentity) = some 7 ∧
    (inFlightRevocationMaterialize .subjectOneArmed).toOption.map
        (fun state => (state.transfers.pending 10).isSome) = some false := by
  native_decide

/-- The offered descendant is sealed, not installed: it is generation 7 of
endpoint 10, derived from subject 1's slot-1 capability (identity 2), with an
envelope in the mailbox and no slot anywhere. -/
theorem inFlightRevocation_offer_seals_child :
    (inFlightRevocationOutcomeAt .subjectOneArmed .offerChild).toOption.map (·.result) =
      some (inFlightRevocationReplyResult .childOffered) ∧
    (inFlightRevocationMaterialize .childOffered).toOption.map
        (fun state =>
          (state.transfers.pending 10).map
            (fun transfer => (transfer.identity, transfer.parent, transfer.sender))) =
      some (some (7, 2, 1)) ∧
    (inFlightRevocationMaterialize .childOffered).toOption.map
        (fun state => (state.transfers.mailbox 10).isSome) = some true ∧
    (inFlightRevocationMaterialize .childOffered).toOption.map
        (fun state => (state.capabilities.slots 2 3).isSome) = some false ∧
    (inFlightRevocationMaterialize .childOffered).toOption.map
        (fun state => state.capabilities.nextIdentity) = some 8 := by
  native_decide

/-- Only the exact delegated revoke authority over the exact lineage root is
accepted; a send-only authority and a foreign root are typed denials that
leave the complete state unchanged. -/
theorem inFlightRevocation_revocation_authority_exact :
    (inFlightRevocationOutcomeAt .childOffered .rejectRevocationWithoutAuthority).toOption.map
        (·.result) = some (inFlightRevocationReplyResult .revocationWithoutAuthorityRejected) ∧
    (inFlightRevocationOutcomeAt .childOffered .rejectWrongLineageRoot).toOption.map
        (·.result) = some (inFlightRevocationReplyResult .wrongLineageRootRejected) ∧
    (inFlightRevocationOutcomeAt .childOffered .revokeLineage).toOption.map (·.result) =
      some (inFlightRevocationReplyResult .lineageRevoked) := by
  native_decide

theorem inFlightRevocation_denied_revocations_inert :
    (inFlightRevocationOutcomeAt .childOffered .rejectRevocationWithoutAuthority).toOption.map
        (·.state) = (inFlightRevocationMaterialize .childOffered).toOption ∧
    (inFlightRevocationOutcomeAt .childOffered .rejectWrongLineageRoot).toOption.map
        (·.state) = (inFlightRevocationMaterialize .childOffered).toOption := by
  exact ⟨rfl, rfl⟩

/-- Accepted revocation reaches the in-flight child: the pending record, the
transfer mailbox, and the IPC mailbox are cleared in the same step that clears
subject 1's revoked slot, while the canceled generation stays recorded in the
append-only derivation history and the identity frontier does not move
backwards. -/
theorem inFlightRevocation_revocation_cancels_in_flight :
    (inFlightRevocationMaterialize .lineageRevoked).toOption.map
        (fun state => (state.transfers.pending 10).isSome) = some false ∧
    (inFlightRevocationMaterialize .lineageRevoked).toOption.map
        (fun state => (state.transfers.mailbox 10).isSome) = some false ∧
    (inFlightRevocationMaterialize .lineageRevoked).toOption.map
        (fun state => (state.ipc.endpoints.mailbox 10).isSome) = some false ∧
    (inFlightRevocationMaterialize .lineageRevoked).toOption.map
        (fun state => (state.capabilities.slots 1 1).isSome) = some false ∧
    (inFlightRevocationMaterialize .lineageRevoked).toOption.map
        (fun state => state.capabilities.derivations 7) =
      some (some (some 2, 10, .endpoint, { send := true })) ∧
    (inFlightRevocationMaterialize .lineageRevoked).toOption.map
        (fun state => state.capabilities.nextIdentity) = some 8 ∧
    (inFlightRevocationMaterialize .lineageRevoked).toOption.map
        (fun state => state.transfers.trace.events 10) =
      some [.offered 10 7 1 { word0 := 0xCAFE, word1 := 0xBEEF }, .canceled 10 7] := by
  native_decide

/-- Unrelated authority survives the revocation exactly: subject 1's address
space and delegated revoke authority, every subject-2 capability, the saved
subject-2 continuation, the ready queue, and the current subject are the
pre-revocation values. -/
theorem inFlightRevocation_unrelated_authority_preserved :
    (inFlightRevocationMaterialize .lineageRevoked).toOption.map
        (fun state =>
          ((state.capabilities.slots 1 0).map (·.identity),
            (state.capabilities.slots 1 2).map (·.identity),
            (state.capabilities.slots 2 0).map (·.identity),
            (state.capabilities.slots 2 1).map (·.identity),
            (state.capabilities.slots 2 2).map (·.identity))) =
      some (some 1, some 6, some 3, some 4, some 5) ∧
    (inFlightRevocationMaterialize .lineageRevoked).toOption.map
        (fun state => state.resumable.contexts.map (·.owner)) =
      (inFlightRevocationMaterialize .childOffered).toOption.map
        (fun state => state.resumable.contexts.map (·.owner)) ∧
    (inFlightRevocationMaterialize .lineageRevoked).toOption.map
        (fun state => (state.scheduler.ready, state.lifecycle.current)) =
      (inFlightRevocationMaterialize .childOffered).toOption.map
        (fun state => (state.scheduler.ready, state.lifecycle.current)) := by
  native_decide

/-- After revocation, subject 1 can neither revoke again nor offer through the
revoked capability; both are typed denials with the complete state unchanged. -/
theorem inFlightRevocation_post_revocation_probes :
    (inFlightRevocationOutcomeAt .lineageRevoked .rejectRepeatedRevocation).toOption.map
        (·.result) = some (inFlightRevocationReplyResult .repeatedRevocationRejected) ∧
    (inFlightRevocationOutcomeAt .lineageRevoked .rejectOfferAfterRevocation).toOption.map
        (·.result) = some (inFlightRevocationReplyResult .offerAfterRevocationRejected) := by
  native_decide

theorem inFlightRevocation_post_revocation_probes_inert :
    (inFlightRevocationOutcomeAt .lineageRevoked .rejectRepeatedRevocation).toOption.map
        (·.state) = (inFlightRevocationMaterialize .lineageRevoked).toOption ∧
    (inFlightRevocationOutcomeAt .lineageRevoked .rejectOfferAfterRevocation).toOption.map
        (·.state) = (inFlightRevocationMaterialize .lineageRevoked).toOption := by
  exact ⟨rfl, rfl⟩

/-- The authoritative switch restores subject 2's saved continuation, and its
receipt through the endpoint that carried the offer is the typed empty
rejection: no handle is delivered and nothing is installed in slot 3. -/
theorem inFlightRevocation_stale_receipt_denied :
    (inFlightRevocationOutcomeAt .lineageRevoked .switchToSubjectTwo).toOption.map
        (·.result) = some (inFlightRevocationReplyResult .subjectTwoRestored) ∧
    (inFlightRevocationMaterialize .subjectTwoRestored).toOption.map
        (fun state => state.execution.core.context.currentSubject) = some 2 ∧
    (inFlightRevocationOutcomeAt .subjectTwoRestored .rejectCanceledReceipt).toOption.map
        (·.result) = some (inFlightRevocationReplyResult .canceledReceiptRejected) ∧
    (inFlightRevocationOutcomeAt .subjectTwoRestored .rejectCanceledReceipt).toOption.map
        (fun outcome => (outcome.state.capabilities.slots 2 3).isSome) = some false := by
  native_decide

theorem inFlightRevocation_stale_receipt_inert :
    (inFlightRevocationOutcomeAt .subjectTwoRestored .rejectCanceledReceipt).toOption.map
        (·.state) = (inFlightRevocationMaterialize .subjectTwoRestored).toOption := by
  rfl

/-- Reusing the destination slot installs a strictly newer generation: slot 3
now holds identity 8, the canceled generation-7 handle is denied as stale
without state drift, and the fresh generation-8 handle carries live send
authority. -/
theorem inFlightRevocation_slot_reuse_distinct_generation :
    (inFlightRevocationOutcomeAt .subjectTwoRestored .replaceDestinationSlot).toOption.map
        (·.result) = some (inFlightRevocationReplyResult .destinationReplaced) ∧
    (inFlightRevocationMaterialize .destinationReplaced).toOption.map
        (fun state => (state.capabilities.slots 2 3).map (·.identity)) = some (some 8) ∧
    (inFlightRevocationMaterialize .destinationReplaced).toOption.map
        (fun state => (state.capabilities.derivations 7).isSome) = some true ∧
    (inFlightRevocationOutcomeAt .destinationReplaced .rejectCanceledHandleReplay).toOption.map
        (·.result) = some (inFlightRevocationReplyResult .canceledHandleReplayRejected) ∧
    (inFlightRevocationOutcomeAt .destinationReplaced .useReplacementHandle).toOption.map
        (·.result) = some (inFlightRevocationReplyResult .replacementUsed) ∧
    (inFlightRevocationMaterialize .replacementUsed).toOption.map
        (fun state => (state.transfers.mailbox 10).map (·.sender)) = some (some 2) := by
  native_decide

theorem inFlightRevocation_canceled_handle_replay_inert :
    (inFlightRevocationOutcomeAt .destinationReplaced .rejectCanceledHandleReplay).toOption.map
        (·.state) = (inFlightRevocationMaterialize .destinationReplaced).toOption := by
  rfl

/-- No edge of this family publishes a handle in result word one; the canceled
child never becomes a returned value. -/
theorem inFlightRevocation_no_handle_published :
    inFlightRevocationCanonicalEdges.all (fun edge =>
      let words := encodeInFlightRevocationCommand edge.command
      dispatchValue (encodeInFlightRevocationState edge.state)
        words.tag words.arg0 words.arg1 words.arg2 words.arg3 = 0) = true := by
  native_decide

/-- The canceled handle words name exactly slot 3 / generation 7 and the
replacement names slot 3 / generation 8: the same bounded slot index, distinct
generations, so slot-only or truncated-generation resolution has an observable
consequence. -/
theorem inFlightRevocation_handles_decode :
    CapabilityHandle.decode 0x70003 = .ok { slot := 3, identity := 7 } ∧
    CapabilityHandle.decode 0x80003 = .ok { slot := 3, identity := 8 } := by
  exact ⟨rfl, rfl⟩

/-! ## Stateful invalidation publication branch

This branch extends the generated composite scalar ABI with the exact
prepare/acknowledge protocol in `InvalidationPublication`.  Its canonical state
tokens name the whole protocol state, including the unchanged published
translation state while an effect is pending. -/

inductive InvalidationStateId where
  | initial
  | wrongOwnerRejected
  | protectPending
  | protectMismatchRejected
  | protectedState
  | releasePending
  | releaseMismatchRejected
  | released
  | staleReleaseRejected
  | destroyPending
  | destroyed
  | switchPending
  | switched
  | reused
  | unmapPending
  | unmappedState
  | switchAwayPending
  | switchedAway
  | switchBackPending
  | switchedBack
  deriving DecidableEq, Repr

def encodeInvalidationState : InvalidationStateId → UInt64
  | .initial => 0x1a01
  | .wrongOwnerRejected => 0x1b01
  | .protectPending => 0x1c01
  | .protectMismatchRejected => 0x1d01
  | .protectedState => 0x1e01
  | .releasePending => 0x1f01
  | .releaseMismatchRejected => 0x2001
  | .released => 0x2101
  | .staleReleaseRejected => 0x2201
  | .destroyPending => 0x2301
  | .destroyed => 0x2401
  | .switchPending => 0x2501
  | .switched => 0x2601
  | .reused => 0x2701
  | .unmapPending => 0x2801
  | .unmappedState => 0x2901
  | .switchAwayPending => 0x2a01
  | .switchedAway => 0x2b01
  | .switchBackPending => 0x2c01
  | .switchedBack => 0x2d01

def decodeInvalidationState (word : UInt64) :
    Except DecodeError InvalidationStateId :=
  if word = 0x1a01 then .ok .initial
  else if word = 0x1b01 then .ok .wrongOwnerRejected
  else if word = 0x1c01 then .ok .protectPending
  else if word = 0x1d01 then .ok .protectMismatchRejected
  else if word = 0x1e01 then .ok .protectedState
  else if word = 0x1f01 then .ok .releasePending
  else if word = 0x2001 then .ok .releaseMismatchRejected
  else if word = 0x2101 then .ok .released
  else if word = 0x2201 then .ok .staleReleaseRejected
  else if word = 0x2301 then .ok .destroyPending
  else if word = 0x2401 then .ok .destroyed
  else if word = 0x2501 then .ok .switchPending
  else if word = 0x2601 then .ok .switched
  else if word = 0x2701 then .ok .reused
  else if word = 0x2801 then .ok .unmapPending
  else if word = 0x2901 then .ok .unmappedState
  else if word = 0x2a01 then .ok .switchAwayPending
  else if word = 0x2b01 then .ok .switchedAway
  else if word = 0x2c01 then .ok .switchBackPending
  else if word = 0x2d01 then .ok .switchedBack
  else if word % 256 != abiVersion then .error .wrongVersion
  else if 0x2e01 ≤ word then .error .reservedBits
  else .error .unknownState

theorem decode_encode_invalidation_state state :
    decodeInvalidationState (encodeInvalidationState state) = .ok state := by
  cases state <;> rfl

inductive InvalidationCommandId where
  | rejectWrongOwnerProtect
  | prepareProtect
  | rejectProtectEffectMismatch
  | acknowledgeProtect
  | prepareRelease
  | rejectReleaseEffectMismatch
  | acknowledgeRelease
  | rejectStaleRelease
  | prepareDestroy
  | acknowledgeDestroy
  | prepareSwitch
  | acknowledgeSwitch
  | publishReuse
  | prepareUnmap
  | acknowledgeUnmap
  | prepareSwitchAway
  | acknowledgeSwitchAway
  | prepareSwitchBack
  | acknowledgeSwitchBack
  deriving DecidableEq, Repr

def encodeInvalidationCommand : InvalidationCommandId → CommandWords
  | .rejectWrongOwnerProtect =>
      { tag := 0x3201, arg0 := 1, arg1 := 1, arg2 := 7, arg3 := 1 }
  | .prepareProtect =>
      { tag := 0x3301, arg0 := 0, arg1 := 1, arg2 := 7, arg3 := 1 }
  | .rejectProtectEffectMismatch =>
      { tag := 0x3401, arg0 := 2, arg1 := 1, arg2 := 0, arg3 := 0 }
  | .acknowledgeProtect =>
      { tag := 0x3501, arg0 := 1, arg1 := 1, arg2 := 7, arg3 := 0 }
  | .prepareRelease =>
      { tag := 0x3601, arg0 := 0, arg1 := 0, arg2 := 0, arg3 := 0 }
  | .rejectReleaseEffectMismatch =>
      { tag := 0x3701, arg0 := 1, arg1 := 1, arg2 := 7, arg3 := 1 }
  | .acknowledgeRelease =>
      { tag := 0x3801, arg0 := 3, arg1 := 0, arg2 := 0, arg3 := 1 }
  | .rejectStaleRelease =>
      { tag := 0x3901, arg0 := 0, arg1 := 0, arg2 := 0, arg3 := 0 }
  | .prepareDestroy =>
      { tag := 0x3a01, arg0 := 0, arg1 := 1, arg2 := 0, arg3 := 0 }
  | .acknowledgeDestroy =>
      { tag := 0x3b01, arg0 := 2, arg1 := 1, arg2 := 0, arg3 := 2 }
  | .prepareSwitch =>
      { tag := 0x3c01, arg0 := 2, arg1 := 0, arg2 := 0, arg3 := 0 }
  | .acknowledgeSwitch =>
      { tag := 0x3d01, arg0 := 3, arg1 := 0, arg2 := 0, arg3 := 3 }
  | .publishReuse =>
      { tag := 0x3e01, arg0 := 11, arg1 := 0, arg2 := 0, arg3 := 0 }
  | .prepareUnmap =>
      { tag := 0x3f01, arg0 := 0, arg1 := 1, arg2 := 7, arg3 := 0 }
  | .acknowledgeUnmap =>
      { tag := 0x4001, arg0 := 1, arg1 := 1, arg2 := 7, arg3 := 0 }
  | .prepareSwitchAway =>
      { tag := 0x4101, arg0 := 2, arg1 := 0, arg2 := 0, arg3 := 0 }
  | .acknowledgeSwitchAway =>
      { tag := 0x4201, arg0 := 3, arg1 := 0, arg2 := 0, arg3 := 0 }
  | .prepareSwitchBack =>
      { tag := 0x4301, arg0 := 1, arg1 := 0, arg2 := 0, arg3 := 0 }
  | .acknowledgeSwitchBack =>
      { tag := 0x4401, arg0 := 3, arg1 := 0, arg2 := 0, arg3 := 1 }

def decodeInvalidationCommand (words : CommandWords) :
    Except DecodeError InvalidationCommandId :=
  if words = encodeInvalidationCommand .rejectWrongOwnerProtect then
    .ok .rejectWrongOwnerProtect
  else if words = encodeInvalidationCommand .prepareProtect then .ok .prepareProtect
  else if words = encodeInvalidationCommand .rejectProtectEffectMismatch then
    .ok .rejectProtectEffectMismatch
  else if words = encodeInvalidationCommand .acknowledgeProtect then .ok .acknowledgeProtect
  else if words = encodeInvalidationCommand .prepareRelease then .ok .prepareRelease
  else if words = encodeInvalidationCommand .rejectReleaseEffectMismatch then
    .ok .rejectReleaseEffectMismatch
  else if words = encodeInvalidationCommand .acknowledgeRelease then .ok .acknowledgeRelease
  else if words = encodeInvalidationCommand .rejectStaleRelease then .ok .rejectStaleRelease
  else if words = encodeInvalidationCommand .prepareDestroy then .ok .prepareDestroy
  else if words = encodeInvalidationCommand .acknowledgeDestroy then .ok .acknowledgeDestroy
  else if words = encodeInvalidationCommand .prepareSwitch then .ok .prepareSwitch
  else if words = encodeInvalidationCommand .acknowledgeSwitch then .ok .acknowledgeSwitch
  else if words = encodeInvalidationCommand .publishReuse then .ok .publishReuse
  else if words = encodeInvalidationCommand .prepareUnmap then .ok .prepareUnmap
  else if words = encodeInvalidationCommand .acknowledgeUnmap then .ok .acknowledgeUnmap
  else if words = encodeInvalidationCommand .prepareSwitchAway then
    .ok .prepareSwitchAway
  else if words = encodeInvalidationCommand .acknowledgeSwitchAway then
    .ok .acknowledgeSwitchAway
  else if words = encodeInvalidationCommand .prepareSwitchBack then
    .ok .prepareSwitchBack
  else if words = encodeInvalidationCommand .acknowledgeSwitchBack then
    .ok .acknowledgeSwitchBack
  else if words.tag % 256 != abiVersion then .error .wrongVersion
  else if 0x4501 ≤ words.tag then .error .reservedBits
  else .error .noncanonicalArguments

theorem decode_encode_invalidation_command command :
    decodeInvalidationCommand (encodeInvalidationCommand command) = .ok command := by
  cases command <;> rfl

inductive InvalidationReplyId where
  | wrongOwnerRejected
  | protectPending
  | protectMismatchRejected
  | protectedState
  | releasePending
  | releaseMismatchRejected
  | released
  | staleReleaseRejected
  | destroyPending
  | destroyed
  | switchPending
  | switched
  | reused
  | unmapPending
  | unmappedState
  | switchAwayPending
  | switchedAway
  | switchBackPending
  | switchedBack
  deriving DecidableEq, Repr

def encodeInvalidationReply : InvalidationReplyId → UInt64
  | .wrongOwnerRejected => 0x321b01
  | .protectPending => 0x331c01
  | .protectMismatchRejected => 0x341d01
  | .protectedState => 0x351e01
  | .releasePending => 0x361f01
  | .releaseMismatchRejected => 0x372001
  | .released => 0x382101
  | .staleReleaseRejected => 0x392201
  | .destroyPending => 0x3a2301
  | .destroyed => 0x3b2401
  | .switchPending => 0x3c2501
  | .switched => 0x3d2601
  | .reused => 0x3e2701
  | .unmapPending => 0x3f2801
  | .unmappedState => 0x402901
  | .switchAwayPending => 0x412a01
  | .switchedAway => 0x422b01
  | .switchBackPending => 0x432c01
  | .switchedBack => 0x442d01

def decodeInvalidationReply (word : UInt64) :
    Except DecodeError InvalidationReplyId :=
  if word = 0x321b01 then .ok .wrongOwnerRejected
  else if word = 0x331c01 then .ok .protectPending
  else if word = 0x341d01 then .ok .protectMismatchRejected
  else if word = 0x351e01 then .ok .protectedState
  else if word = 0x361f01 then .ok .releasePending
  else if word = 0x372001 then .ok .releaseMismatchRejected
  else if word = 0x382101 then .ok .released
  else if word = 0x392201 then .ok .staleReleaseRejected
  else if word = 0x3a2301 then .ok .destroyPending
  else if word = 0x3b2401 then .ok .destroyed
  else if word = 0x3c2501 then .ok .switchPending
  else if word = 0x3d2601 then .ok .switched
  else if word = 0x3e2701 then .ok .reused
  else if word = 0x3f2801 then .ok .unmapPending
  else if word = 0x402901 then .ok .unmappedState
  else if word = 0x412a01 then .ok .switchAwayPending
  else if word = 0x422b01 then .ok .switchedAway
  else if word = 0x432c01 then .ok .switchBackPending
  else if word = 0x442d01 then .ok .switchedBack
  else if word % 256 != abiVersion then .error .wrongVersion
  else if 0x450001 ≤ word then .error .reservedBits
  else .error .unknownCommand

theorem decode_encode_invalidation_reply reply :
    decodeInvalidationReply (encodeInvalidationReply reply) = .ok reply := by
  cases reply <;> rfl

def invalidationNextState :
    InvalidationStateId → InvalidationCommandId → Option InvalidationStateId
  | .initial, .rejectWrongOwnerProtect => some .wrongOwnerRejected
  | .wrongOwnerRejected, .prepareProtect => some .protectPending
  | .protectPending, .rejectProtectEffectMismatch => some .protectMismatchRejected
  | .protectMismatchRejected, .acknowledgeProtect => some .protectedState
  | .protectedState, .prepareRelease => some .releasePending
  | .releasePending, .rejectReleaseEffectMismatch => some .releaseMismatchRejected
  | .releaseMismatchRejected, .acknowledgeRelease => some .released
  | .released, .rejectStaleRelease => some .staleReleaseRejected
  | .staleReleaseRejected, .prepareDestroy => some .destroyPending
  | .destroyPending, .acknowledgeDestroy => some .destroyed
  | .destroyed, .prepareSwitch => some .switchPending
  | .switchPending, .acknowledgeSwitch => some .switched
  | .switched, .publishReuse => some .reused
  | .initial, .prepareUnmap => some .unmapPending
  | .unmapPending, .acknowledgeUnmap => some .unmappedState
  | .initial, .prepareSwitchAway => some .switchAwayPending
  | .switchAwayPending, .acknowledgeSwitchAway => some .switchedAway
  | .switchedAway, .prepareSwitchBack => some .switchBackPending
  | .switchBackPending, .acknowledgeSwitchBack => some .switchedBack
  | _, _ => none

def invalidationReplyId :
    InvalidationStateId → InvalidationCommandId → Option InvalidationReplyId
  | .initial, .rejectWrongOwnerProtect => some .wrongOwnerRejected
  | .wrongOwnerRejected, .prepareProtect => some .protectPending
  | .protectPending, .rejectProtectEffectMismatch => some .protectMismatchRejected
  | .protectMismatchRejected, .acknowledgeProtect => some .protectedState
  | .protectedState, .prepareRelease => some .releasePending
  | .releasePending, .rejectReleaseEffectMismatch => some .releaseMismatchRejected
  | .releaseMismatchRejected, .acknowledgeRelease => some .released
  | .released, .rejectStaleRelease => some .staleReleaseRejected
  | .staleReleaseRejected, .prepareDestroy => some .destroyPending
  | .destroyPending, .acknowledgeDestroy => some .destroyed
  | .destroyed, .prepareSwitch => some .switchPending
  | .switchPending, .acknowledgeSwitch => some .switched
  | .switched, .publishReuse => some .reused
  | .initial, .prepareUnmap => some .unmapPending
  | .unmapPending, .acknowledgeUnmap => some .unmappedState
  | .initial, .prepareSwitchAway => some .switchAwayPending
  | .switchAwayPending, .acknowledgeSwitchAway => some .switchedAway
  | .switchedAway, .prepareSwitchBack => some .switchBackPending
  | .switchBackPending, .acknowledgeSwitchBack => some .switchedBack
  | _, _ => none

/-- Exact effect meaning of every protocol reply.  Rejections and bounded reuse
request no machine mutation; prepare and successful acknowledgement replies
name the same checked effect. -/
def invalidationReplyEffect : InvalidationReplyId → StaleTranslation.Effect
  | .unmapPending | .unmappedState => .page 1 7
  | .protectPending | .protectedState => .page 1 7
  | .releasePending | .released => .flush
  | .destroyPending | .destroyed => .space 1
  | .switchPending | .switched => .flush
  | .switchAwayPending | .switchedAway |
      .switchBackPending | .switchedBack => .flush
  | _ => .none

def invalidationMaterialize :
    InvalidationStateId → InvalidationPublication.State
  | .initial => InvalidationPublication.initial
  | .wrongOwnerRejected => InvalidationPublication.wrongOwnerRejected
  | .protectPending => InvalidationPublication.protectPending
  | .protectMismatchRejected => InvalidationPublication.protectMismatchRejected
  | .protectedState => InvalidationPublication.protectedState
  | .releasePending => InvalidationPublication.releasePending
  | .releaseMismatchRejected => InvalidationPublication.releaseMismatchRejected
  | .released => InvalidationPublication.released
  | .staleReleaseRejected => InvalidationPublication.staleReleaseRejected
  | .destroyPending => InvalidationPublication.destroyPending
  | .destroyed => InvalidationPublication.destroyed
  | .switchPending => InvalidationPublication.switchPending
  | .switched => InvalidationPublication.switched
  | .reused => InvalidationPublication.reused
  | .unmapPending => InvalidationPublication.unmapPending
  | .unmappedState => InvalidationPublication.unmappedState
  | .switchAwayPending => InvalidationPublication.switchAwayPending
  | .switchedAway => InvalidationPublication.switchedAway
  | .switchBackPending => InvalidationPublication.switchBackPending
  | .switchedBack => InvalidationPublication.switchedBack

def invalidationOutcome :
    InvalidationStateId → InvalidationCommandId →
      Option InvalidationPublication.Outcome
  | .initial, .rejectWrongOwnerProtect =>
      some (InvalidationPublication.prepare InvalidationPublication.initial
        .protect (.protect 1 1 7 { read := true }))
  | .wrongOwnerRejected, .prepareProtect =>
      some (InvalidationPublication.prepare InvalidationPublication.wrongOwnerRejected
        .protect (.protect 0 1 7 { read := true }))
  | .protectPending, .rejectProtectEffectMismatch =>
      some (InvalidationPublication.acknowledge
        InvalidationPublication.protectPending { ticket := 0, effect := .space 1 })
  | .protectMismatchRejected, .acknowledgeProtect =>
      some (InvalidationPublication.acknowledge
        InvalidationPublication.protectMismatchRejected
          { ticket := 0, effect := .page 1 7 })
  | .protectedState, .prepareRelease =>
      some (InvalidationPublication.prepare InvalidationPublication.protectedState
        .release (.release 0 0))
  | .releasePending, .rejectReleaseEffectMismatch =>
      some (InvalidationPublication.acknowledge
        InvalidationPublication.releasePending { ticket := 1, effect := .page 1 7 })
  | .releaseMismatchRejected, .acknowledgeRelease =>
      some (InvalidationPublication.acknowledge
        InvalidationPublication.releaseMismatchRejected
          { ticket := 1, effect := .flush })
  | .released, .rejectStaleRelease =>
      some (InvalidationPublication.prepare InvalidationPublication.released
        .release (.release 0 0))
  | .staleReleaseRejected, .prepareDestroy =>
      some (InvalidationPublication.prepare InvalidationPublication.staleReleaseRejected
        .destroy (.destroy 0 1))
  | .destroyPending, .acknowledgeDestroy =>
      some (InvalidationPublication.acknowledge
        InvalidationPublication.destroyPending { ticket := 2, effect := .space 1 })
  | .destroyed, .prepareSwitch =>
      some (InvalidationPublication.prepare InvalidationPublication.destroyed
        .switch (.switch 2))
  | .switchPending, .acknowledgeSwitch =>
      some (InvalidationPublication.acknowledge
        InvalidationPublication.switchPending { ticket := 3, effect := .flush })
  | .switched, .publishReuse =>
      some (InvalidationPublication.publishReuse InvalidationPublication.switched)
  | .initial, .prepareUnmap =>
      some (InvalidationPublication.prepare InvalidationPublication.initial
        .unmap (.unmap 0 1 7))
  | .unmapPending, .acknowledgeUnmap =>
      some (InvalidationPublication.acknowledge
        InvalidationPublication.unmapPending
          { ticket := 0, effect := .page 1 7 })
  | .initial, .prepareSwitchAway =>
      some (InvalidationPublication.prepare InvalidationPublication.initial
        .switch (.switch 2))
  | .switchAwayPending, .acknowledgeSwitchAway =>
      some (InvalidationPublication.acknowledge
        InvalidationPublication.switchAwayPending
          { ticket := 0, effect := .flush })
  | .switchedAway, .prepareSwitchBack =>
      some (InvalidationPublication.prepare InvalidationPublication.switchedAway
        .switch (.switch 1))
  | .switchBackPending, .acknowledgeSwitchBack =>
      some (InvalidationPublication.acknowledge
        InvalidationPublication.switchBackPending
          { ticket := 1, effect := .flush })
  | _, _ => none

theorem invalidation_dispatch_canonical state command :
    let words := encodeInvalidationCommand command
    dispatch (encodeInvalidationState state)
      words.tag words.arg0 words.arg1 words.arg2 words.arg3 =
      ((invalidationReplyId state command).map encodeInvalidationReply).getD
        (errorWord .invalidSequence) := by
  cases state <;> cases command <;> native_decide

structure CanonicalInvalidationEdge where
  state : InvalidationStateId
  command : InvalidationCommandId
  next : InvalidationStateId
  reply : InvalidationReplyId
  next_exact : invalidationNextState state command = some next
  reply_exact : invalidationReplyId state command = some reply

def invalidationCanonicalEdges : List CanonicalInvalidationEdge :=
  [{ state := .initial, command := .rejectWrongOwnerProtect,
     next := .wrongOwnerRejected, reply := .wrongOwnerRejected,
     next_exact := rfl, reply_exact := rfl },
   { state := .wrongOwnerRejected, command := .prepareProtect,
     next := .protectPending, reply := .protectPending,
     next_exact := rfl, reply_exact := rfl },
   { state := .protectPending, command := .rejectProtectEffectMismatch,
     next := .protectMismatchRejected, reply := .protectMismatchRejected,
     next_exact := rfl, reply_exact := rfl },
   { state := .protectMismatchRejected, command := .acknowledgeProtect,
     next := .protectedState, reply := .protectedState,
     next_exact := rfl, reply_exact := rfl },
   { state := .protectedState, command := .prepareRelease,
     next := .releasePending, reply := .releasePending,
     next_exact := rfl, reply_exact := rfl },
   { state := .releasePending, command := .rejectReleaseEffectMismatch,
     next := .releaseMismatchRejected, reply := .releaseMismatchRejected,
     next_exact := rfl, reply_exact := rfl },
   { state := .releaseMismatchRejected, command := .acknowledgeRelease,
     next := .released, reply := .released,
     next_exact := rfl, reply_exact := rfl },
   { state := .released, command := .rejectStaleRelease,
     next := .staleReleaseRejected, reply := .staleReleaseRejected,
     next_exact := rfl, reply_exact := rfl },
   { state := .staleReleaseRejected, command := .prepareDestroy,
     next := .destroyPending, reply := .destroyPending,
     next_exact := rfl, reply_exact := rfl },
   { state := .destroyPending, command := .acknowledgeDestroy,
     next := .destroyed, reply := .destroyed,
     next_exact := rfl, reply_exact := rfl },
   { state := .destroyed, command := .prepareSwitch,
     next := .switchPending, reply := .switchPending,
     next_exact := rfl, reply_exact := rfl },
   { state := .switchPending, command := .acknowledgeSwitch,
     next := .switched, reply := .switched,
     next_exact := rfl, reply_exact := rfl },
   { state := .switched, command := .publishReuse,
     next := .reused, reply := .reused,
     next_exact := rfl, reply_exact := rfl },
   { state := .initial, command := .prepareUnmap,
     next := .unmapPending, reply := .unmapPending,
     next_exact := rfl, reply_exact := rfl },
   { state := .unmapPending, command := .acknowledgeUnmap,
     next := .unmappedState, reply := .unmappedState,
     next_exact := rfl, reply_exact := rfl },
   { state := .initial, command := .prepareSwitchAway,
     next := .switchAwayPending, reply := .switchAwayPending,
     next_exact := rfl, reply_exact := rfl },
   { state := .switchAwayPending, command := .acknowledgeSwitchAway,
     next := .switchedAway, reply := .switchedAway,
     next_exact := rfl, reply_exact := rfl },
   { state := .switchedAway, command := .prepareSwitchBack,
     next := .switchBackPending, reply := .switchBackPending,
     next_exact := rfl, reply_exact := rfl },
   { state := .switchBackPending, command := .acknowledgeSwitchBack,
     next := .switchedBack, reply := .switchedBack,
     next_exact := rfl, reply_exact := rfl }]

def CanonicalInvalidationEdge.Refines (edge : CanonicalInvalidationEdge) : Prop :=
  ∃ outcome,
    invalidationOutcome edge.state edge.command = some outcome ∧
    outcome.state = invalidationMaterialize edge.next ∧
    outcome.effect = invalidationReplyEffect edge.reply ∧
    let words := encodeInvalidationCommand edge.command
    decodeInvalidationReply
        (dispatch (encodeInvalidationState edge.state)
          words.tag words.arg0 words.arg1 words.arg2 words.arg3) =
      .ok edge.reply

theorem invalidation_edge_refines state command next reply
    (hnext : invalidationNextState state command = some next)
    (hreply : invalidationReplyId state command = some reply) :
    (CanonicalInvalidationEdge.mk state command next reply hnext hreply).Refines := by
  change ∃ outcome,
    invalidationOutcome state command = some outcome ∧
    outcome.state = invalidationMaterialize next ∧
    outcome.effect = invalidationReplyEffect reply ∧
    (let words := encodeInvalidationCommand command
     decodeInvalidationReply
        (dispatch (encodeInvalidationState state)
          words.tag words.arg0 words.arg1 words.arg2 words.arg3) = .ok reply)
  cases state <;> cases command <;> simp [invalidationNextState] at hnext
  all_goals subst next
  all_goals simp [invalidationReplyId] at hreply
  all_goals subst reply
  all_goals refine ⟨_, rfl, rfl, rfl, ?_⟩
  all_goals
    dsimp
    rw [invalidation_dispatch_canonical]
    rfl

theorem invalidationCanonicalEdges_refine :
    ∀ edge ∈ invalidationCanonicalEdges, edge.Refines := by
  intro edge _hmembership
  exact invalidation_edge_refines edge.state edge.command edge.next edge.reply
    edge.next_exact edge.reply_exact

/-- Malformed effects and valid effects paired with the wrong pending state are
rejected by the scalar boundary before they can acknowledge or publish. -/
theorem invalidation_malformed_and_mismatched_rejected :
    dispatch 0x1d01 0x3501 1 1 7 1 = errorWord .noncanonicalArguments ∧
    dispatch 0x1f01 0x3501 1 1 7 0 = errorWord .invalidSequence ∧
    dispatch 0x2501 0x3d01 3 0 0 1 = errorWord .noncanonicalArguments := by
  native_decide

example : dispatch 0x0001 0x0101 1 0 0 0 = encodeReply
    { next := .subjectCreated, reply := 1 } := by native_decide
example : dispatch 0x0101 0x0201 99 0 0 0 = encodeReply
    { next := .unknownSyscallRejected, reply := 2 } := by native_decide
example : dispatch 0x0401 0x0501 1 0 0 0 = encodeReply
    { next := .subjectTerminated, reply := 5 } := by native_decide
example : dispatch 0x0501 0x0601 0 0 0 0 = encodeReply
    { next := .fatalEntered, reply := 6 } := by native_decide
example : dispatch 0x0601 0x0701 0 0 0 0 = encodeReply
    { next := .postFatalRejected, reply := 7 } := by native_decide
example : dispatch 0x0101 0x0201 99 1 0 0 =
    0xff05 := by native_decide
example : dispatch 0x0001 0x0201 99 0 0 0 =
    0xff06 := by native_decide
example : dispatch 0x0002 0x0101 1 0 0 0 =
    0xff01 := by native_decide
example : dispatch 0x10001 0x0101 1 0 0 0 =
    0xff02 := by native_decide
example : dispatch 0x0101 0x0801 0x10000 7 1 0 = 0x080101 := by native_decide
example : dispatch 0x0101 0x0901 0x10000 0 0 0 = 0x090101 := by native_decide
example : dispatch 0x0101 0x0a01 0 0 1 0 = 0x0a0101 := by native_decide
example : dispatch 0x0101 0x0b01 0 0 0 0 = 0x0b0101 := by native_decide
example : dispatch 0x0101 0x0c01 0 0 0 0 = 0x0c0101 := by native_decide
example : validateQ35DMASnapshot
    1 0x0001000800020002
    0x0006000029c08086 0x0001
    0x0003000011111234 0x0001
    0 0
    0x0006010029188086 0xc001
    0x0001060129228086 0x8001
    0x000c050029308086 0x8001 = 0 := by native_decide
example : validateQ35DMASnapshot
    1 0x0001000800020002
    0x0006000029c08086 0x0001
    0x0003000011111234 0x0011
    0 0
    0x0006010029188086 0xc001
    0x0001060129228086 0x8001
    0x000c050029308086 0x8001 =
      DMAQuarantine.rejectReasonTag .busMasterEnabled := by native_decide
example : dispatch 0x0f01 0x3001 7 0 0 0 = 0x301901 := by native_decide
example : dispatch 0x0f01 0x3101 9 0 0 0 = 0x310f01 := by native_decide

end LeanOS.CompositeDispatcher
