import LeanOS.FailStop

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

Every reserved field must be zero.  The single result word records the ABI
version, exact next-state token, and typed-reply token.  Unsupported state /
command pairs reject before `authoritativeGate` is evaluated.  This finite
slice is the seed for later bounded snapshot families; generated C, its scalar
calling convention, and the compiler remain trusted hosted-test boundaries.
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
  else if tag % 256 != abiVersion then 0xff01
  else if 0x3001 ≤ tag then 0xff02
  else 0xff04

/-- Allocation-free generated entry point.  It validates every scalar before
selecting one exact trace edge.  The proof below connects each success word to
the full authoritative gate; this executable definition intentionally contains
no shadow kernel state. -/
@[export leanos_composite_dispatch]
def dispatch (stateWord tag arg0 arg1 arg2 arg3 : UInt64) : UInt64 :=
  if stateWord = 0x0801 || stateWord = 0x0901 || stateWord = 0x0a01 ||
      stateWord = 0x0b01 || stateWord = 0x0c01 || stateWord = 0x0d01 ||
      stateWord = 0x0e01 || stateWord = 0x0f01 || stateWord = 0x1001 ||
      stateWord = 0x1101 || stateWord = 0x1201 || stateWord = 0x1301 ||
      stateWord = 0x1401 || stateWord = 0x1501 || stateWord = 0x1601 ||
      stateWord = 0x1701 || stateWord = 0x1801 then
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
  deriving DecidableEq, Repr

def encodeMixedState : MixedStateId → UInt64
  | .initial => 0x0801
  | .transferOffered => 0x0901
  | .transferAccepted => 0x0a01
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

def decodeMixedState (word : UInt64) : Except DecodeError MixedStateId :=
  if word = 0x0801 then .ok .initial
  else if word = 0x0901 then .ok .transferOffered
  else if word = 0x0a01 then .ok .transferAccepted
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
  else if word % 256 != abiVersion then .error .wrongVersion
  else if 0x1901 ≤ word then .error .reservedBits
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
  deriving DecidableEq, Repr

def encodeMixedCommand : MixedCommandId → CommandWords
  | .offerTransfer =>
      { tag := 0x2001, arg0 := 0x30000, arg1 := 0x30000,
        arg2 := 0xCAFE, arg3 := 0xBEEF }
  | .acceptTransfer =>
      { tag := 0x2101, arg0 := 0x30000, arg1 := 3, arg2 := 0, arg3 := 0 }
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

def decodeMixedCommand (words : CommandWords) :
    Except DecodeError MixedCommandId :=
  if words = encodeMixedCommand .offerTransfer then .ok .offerTransfer
  else if words = encodeMixedCommand .acceptTransfer then .ok .acceptTransfer
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
  else if words.tag % 256 != abiVersion then .error .wrongVersion
  else if 0x3001 ≤ words.tag then .error .reservedBits
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

def mixedNextState : MixedStateId → MixedCommandId → Option MixedStateId
  | .initial, .offerTransfer => some .transferOffered
  | .transferOffered, .acceptTransfer => some .transferAccepted
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
  | _, _ => none

def mixedExpectedReply : MixedStateId → MixedCommandId → Option UInt64
  | .initial, .offerTransfer => some 0x200901
  | .transferOffered, .acceptTransfer => some 0x210a01
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
  | _, _ => none

inductive MixedReplyId where
  | transferOffered
  | transferAccepted
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
  deriving DecidableEq, Repr

def encodeMixedReply : MixedReplyId → UInt64
  | .transferOffered => 0x200901
  | .transferAccepted => 0x210a01
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

def decodeMixedReply (word : UInt64) : Except DecodeError MixedReplyId :=
  if word = 0x200901 then .ok .transferOffered
  else if word = 0x210a01 then .ok .transferAccepted
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
  else if word % 256 != abiVersion then .error .wrongVersion
  else if 0x300001 ≤ word then .error .reservedBits
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

def mixedInitialState : Except DecodeError CompositeState :=
  match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
  | .ok plan => .ok (compositeDispatcherInitial plan)
  | .error _ => .error .reservedBits

def mixedMaterialize (id : MixedStateId) : Except DecodeError CompositeState := do
  let initial ← mixedInitialState
  pure (runAuthoritativeOperations initial
    ((mixedPrefix id).map mixedCommandOperation))

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
   { state := .transferOffered, command := .acceptTransfer,
     next := .transferAccepted, reply := .transferAccepted,
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

/-- The hosted 16-edge corpus inherits its state/result meaning solely from
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
    encodeMixedState next = encodeMixedState state + 0x100 := by
  cases state <;> cases command <;> simp [mixedNextState] at hnext
  all_goals subst next <;> rfl

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
    1 0x000800020002
    0x0006000029c08086 0x0001
    0x0003000011111234 0x0001
    0 0
    0x0006010029188086 0xc001
    0x0001060129228086 0x8001
    0x000c050029308086 0x8001 = 0 := by native_decide
example : validateQ35DMASnapshot
    1 0x000800020002
    0x0006000029c08086 0x0001
    0x0003000011111234 0x0011
    0 0
    0x0006010029188086 0xc001
    0x0001060129228086 0x8001
    0x000c050029308086 0x8001 =
      DMAQuarantine.rejectReasonTag .busMasterEnabled := by native_decide

end LeanOS.CompositeDispatcher
