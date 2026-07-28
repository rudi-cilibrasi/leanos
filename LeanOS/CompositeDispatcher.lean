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

/-- Allocation-free generated entry point.  It validates every scalar before
selecting one exact trace edge.  The proof below connects each success word to
the full authoritative gate; this executable definition intentionally contains
no shadow kernel state. -/
@[export leanos_composite_dispatch]
def dispatch (stateWord tag arg0 arg1 arg2 arg3 : UInt64) : UInt64 :=
  if stateWord != 0x0001 && stateWord != 0x0101 && stateWord != 0x0201 &&
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

end LeanOS.CompositeDispatcher
