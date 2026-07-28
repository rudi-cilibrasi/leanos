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
  deriving DecidableEq, Repr

def encodeStateId : StateId → UInt64
  | .initial => 0x0001
  | .subjectCreated => 0x0101
  | .unknownSyscallRejected => 0x0201
  | .malformedMapRejected => 0x0301
  | .schedulerObserved => 0x0401

def decodeStateId (word : UInt64) : Except DecodeError StateId :=
  if word = 0x0001 then .ok .initial
  else if word = 0x0101 then .ok .subjectCreated
  else if word = 0x0201 then .ok .unknownSyscallRejected
  else if word = 0x0301 then .ok .malformedMapRejected
  else if word = 0x0401 then .ok .schedulerObserved
  else if word % 256 != abiVersion then .error .wrongVersion
  else if 0x0501 ≤ word then .error .reservedBits
  else .error .unknownState

theorem decode_encode_state (id : StateId) :
    decodeStateId (encodeStateId id) = .ok id := by
  cases id <;> rfl

theorem state_encoding_injective (first second : StateId)
    (h : encodeStateId first = encodeStateId second) : first = second := by
  cases first <;> cases second <;> simp_all [encodeStateId]

inductive CommandId where
  | createSubjectOne
  | rejectUnknownSyscall
  | rejectMalformedMap
  | observeScheduler
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
  | .rejectUnknownSyscall =>
      { tag := 0x0201, arg0 := 99, arg1 := 0, arg2 := 0, arg3 := 0 }
  | .rejectMalformedMap =>
      { tag := 0x0301, arg0 := 0, arg1 := 0, arg2 := 0, arg3 := 0 }
  | .observeScheduler =>
      { tag := 0x0401, arg0 := 0, arg1 := 0, arg2 := 0, arg3 := 0 }

def decodeCommand (words : CommandWords) : Except DecodeError CommandId :=
  if words.tag = 0x0101 then
    if words.arg0 = 1 && words.arg1 = 0 && words.arg2 = 0 && words.arg3 = 0 then
      .ok .createSubjectOne
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
  else if words.tag % 256 != abiVersion then .error .wrongVersion
  else if 0x0501 ≤ words.tag then .error .reservedBits
  else .error .unknownCommand

theorem decode_encode_command (id : CommandId) :
    decodeCommand (encodeCommand id) = .ok id := by
  cases id <;> rfl

theorem command_encoding_injective (first second : CommandId)
    (h : encodeCommand first = encodeCommand second) : first = second := by
  cases first <;> cases second <;> simp_all [encodeCommand]

/-- The normalized public commands carry only raw syscall words or a bounded
subject selector.  Caller and address-space identity remain absent. -/
def commandOperation : CommandId → AuthoritativeOperation
  | .createSubjectOne => .ordinary (.createSubject 1)
  | .rejectUnknownSyscall =>
      .ordinary (.syscall { number := 99, arg0 := 0, arg1 := 0, arg2 := 0 })
  | .rejectMalformedMap =>
      .ordinary (.syscall { number := 0, arg0 := 0, arg1 := 0, arg2 := 0 })
  | .observeScheduler => .ordinary .scheduleNext

def nextState : StateId → CommandId → Option StateId
  | .initial, .createSubjectOne => some .subjectCreated
  | .subjectCreated, .rejectUnknownSyscall => some .unknownSyscallRejected
  | .unknownSyscallRejected, .rejectMalformedMap => some .malformedMapRejected
  | .malformedMapRejected, .observeScheduler => some .schedulerObserved
  | _, _ => none

structure ReplyToken where
  next : StateId
  reply : UInt64
  deriving DecidableEq, Repr

def replyToken : StateId → CommandId → Option ReplyToken
  | .initial, .createSubjectOne => some { next := .subjectCreated, reply := 1 }
  | .subjectCreated, .rejectUnknownSyscall =>
      some { next := .unknownSyscallRejected, reply := 2 }
  | .unknownSyscallRejected, .rejectMalformedMap =>
      some { next := .malformedMapRejected, reply := 3 }
  | .malformedMapRejected, .observeScheduler =>
      some { next := .schedulerObserved, reply := 4 }
  | _, _ => none

/-- Version byte, next-state byte, and reply byte; all upper bits are reserved. -/
def encodeReply (token : ReplyToken) : UInt64 :=
  abiVersion + ((encodeStateId token.next / 256) * 256) + token.reply * 65536

def decodeReply (word : UInt64) : Except DecodeError ReplyToken :=
  if word = 0x010101 then .ok { next := .subjectCreated, reply := 1 }
  else if word = 0x020201 then .ok { next := .unknownSyscallRejected, reply := 2 }
  else if word = 0x030301 then .ok { next := .malformedMapRejected, reply := 3 }
  else if word = 0x040401 then .ok { next := .schedulerObserved, reply := 4 }
  else if word % 256 != abiVersion then .error .wrongVersion
  else if 0x050501 ≤ word then .error .reservedBits
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
      stateWord != 0x0301 && stateWord != 0x0401 then
    if stateWord % 256 != abiVersion then 0xff01
    else if 0x0501 ≤ stateWord then 0xff02
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
  else if tag % 256 != abiVersion then 0xff01
  else if 0x0501 ≤ tag then 0xff02
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

def materialize : StateId → Except DecodeError CompositeState
  | .initial => initialState
  | .subjectCreated => subjectCreatedState
  | .unknownSyscallRejected => unknownSyscallRejectedState
  | .malformedMapRejected => malformedMapRejectedState
  | .schedulerObserved => schedulerObservedState

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
    (state = .initial ∧ command = .createSubjectOne ∧ next = .subjectCreated) ∨
    (state = .subjectCreated ∧ command = .rejectUnknownSyscall ∧
      next = .unknownSyscallRejected) ∨
    (state = .unknownSyscallRejected ∧ command = .rejectMalformedMap ∧
      next = .malformedMapRejected) ∨
    (state = .malformedMapRejected ∧ command = .observeScheduler ∧
      next = .schedulerObserved) := by
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
      malformedMapRejectedState, schedulerObservedState] at hpre ⊢
    rw [hpre]
    rfl

/-- Finite-list refinement for the complete version-one corpus. -/
def canonicalTrace : List (StateId × CommandId) :=
  [(.initial, .createSubjectOne),
   (.subjectCreated, .rejectUnknownSyscall),
   (.unknownSyscallRejected, .rejectMalformedMap),
   (.malformedMapRejected, .observeScheduler)]

theorem canonicalTrace_all_exact :
    canonicalTrace.all (fun edge =>
      (nextState edge.1 edge.2).isSome) = true := by
  native_decide

example : dispatch 0x0001 0x0101 1 0 0 0 = encodeReply
    { next := .subjectCreated, reply := 1 } := by native_decide
example : dispatch 0x0101 0x0201 99 0 0 0 = encodeReply
    { next := .unknownSyscallRejected, reply := 2 } := by native_decide
example : dispatch 0x0101 0x0201 99 1 0 0 =
    0xff05 := by native_decide
example : dispatch 0x0001 0x0201 99 0 0 0 =
    0xff06 := by native_decide
example : dispatch 0x0002 0x0101 1 0 0 0 =
    0xff01 := by native_decide
example : dispatch 0x10001 0x0101 1 0 0 0 =
    0xff02 := by native_decide

end LeanOS.CompositeDispatcher
