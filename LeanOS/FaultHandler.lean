import LeanOS.FaultDispatch
import LeanOS.UserFaultContainmentVocabulary

/-!
# Fault handler subject for one typed fault (issue #488)

A boot-fixed `Binding` names one contained fault class, the subject whose
faults of that class are handled, and the handler subject.  The transition
`fault` wraps `FaultDispatch.dispatch` without changing it:

* **No handler bound (the default).**  The result is exactly
  `FaultDispatch.dispatch` on the core state: the same cleanup, survivor,
  idle, rejection, or fatal outcome as before this module existed
  (`unbound_is_default`, `unbound_class_is_default`).
* **Handler bound.**  Only when the default transition would have contained
  the fault (a live, runnable, kernel-selected current subject, the
  manifest-decoded class, CPL3 origin) and the class and faulting subject are
  the bound ones does the handler path apply.  The faulting subject is
  suspended (not runnable, not current, not queued), and the handler's
  one-record fault inbox receives exactly the typed `FaultRecord`
  (class, vector, faulting subject, saved RIP, architectural error word) built
  from the normalized frame.  No capability, register, or memory word of the
  faulting subject is part of the record, and the capability state is
  unchanged (`delivered_exact`, `delivered_no_amplification`).  If the
  handler is unavailable (dead, already holding a record, or the faulting
  subject itself) the default applies.
* **Reply.**  The handler's only action in this slice is `terminate`: the
  suspended subject is cleaned up by the existing
  `ResumablePreemption.cleanupSubject` (the same cleanup as the default) and
  never resumes (`reply_terminates`).  Cleanup only removes capability slots,
  so no holder (in particular the handler) gains authority
  (`reply_no_amplification`).
* **Receive.**  A subject takes only its own inbox; a subject that is not the
  bound handler never holds a record (`InboxBound`, preserved by every step).

The allocation-free boot witness `faultHandlerRoute` is tied to these
transitions on a concrete three-subject system by `faultHandlerRoute_agrees`.
-/
namespace LeanOS.FaultHandler

open LeanOS
set_option linter.unusedSimpArgs false

abbrev SubjectId := Capability.SubjectId

/-- One boot-fixed handler binding for one typed fault class. -/
structure Binding where
  reason : InterruptEntry.ContainedReason
  faulting : SubjectId
  handler : SubjectId
  deriving DecidableEq, Repr

/-- The typed fault record: everything, and the only thing, a handler
receives.  The address word is the normalized saved RIP; the error word is the
architectural error code, or zero for a class that pushes none. -/
structure FaultRecord where
  reason : InterruptEntry.ContainedReason
  vector : UInt64
  faulting : SubjectId
  address : UInt64
  errorWord : UInt64
  deriving DecidableEq, Repr

def recordOf (reason : InterruptEntry.ContainedReason)
    (frame : InterruptEntry.NormalizedFrame) : FaultRecord :=
  { reason, vector := frame.vector, faulting := frame.currentSubject
    address := frame.rip, errorWord := frame.errorCode.getD 0 }

/-- The record's machine words, in the registers the handler's blocked
receive is woken with (RAX, RBX, RCX, RDX). -/
def FaultRecord.words (record : FaultRecord) : UInt64 × UInt64 × UInt64 × UInt64 :=
  (record.reason.code + record.vector * 0x100, UInt64.ofNat record.faulting,
    record.address, record.errorWord)

structure System where
  core : ResumablePreemption.State
  /-- Fixed at boot; no transition changes it. -/
  binding : Option Binding
  /-- The subject suspended awaiting its handler's decision. -/
  suspended : Option SubjectId := none
  /-- Each subject's one-record fault inbox. -/
  inbox : SubjectId → Option FaultRecord := fun _ => none

inductive Decision where
  | terminate
  deriving DecidableEq, Repr

inductive RejectReason where
  | notHandler | nothingSuspended | emptyInbox
  deriving DecidableEq, Repr

inductive Action where
  /-- The unchanged default: exactly `FaultDispatch.dispatch`'s action. -/
  | default (action : FaultDispatch.Action)
  | delivered (handler : SubjectId) (record : FaultRecord)
  | received (record : FaultRecord)
  | terminated (faulting : SubjectId)
  | rejected (reason : RejectReason)
  deriving DecidableEq, Repr

def contained : FaultDispatch.Action → Bool
  | .idle _ | .dispatch _ _ => true
  | _ => false

/-- The binding applies to this entry: an accepted frame of the bound class
raised by the bound subject. -/
def boundFor (binding : Option Binding) (entry : InterruptEntry.Result) :
    Option (Binding × FaultRecord) :=
  match binding, entry with
  | some b, .accepted frame =>
      match InterruptEntry.containedReason? frame.vector with
      | some reason =>
          if reason = b.reason ∧ frame.currentSubject = b.faulting then
            some (b, recordOf reason frame)
          else none
      | none => none
  | _, _ => none

/-- Suspend: clear the runnable bit, the current slot, and queue membership.
Capabilities, contexts, memory, and mappings are untouched. -/
def suspendCore (core : ResumablePreemption.State) (subject : SubjectId) :
    ResumablePreemption.State :=
  { core with scheduler := { core.scheduler with
      lifecycle := { core.scheduler.lifecycle with
        runnable := fun s => if s = subject then false else core.scheduler.lifecycle.runnable s
        current := none }
      ready := core.scheduler.ready.filter (· != subject) } }

def setInbox (inbox : SubjectId → Option FaultRecord) (subject : SubjectId)
    (value : Option FaultRecord) : SubjectId → Option FaultRecord :=
  fun s => if s = subject then value else inbox s

/-- The default transition, lifted to the system. -/
def defaultStep (sys : System) (entry : InterruptEntry.Result) : System × Action :=
  let outcome := FaultDispatch.dispatch sys.core entry
  ({ sys with core := outcome.state }, .default outcome.action)

def handlerAvailable (sys : System) (b : Binding) : Bool :=
  b.handler != b.faulting && sys.suspended.isNone && (sys.inbox b.handler).isNone &&
    sys.core.scheduler.lifecycle.capabilities.subjects b.handler

def fault (sys : System) (entry : InterruptEntry.Result) : System × Action :=
  if contained (FaultDispatch.dispatch sys.core entry).action then
    match boundFor sys.binding entry with
    | none => defaultStep sys entry
    | some (b, record) =>
        if handlerAvailable sys b then
          ({ sys with core := suspendCore sys.core b.faulting
                      suspended := some b.faulting
                      inbox := setInbox sys.inbox b.handler (some record) },
            .delivered b.handler record)
        else defaultStep sys entry
  else defaultStep sys entry

def receive (sys : System) (subject : SubjectId) : System × Action :=
  match sys.inbox subject with
  | some record => ({ sys with inbox := setInbox sys.inbox subject none }, .received record)
  | none => (sys, .rejected .emptyInbox)

def reply (sys : System) (subject : SubjectId) (_decision : Decision) : System × Action :=
  match sys.binding, sys.suspended with
  | some b, some faulting =>
      if b.handler = subject ∧ b.faulting = faulting then
        ({ sys with core := ResumablePreemption.cleanupSubject sys.core faulting
                    suspended := none }, .terminated faulting)
      else (sys, .rejected .notHandler)
  | _, none => (sys, .rejected .nothingSuspended)
  | none, some _ => (sys, .rejected .notHandler)

inductive Op where
  | fault (entry : InterruptEntry.Result)
  | receive (subject : SubjectId)
  | reply (subject : SubjectId) (decision : Decision)

def step (sys : System) : Op → System × Action
  | .fault entry => fault sys entry
  | .receive subject => receive sys subject
  | .reply subject decision => reply sys subject decision

/-! ## (a) No handler bound: the default, exactly -/

/-- With no handler bound, `fault` is exactly the existing fault dispatch. -/
theorem unbound_is_default sys entry (h : sys.binding = none) :
    fault sys entry =
      ({ sys with core := (FaultDispatch.dispatch sys.core entry).state },
        .default (FaultDispatch.dispatch sys.core entry).action) := by
  unfold fault defaultStep
  split <;> simp [boundFor, h]

/-- A fault of another class, or from another subject, also takes the
default even when a handler is bound. -/
theorem unbound_class_is_default sys entry
    (h : boundFor sys.binding entry = none) :
    fault sys entry = defaultStep sys entry := by
  unfold fault
  split <;> simp [h]

/-- Every fault outcome is either the default or a delivery. -/
theorem fault_default_or_delivered sys entry :
    (fault sys entry = defaultStep sys entry) ∨
      ∃ handler record, (fault sys entry).2 = .delivered handler record := by
  unfold fault
  split
  · split
    · exact Or.inl rfl
    · split
      · exact Or.inr ⟨_, _, rfl⟩
      · exact Or.inl rfl
  · exact Or.inl rfl

/-! ## (b) Handler bound: suspension, the exact record, no amplification -/

theorem boundFor_some binding entry b record
    (h : boundFor binding entry = some (b, record)) :
    ∃ frame reason, binding = some b ∧ entry = .accepted frame ∧
      InterruptEntry.containedReason? frame.vector = some reason ∧
      reason = b.reason ∧ frame.currentSubject = b.faulting ∧
      record = recordOf reason frame := by
  unfold boundFor at h
  split at h
  · rename_i b' frame
    split at h
    · rename_i reason hreason
      split at h
      · rename_i hbound
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨frame, reason, rfl, rfl, hreason, hbound.1, hbound.2, rfl⟩
      · simp at h
    · simp at h
  · simp at h

/-- A delivery happens only for the bound class and subject, only when the
default would have contained the fault, and hands the bound handler exactly
`recordOf` the normalized frame.  The faulting subject was the live, runnable,
kernel-selected current subject; afterwards it is suspended (not runnable, not
current, not queued), the handler's inbox holds the record, every other inbox
is unchanged, and the capability state, context bank, and translations are
unchanged. -/
theorem delivered_exact sys entry handler record
    (h : (fault sys entry).2 = .delivered handler record) :
    ∃ b frame reason,
      sys.binding = some b ∧ handler = b.handler ∧ entry = .accepted frame ∧
      InterruptEntry.containedReason? frame.vector = some reason ∧ reason = b.reason ∧
      record = recordOf reason frame ∧ record.faulting = b.faulting ∧
      b.handler ≠ b.faulting ∧
      sys.core.scheduler.lifecycle.current = some b.faulting ∧
      sys.core.scheduler.lifecycle.capabilities.subjects b.faulting = true ∧
      sys.core.scheduler.lifecycle.runnable b.faulting = true ∧
      let next := (fault sys entry).1
      next.suspended = some b.faulting ∧
      next.inbox b.handler = some record ∧
      (∀ s, s ≠ b.handler → next.inbox s = sys.inbox s) ∧
      next.core.scheduler.lifecycle.runnable b.faulting = false ∧
      next.core.scheduler.lifecycle.current = none ∧
      b.faulting ∉ next.core.scheduler.ready ∧
      next.core.scheduler.lifecycle.capabilities = sys.core.scheduler.lifecycle.capabilities ∧
      next.core.contexts = sys.core.contexts ∧
      next.core.translations = sys.core.translations := by
  unfold fault at h
  split at h
  · rename_i hcontained
    split at h
    · simp [defaultStep] at h
    · rename_i b record' hbound
      split at h
      · rename_i havailable
        simp only [Action.delivered.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨frame, reason, hbinding, hentry, hreason, hreasonEq, hcurrent, hrecord⟩ :=
          boundFor_some _ _ _ _ hbound
        have hsuccess :
            (∃ r, (FaultDispatch.dispatch sys.core entry).action = .idle r) ∨
              ∃ r c, (FaultDispatch.dispatch sys.core entry).action = .dispatch r c := by
          revert hcontained
          cases (FaultDispatch.dispatch sys.core entry).action <;> simp [contained]
        obtain ⟨faulting, hcur, hlive, hrun⟩ :=
          FaultDispatch.successful_faulting_live_runnable sys.core entry hsuccess
        have hframeCurrent : frame.currentSubject = faulting := by
          subst hentry
          rcases hsuccess with ⟨r, hr⟩ | ⟨r, c, hr⟩
          · rcases FaultDispatch.idle_is_clean_empty sys.core _ r hr with ⟨f, hf, _⟩
            simp only [FaultDispatch.dispatch] at hr
            split at hr <;> try simp_all [FaultDispatch.halt, FaultDispatch.reject]
            all_goals split at hr <;> try simp_all [FaultDispatch.halt, FaultDispatch.reject]
            all_goals split at hr <;> try simp_all [FaultDispatch.halt, FaultDispatch.reject]
            all_goals split at hr <;> try simp_all [FaultDispatch.halt, FaultDispatch.reject]
            all_goals split at hr <;> try simp_all [FaultDispatch.halt, FaultDispatch.reject]
            all_goals split at hr <;> try simp_all [FaultDispatch.halt, FaultDispatch.reject]
            all_goals (try split at hr) <;> try simp_all [FaultDispatch.halt, FaultDispatch.reject]
            all_goals (try split at hr) <;> try simp_all [FaultDispatch.halt, FaultDispatch.reject]
            all_goals (try split at hr) <;> try simp_all [FaultDispatch.halt, FaultDispatch.reject]
            all_goals grind
          · simp only [FaultDispatch.dispatch] at hr
            split at hr <;> try simp_all [FaultDispatch.halt, FaultDispatch.reject]
            all_goals split at hr <;> try simp_all [FaultDispatch.halt, FaultDispatch.reject]
            all_goals split at hr <;> try simp_all [FaultDispatch.halt, FaultDispatch.reject]
            all_goals split at hr <;> try simp_all [FaultDispatch.halt, FaultDispatch.reject]
            all_goals split at hr <;> try simp_all [FaultDispatch.halt, FaultDispatch.reject]
            all_goals split at hr <;> try simp_all [FaultDispatch.halt, FaultDispatch.reject]
            all_goals (try split at hr) <;> try simp_all [FaultDispatch.halt, FaultDispatch.reject]
            all_goals (try split at hr) <;> try simp_all [FaultDispatch.halt, FaultDispatch.reject]
            all_goals (try split at hr) <;> try simp_all [FaultDispatch.halt, FaultDispatch.reject]
            all_goals grind
        have hfaulting : faulting = b.faulting := by rw [← hframeCurrent, hcurrent]
        subst hfaulting
        have hdistinct : b.handler ≠ b.faulting := by
          simp [handlerAvailable] at havailable
          exact havailable.1.1.1
        simp only [fault, hcontained, hbound, havailable, ite_true]
        refine ⟨b, frame, reason, hbinding, rfl, hentry, hreason, hreasonEq, hrecord, ?_,
          hdistinct, hcur, hlive, hrun, ?_⟩
        · rw [hrecord]; simp [recordOf, hframeCurrent]
        · simp only [setInbox, suspendCore]
          refine ⟨by simp, by simp, ?_, by simp, by simp, by simp, by simp, by simp, by simp⟩
          intro s hs
          simp [hs]
      · simp [defaultStep] at h
  · simp [defaultStep] at h

/-- The delivered record is a function of the binding's fault fields only:
two entries that agree on the class vector, faulting subject, saved RIP, and
error word deliver the same record, whatever else differs. -/
theorem record_fields_only reason (left right : InterruptEntry.NormalizedFrame)
    (hvector : left.vector = right.vector) (hsubject : left.currentSubject = right.currentSubject)
    (hrip : left.rip = right.rip) (herror : left.errorCode = right.errorCode) :
    recordOf reason left = recordOf reason right := by
  simp [recordOf, hvector, hsubject, hrip, herror]

/-- No amplification at delivery: the capability state (every holder's slots,
live subjects, and objects) is unchanged by any fault step that delivers. -/
theorem delivered_no_amplification sys entry handler record
    (h : (fault sys entry).2 = .delivered handler record) :
    (fault sys entry).1.core.scheduler.lifecycle.capabilities =
      sys.core.scheduler.lifecycle.capabilities := by
  obtain ⟨b, frame, reason, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hcaps, _⟩ :=
    delivered_exact sys entry handler record h
  exact hcaps

theorem receive_core sys subject : (receive sys subject).1.core = sys.core := by
  unfold receive; split <;> rfl

/-- A subject receives only the record in its own inbox. -/
theorem received_own_inbox sys subject record
    (h : (receive sys subject).2 = .received record) :
    sys.inbox subject = some record := by
  unfold receive at h
  split at h <;> simp_all

/-- The handler's reply terminates exactly the suspended, bound subject with
the existing cleanup: it is no longer live or runnable, is neither current nor
queued, and has no resumable context.  Nothing is suspended afterwards. -/
theorem reply_terminates sys subject decision faulting
    (h : (reply sys subject decision).2 = .terminated faulting) :
    ∃ b, sys.binding = some b ∧ b.handler = subject ∧ b.faulting = faulting ∧
      sys.suspended = some faulting ∧
      let next := (reply sys subject decision).1
      next.core = ResumablePreemption.cleanupSubject sys.core faulting ∧
      next.suspended = none ∧
      next.core.scheduler.lifecycle.capabilities.subjects faulting = false ∧
      faulting ∉ next.core.scheduler.ready ∧
      next.core.scheduler.lifecycle.current ≠ some faulting ∧
      ResumablePreemption.contextFor next.core.contexts faulting = none := by
  unfold reply at h ⊢
  split at h
  · rename_i b f hb hs
    split at h
    · rename_i hbound
      simp only [Action.terminated.injEq] at h
      subst h
      refine ⟨b, hb, hbound.1, hbound.2, hs, ?_⟩
      simp only [hbound, and_self, ite_true]
      exact ⟨trivial, trivial, ResumablePreemption.cleanup_terminates_subject _ _,
        (ResumablePreemption.cleanup_removes_scheduler_membership _ _).1,
        (ResumablePreemption.cleanup_removes_scheduler_membership _ _).2,
        ResumablePreemption.cleanup_removes_context _ _⟩
    · simp at h
  · simp at h
  · simp at h

/-- Only the bound handler's reply terminates; any other subject's reply is a
state-preserving rejection. -/
theorem reply_other_rejected sys subject decision b
    (hb : sys.binding = some b) (hother : subject ≠ b.handler) :
    reply sys subject decision = (sys, .rejected (match sys.suspended with
      | some _ => .notHandler | none => .nothingSuspended)) := by
  unfold reply
  cases hs : sys.suspended <;> simp [hb, hs]
  intro h; exact absurd h.symm hother

/-- No amplification at reply: cleanup only removes capability slots, so every
slot any holder (in particular the handler) has afterwards it had before. -/
theorem reply_no_amplification sys subject decision holder slot capability
    (h : (reply sys subject decision).1.core.scheduler.lifecycle.capabilities.slots
      holder slot = some capability) :
    sys.core.scheduler.lifecycle.capabilities.slots holder slot = some capability := by
  unfold reply at h
  split at h
  · split at h
    · simp only [ResumablePreemption.cleanupSubject,
        ResumablePreemption.retireOwnedAddressSpaces, SubjectLifecycle.terminateState,
        SubjectLifecycle.terminatedCapabilities] at h
      split at h
      · simp at h
      · rename_i cap hcap
        split at h
        · simp at h
        · simp only [Option.some.injEq] at h
          subst h
          split at hcap
          · simp at hcap
          · rename_i c hc
            split at hcap
            · simp at hcap
            · simp only [Option.some.injEq] at hcap
              subst hcap
              exact hc
    · exact h
  · exact h
  · exact h

/-- The handler's inbox is the only inbox the binding ever fills. -/
def InboxBound (sys : System) : Prop :=
  ∀ s record, sys.inbox s = some record → ∃ b, sys.binding = some b ∧ s = b.handler

theorem fault_preserves_binding sys entry : (fault sys entry).1.binding = sys.binding := by
  unfold fault defaultStep
  split
  · split
    · rfl
    · split <;> rfl
  · rfl

theorem receive_preserves_binding sys subject :
    (receive sys subject).1.binding = sys.binding := by
  unfold receive; split <;> rfl

theorem reply_preserves_binding sys subject decision :
    (reply sys subject decision).1.binding = sys.binding := by
  unfold reply
  split
  · split <;> rfl
  · rfl
  · rfl

theorem step_preserves_binding sys op : (step sys op).1.binding = sys.binding := by
  cases op with
  | fault entry => exact fault_preserves_binding sys entry
  | receive subject => exact receive_preserves_binding sys subject
  | reply subject decision => exact reply_preserves_binding sys subject decision

/-- A subject that is not the bound handler never receives a record: the
inbox invariant holds initially (all inboxes empty) and every step keeps it. -/
theorem step_preserves_inboxBound sys op (h : InboxBound sys) :
    InboxBound (step sys op).1 := by
  intro s record hrecord
  rw [step_preserves_binding]
  cases op with
  | fault entry =>
      simp only [step] at hrecord
      unfold fault defaultStep at hrecord
      split at hrecord
      · split at hrecord
        · exact h s record hrecord
        · rename_i b r hbound
          split at hrecord
          · simp only [setInbox] at hrecord
            split at hrecord
            · rename_i hs
              obtain ⟨frame, reason, hbinding, _⟩ := boundFor_some _ _ _ _ hbound
              exact ⟨b, hbinding, hs⟩
            · exact h s record hrecord
          · exact h s record hrecord
      · exact h s record hrecord
  | receive subject =>
      simp only [step, receive] at hrecord
      split at hrecord
      · simp only [setInbox] at hrecord
        split at hrecord
        · simp at hrecord
        · exact h s record hrecord
      · exact h s record hrecord
  | reply subject decision =>
      simp only [step, reply] at hrecord
      split at hrecord
      · split at hrecord <;> exact h s record hrecord
      · exact h s record hrecord
      · exact h s record hrecord

theorem received_only_by_handler sys subject record (hinv : InboxBound sys)
    (h : (receive sys subject).2 = .received record) :
    ∃ b, sys.binding = some b ∧ subject = b.handler :=
  hinv subject record (received_own_inbox sys subject record h)

/-! ## Concrete three-subject system and the boot witness

Subject A (1) is current; B (2) is the queued survivor; C (3) is the live
handler, bound for divide errors raised by A.  This is the shared containment
witness state with C added as a live subject. -/

/-- The image's boot-fixed binding: `#DE` from A (1) goes to C (3). -/
def bootBinding : Binding := { reason := .divideError, faulting := 1, handler := 3 }

def witnessCore : ResumablePreemption.State :=
  let s := DirectPortContainment.witnessSchedule
  { s with scheduler := { s.scheduler with
      lifecycle := { s.scheduler.lifecycle with
        capabilities := { s.scheduler.lifecycle.capabilities with
          subjects := fun subject => subject = 1 || subject = 2 || subject = 3 }
        issuedSubjects := fun subject => subject = 1 || subject = 2 || subject = 3 } } }

def witnessSystem : System := { core := witnessCore, binding := some bootBinding }

def unboundSystem : System := { core := witnessCore, binding := none }

def pendingRecord : FaultRecord :=
  { reason := .divideError, vector := 0, faulting := 1, address := 0, errorWord := 0 }

/-- C already holds an undelivered record: the handler is busy. -/
def busySystem : System :=
  { witnessSystem with inbox := setInbox witnessSystem.inbox 3 (some pendingRecord) }

/-- The system after the divide error has been delivered. -/
def deliveredSystem : System := (fault witnessSystem UserFaultContainmentVocabulary.divideErrorEntry).1

/-- A divide error raised by B (2) while A is current: the default rejects it
as stale, and the binding does not apply. -/
def staleDivideEntry : InterruptEntry.Result :=
  match UserFaultContainmentVocabulary.divideErrorEntry with
  | .accepted frame => .accepted { frame with currentSubject := 2, activeAddressSpace := 2 }
  | other => other

def encodeAction : Action → UInt64
  | .delivered handler record =>
      1 + UInt64.ofNat handler * 0x100 + record.reason.code * 0x10000 +
        UInt64.ofNat record.faulting * 0x1000000 + record.vector * 0x100000000
  | .default _ => 2
  | .terminated faulting => 3 + UInt64.ofNat faulting * 0x1000000
  | .received _ => 4
  | .rejected _ => 0

/-- Allocation-free generated witness for the fault-handler image.

`event = 0` is a fault: `vector` is the hardware vector, `subject` the
kernel-selected faulting subject, and `word` is 1 when the handler is blocked
receiving with an empty fault inbox.  The answer is the delivery word
(`1 | handler << 8 | reason << 16 | faulting << 24 | vector << 32`) for the
image's one binding, `#DE` from A (1) to C (3), and 2 ("take the image's
default path") for everything else, including any fault raised by C itself.

`event = 1` is the handler's reply: `vector` carries the suspended subject,
`subject` the replying subject, and `word` the decision (1 = terminate).  The
answer is `3 | faulting << 24` for the bound handler's terminate, and 0
(refused) otherwise.  Every other event is refused with 0. -/
@[export leanos_fault_handler_route]
def faultHandlerRoute (event vector subject word : UInt64) : UInt64 :=
  if event == 0 then
    if vector == 0 && subject == 1 && word == 1 then 0x01010301 else 2
  else if event == 1 then
    if vector == 1 && subject == 3 && word == 1 then 0x01000003 else 0
  else 0

/-- The generated witness answers exactly the model's encoded action on the
concrete system: the bound delivery, the unbound default, another class, a
busy handler, a stale fault from another subject, the bound handler's
terminate, and the refused replies (wrong subject, nothing suspended). -/
theorem faultHandlerRoute_agrees :
    faultHandlerRoute 0 0 1 1 =
        encodeAction (fault witnessSystem UserFaultContainmentVocabulary.divideErrorEntry).2 ∧
      faultHandlerRoute 0 0 1 1 ≠ faultHandlerRoute 0 3 1 1 ∧
      faultHandlerRoute 0 3 1 1 =
        encodeAction (fault witnessSystem UserFaultContainmentVocabulary.breakpointEntry).2 ∧
      faultHandlerRoute 0 0 1 0 =
        encodeAction (fault busySystem UserFaultContainmentVocabulary.divideErrorEntry).2 ∧
      faultHandlerRoute 0 0 2 1 = encodeAction (fault witnessSystem staleDivideEntry).2 ∧
      faultHandlerRoute 0 14 1 1 =
        encodeAction (fault witnessSystem DirectPortContainment.witnessEntry).2 ∧
      faultHandlerRoute 1 1 3 1 = encodeAction (reply deliveredSystem 3 .terminate).2 ∧
      faultHandlerRoute 1 1 2 1 = encodeAction (reply deliveredSystem 2 .terminate).2 ∧
      faultHandlerRoute 1 0 3 1 = encodeAction (reply witnessSystem 3 .terminate).2 := by
  native_decide

/-- With no handler bound, the same divide error is the existing containment:
A retired, B dispatched. -/
theorem unbound_witness_is_containment :
    (fault unboundSystem UserFaultContainmentVocabulary.divideErrorEntry).2 =
      .default (.dispatch .divideError DirectPortContainment.witnessSurvivorContext) := by
  native_decide

/-- The bound divide error delivers exactly A's record to C: class word 1
(`#DE`, vector 0), faulting subject 1, the saved RIP of the divide, and no
error word.  A is suspended and C's inbox holds the record. -/
theorem witness_delivery :
    (fault witnessSystem UserFaultContainmentVocabulary.divideErrorEntry).2 =
        .delivered 3 { reason := .divideError, vector := 0, faulting := 1
                       address := 0x400200, errorWord := 0 } ∧
      ({ reason := .divideError, vector := 0, faulting := 1, address := 0x400200,
          errorWord := 0 } : FaultRecord).words = (1, 1, 0x400200, 0) ∧
      deliveredSystem.suspended = some 1 ∧
      deliveredSystem.core.scheduler.lifecycle.runnable 1 = false ∧
      deliveredSystem.inbox 2 = none := by
  native_decide

/-- C's terminate retires A with the default cleanup; B's resources are
untouched and A is never resumed. -/
theorem witness_terminate :
    (reply deliveredSystem 3 .terminate).2 = .terminated 1 ∧
      (reply deliveredSystem 3 .terminate).1.core.scheduler.lifecycle.capabilities.subjects 1 =
        false ∧
      (reply deliveredSystem 3 .terminate).1.core.scheduler.lifecycle.capabilities.slots 2 7 =
        witnessCore.scheduler.lifecycle.capabilities.slots 2 7 := by
  native_decide

end LeanOS.FaultHandler
