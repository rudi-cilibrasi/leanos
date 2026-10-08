import LeanOS.Capability

/-!
# Notifications and reply capabilities (issue #471)

Two finite kernel objects layered over an unmodified `Capability.State`, in the
style of `DeviceCapability`, so every capability theorem (in particular
`Capability.copy_no_authority_amplification`, SC-CAP-AUTH) applies unchanged.

* A **notification** is an endpoint-kind capability object whose pending
  signal bits live in `System.notifications`. `signal` ORs bits into the word
  and never blocks; it needs the `send` right. `wait` needs `receive`: it takes
  and clears pending bits, or reports `blocked` while none are pending (the
  machine parks the waiter on the `BlockingIPC` waiter queue). Nothing is
  queued beyond the one word.
* A **reply capability** is created by the kernel when a client `call`s an
  endpoint and is recorded in the serving subject's reply slots
  (`System.replies`), outside the copyable capability slots. It names the
  caller and the caller's generation at the time of the call; it confers only
  the right to `reply` once to that caller; and no transition copies it.

Theorems: capability slots change only through capability operations
(no amplification), reply capabilities are created only by `call` and name
its caller, stale replies are rejected without effect, a reply is single-use,
an exhausted reply pool is a typed rejection without effect, and no
transition touches another subject's reply slots.
-/
namespace LeanOS.NotifyReply

open LeanOS.Capability

/-- The kernel-created authority to answer one call. -/
structure ReplyCap where
  caller : SubjectId
  callerGeneration : Nat
  deriving DecidableEq, Repr

structure System where
  caps : Capability.State
  /-- Pending signal bits of each notification object; `none` for objects
  that are not notifications. -/
  notifications : ObjectId → Option UInt64
  /-- The subject that receives calls on an endpoint object. -/
  endpointServer : ObjectId → Option SubjectId
  /-- Each subject's generation; termination advances it. -/
  generation : SubjectId → Nat
  alive : SubjectId → Bool
  /-- Number of reply slots each serving subject owns. -/
  replyCapacity : SubjectId → Nat
  replies : SubjectId → Nat → Option ReplyCap
  /-- The reply word most recently delivered to a caller. -/
  delivered : SubjectId → Option UInt64

inductive Transition where
  | cap (op : Capability.State → Capability.Outcome)
  | signal (subject : SubjectId) (slot : SlotId) (bits : UInt64)
  | wait (subject : SubjectId) (slot : SlotId)
  | call (subject : SubjectId) (slot : SlotId)
  | reply (subject : SubjectId) (replySlot : Nat) (word : UInt64)
  /-- Attempt to hand a reply capability to another subject. -/
  | copyReply (subject : SubjectId) (replySlot : Nat) (destination : SubjectId)
  | terminate (subject : SubjectId)

inductive Denial where
  | capability (reason : Capability.Denial)
  | notNotification
  | notEndpoint
  | missingRight
  | deadSubject
  | full
  | noReply
  | staleCaller
  | notCopyable
  deriving DecidableEq, Repr

inductive Reply where
  | accepted
  | woke (bits : UInt64)
  | blocked
  | called (replySlot : Nat)
  | rejected (reason : Denial)
  deriving DecidableEq, Repr

/-- The lowest free reply slot of `server`, if its pool is not exhausted. -/
def freeReplySlot (sys : System) (server : SubjectId) : Option Nat :=
  (List.range (sys.replyCapacity server)).find? fun r => (sys.replies server r).isNone

def setNotification (sys : System) (object : ObjectId) (bits : UInt64) : System :=
  { sys with notifications := fun o => if o = object then some bits else sys.notifications o }

/-- Record a fresh reply capability in `server`'s slot `r`. -/
def addReply (sys : System) (server : SubjectId) (r : Nat) (rc : ReplyCap) : System :=
  { sys with replies := fun s q => if s = server ∧ q = r then some rc else sys.replies s q }

/-- Consume `server`'s reply slot `r` and deliver `word` to `caller`. -/
def consumeReply (sys : System) (server : SubjectId) (r : Nat) (caller : SubjectId)
    (word : UInt64) : System :=
  { sys with
      replies := fun s q => if s = server ∧ q = r then none else sys.replies s q
      delivered := fun s => if s = caller then some word else sys.delivered s }

def terminateSubject (sys : System) (subject : SubjectId) : System :=
  { sys with
      alive := fun s => if s = subject then false else sys.alive s
      generation := fun s => if s = subject then sys.generation s + 1 else sys.generation s }

/-- One transition. Every rejection returns the system unchanged. -/
def step (sys : System) : Transition → System × Reply
  | .cap op => ({ sys with caps := (op sys.caps).state }, .accepted)
  | .signal subject slot bits =>
    match authorizeKind sys.caps subject slot .endpoint with
    | .error reason => (sys, .rejected (.capability reason))
    | .ok capability =>
      match sys.notifications capability.object with
      | none => (sys, .rejected .notNotification)
      | some pending =>
        if capability.rights.send then
          (setNotification sys capability.object (pending ||| bits), .accepted)
        else (sys, .rejected .missingRight)
  | .wait subject slot =>
    match authorizeKind sys.caps subject slot .endpoint with
    | .error reason => (sys, .rejected (.capability reason))
    | .ok capability =>
      match sys.notifications capability.object with
      | none => (sys, .rejected .notNotification)
      | some pending =>
        if !capability.rights.receive then (sys, .rejected .missingRight)
        else if pending == 0 then (sys, .blocked)
        else (setNotification sys capability.object 0, .woke pending)
  | .call subject slot =>
    match authorizeKind sys.caps subject slot .endpoint with
    | .error reason => (sys, .rejected (.capability reason))
    | .ok capability =>
      match sys.endpointServer capability.object with
      | none => (sys, .rejected .notEndpoint)
      | some server =>
        if !capability.rights.send then (sys, .rejected .missingRight)
        else if !sys.alive subject || !sys.alive server then (sys, .rejected .deadSubject)
        else match freeReplySlot sys server with
          | none => (sys, .rejected .full)
          | some r =>
            (addReply sys server r ⟨subject, sys.generation subject⟩, .called r)
  | .reply subject replySlot word =>
    match sys.replies subject replySlot with
    | none => (sys, .rejected .noReply)
    | some rc =>
      if !sys.alive rc.caller || sys.generation rc.caller != rc.callerGeneration then
        (sys, .rejected .staleCaller)
      else (consumeReply sys subject replySlot rc.caller word, .accepted)
  | .copyReply _ _ _ => (sys, .rejected .notCopyable)
  | .terminate subject => (terminateSubject sys subject, .accepted)

/-! ## No authority amplification -/

/-- Only capability operations change the capability state; notifications,
calls, replies, reply copies and terminations install no capability. Every
capability change is therefore a `Capability` operation, to which
`Capability.copy_no_authority_amplification` (SC-CAP-AUTH) applies. -/
theorem non_cap_step_caps (sys : System) (t : Transition) (h : ∀ op, t ≠ .cap op) :
    (step sys t).1.caps = sys.caps := by
  cases t with
  | cap op => exact absurd rfl (h op)
  | _ =>
    simp only [step]
    repeat' split
    all_goals simp [setNotification, addReply, consumeReply, terminateSubject]

/-- A reply capability appears only through `call`, and it names exactly the
calling subject at its current generation. -/
theorem reply_created_only_by_call (sys : System) (t : Transition)
    (server : SubjectId) (r : Nat) (rc : ReplyCap)
    (hnew : (step sys t).1.replies server r = some rc)
    (hold : sys.replies server r ≠ some rc) :
    ∃ slot, t = .call rc.caller slot ∧ rc.callerGeneration = sys.generation rc.caller := by
  cases t with
  | call client slot =>
    simp only [step] at hnew
    repeat' split at hnew
    all_goals first
      | exact absurd hnew hold
      | (simp only [addReply] at hnew
         split at hnew
         · simp only [Option.some.injEq] at hnew
           subst hnew; exact ⟨slot, rfl, rfl⟩
         · exact absurd hnew hold)
  | _ =>
    simp only [step] at hnew
    repeat' split at hnew
    all_goals first
      | exact absurd hnew hold
      | (simp at hnew; exact absurd hnew hold)
      | (simp only [consumeReply] at hnew; split at hnew
         · simp at hnew
         · exact absurd hnew hold)

/-! ## No stale reuse, single use, exhaustion -/

/-- A reply whose caller has terminated, or whose caller's identity has moved
to a new generation, is rejected and changes nothing. -/
theorem stale_reply_rejected (sys : System) (server : SubjectId) (r : Nat)
    (rc : ReplyCap) (word : UInt64) (hreply : sys.replies server r = some rc)
    (hstale : sys.alive rc.caller = false ∨ sys.generation rc.caller ≠ rc.callerGeneration) :
    step sys (.reply server r word) = (sys, .rejected .staleCaller) := by
  rcases hstale with h | h
  · simp [step, hreply, h]
  · simp [step, hreply, h]

/-- A reply consumes its reply capability: replying again through the same
slot is rejected and changes nothing. -/
theorem reply_single_use (sys : System) (server : SubjectId) (r : Nat)
    (word word' : UInt64) (h : (step sys (.reply server r word)).2 = .accepted) :
    step (step sys (.reply server r word)).1 (.reply server r word') =
      ((step sys (.reply server r word)).1, .rejected .noReply) := by
  cases hrc : sys.replies server r with
  | none => simp [step, hrc] at h
  | some rc =>
    by_cases hs : (!sys.alive rc.caller || sys.generation rc.caller != rc.callerGeneration) = true
    · simp only [step, hrc, hs] at h
      cases h
    · simp only [step, hrc, hs]
      simp [consumeReply]

/-- A reply capability can never be handed to another subject. -/
theorem copyReply_rejected (sys : System) (server : SubjectId) (r : Nat)
    (destination : SubjectId) :
    step sys (.copyReply server r destination) = (sys, .rejected .notCopyable) := rfl

/-- A call to a server whose reply pool is exhausted is a typed rejection and
changes nothing. -/
theorem call_exhausted_unchanged (sys : System) (client : SubjectId) (slot : SlotId)
    (capability : Capability) (server : SubjectId)
    (hcap : authorizeKind sys.caps client slot .endpoint = .ok capability)
    (hserver : sys.endpointServer capability.object = some server)
    (hsend : capability.rights.send = true)
    (halive : sys.alive client = true ∧ sys.alive server = true)
    (hfull : freeReplySlot sys server = none) :
    step sys (.call client slot) = (sys, .rejected .full) := by
  simp [step, hcap, hserver, hsend, halive.1, halive.2, hfull]

/-- Signalling without the `send` right is rejected and changes nothing. -/
theorem signal_without_send_rejected (sys : System) (subject : SubjectId) (slot : SlotId)
    (bits : UInt64) (capability : Capability) (pending : UInt64)
    (hcap : authorizeKind sys.caps subject slot .endpoint = .ok capability)
    (hnote : sys.notifications capability.object = some pending)
    (hsend : capability.rights.send = false) :
    step sys (.signal subject slot bits) = (sys, .rejected .missingRight) := by
  simp [step, hcap, hnote, hsend]

/-! ## Budget preservation -/

/-- No transition changes the reply slots of a subject other than the server
it addresses: a call fills one slot of the called endpoint's server, a reply
empties one slot of the replying subject, and nothing else touches them. -/
theorem replies_change_only_at_server (sys : System) (t : Transition) (other : SubjectId)
    (hchanged : (step sys t).1.replies other ≠ sys.replies other) :
    (∃ client slot capability, t = .call client slot ∧
        authorizeKind sys.caps client slot .endpoint = .ok capability ∧
        sys.endpointServer capability.object = some other) ∨
    (∃ r word, t = .reply other r word) := by
  cases t with
  | call client slot =>
    simp only [step] at hchanged
    split at hchanged
    · exact absurd rfl hchanged
    · rename_i capability hcap
      split at hchanged
      · exact absurd rfl hchanged
      · rename_i server hserver
        repeat' split at hchanged
        all_goals first
          | exact absurd rfl hchanged
          | (by_cases hos : other = server
             · subst hos; exact .inl ⟨client, slot, capability, rfl, hcap, hserver⟩
             · exact absurd (by funext q; simp [addReply, hos]) hchanged)
  | reply s r w =>
    simp only [step] at hchanged
    repeat' split at hchanged
    all_goals first
      | exact absurd rfl hchanged
      | (by_cases hos : other = s
         · subst hos; exact .inr ⟨r, w, rfl⟩
         · exact absurd (by funext q; simp [consumeReply, hos]) hchanged)
  | _ =>
    simp only [step] at hchanged
    repeat' split at hchanged
    all_goals first
      | exact absurd rfl hchanged
      | exact absurd (by simp [setNotification, terminateSubject]) hchanged


/-! ## The boot scenario and its generated witness

Subjects 1 (client A) and 2 (server B). Object 20 is a notification: A holds
it with `send`, B with `receive`. Object 10 is B's endpoint: A holds it with
`send`. B has one reply slot. -/

def demoCaps : Capability.State :=
  { subjects := fun s => s = 1 ∨ s = 2
    objects := fun o => o = 10 ∨ o = 20
    kinds := fun o => if o = 10 ∨ o = 20 then some .endpoint else none
    slots := fun s slot =>
      if s = 1 ∧ slot = 0 then some { object := 20, kind := .endpoint, rights := { send := true } }
      else if s = 1 ∧ slot = 1 then some { object := 10, kind := .endpoint, rights := { send := true } }
      else if s = 2 ∧ slot = 0 then
        some { object := 20, kind := .endpoint, rights := { receive := true } }
      else none }

def demoSystem : System :=
  { caps := demoCaps
    notifications := fun o => if o = 20 then some 0 else none
    endpointServer := fun o => if o = 10 then some 2 else none
    generation := fun _ => 0
    alive := fun s => s = 1 ∨ s = 2
    replyCapacity := fun s => if s = 2 then 1 else 0
    replies := fun _ _ => none
    delivered := fun _ => none }

/-- The machine scenario: B waits (nothing pending), A signals bits 5, B's
wait returns them, A calls B, B replies `0x4c45414e` once, and a second
reply is rejected. -/
def scenario : List Transition :=
  [.wait 2 0, .signal 1 0 5, .wait 2 0, .call 1 1, .reply 2 0 0x4c45414e,
   .reply 2 0 0x4c45414e]

/-- Rejected edges the oracle also exercises: B signalling without `send`,
B handing its reply capability to A, a call whose caller then terminates
followed by a reply to it. -/
def negativeScript : List Transition :=
  [.signal 2 0 1, .call 1 1, .copyReply 2 0 1, .terminate 1, .reply 2 0 7]

def runReplies (sys : System) : List Transition → List Reply
  | [] => []
  | t :: ts => (step sys t).2 :: runReplies (step sys t).1 ts

def denialCode : Denial → UInt64
  | .capability _ => 1 | .notNotification => 2 | .notEndpoint => 3
  | .missingRight => 4 | .deadSubject => 5 | .full => 6 | .noReply => 7
  | .staleCaller => 8 | .notCopyable => 9

def replyCode : Reply → UInt64
  | .accepted => 1
  | .blocked => 2
  | .woke bits => 0x100 + bits
  | .called r => 0x200 + r.toUInt64
  | .rejected d => 0x1000 + denialCode d

/-- Operation codes on the machine boundary. -/
def opCode : Transition → UInt64
  | .cap _ => 0 | .signal .. => 1 | .wait .. => 2 | .call .. => 3
  | .reply .. => 4 | .copyReply .. => 5 | .terminate _ => 6

def subjectOf : Transition → UInt64
  | .cap _ => 0 | .signal s .. => s.toUInt64 | .wait s .. => s.toUInt64
  | .call s .. => s.toUInt64 | .reply s .. => s.toUInt64
  | .copyReply s .. => s.toUInt64 | .terminate s => s.toUInt64

/-- Allocation-free generated witness for the two scripts: script 0 is the
machine scenario, script 1 the negative edges. It returns the model's reply
code for the scripted edge `(script, step, op, subject)`, and 0 for anything
that is not a scripted edge. The words are literals so the export needs no
Lean runtime (ADR 0002); `notifyReplyEvent_agrees` ties them to `step`. -/
@[export leanos_notify_reply_event]
def notifyReplyEvent (script stepIndex operation subject : UInt64) : UInt64 :=
  if script == 0 then
    if stepIndex == 0 && operation == 2 && subject == 2 then 2
    else if stepIndex == 1 && operation == 1 && subject == 1 then 1
    else if stepIndex == 2 && operation == 2 && subject == 2 then 0x105
    else if stepIndex == 3 && operation == 3 && subject == 1 then 0x200
    else if stepIndex == 4 && operation == 4 && subject == 2 then 1
    else if stepIndex == 5 && operation == 4 && subject == 2 then 0x1007
    else 0
  else if script == 1 then
    if stepIndex == 0 && operation == 1 && subject == 2 then 0x1004
    else if stepIndex == 1 && operation == 3 && subject == 1 then 0x200
    else if stepIndex == 2 && operation == 5 && subject == 2 then 0x1009
    else if stepIndex == 3 && operation == 6 && subject == 1 then 1
    else if stepIndex == 4 && operation == 4 && subject == 2 then 0x1008
    else 0
  else 0

def scriptCodes (script : UInt64) (ts : List Transition) : List UInt64 :=
  (List.range ts.length).zip ts |>.map fun (i, t) =>
    notifyReplyEvent script i.toUInt64 (opCode t) (subjectOf t)

/-- The generated witness returns exactly the model's replies along both
scripts. -/
theorem notifyReplyEvent_agrees :
    scriptCodes 0 scenario = (runReplies demoSystem scenario).map replyCode ∧
    scriptCodes 1 negativeScript = (runReplies demoSystem negativeScript).map replyCode := by
  decide

/-- Off-script edges are refused (the witness answers 0, a code no reply
has). -/
theorem notifyReplyEvent_unknown_zero (script stepIndex operation subject : UInt64)
    (h : script ≠ 0 ∧ script ≠ 1) :
    notifyReplyEvent script stepIndex operation subject = 0 := by
  simp [notifyReplyEvent, h.1, h.2]

end LeanOS.NotifyReply
