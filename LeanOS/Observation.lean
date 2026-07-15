import LeanOS.IPCSyscall
import LeanOS.UserCopy

/-!
# Observer-relative one-step isolation

This is a small sequential unwinding model for the operation classes already
present in LeanOS.  An observer sees its liveness, capability-slot rights,
authorized bytes, owned virtual mappings, syscall reply, declared endpoint
deliveries, and the explicitly visible scheduler selection.  Raw object and
frame identifiers are deliberately absent from the view.

The theorem is termination-insensitive and applies only to steps whose footprint
is private to an unrelated actor.  Capability delivery/revocation involving the
observer, endpoint delivery to the observer, global resource outcomes, and
scheduler selection are explicit channels and therefore are not called silent.
-/
namespace LeanOS.Observation

open LeanOS
set_option linter.unusedSimpArgs false

abbrev SubjectId := Capability.SubjectId
abbrev SlotId := Capability.SlotId
abbrev Page := VirtualMapping.VirtualPage
abbrev Address := Nat

structure Delivery where
  /-- Observer-local endpoint handle, not a raw kernel object identifier. -/
  handle : SlotId
  sender : SubjectId
  word0 : UInt64
  word1 : UInt64
  deriving BEq, DecidableEq, Repr

inductive Reply where
  | none | accepted | rejected (code : Nat) | access (allowed : Bool)
  | allocated (token : Nat) | exhausted | ipcFull | ipcEmpty
  | ipcDelivered (delivery : Delivery)
  deriving BEq, DecidableEq, Repr

structure State where
  live : SubjectId -> Bool
  held : SubjectId -> SlotId -> Option Capability.Rights
  /-- Bytes in the actor-local, non-aliased region covered by the theorem. -/
  authorizedBytes : SubjectId -> Address -> UInt8
  /-- Explicitly shared bytes, visible to every authorized participant here. -/
  sharedBytes : Address -> UInt8
  ownedMappings : SubjectId -> Page -> Option VirtualMapping.Permissions
  reply : SubjectId -> Reply
  deliveries : SubjectId -> List Delivery
  privateSecret : SubjectId -> Nat
  resourcesRemaining : Nat
  schedulerCurrent : Option SubjectId

/-- Everything directly visible to one subject.  Object and frame identifiers
are not represented: capabilities are observer-local slots plus attenuated
rights, and mappings expose permissions only. -/
structure View where
  live : Bool
  held : SlotId -> Option Capability.Rights
  authorizedBytes : Address -> UInt8
  sharedBytes : Address -> UInt8
  ownedMappings : Page -> Option VirtualMapping.Permissions
  reply : Reply
  deliveries : List Delivery
  schedulerCurrent : Option SubjectId

@[ext]
theorem View.ext {left right : View}
    (hlive : left.live = right.live)
    (hheld : left.held = right.held)
    (hbytes : left.authorizedBytes = right.authorizedBytes)
    (hsharedBytes : left.sharedBytes = right.sharedBytes)
    (hmappings : left.ownedMappings = right.ownedMappings)
    (hreply : left.reply = right.reply)
    (hdeliveries : left.deliveries = right.deliveries)
    (hscheduler : left.schedulerCurrent = right.schedulerCurrent) :
    left = right := by
  cases left
  cases right
  simp_all

def observe (observer : SubjectId) (state : State) : View :=
  { live := state.live observer
    held := state.held observer
    authorizedBytes := state.authorizedBytes observer
    sharedBytes := state.sharedBytes
    ownedMappings := state.ownedMappings observer
    reply := state.reply observer
    deliveries := state.deliveries observer
    schedulerCurrent := state.schedulerCurrent }

/-- Observer-relative low equivalence is equality of the complete declared view. -/
def LowEquiv (observer : SubjectId) (left right : State) : Prop :=
  observe observer left = observe observer right

def set1 (values : Nat -> α) (key : Nat) (value : α) : Nat -> α :=
  fun candidate => if candidate = key then value else values candidate

def set2 (values : Nat -> Nat -> α) (first second : Nat) (value : α) : Nat -> Nat -> α :=
  fun candidate candidateSecond =>
    if candidate = first && candidateSecond = second then value
    else values candidate candidateSecond

inductive Step where
  | privateWrite (actor : SubjectId) (address : Address) (value : UInt8)
  | sharedWrite (actor : SubjectId) (address : Address) (value : UInt8)
  | map (actor : SubjectId) (page : Page) (permissions : VirtualMapping.Permissions)
  | unmap (actor : SubjectId) (page : Page)
  | access (actor : SubjectId) (allowed : Bool)
  | boundedCopy (actor : SubjectId) (start : Address) (values : List UInt8)
  | delegate (actor recipient : SubjectId) (slot : SlotId) (rights : Capability.Rights)
  | revoke (actor victim : SubjectId) (slot : SlotId)
  | reject (actor : SubjectId) (code : Nat)
  | send (actor recipient : SubjectId) (handle : SlotId) (word0 word1 : UInt64)
  | receive (actor : SubjectId)
  | allocate (actor : SubjectId)
  | schedule (next : Option SubjectId)
  deriving Repr

def writeBytes (bytes : Address -> UInt8) (address : Address) :
    List UInt8 -> Address -> UInt8
  | [] => bytes
  | value :: values => writeBytes (set1 bytes address value) (address + 1) values

def transition (state : State) : Step -> State
  | .privateWrite actor address value =>
      { state with authorizedBytes := set2 state.authorizedBytes actor address value }
  | .sharedWrite _ address value =>
      { state with sharedBytes := set1 state.sharedBytes address value }
  | .map actor page permissions =>
      { state with
        ownedMappings := set2 state.ownedMappings actor page (some permissions)
        reply := set1 state.reply actor .accepted }
  | .unmap actor page =>
      { state with
        ownedMappings := set2 state.ownedMappings actor page none
        reply := set1 state.reply actor .accepted }
  | .access actor allowed =>
      { state with reply := set1 state.reply actor (.access allowed) }
  | .boundedCopy actor start values =>
      { state with
        authorizedBytes := fun subject =>
          if subject = actor then writeBytes (state.authorizedBytes subject) start values
          else state.authorizedBytes subject
        reply := set1 state.reply actor .accepted }
  | .delegate _ recipient slot rights =>
      { state with held := set2 state.held recipient slot (some rights) }
  | .revoke _ victim slot =>
      { state with held := set2 state.held victim slot none }
  | .reject actor code =>
      { state with reply := set1 state.reply actor (.rejected code) }
  | .send actor recipient handle word0 word1 =>
      let delivery : Delivery :=
        { handle := handle
          sender := actor
          word0 := word0
          word1 := word1 }
      let empty := (state.deliveries recipient).isEmpty
      { state with
        deliveries := if empty then set1 state.deliveries recipient [delivery]
          else state.deliveries
        reply := set1 state.reply actor (if empty then .accepted else .ipcFull) }
  | .receive actor =>
      match state.deliveries actor with
      | [] => { state with reply := set1 state.reply actor .ipcEmpty }
      | delivery :: remaining =>
          { state with
            deliveries := set1 state.deliveries actor remaining
            reply := set1 state.reply actor (.ipcDelivered delivery) }
  | .allocate actor =>
      if state.resourcesRemaining = 0 then
        { state with reply := set1 state.reply actor .exhausted }
      else
        { state with
          resourcesRemaining := state.resourcesRemaining - 1
          reply := set1 state.reply actor (.allocated state.resourcesRemaining) }
  | .schedule next => { state with schedulerCurrent := next }

/-- The exact side condition for an operation to be private to the observer.
Resource allocation and scheduling are intentionally absent. -/
def SilentFor (observer : SubjectId) : Step -> Prop
  | .privateWrite actor _ _ | .map actor _ _ | .unmap actor _ |
      .access actor _ | .boundedCopy actor _ _ | .reject actor _ |
      .receive actor => observer != actor
  | .delegate _ recipient _ _ => observer != recipient
  | .revoke _ victim _ => observer != victim
  | .send actor recipient _ _ _ => observer != actor ∧ observer != recipient
  | .sharedWrite _ _ _ | .allocate _ | .schedule _ => False

theorem silent_observe_unchanged (observer : SubjectId) (state : State) (step : Step)
    (hsilent : SilentFor observer step) :
    observe observer (transition state step) = observe observer state := by
  cases step <;> apply View.ext <;>
    simp_all [observe, transition, SilentFor, set1, set2] <;>
    (try split <;> simp_all [set1])
  all_goals funext key
  all_goals simp_all [observe, transition, SilentFor, set1, set2]

/-- Scoped one-step unwinding: independently chosen high steps preserve an
observer's low equivalence when each step is silent for that observer. -/
theorem silent_steps_lowEquiv (observer : SubjectId) (left right : State)
    (leftStep rightStep : Step) (hlow : LowEquiv observer left right)
    (hleft : SilentFor observer leftStep) (hright : SilentFor observer rightStep) :
    LowEquiv observer (transition left leftStep) (transition right rightStep) := by
  rw [LowEquiv, silent_observe_unchanged observer left leftStep hleft,
    silent_observe_unchanged observer right rightStep hright]
  exact hlow

/-- The observer-visible reply is consequently equal after every scoped step. -/
theorem silent_steps_equal_reply (observer : SubjectId) (left right : State)
    (leftStep rightStep : Step) (hlow : LowEquiv observer left right)
    (hleft : SilentFor observer leftStep) (hright : SilentFor observer rightStep) :
    (transition left leftStep).reply observer = (transition right rightStep).reply observer := by
  have h := silent_steps_lowEquiv observer left right leftStep rightStep hlow hleft hright
  simpa [LowEquiv, observe] using congrArg View.reply h

private def emptyState (secret : SubjectId -> Nat) (resources : Nat) : State :=
  { live := fun subject => subject < 2
    held := fun _ _ => none
    authorizedBytes := fun _ _ => 0
    sharedBytes := fun _ => 0
    ownedMappings := fun _ _ => none
    reply := fun _ => .none
    deliveries := fun _ => []
    privateSecret := secret
    resourcesRemaining := resources
    schedulerCurrent := none }

private def leftSecret := emptyState (fun subject => if subject = 1 then 7 else 0) 1
private def rightSecret := emptyState (fun subject => if subject = 1 then 99 else 0) 1

-- Paired private states are indistinguishable to subject 0.
example : LowEquiv 0 leftSecret rightSecret := by rfl
example : LowEquiv 0 (transition leftSecret (.privateWrite 1 4 0xaa))
    (transition rightSecret (.privateWrite 1 4 0xbb)) := by rfl
example : LowEquiv 0 (transition leftSecret (.privateWrite 1 4 0xaa))
    (transition rightSecret (.map 1 8 { read := true })) := by
  exact silent_steps_lowEquiv 0 leftSecret rightSecret _ _ (by rfl)
    (by simp [SilentFor]) (by simp [SilentFor])
example : LowEquiv 0 (transition leftSecret (.map 1 8 { read := true }))
    (transition rightSecret (.map 1 8 { read := true })) := by rfl
example : LowEquiv 0 (transition leftSecret (.unmap 1 8))
    (transition rightSecret (.unmap 1 8)) := by rfl
example : LowEquiv 0 (transition leftSecret (.access 1 true))
    (transition rightSecret (.access 1 true)) := by rfl
example : LowEquiv 0 (transition leftSecret (.boundedCopy 1 0 [1, 2, 3]))
    (transition rightSecret (.boundedCopy 1 0 [1, 2, 3])) := by rfl
example : LowEquiv 0 (transition leftSecret (.delegate 1 1 3 { read := true }))
    (transition rightSecret (.delegate 1 1 3 { read := true })) := by rfl
example : LowEquiv 0 (transition leftSecret (.revoke 1 1 3))
    (transition rightSecret (.revoke 1 1 3)) := by rfl
example : LowEquiv 0 (transition leftSecret (.reject 1 4))
    (transition rightSecret (.reject 1 4)) := by rfl
example : LowEquiv 0 (transition leftSecret (.send 1 1 2 0x41 0x42))
    (transition rightSecret (.send 1 1 2 0x41 0x42)) := by rfl
example : LowEquiv 0 (transition leftSecret (.receive 1))
    (transition rightSecret (.receive 1)) := by rfl
example :
    let delivery : Delivery := { handle := 2, sender := 1, word0 := 0x41, word1 := 0x42 }
    let left := { leftSecret with deliveries := set1 leftSecret.deliveries 0 [delivery] }
    let right := { rightSecret with deliveries := set1 rightSecret.deliveries 0 [delivery] }
    (transition left (.receive 0)).reply 0 =
      .ipcDelivered delivery ∧
    (transition left (.receive 0)).reply 0 = (transition right (.receive 0)).reply 0 := by
  simp [transition, set1]

-- Deliberate declared channels permit an observer-visible difference.
example : ¬ LowEquiv 0 leftSecret
    (transition rightSecret (.delegate 1 0 3 { read := true })) := by
  intro h
  have hheld := congrArg (fun view => view.held 3) h
  simp [LowEquiv, observe, transition, set2, leftSecret, rightSecret, emptyState] at hheld
example : ¬ LowEquiv 0 leftSecret
    (transition rightSecret (.send 1 0 2 0x41 0x42)) := by
  intro h
  have hdeliveries := congrArg View.deliveries h
  simp [LowEquiv, observe, transition, set1, leftSecret, rightSecret, emptyState] at hdeliveries
-- Shared/aliased memory is an explicit channel, not a silent private write.
example : ¬ LowEquiv 0 leftSecret
    (transition rightSecret (.sharedWrite 1 4 0xaa)) := by
  intro h
  have hbytes := congrArg (fun view => view.sharedBytes 4) h
  simp [LowEquiv, observe, transition, set1, leftSecret, rightSecret, emptyState] at hbytes
example : ¬ LowEquiv 0
    (transition { leftSecret with deliveries :=
      (set1 leftSecret.deliveries 1
        [{ handle := 2
           sender := 0
           word0 := 1
           word1 := 2 }]) }
      (.send 0 1 2 0x41 0x42))
    (transition rightSecret (.send 0 1 2 0x41 0x42)) := by
  intro h
  have hreply := congrArg View.reply h
  simp [LowEquiv, observe, transition, set1, leftSecret, rightSecret, emptyState] at hreply
example : ¬ LowEquiv 0 (transition (emptyState (fun _ => 0) 0) (.allocate 0))
    (transition (emptyState (fun _ => 0) 1) (.allocate 0)) := by
  intro h
  have hreply := congrArg View.reply h
  simp [LowEquiv, observe, transition, emptyState, set1] at hreply
example : ¬ LowEquiv 0 leftSecret (transition rightSecret (.schedule (some 1))) := by
  intro h
  have hscheduler := congrArg View.schedulerCurrent h
  simp [LowEquiv, observe, transition, leftSecret, rightSecret, emptyState] at hscheduler

end LeanOS.Observation
