import LeanOS.ChildLoader
import LeanOS.FailStop.SpawnRollback
import LeanOS.FailStop.SpawnAccountingTraces

/-!
# The run-time loader and the composite model together (#571)

`LeanOS.ChildLoader` models the loading of one spawned child's pages, and
`LeanOS.FailStop` models the spawn family on the complete composite state.
The kernel runs them together: a rejection that rolls the loader back also
terminates the child through the composite gate, and the started child's send
is a composite step.  This module puts the two models side by side in one
state (`Joint`) and proves what the pairing does.

## Steps

* `spawnStep`: the composite spawn (`childGate (.spawn _)`); an accepted spawn
  hands the loader the child's control word, with no frames.
* `grantStep`: a frame grant (`childGate (.grantFrames _ _)`); the frames moved
  are credited to the child being loaded.
* `loaderStep`: one loader request (`ChildLoader.step`).  A reply that rolls
  the loader back is paired, as in the kernel's `loader_rollback`, with the
  composite termination of the child the request names
  (`childGate (.terminateChild control)`).  Every other reply leaves the
  composite state alone.
* `childSendStep`: once the loader has started the child, the child's one
  send (syscall 8) is the composite step `FailStop.childSend` for the subject
  the control word names (`ChildTraceStep.childSend`).

## Theorems

* **Joint rollback** (`joint_rollback_restores`).  From a composite state
  satisfying the invariants and a loader with no child, spawn a child, grant
  it frames, run any loader requests, and let a request roll the loader back:
  the loader is exactly the loader before the spawn, and the composite state
  is `SpawnRestored` against the state before the spawn.  This is the joint
  form of `spawn_rejected_unchanged`, which says the same of a rejected spawn
  with equality.  Equality of the whole composite state is impossible here,
  because identities are never reused: the child's identity stays issued and
  the control generation has advanced (`SpawnRestored.issued`,
  `SpawnRestored.generation`).
* **The started child's send is confined** (`joint_child_send_confined`).
  The subject the started child's send runs as is the spawned child, and an
  accepted send writes only the mailbox of the endpoint spawn granted it,
  with the rights the spawn request named.  Every other mailbox and every
  other projection of the composite state is unchanged.
-/
namespace LeanOS.ChildLoaderJoint

open LeanOS
open LeanOS.FailStop
set_option linter.unusedSimpArgs false

/-- The composite state and the loader state side by side. -/
structure Joint where
  composite : CompositeState
  loader : ChildLoader.State

/-- The control word a loader request names. -/
def requestControl : ChildLoader.Request → UInt64
  | .load control _ _ => control
  | .start control => control

/-- One loader request.  A rollback terminates the named child in the
composite model. -/
def loaderStep (joint : Joint) (request : ChildLoader.Request) : Joint × ChildLoader.Reply :=
  match (ChildLoader.step joint.loader request).2 with
  | .rolledBack reason =>
      ({ composite :=
          (childGate joint.composite (.terminateChild (requestControl request))).state
         loader := (ChildLoader.step joint.loader request).1 }, .rolledBack reason)
  | reply => ({ joint with loader := (ChildLoader.step joint.loader request).1 }, reply)

/-- Run loader requests in order. -/
def runLoader (joint : Joint) : List ChildLoader.Request → Joint
  | [] => joint
  | request :: rest => runLoader (loaderStep joint request).1 rest

/-- The loader learns the child an accepted spawn returned, with no frames. -/
def attach (loader : ChildLoader.State) (control : UInt64) : ChildLoader.State :=
  { loader with child := some ⟨control, 0⟩ }

/-- A composite spawn; an accepted one hands the loader the child's control
word. -/
def spawnStep (joint : Joint) (request : SpawnRequest) : Joint :=
  match (childGate joint.composite (.spawn request)).result with
  | .completed (.spawned _ _ control) =>
      { composite := (childGate joint.composite (.spawn request)).state
        loader := attach joint.loader control }
  | _ => { joint with composite := (childGate joint.composite (.spawn request)).state }

/-- The frames a grant moved, credited to the child the control word names. -/
def credit (loader : ChildLoader.State) (control : UInt64) (moved : Nat) : ChildLoader.State :=
  { loader with child := loader.child.map fun child =>
      if child.control = control then { child with frames := child.frames + moved } else child }

/-- A composite frame grant; the loader's child gains the frames moved. -/
def grantStep (joint : Joint) (control : UInt64) (frames : Nat) : Joint :=
  match (childGate joint.composite (.grantFrames control frames)).result with
  | .completed (.framesGranted _ moved) =>
      { composite := (childGate joint.composite (.grantFrames control frames)).state
        loader := credit joint.loader control moved }
  | _ => { joint with composite := (childGate joint.composite (.grantFrames control frames)).state }

/-- Run frame grants for one control word in order. -/
def grantSteps (joint : Joint) (control : UInt64) : List Nat → Joint
  | [] => joint
  | frames :: rest => grantSteps (grantStep joint control frames) control rest

/-- The subject the started child is: the child the loader's control word
names in the parent's child table, once the loader has started it. -/
def startedChild (joint : Joint) : Option Nat :=
  match joint.loader.child with
  | some child =>
      if joint.loader.started then
        match resolveControl joint.composite child.control with
        | .ok (_, entry) => some entry.child
        | .error _ => none
      else none
  | none => none

/-- The started child's send: the composite step `childSend` for the started
child. -/
def childSendStep (joint : Joint) (word : UInt64) : Joint × ChildSendResult :=
  match startedChild joint with
  | some child =>
      ({ joint with composite := (childSend joint.composite child word).state },
        (childSend joint.composite child word).result)
  | none => (joint, .notChild)

/-! ## The loader's records along a run -/

/-- A request never changes the reserved range, the plan or the file. -/
theorem step_constants (loader : ChildLoader.State) (request : ChildLoader.Request) :
    (ChildLoader.step loader request).1.start = loader.start ∧
      (ChildLoader.step loader request).1.stop = loader.stop ∧
      (ChildLoader.step loader request).1.plan = loader.plan ∧
      (ChildLoader.step loader request).1.file = loader.file := by
  cases request with
  | load control index source =>
      simp only [ChildLoader.step]
      split
      · exact ⟨rfl, rfl, rfl, rfl⟩
      · split
        · exact ⟨rfl, rfl, rfl, rfl⟩
        · split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  | start control =>
      simp only [ChildLoader.step]
      split
      · exact ⟨rfl, rfl, rfl, rfl⟩
      · split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- A request keeps the child being loaded, or discards it. -/
theorem step_child (loader : ChildLoader.State) (request : ChildLoader.Request) :
    (ChildLoader.step loader request).1.child = loader.child ∨
      (ChildLoader.step loader request).1.child = none := by
  cases request with
  | load control index source =>
      simp only [ChildLoader.step]
      split
      · exact Or.inl rfl
      · split
        · exact Or.inr rfl
        · split
          · exact Or.inl rfl
          · exact Or.inr rfl
  | start control =>
      simp only [ChildLoader.step]
      split
      · exact Or.inl rfl
      · split
        · exact Or.inl rfl
        · exact Or.inr rfl

/-- A rollback happens only for the live child the request names. -/
theorem rolledBack_live (loader : ChildLoader.State) (request : ChildLoader.Request)
    (reason : ChildLoader.Rejection)
    (rolled : (ChildLoader.step loader request).2 = .rolledBack reason) :
    ∃ child, loader.child = some child ∧ child.control = requestControl request := by
  have live : ∃ child, ChildLoader.liveChild loader (requestControl request) = some child := by
    cases request with
    | load control index source =>
        simp only [ChildLoader.step] at rolled
        cases found : ChildLoader.liveChild loader control with
        | none => simp [found] at rolled
        | some child => exact ⟨child, found⟩
    | start control =>
        simp only [ChildLoader.step] at rolled
        cases found : ChildLoader.liveChild loader control with
        | none => simp [found] at rolled
        | some child => exact ⟨child, found⟩
  obtain ⟨child, found⟩ := live
  simp only [ChildLoader.liveChild] at found
  cases held : loader.child with
  | none => simp [held] at found
  | some actual =>
      simp only [held] at found
      split at found
      · next named =>
        cases found
        simp only [Bool.and_eq_true, decide_eq_true_eq] at named
        exact ⟨child, rfl, named.1⟩
      · cases found

/-- Rollback reads only the reserved range, the plan and the file. -/
theorem rollback_congr {left right : ChildLoader.State} (start : left.start = right.start)
    (stop : left.stop = right.stop) (plan : left.plan = right.plan)
    (file : left.file = right.file) :
    ChildLoader.rollback left = ChildLoader.rollback right := by
  cases left; cases right
  simp only at start stop plan file
  subst start stop plan file
  rfl

/-- What a run of loader requests keeps, from a loader whose child is the
spawned child: the loader's constant records, and either the composite state
is still the one the requests started from and every child the loader holds
is named by the spawn's control word, or the loader has no child. -/
def Tracks (joint : Joint) (composite : CompositeState) (control : UInt64)
    (idle : ChildLoader.State) : Prop :=
  joint.loader.start = idle.start ∧ joint.loader.stop = idle.stop ∧
    joint.loader.plan = idle.plan ∧ joint.loader.file = idle.file ∧
    ((joint.composite = composite ∧ ∀ child, joint.loader.child = some child →
        child.control = control) ∨ joint.loader.child = none)

theorem loaderStep_tracks {joint : Joint} {composite : CompositeState} {control : UInt64}
    {idle : ChildLoader.State} (tracks : Tracks joint composite control idle)
    (request : ChildLoader.Request) :
    Tracks (loaderStep joint request).1 composite control idle := by
  obtain ⟨start, stop, plan, file, current⟩ := tracks
  obtain ⟨start', stop', plan', file'⟩ := step_constants joint.loader request
  unfold loaderStep
  split
  · next reason rolled =>
    refine ⟨start'.trans start, stop'.trans stop, plan'.trans plan, file'.trans file, Or.inr ?_⟩
    simp only
    rw [ChildLoader.rejection_rolls_back joint.loader request reason rolled]
    rfl
  · refine ⟨start'.trans start, stop'.trans stop, plan'.trans plan, file'.trans file, ?_⟩
    simp only
    rcases step_child joint.loader request with same | gone
    · rw [same]; exact current
    · exact Or.inr gone

theorem runLoader_tracks {joint : Joint} {composite : CompositeState} {control : UInt64}
    {idle : ChildLoader.State} (tracks : Tracks joint composite control idle)
    (requests : List ChildLoader.Request) :
    Tracks (runLoader joint requests) composite control idle := by
  induction requests generalizing joint with
  | nil => exact tracks
  | cons request rest ih => exact ih (loaderStep_tracks tracks request)

/-- Grants act on the composite state exactly as `grantAll`. -/
theorem grantSteps_composite (joint : Joint) (control : UInt64) (grants : List Nat) :
    (grantSteps joint control grants).composite = grantAll joint.composite control grants := by
  induction grants generalizing joint with
  | nil => rfl
  | cons frames rest ih =>
      simp only [grantSteps, grantAll]
      rw [ih]
      congr 1
      unfold grantStep
      split <;> rfl

/-- Grants only credit frames to the loader's child. -/
theorem grantSteps_loader (loader : ChildLoader.State) (composite : CompositeState)
    (control : UInt64) (frames : Nat) (grants : List Nat) :
    ∃ total, (grantSteps ⟨composite, { loader with child := some ⟨control, frames⟩ }⟩ control
      grants).loader = { loader with child := some ⟨control, total⟩ } := by
  induction grants generalizing composite frames with
  | nil => exact ⟨frames, rfl⟩
  | cons first rest ih =>
      simp only [grantSteps]
      unfold grantStep
      split
      · next moved _ =>
        simp only [credit, Option.map_some, ↓reduceIte]
        exact ih _ (frames + moved)
      · exact ih _ frames

/-! ## Joint rollback -/

/-- **Joint rollback restores the pre-spawn state.**  From a composite state
satisfying the invariants under the running latch and a loader with no child
(`rollback idle = idle`, the state after any rollback), spawn a child through
the gate, give it frames any number of times, and run any loader requests.
If a request then rolls the loader back, the kernel's pairing (the loader's
rollback and `childGate (.terminateChild _)` for the control word the request
names) leaves the loader exactly as it was before the spawn and the composite
state `SpawnRestored` against the state before the spawn: the same live
subjects and capability slots, runnable set and current subject, ownership
records, frame commitments, allocator, bindings and frame contents, child
tables and spawn authority; only the never-reused histories have advanced. -/
theorem joint_rollback_restores (pre : CompositeState) (idle : ChildLoader.State)
    (request : SpawnRequest) (grants : List Nat) (requests : List ChildLoader.Request)
    (last : ChildLoader.Request) (child addressSpace : Nat) (control : UInt64)
    (reason : ChildLoader.Rejection)
    (running : pre.execution.mode = .running) (holds : ResourceRuntimeWellFormed pre)
    (accounting : ChildAccountingWellFormed pre) (noChild : ChildLoader.rollback idle = idle)
    (spawned : (childGate pre (.spawn request)).result =
      .completed (.spawned child addressSpace control))
    (rolledBack : (loaderStep (runLoader (grantSteps (spawnStep ⟨pre, idle⟩ request) control
      grants) requests) last).2 = .rolledBack reason) :
    (loaderStep (runLoader (grantSteps (spawnStep ⟨pre, idle⟩ request) control grants)
        requests) last).1.loader = idle ∧
      SpawnRestored pre (loaderStep (runLoader (grantSteps (spawnStep ⟨pre, idle⟩ request)
        control grants) requests) last).1.composite child := by
  have spawnEq : spawnStep ⟨pre, idle⟩ request =
      ⟨(childGate pre (.spawn request)).state, attach idle control⟩ := by
    simp [spawnStep, spawned]
  rw [spawnEq] at rolledBack ⊢
  obtain ⟨frames, grantedLoader⟩ := grantSteps_loader idle (childGate pre (.spawn request)).state
    control 0 grants
  have grantedComposite := grantSteps_composite
    ⟨(childGate pre (.spawn request)).state, attach idle control⟩ control grants
  simp only at grantedComposite
  have tracks : Tracks (grantSteps ⟨(childGate pre (.spawn request)).state,
      attach idle control⟩ control grants)
      (grantAll (childGate pre (.spawn request)).state control grants) control idle := by
    simp only [attach] at grantedLoader ⊢
    refine ⟨?_, ?_, ?_, ?_, Or.inl ⟨grantedComposite, fun found held => ?_⟩⟩
    · rw [grantedLoader]
    · rw [grantedLoader]
    · rw [grantedLoader]
    · rw [grantedLoader]
    · rw [grantedLoader] at held
      cases held
      rfl
  generalize grantSteps ⟨(childGate pre (.spawn request)).state, attach idle control⟩ control
    grants = granted at tracks rolledBack ⊢
  have runTracks := runLoader_tracks tracks requests
  generalize runLoader granted requests = ran at runTracks rolledBack ⊢
  obtain ⟨start, stop, plan, file, current⟩ := runTracks
  have loaderRolled : (ChildLoader.step ran.loader last).2 = .rolledBack reason := by
    cases h : (ChildLoader.step ran.loader last).2 with
    | rolledBack found => simp [loaderStep, h] at rolledBack; rw [rolledBack]
    | loaded => simp [loaderStep, h] at rolledBack
    | started => simp [loaderStep, h] at rolledBack
    | refused found => simp [loaderStep, h] at rolledBack
  obtain ⟨liveChild, held, named⟩ := rolledBack_live ran.loader last reason loaderRolled
  rcases current with ⟨compositeEq, controls⟩ | gone
  · have controlEq : requestControl last = control := named.symm.trans (controls _ held)
    have stepEq : loaderStep ran last =
        ({ composite := (childGate ran.composite (.terminateChild control)).state
           loader := (ChildLoader.step ran.loader last).1 }, .rolledBack reason) := by
      unfold loaderStep
      rw [loaderRolled, controlEq]
    rw [stepEq]
    refine ⟨?_, ?_⟩
    · show (ChildLoader.step ran.loader last).1 = idle
      rw [ChildLoader.rejection_rolls_back ran.loader last reason loaderRolled]
      rw [rollback_congr start stop plan file, noChild]
    · show SpawnRestored pre (childGate ran.composite (.terminateChild control)).state child
      rw [compositeEq]
      exact (spawn_rollback_restores pre request grants child addressSpace control running holds
        accounting spawned).2
  · rw [held] at gone; cases gone

/-! ## The started child's send -/

/-- **The started child's send is a composite trace step**: the joint step
runs `ChildTraceStep.childSend` for the started child. -/
theorem childSendStep_trace (joint : Joint) (word : UInt64) (child : Nat)
    (started : startedChild joint = some child) :
    (childSendStep joint word).1.composite =
      ChildTraceStep.apply joint.composite (.childSend child word) := by
  simp [childSendStep, started, ChildTraceStep.apply]

/-- **The started child sends only to the endpoint spawn granted it.**  After
a spawn through the gate, any frame grants and any loader requests that leave
the child started, the started child is the spawned child; and if its send is
accepted, the one envelope it writes goes to the mailbox of the endpoint the
parent's capability names (the capability the spawn request resolved), sent
with exactly the rights the request named.  Every other mailbox and every
projection of the composite state other than the two IPC views is
unchanged. -/
theorem joint_child_send_confined (pre : CompositeState) (idle : ChildLoader.State)
    (request : SpawnRequest) (grants : List Nat) (requests : List ChildLoader.Request)
    (child addressSpace : Nat) (control : UInt64) (word : UInt64)
    (running : pre.execution.mode = .running) (holds : ResourceRuntimeWellFormed pre)
    (accounting : ChildAccountingWellFormed pre)
    (spawned : (childGate pre (.spawn request)).result =
      .completed (.spawned child addressSpace control))
    (loaded : ∃ loading, (runLoader (grantSteps (spawnStep ⟨pre, idle⟩ request) control grants)
      requests).loader.child = some loading)
    (isStarted : (runLoader (grantSteps (spawnStep ⟨pre, idle⟩ request) control grants)
      requests).loader.started = true) :
    let ran := runLoader (grantSteps (spawnStep ⟨pre, idle⟩ request) control grants) requests
    startedChild ran = some child ∧
      ((childSendStep ran word).2 = .sent →
        ∃ slot endpoint,
          pre.capabilities.slots (spawnParent pre) slot = some endpoint ∧
          endpoint.kind = .endpoint ∧
          ran.composite.capabilities.slots child childEndpointSlot =
            some ⟨endpoint.object, .endpoint, request.rights,
              pre.capabilities.nextIdentity + 1, some endpoint.identity⟩ ∧
          (childSendStep ran word).1.composite.ipc.endpoints.mailbox endpoint.object =
            some { endpoint := endpoint.object, sender := child,
                   payload := childSendPayload word } ∧
          (∀ object, object ≠ endpoint.object →
            (childSendStep ran word).1.composite.ipc.endpoints.mailbox object =
              ran.composite.ipc.endpoints.mailbox object) ∧
          { (childSendStep ran word).1.composite with
              ipc := ran.composite.ipc, transfers := ran.composite.transfers } =
            ran.composite) := by
  intro ran
  have spawnEq : spawnStep ⟨pre, idle⟩ request =
      ⟨(childGate pre (.spawn request)).state, attach idle control⟩ := by
    simp [spawnStep, spawned]
  obtain ⟨frames, grantedLoader⟩ := grantSteps_loader idle (childGate pre (.spawn request)).state
    control 0 grants
  have grantedComposite := grantSteps_composite
    ⟨(childGate pre (.spawn request)).state, attach idle control⟩ control grants
  simp only at grantedComposite
  have tracks : Tracks (grantSteps ⟨(childGate pre (.spawn request)).state,
      attach idle control⟩ control grants)
      (grantAll (childGate pre (.spawn request)).state control grants) control idle := by
    simp only [attach] at grantedLoader ⊢
    refine ⟨?_, ?_, ?_, ?_, Or.inl ⟨grantedComposite, fun found held => ?_⟩⟩
    · rw [grantedLoader]
    · rw [grantedLoader]
    · rw [grantedLoader]
    · rw [grantedLoader]
    · rw [grantedLoader] at held
      cases held
      rfl
  have runTracks := runLoader_tracks tracks requests
  simp only [ran, spawnEq] at loaded isStarted ⊢
  generalize runLoader (grantSteps ⟨(childGate pre (.spawn request)).state, attach idle control⟩
    control grants) requests = current at runTracks loaded isStarted ⊢
  obtain ⟨_, _, _, _, tracked⟩ := runTracks
  obtain ⟨loading, held⟩ := loaded
  obtain ⟨compositeEq, controls⟩ : current.composite =
      grantAll (childGate pre (.spawn request)).state control grants ∧
      ∀ child, current.loader.child = some child → child.control = control := by
    rcases tracked with both | gone
    · exact both
    · rw [held] at gone; cases gone
  have loadingControl := controls loading held
  obtain ⟨spawnedRaw, _, grantedCaps, grantedHolds, slot, entry, resolved, entryChild⟩ :=
    spawn_grants_child pre request grants child addressSpace control running holds accounting
      spawned
  have startedEq : startedChild current = some child := by
    simp only [startedChild, held, isStarted, ↓reduceIte, compositeEq, loadingControl, resolved,
      entryChild]
  refine ⟨startedEq, fun sent => ?_⟩
  have sendEq : childSendStep current word =
      ({ current with composite := (childSend current.composite child word).state },
        (childSend current.composite child word).result) := by
    simp [childSendStep, startedEq]
  rw [sendEq] at sent ⊢
  simp only at sent ⊢
  rw [compositeEq] at sent ⊢
  obtain ⟨capability, capHeld, _, _, others, _, rest⟩ :=
    childSend_confined _ child word grantedHolds.1.left sent
  obtain ⟨endpointSlot, endpoint, parentHeld, kind, _, _, childSlots⟩ :=
    spawn_child_capabilities pre request child addressSpace holds.1.left spawnedRaw
  have slotZero := childSlots childEndpointSlot
  simp only [↓reduceIte] at slotZero
  rw [grantedCaps, slotZero] at capHeld
  cases capHeld
  obtain ⟨sentCapability, sentHeld, _, _, _, stateEq⟩ :=
    childSend_sent _ child word grantedHolds.1.left sent
  rw [grantedCaps, slotZero] at sentHeld
  cases sentHeld
  refine ⟨endpointSlot, endpoint, parentHeld, kind, by rw [grantedCaps, slotZero], ?_, others,
    rest⟩
  rw [stateEq]
  simp [installIPC, EndpointIPC.setOption]

end LeanOS.ChildLoaderJoint
