import LeanOS.FailStop.AuthoritativeGate

/-!
# Fail-stop composite: authoritative blocking slices and traces

Blocking receive, send, and cancel slices of the authoritative gate,
admissibility, `runAuthoritativeOperations`, and the mixed-trace preservation
and halting theorems.
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

/-- Delivery changes only mailbox/completion payload state.  Every projection
observed by dormant cancellation remains literally unchanged. -/
theorem dispatchBlockingReceive_delivered_dormant_projections_exact
    state handleWord frame registers envelope
    (hdelivered :
      (dispatchBlockingReceive state handleWord frame registers).reply =
        .delivered envelope) :
    let next := (dispatchBlockingReceive state handleWord frame registers).state
    next.deferredCancels = state.deferredCancels ∧
      next.blockingContexts = state.blockingContexts ∧
      next.resumable.contexts = state.resumable.contexts ∧
      next.blockingIPC.waiterEndpoint = state.blockingIPC.waiterEndpoint ∧
      next.blockingIPC.scheduler = state.blockingIPC.scheduler := by
  cases hresolve : CapabilityHandle.resolveCurrent
      state.blockingIPC.scheduler.lifecycle.capabilities
      { caller := state.execution.core.context.currentSubject } handleWord .endpoint with
  | error reason => simp [dispatchBlockingReceive, hresolve] at hdelivered
  | ok resolution =>
      let saved := state.blockingSavedContext frame registers
      cases houtcome : BlockingIPCContext.receiveOrBlock state.blockingIPCContext
          state.execution.core.context.currentSubject resolution.handle.slot saved with
      | mk blocking result =>
          cases result with
          | contextRejected reason =>
              simp [dispatchBlockingReceive, hresolve, saved, houtcome] at hdelivered
          | completed result =>
              cases result with
              | rejected reason =>
                  simp [dispatchBlockingReceive, hresolve, saved, houtcome] at hdelivered
              | blocked =>
                  by_cases hsome : blocking.ipc.scheduler.lifecycle.current.isSome = true
                  · cases hrestore : restoreBlockingPeer state blocking <;>
                      simp [dispatchBlockingReceive, hresolve, saved, houtcome, hsome,
                        hrestore] at hdelivered
                  · simp [dispatchBlockingReceive, hresolve, saved, houtcome, hsome]
                      at hdelivered
              | delivered actual =>
                  simp [dispatchBlockingReceive, hresolve, saved, houtcome] at hdelivered
                  subst actual
                  have hcompleted :
                      (BlockingIPCContext.receiveOrBlock state.blockingIPCContext
                        state.execution.core.context.currentSubject
                        resolution.handle.slot saved).result =
                          .completed (.delivered envelope) := by
                    simp [houtcome]
                  have hblocked :=
                    BlockingIPCContext.receive_delivered_blocked_unchanged
                      state.blockingIPCContext
                      state.execution.core.context.currentSubject resolution.handle.slot
                      saved envelope hcompleted
                  have hexact :=
                    BlockingIPCContext.receive_delivered_ipc_exact
                      state.blockingIPCContext
                      state.execution.core.context.currentSubject resolution.handle.slot
                      saved envelope hcompleted
                  have hwaiter :=
                    BlockingIPC.receive_delivered_waiterEndpoint_unchanged
                      state.blockingIPC state.execution.core.context.currentSubject
                      resolution.handle.slot envelope hexact.2
                  have hscheduler :=
                    BlockingIPC.receive_delivered_scheduler_unchanged
                      state.blockingIPC state.execution.core.context.currentSubject
                      resolution.handle.slot envelope hexact.2
                  rw [houtcome] at hblocked hexact
                  have hblocked' : blocking.blocked = state.blockingContexts := by
                    simpa [CompositeState.blockingIPCContext] using hblocked
                  have hipc : blocking.ipc =
                      (BlockingIPC.receiveOrBlock state.blockingIPC
                        state.execution.core.context.currentSubject
                        resolution.handle.slot).state := by
                    simpa [CompositeState.blockingIPCContext] using hexact.1
                  simp [dispatchBlockingReceive, hresolve, saved, houtcome,
                    publishBlockingIPCContext, hblocked', hipc, hwaiter, hscheduler]

/-- An idle block publishes exactly the caller's waiter/context entries and
the canonical scheduler transition, leaving the resumable bank untouched. -/
theorem dispatchBlockingReceive_idle_block_projection_exact
    state handleWord frame registers
    (hblocked :
      (dispatchBlockingReceive state handleWord frame registers).reply = .blocked)
    (hidle :
      (dispatchBlockingReceive state handleWord frame registers).state.scheduler.lifecycle.current =
        none) :
    let next := (dispatchBlockingReceive state handleWord frame registers).state
    let caller := state.execution.core.context.currentSubject
    let saved := state.blockingSavedContext frame registers
    ∃ endpoint,
      next.deferredCancels = state.deferredCancels ∧
      next.blockingContexts =
        BlockingIPCContext.setBlocked state.blockingContexts caller (some saved) ∧
      next.resumable.contexts = state.resumable.contexts ∧
      next.blockingIPC.waiterEndpoint =
        BlockingIPC.setWaiterEndpoint state.blockingIPC.waiterEndpoint caller
          (some endpoint) ∧
      state.blockingIPC.scheduler.ready = [] ∧
      next.blockingIPC.scheduler =
        { state.blockingIPC.scheduler with
          lifecycle := { state.blockingIPC.scheduler.lifecycle with
            runnable := SubjectLifecycle.setBool
              state.blockingIPC.scheduler.lifecycle.runnable caller false
            current := none } } := by
  cases hresolve : CapabilityHandle.resolveCurrent
      state.blockingIPC.scheduler.lifecycle.capabilities
      { caller := state.execution.core.context.currentSubject } handleWord .endpoint with
  | error reason => simp [dispatchBlockingReceive, hresolve] at hblocked
  | ok resolution =>
      let saved := state.blockingSavedContext frame registers
      cases houtcome : BlockingIPCContext.receiveOrBlock state.blockingIPCContext
          state.execution.core.context.currentSubject resolution.handle.slot saved with
      | mk blocking result =>
          cases result with
          | contextRejected reason =>
              simp [dispatchBlockingReceive, hresolve, saved, houtcome] at hblocked
          | completed result =>
              cases result with
              | rejected reason =>
                  simp [dispatchBlockingReceive, hresolve, saved, houtcome] at hblocked
              | delivered envelope =>
                  simp [dispatchBlockingReceive, hresolve, saved, houtcome] at hblocked
              | blocked =>
                  by_cases hsome : blocking.ipc.scheduler.lifecycle.current.isSome = true
                  · cases hrestore : restoreBlockingPeer state blocking with
                    | error reason =>
                        simp [dispatchBlockingReceive, hresolve, saved, houtcome, hsome,
                          hrestore] at hblocked
                    | ok published =>
                        obtain ⟨selected, destination, hselected, _, _, _, _, _, _, hcontext⟩ :=
                          restoreBlockingPeer_exact state blocking published hrestore
                        have hpublishedCurrent :
                            published.scheduler.lifecycle.current = some selected := by
                          rw [← (restoreBlockingPeer_blockingCoherent
                            state blocking published hrestore).1]
                          change
                            published.blockingIPC.scheduler.lifecycle.current = some selected
                          have hipc : published.blockingIPC = blocking.ipc := congrArg
                            BlockingIPCContext.State.ipc hcontext
                          rw [hipc]
                          exact hselected
                        have hpublishedIdle :
                            published.scheduler.lifecycle.current = none := by
                          simpa [dispatchBlockingReceive, hresolve, saved, houtcome, hsome,
                            hrestore] using hidle
                        rw [hpublishedCurrent] at hpublishedIdle
                        contradiction
                  · have hcompleted :
                        (BlockingIPCContext.receiveOrBlock state.blockingIPCContext
                          state.execution.core.context.currentSubject
                          resolution.handle.slot saved).result =
                            .completed .blocked := by
                      simp [houtcome]
                    have hipcExact :=
                      BlockingIPCContext.receive_blocked_ipc_exact
                        state.blockingIPCContext
                        state.execution.core.context.currentSubject resolution.handle.slot
                        saved hcompleted
                    have hblockedExact :=
                      BlockingIPCContext.receive_blocked_blocked_exact
                        state.blockingIPCContext
                        state.execution.core.context.currentSubject resolution.handle.slot
                        saved hcompleted
                    have hraw := hipcExact.2
                    obtain ⟨endpoint, hwaiter⟩ :=
                      BlockingIPC.receive_blocked_waiterEndpoint_exact
                        state.blockingIPC
                        state.execution.core.context.currentSubject
                        resolution.handle.slot hraw
                    rw [houtcome] at hipcExact hblockedExact
                    have hipc : blocking.ipc =
                        (BlockingIPC.receiveOrBlock state.blockingIPC
                          state.execution.core.context.currentSubject
                          resolution.handle.slot).state := by
                      simpa [CompositeState.blockingIPCContext] using hipcExact.1
                    have hblockingIdle :
                        blocking.ipc.scheduler.lifecycle.current = none := by
                      cases hcurrent : blocking.ipc.scheduler.lifecycle.current <;>
                        simp_all
                    have hscheduler :=
                      BlockingIPC.receive_blocked_idle_scheduler_exact
                        state.blockingIPC
                        state.execution.core.context.currentSubject
                        resolution.handle.slot hraw (by
                          rw [← hipc]
                          exact hblockingIdle)
                    have hblocked' :
                        blocking.blocked =
                          BlockingIPCContext.setBlocked state.blockingContexts
                            state.execution.core.context.currentSubject (some saved) := by
                      simpa [CompositeState.blockingIPCContext] using hblockedExact
                    refine ⟨endpoint, ?_⟩
                    simp [dispatchBlockingReceive, hresolve, saved, houtcome, hsome,
                      publishBlockingIPCContext, hblocked', hipc, hwaiter, hscheduler]

/-- A block with an immediate peer handoff publishes the caller's exact
waiter/context entries, consumes exactly the selected peer context, and
performs the canonical head-selection scheduler transition. -/
theorem dispatchBlockingReceive_selected_block_projection_exact
    state handleWord frame registers selected
    (hblocked :
      (dispatchBlockingReceive state handleWord frame registers).reply = .blocked)
    (hselected : (dispatchBlockingReceive state handleWord frame registers).state.blockingIPC.scheduler.lifecycle.current =
      some selected) :
    let next := (dispatchBlockingReceive state handleWord frame registers).state
    let caller := state.execution.core.context.currentSubject
    let saved := state.blockingSavedContext frame registers
    ∃ endpoint rest destination,
      next.deferredCancels = state.deferredCancels ∧
      next.blockingContexts =
        BlockingIPCContext.setBlocked state.blockingContexts caller (some saved) ∧
      next.resumable.contexts =
        ResumablePreemption.eraseContext state.resumable.contexts selected ∧
      ResumablePreemption.contextFor state.resumable.contexts selected =
        some destination ∧
      destination.owner = selected ∧
      next.blockingIPC.waiterEndpoint =
        BlockingIPC.setWaiterEndpoint state.blockingIPC.waiterEndpoint caller
          (some endpoint) ∧
      state.blockingIPC.scheduler.ready = selected :: rest ∧
      next.blockingIPC.scheduler =
        { state.blockingIPC.scheduler with
          ready := rest
          lifecycle := { state.blockingIPC.scheduler.lifecycle with
            runnable := SubjectLifecycle.setBool
              state.blockingIPC.scheduler.lifecycle.runnable caller false
            current := some selected } } := by
  cases hresolve : CapabilityHandle.resolveCurrent
      state.blockingIPC.scheduler.lifecycle.capabilities
      { caller := state.execution.core.context.currentSubject } handleWord .endpoint with
  | error reason => simp [dispatchBlockingReceive, hresolve] at hblocked
  | ok resolution =>
      let saved := state.blockingSavedContext frame registers
      cases houtcome : BlockingIPCContext.receiveOrBlock state.blockingIPCContext
          state.execution.core.context.currentSubject resolution.handle.slot saved with
      | mk blocking result =>
          cases result with
          | contextRejected reason =>
              simp [dispatchBlockingReceive, hresolve, saved, houtcome] at hblocked
          | completed result =>
              cases result with
              | rejected reason =>
                  simp [dispatchBlockingReceive, hresolve, saved, houtcome] at hblocked
              | delivered envelope =>
                  simp [dispatchBlockingReceive, hresolve, saved, houtcome] at hblocked
              | blocked =>
                  by_cases hsome : blocking.ipc.scheduler.lifecycle.current.isSome = true
                  · cases hrestore : restoreBlockingPeer state blocking with
                    | error reason =>
                        simp [dispatchBlockingReceive, hresolve, saved, houtcome, hsome,
                          hrestore] at hblocked
                    | ok published =>
                        have hcompleted :
                            (BlockingIPCContext.receiveOrBlock state.blockingIPCContext
                              state.execution.core.context.currentSubject
                              resolution.handle.slot saved).result =
                                .completed .blocked := by
                          simp [houtcome]
                        have hipcExact :=
                          BlockingIPCContext.receive_blocked_ipc_exact
                            state.blockingIPCContext
                            state.execution.core.context.currentSubject
                            resolution.handle.slot saved hcompleted
                        have hblockedExact :=
                          BlockingIPCContext.receive_blocked_blocked_exact
                            state.blockingIPCContext
                            state.execution.core.context.currentSubject
                            resolution.handle.slot saved hcompleted
                        have hraw := hipcExact.2
                        obtain ⟨endpoint, hwaiter⟩ :=
                          BlockingIPC.receive_blocked_waiterEndpoint_exact
                            state.blockingIPC
                            state.execution.core.context.currentSubject
                            resolution.handle.slot hraw
                        rw [houtcome] at hipcExact hblockedExact
                        have hipc : blocking.ipc =
                            (BlockingIPC.receiveOrBlock state.blockingIPC
                              state.execution.core.context.currentSubject
                              resolution.handle.slot).state := by
                          simpa [CompositeState.blockingIPCContext] using hipcExact.1
                        obtain ⟨actual, destination, hactual, hcontext, howner,
                          hcontexts⟩ :=
                          restoreBlockingPeer_resumableContexts_exact
                            state blocking published hrestore
                        have hpublishedIPC : published.blockingIPC = blocking.ipc := by
                          exact congrArg BlockingIPCContext.State.ipc
                            (restoreBlockingPeer_context_exact
                              state blocking published hrestore)
                        have hactualSelected : actual = selected := by
                          have hpublishedSelected :
                              published.blockingIPC.scheduler.lifecycle.current =
                                some selected := by
                            simpa [dispatchBlockingReceive, hresolve, saved, houtcome,
                              hsome, hrestore] using hselected
                          rw [hpublishedIPC, hactual] at hpublishedSelected
                          injection hpublishedSelected
                        obtain ⟨rest, hready, hscheduler⟩ :=
                          BlockingIPC.receive_blocked_selected_scheduler_exact
                            state.blockingIPC
                            state.execution.core.context.currentSubject
                            resolution.handle.slot actual hraw (by
                              rw [← hipc]
                              exact hactual)
                        have hblocked' :
                            blocking.blocked =
                              BlockingIPCContext.setBlocked state.blockingContexts
                                state.execution.core.context.currentSubject
                                (some saved) := by
                          simpa [CompositeState.blockingIPCContext] using hblockedExact
                        simp only [dispatchBlockingReceive, hresolve, saved, houtcome,
                          hsome, hrestore, ite_true]
                        refine ⟨endpoint, rest, destination, ?_⟩
                        have hdeferred :=
                          restoreBlockingPeer_deferredExact
                            state blocking published hrestore
                        have hpublishedBlocked :
                            published.blockingContexts = blocking.blocked := by
                          exact congrArg BlockingIPCContext.State.blocked
                            (restoreBlockingPeer_context_exact
                              state blocking published hrestore)
                        refine ⟨hdeferred, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                        · rw [hpublishedBlocked]
                          exact hblocked'
                        · simpa [hactualSelected] using hcontexts
                        · simpa [hactualSelected] using hcontext
                        · exact howner.trans hactualSelected
                        · rw [hpublishedIPC, hipc]
                          exact hwaiter
                        · simpa [hactualSelected] using hready
                        · rw [hpublishedIPC, hipc]
                          simpa [hactualSelected] using hscheduler
                  · have hblockingIdle :
                        blocking.ipc.scheduler.lifecycle.current = none := by
                      cases hcurrent : blocking.ipc.scheduler.lifecycle.current <;>
                        simp_all
                    have hpublishedIdle :
                        (publishBlockingIPCContext state blocking).blockingIPC.scheduler.lifecycle.current =
                          none := by
                      simpa [publishBlockingIPCContext] using hblockingIdle
                    simp [dispatchBlockingReceive, hresolve, saved, houtcome, hsome,
                      hpublishedIdle] at hselected

/-- A composite block retains the dependency proof that the authoritative
blocking scheduler selected the execution-derived caller in the pre-state. -/
theorem dispatchBlockingReceive_blocked_current
    state handleWord frame registers
    (hblocked :
      (dispatchBlockingReceive state handleWord frame registers).reply = .blocked) :
    state.blockingIPC.scheduler.lifecycle.current =
      some state.execution.core.context.currentSubject := by
  cases hresolve : CapabilityHandle.resolveCurrent
      state.blockingIPC.scheduler.lifecycle.capabilities
      { caller := state.execution.core.context.currentSubject } handleWord .endpoint with
  | error reason => simp [dispatchBlockingReceive, hresolve] at hblocked
  | ok resolution =>
      let saved := state.blockingSavedContext frame registers
      cases houtcome : BlockingIPCContext.receiveOrBlock state.blockingIPCContext
          state.execution.core.context.currentSubject resolution.handle.slot saved with
      | mk blocking result =>
          cases result with
          | contextRejected reason =>
              simp [dispatchBlockingReceive, hresolve, saved, houtcome] at hblocked
          | completed result =>
              cases result with
              | rejected reason =>
                  simp [dispatchBlockingReceive, hresolve, saved, houtcome] at hblocked
              | delivered envelope =>
                  simp [dispatchBlockingReceive, hresolve, saved, houtcome] at hblocked
              | blocked =>
                  have hcompleted :
                      (BlockingIPCContext.receiveOrBlock state.blockingIPCContext
                        state.execution.core.context.currentSubject
                        resolution.handle.slot saved).result =
                          .completed .blocked := by
                    simp [houtcome]
                  have hraw :=
                    (BlockingIPCContext.receive_blocked_ipc_exact
                      state.blockingIPCContext
                      state.execution.core.context.currentSubject
                      resolution.handle.slot saved hcompleted).2
                  exact BlockingIPC.receive_blocked_current state.blockingIPC
                    state.execution.core.context.currentSubject
                    resolution.handle.slot hraw

/-- Every outcome of authoritative blocking receive preserves the dormant
cancellation classification.  Delivery leaves its observed projections
literal, while blocking adds only the selected current caller and consumes at
most the old ready-queue head, neither of which can be retained. -/
theorem blockingReceive_authoritativeOperationCompatible
    state handleWord frame registers
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeOperationCompatible state
      (.blocking (.receive handleWord frame registers)) := by
  cases hmode : state.execution.mode with
  | handling active =>
      apply dormantCancellationCompatible_of_exact_projections state _ hstate
      all_goals simp [authoritativeGate, hmode]
  | halted record =>
      apply dormantCancellationCompatible_of_exact_projections state _ hstate
      all_goals simp [authoritativeGate, hmode]
  | running =>
      have hgate :
          (authoritativeGate state
            (.blocking (.receive handleWord frame registers))).state =
              (dispatchBlockingReceive state handleWord frame registers).state := by
        simp [authoritativeGate, hmode, applyAuthoritativeOperation,
          applyBlockingOperation]
      change DormantCancellationCompatible state
        (authoritativeGate state
          (.blocking (.receive handleWord frame registers))).state
      rw [hgate]
      cases hreply :
          (dispatchBlockingReceive state handleWord frame registers).reply with
      | handleRejected reason =>
          rw [dispatchBlockingReceive_rejected_atomic
            state handleWord frame registers _ (.handle reason) hreply]
          exact dormantCancellationCompatible_of_exact_projections
            state state hstate rfl rfl rfl rfl
      | contextRejected reason =>
          rw [dispatchBlockingReceive_rejected_atomic
            state handleWord frame registers _ (.context reason) hreply]
          exact dormantCancellationCompatible_of_exact_projections
            state state hstate rfl rfl rfl rfl
      | switchRequired =>
          rw [dispatchBlockingReceive_rejected_atomic
            state handleWord frame registers _ .switchRequired hreply]
          exact dormantCancellationCompatible_of_exact_projections
            state state hstate rfl rfl rfl rfl
      | rejected reason =>
          rw [dispatchBlockingReceive_rejected_atomic
            state handleWord frame registers _ (.ipc reason) hreply]
          exact dormantCancellationCompatible_of_exact_projections
            state state hstate rfl rfl rfl rfl
      | delivered envelope =>
          have hshape :=
            dispatchBlockingReceive_delivered_dormant_projections_exact
              state handleWord frame registers envelope hreply
          dsimp only at hshape
          rcases hshape with
            ⟨hdeferred, hblocked, hcontexts, hwaiter, hscheduler⟩
          refine ⟨hdeferred, ?_, ?_, ?_⟩
          · intro subject hsome
            rw [hblocked] at hsome
            rw [hdeferred]
            exact hstate.2.1.2.1 subject hsome
          · intro subject saved hsaved
            rw [hblocked] at hsaved
            rw [hcontexts]
            exact hstate.2.2.1 subject saved hsaved
          · intro subject saved hretained
            have hvalid := hstate.2.1.2.2 subject saved hretained
            rw [hwaiter, hscheduler, hcontexts]
            exact ⟨hvalid.2.1, hvalid.2.2.1, hvalid.2.2.2.1,
              hvalid.2.2.2.2.1, hvalid.2.2.2.2.2.1,
              hvalid.2.2.2.2.2.2, hstate.2.2.2 subject saved hretained⟩
      | blocked =>
          have hcurrent := dispatchBlockingReceive_blocked_current
            state handleWord frame registers hreply
          have hcallerAbsent :
              ResumablePreemption.contextFor state.resumable.contexts
                state.execution.core.context.currentSubject = none := by
            rcases hstate.1 with
              ⟨hcoherent, _, _, _, _, _, _, _, hresumable, _, _, _, _, _⟩
            have hresumableScheduler :
                state.resumable.scheduler = state.scheduler := by
              rcases hcoherent with ⟨_, _, _, _, _, _, _, hscheduler, _, _, _, _, _⟩
              exact hscheduler
            exact hresumable.2.2.2.2.1
              state.execution.core.context.currentSubject
              (by simpa [hstate.1.blockingScheduler, hresumableScheduler] using hcurrent)
          have hcallerNotRetained :
              state.deferredCancels.retained
                state.execution.core.context.currentSubject = none := by
            cases hretained :
                state.deferredCancels.retained
                  state.execution.core.context.currentSubject with
            | none => rfl
            | some saved =>
                have hquiescent :=
                  (hstate.2.1.2.2 state.execution.core.context.currentSubject
                    saved hretained).2.2.2.2.1
                exact False.elim (hquiescent hcurrent)
          have hpostCoherent :
              (dispatchBlockingReceive state handleWord frame registers).state.BlockingIPCCoherent := by
            have hcoherent : state.BlockingIPCCoherent := by
              rcases hstate.blocking.1 with
                ⟨_, _, _, _, _, _, _, _, _, _, _, _, hblocking, _⟩
              exact hblocking
            exact dispatchBlockingReceive_preserves_coherent
              state handleWord frame registers hcoherent
          cases hnext :
              (dispatchBlockingReceive state handleWord frame registers).state.blockingIPC.scheduler.lifecycle.current with
          | none =>
              have hnextScheduler :
                  (dispatchBlockingReceive state handleWord frame registers).state.scheduler.lifecycle.current =
                    none := by
                rw [← hpostCoherent.1]
                exact hnext
              have hshape :=
                dispatchBlockingReceive_idle_block_projection_exact
                  state handleWord frame registers hreply hnextScheduler
              dsimp only at hshape
              obtain ⟨endpoint, hdeferred, hblocked, hcontexts, hwaiter,
                hready, hscheduler⟩ := hshape
              refine ⟨hdeferred, ?_, ?_, ?_⟩
              · intro candidate hsome
                rw [hblocked] at hsome
                by_cases heq :
                    candidate = state.execution.core.context.currentSubject
                · subst candidate
                  simpa [hdeferred] using hcallerNotRetained
                · rw [hdeferred]
                  apply hstate.2.1.2.1 candidate
                  change (state.blockingContexts candidate).isSome = true
                  simpa [BlockingIPCContext.setBlocked, heq] using hsome
              · intro candidate saved hsaved
                rw [hblocked] at hsaved
                by_cases heq :
                    candidate = state.execution.core.context.currentSubject
                · subst candidate
                  simpa [hcontexts] using hcallerAbsent
                · have hbefore :
                      state.blockingContexts candidate = some saved := by
                    simpa [BlockingIPCContext.setBlocked, heq] using hsaved
                  rw [hcontexts]
                  exact hstate.2.2.1 candidate saved hbefore
              · intro candidate saved hretained
                have hvalid := hstate.2.1.2.2 candidate saved hretained
                have hne :
                    candidate ≠ state.execution.core.context.currentSubject := by
                  intro heq
                  subst candidate
                  rw [hcallerNotRetained] at hretained
                  contradiction
                rw [hwaiter, hscheduler, hcontexts]
                simp only [CompositeState.blockingIPCContext] at hvalid
                refine ⟨?_, hvalid.2.2.1, ?_, ?_, ?_, hvalid.2.2.2.2.2.2,
                  hstate.2.2.2 candidate saved hretained⟩
                · simpa [BlockingIPC.setWaiterEndpoint, hne] using hvalid.2.1
                · simpa [SubjectLifecycle.setBool, hne] using hvalid.2.2.2.1
                · simp
                · simp [hready]
          | some selected =>
              have hshape :=
                dispatchBlockingReceive_selected_block_projection_exact
                  state handleWord frame registers selected hreply hnext
              dsimp only at hshape
              obtain ⟨endpoint, rest, destination, hdeferred, hblocked,
                hcontexts, hdestination, howner, hwaiter, hready,
                hscheduler⟩ := hshape
              refine ⟨hdeferred, ?_, ?_, ?_⟩
              · intro candidate hsome
                rw [hblocked] at hsome
                by_cases heq :
                    candidate = state.execution.core.context.currentSubject
                · subst candidate
                  simpa [hdeferred] using hcallerNotRetained
                · rw [hdeferred]
                  apply hstate.2.1.2.1 candidate
                  change (state.blockingContexts candidate).isSome = true
                  simpa [BlockingIPCContext.setBlocked, heq] using hsome
              · intro candidate saved hsaved
                rw [hblocked] at hsaved
                by_cases hcaller :
                    candidate = state.execution.core.context.currentSubject
                · subst candidate
                  rw [hcontexts]
                  by_cases heq :
                      state.execution.core.context.currentSubject = selected
                  · rw [← heq]
                    exact ResumablePreemption.contextFor_erase_self _ _
                  · exact
                      (ResumablePreemption.contextFor_erase_other
                        state.resumable.contexts selected
                        state.execution.core.context.currentSubject heq).trans
                        hcallerAbsent
                · have hbefore :
                      state.blockingContexts candidate = some saved := by
                    simpa [BlockingIPCContext.setBlocked, hcaller] using hsaved
                  have habsent := hstate.2.2.1 candidate saved hbefore
                  rw [hcontexts]
                  by_cases heq : candidate = selected
                  · rw [← heq]
                    exact ResumablePreemption.contextFor_erase_self _ _
                  · exact
                      (ResumablePreemption.contextFor_erase_other
                        state.resumable.contexts selected candidate heq).trans habsent
              · intro candidate saved hretained
                have hvalid := hstate.2.1.2.2 candidate saved hretained
                have hnotCaller :
                    candidate ≠ state.execution.core.context.currentSubject := by
                  intro heq
                  subst candidate
                  rw [hcallerNotRetained] at hretained
                  contradiction
                have hnotSelected : candidate ≠ selected := by
                  have hnotReady := hvalid.2.2.2.2.2.1
                  simp only [CompositeState.blockingIPCContext] at hnotReady
                  rw [hready] at hnotReady
                  intro heq
                  subst candidate
                  exact hnotReady (by simp)
                simp only [CompositeState.blockingIPCContext] at hvalid
                rw [hwaiter, hscheduler, hcontexts]
                refine ⟨?_, hvalid.2.2.1, ?_, ?_, ?_,
                  hvalid.2.2.2.2.2.2, ?_⟩
                · simpa [BlockingIPC.setWaiterEndpoint, hnotCaller] using hvalid.2.1
                · simpa [SubjectLifecycle.setBool, hnotCaller] using hvalid.2.2.2.1
                · simpa using Ne.symm hnotSelected
                · intro hmember
                  exact hvalid.2.2.2.2.2.1 (by
                    rw [hready]
                    exact List.mem_cons_of_mem selected hmember)
                · exact
                    (ResumablePreemption.contextFor_erase_other
                      state.resumable.contexts selected candidate hnotSelected).trans
                      (hstate.2.2.2 candidate saved hretained)

/-- Blocking receive has a closed preservation theorem at the folded
authoritative boundary; callers need no post-state compatibility witness. -/
theorem authoritativeGate_blockingReceive_preserves_authoritativeRuntimeWellFormed
    state handleWord frame registers
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeGate state
        (.blocking (.receive handleWord frame registers))).state :=
  authoritativeGate_preserves_authoritativeRuntimeWellFormed_of_compatible state
    (.blocking (.receive handleWord frame registers)) hstate
    (blockingReceive_authoritativeOperationCompatible
      state handleWord frame registers hstate)

/-- A successful blocking receive cannot select an identity held in the
dormant cancellation bank: blocking requires that identity to be the current
subject, while retained cancellation requires it to be quiescent. -/
theorem dispatchBlockingReceive_blocked_not_retained state handleWord frame registers
    subject retained
    (hstate : AuthoritativeRuntimeWellFormed state)
    (hretained : state.deferredCancels.retained subject = some retained)
    (hblocked :
      (dispatchBlockingReceive state handleWord frame registers).reply = .blocked) :
    state.execution.core.context.currentSubject ≠ subject := by
  intro hcaller
  have hnotCurrent :=
    (hstate.2.1.2.2 subject retained hretained).2.2.2.2.1
  cases hresolve : CapabilityHandle.resolveCurrent
      state.blockingIPC.scheduler.lifecycle.capabilities
      { caller := state.execution.core.context.currentSubject } handleWord .endpoint with
  | error reason => simp [dispatchBlockingReceive, hresolve] at hblocked
  | ok resolution =>
      let saved := state.blockingSavedContext frame registers
      cases houtcome : BlockingIPCContext.receiveOrBlock state.blockingIPCContext
          state.execution.core.context.currentSubject resolution.handle.slot saved with
      | mk next result =>
          cases result with
          | contextRejected reason =>
              simp [dispatchBlockingReceive, hresolve, saved, houtcome] at hblocked
          | completed result =>
              cases result with
              | rejected reason =>
                  simp [dispatchBlockingReceive, hresolve, saved, houtcome] at hblocked
              | delivered envelope =>
                  simp [dispatchBlockingReceive, hresolve, saved, houtcome] at hblocked
              | blocked =>
                  have hexact := BlockingIPCContext.receive_blocked_ipc_exact
                    state.blockingIPCContext state.execution.core.context.currentSubject
                    resolution.handle.slot saved (by simp [houtcome])
                  have hcurrent := BlockingIPC.receive_blocked_current
                    state.blockingIPC state.execution.core.context.currentSubject
                    resolution.handle.slot hexact.2
                  apply hnotCurrent
                  change state.blockingIPC.scheduler.lifecycle.current = some subject
                  simpa [hcaller] using hcurrent

/-- A successful blocking send can wake only a subject with a saved waiter
context.  Such an owner is disjoint from every dormant retained cancellation,
so send cannot silently reactivate retained authority. -/
theorem dispatchBlockingSend_woke_not_retained state handleWord word0 word1 restored
    subject retained
    (hstate : AuthoritativeRuntimeWellFormed state)
    (hretained : state.deferredCancels.retained subject = some retained)
    (hwoke :
      (dispatchBlockingSend state handleWord word0 word1).reply = .woke restored) :
    restored.owner ≠ subject := by
  have hcoherent : state.BlockingIPCCoherent := by
    rcases hstate.blocking.1 with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, hblocking, _⟩
    exact hblocking
  obtain ⟨receiver, hstored, _, _⟩ := dispatchBlockingSend_woke_exact
    state handleWord word0 word1 restored
      ⟨hstate.blocking.2, hcoherent⟩ hwoke
  have howner : restored.owner = receiver :=
    BlockingIPCContext.validSaved_owner receiver restored
      (hstate.blocking.2.2.2 receiver restored hstored)
  have hnotRetained :
      state.deferredCancels.retained receiver = none :=
    hstate.2.1.2.1 receiver (by
      change (state.blockingContexts receiver).isSome = true
      rw [hstored]
      rfl)
  intro heq
  have hreceiver : receiver = subject := howner.symm.trans heq
  rw [hreceiver, hretained] at hnotRetained
  simp [hretained] at hnotRetained

/-- A successful blocking send wake has one exact affected identity.  The
released waiter is removed from the blocked bank, appended to the resumable
bank, and is the only identity whose scheduler/waiter projections change. -/
theorem dispatchBlockingSend_woke_projection_exact state handleWord word0 word1 saved
    (hstate : BlockingReceiveWellFormed state)
    (hwoke : (dispatchBlockingSend state handleWord word0 word1).reply = .woke saved) :
    let next := (dispatchBlockingSend state handleWord word0 word1).state
    ∃ endpoint receiver rest,
      state.blockingContexts receiver = some saved ∧
      saved.owner = receiver ∧
      next.deferredCancels = state.deferredCancels ∧
      next.blockingContexts =
        BlockingIPCContext.setBlocked state.blockingContexts receiver none ∧
      next.blockingIPC =
        BlockingIPC.wakeState state.blockingIPC endpoint receiver
          { endpoint
            sender := state.execution.core.context.currentSubject
            payload := { word0, word1 } } ∧
      next.resumable.contexts = saved :: state.resumable.contexts ∧
      state.blockingIPC.waiters endpoint = receiver :: rest := by
  cases hresolve : CapabilityHandle.resolveCurrent
      state.blockingIPC.scheduler.lifecycle.capabilities
      { caller := state.execution.core.context.currentSubject } handleWord .endpoint with
  | error reason => simp [dispatchBlockingSend, hresolve] at hwoke
  | ok resolution =>
      let payload : BlockingIPC.Payload := { word0, word1 }
      cases houtcome : BlockingIPCContext.send state.blockingIPCContext
          state.execution.core.context.currentSubject resolution.handle.slot payload with
      | mk blocking result released =>
          cases result with
          | ipcRejected reason =>
              simp [dispatchBlockingSend, hresolve, payload, houtcome] at hwoke
          | contextRejected reason =>
              simp [dispatchBlockingSend, hresolve, payload, houtcome] at hwoke
          | accepted =>
              cases released with
              | none => simp [dispatchBlockingSend, hresolve, payload, houtcome] at hwoke
              | some actual =>
                  cases hrestore :
                      publishReleasedBlockingContext state blocking actual with
                  | error reason =>
                      simp [dispatchBlockingSend, hresolve, payload, houtcome, hrestore] at hwoke
                  | ok published =>
                      simp [dispatchBlockingSend, hresolve, payload, houtcome, hrestore] at hwoke
                      subst actual
                      obtain ⟨endpoint, receiver, rest, hendpoint, hqueue, hstored,
                        haccepted, hcleared⟩ :=
                        BlockingIPCContext.send_released_exact state.blockingIPCContext
                          state.execution.core.context.currentSubject resolution.handle.slot
                          payload saved (by simp [houtcome])
                      have hipcExact :=
                        (BlockingIPCContext.send_accepted_ipc_exact
                          state.blockingIPCContext
                          state.execution.core.context.currentSubject resolution.handle.slot
                          payload haccepted).1
                      have hrawAccepted :=
                        (BlockingIPCContext.send_accepted_ipc_exact
                          state.blockingIPCContext
                          state.execution.core.context.currentSubject resolution.handle.slot
                          payload haccepted).2
                      rw [houtcome] at hipcExact hcleared
                      have hraw :
                          (BlockingIPC.send state.blockingIPC
                            state.execution.core.context.currentSubject
                            resolution.handle.slot payload).state =
                            BlockingIPC.wakeState state.blockingIPC endpoint receiver
                              { endpoint
                                sender := state.execution.core.context.currentSubject
                                payload } :=
                        BlockingIPC.send_accepted_wake_exact
                          state.blockingIPC state.execution.core.context.currentSubject
                          resolution.handle.slot payload endpoint receiver rest
                          hendpoint hqueue hrawAccepted
                      obtain ⟨actualReceiver, hstoredActual, hblockedExact⟩ :=
                        BlockingIPCContext.send_released_blocked_exact
                          state.blockingIPCContext
                          state.execution.core.context.currentSubject resolution.handle.slot
                          payload saved (by simp [houtcome])
                      have hcontext :=
                        (publishReleasedBlockingContext_restores_exact
                          state blocking saved published hrestore).2
                      have howner : saved.owner = receiver :=
                        BlockingIPCContext.validSaved_owner receiver saved
                          (hstate.1.2.2 receiver saved hstored)
                      have hownerActual : saved.owner = actualReceiver :=
                        BlockingIPCContext.validSaved_owner actualReceiver saved
                          (hstate.1.2.2 actualReceiver saved hstoredActual)
                      have hreceiver : actualReceiver = receiver :=
                        hownerActual.symm.trans howner
                      subst actualReceiver
                      rw [houtcome] at hblockedExact
                      have hrestoreExact := hrestore
                      unfold publishReleasedBlockingContext at hrestoreExact
                      split at hrestoreExact <;> try contradiction
                      split at hrestoreExact <;> try contradiction
                      split at hrestoreExact <;> try contradiction
                      split at hrestoreExact <;> try contradiction
                      simp only [Except.ok.injEq] at hrestoreExact
                      subst published
                      rw [howner] at hblockedExact
                      have hblockedWake :
                          blocking.blocked =
                            BlockingIPCContext.setBlocked
                              state.blockingContexts receiver none := by
                        simpa [CompositeState.blockingIPCContext] using hblockedExact
                      have hipcExact' :
                          blocking.ipc =
                            (BlockingIPC.send state.blockingIPC
                              state.execution.core.context.currentSubject
                              resolution.handle.slot payload).state := by
                        simpa [CompositeState.blockingIPCContext] using hipcExact
                      have hipcWake :
                          blocking.ipc =
                            BlockingIPC.wakeState state.blockingIPC endpoint receiver
                              { endpoint
                                sender := state.execution.core.context.currentSubject
                                payload := { word0, word1 } } := by
                        exact hipcExact'.trans (by simpa [payload] using hraw)
                      refine ⟨endpoint, receiver, rest, hstored, howner, ?_⟩
                      simp [dispatchBlockingSend, hresolve, payload, houtcome, hrestore,
                        publishBlockingIPCContext, hipcWake]
                      exact ⟨hblockedWake, hqueue⟩

/-- A mailbox-only blocking send changes no projection observed by dormant
cancellation except the mailbox itself. -/
theorem dispatchBlockingSend_sent_dormant_projections_exact
    state handleWord word0 word1
    (hsent : (dispatchBlockingSend state handleWord word0 word1).reply = .sent) :
    let next := (dispatchBlockingSend state handleWord word0 word1).state
    next.deferredCancels = state.deferredCancels ∧
      next.blockingContexts = state.blockingContexts ∧
      next.resumable.contexts = state.resumable.contexts ∧
      next.blockingIPC.waiterEndpoint = state.blockingIPC.waiterEndpoint ∧
      next.blockingIPC.scheduler = state.blockingIPC.scheduler := by
  cases hresolve : CapabilityHandle.resolveCurrent
      state.blockingIPC.scheduler.lifecycle.capabilities
      { caller := state.execution.core.context.currentSubject } handleWord .endpoint with
  | error reason => simp [dispatchBlockingSend, hresolve] at hsent
  | ok resolution =>
      let payload : BlockingIPC.Payload := { word0, word1 }
      cases houtcome : BlockingIPCContext.send state.blockingIPCContext
          state.execution.core.context.currentSubject resolution.handle.slot payload with
      | mk blocking result released =>
          cases result with
          | ipcRejected reason =>
              simp [dispatchBlockingSend, hresolve, payload, houtcome] at hsent
          | contextRejected reason =>
              simp [dispatchBlockingSend, hresolve, payload, houtcome] at hsent
          | accepted =>
              cases released with
              | some saved =>
                  cases hrestore : publishReleasedBlockingContext state blocking saved <;>
                    simp [dispatchBlockingSend, hresolve, payload, houtcome, hrestore] at hsent
              | none =>
                  have haccepted :
                      (BlockingIPCContext.send state.blockingIPCContext
                        state.execution.core.context.currentSubject resolution.handle.slot
                        payload).result = .accepted := by
                    simp [houtcome]
                  have hunreleased :
                      (BlockingIPCContext.send state.blockingIPCContext
                        state.execution.core.context.currentSubject resolution.handle.slot
                        payload).released = none := by
                    simp [houtcome]
                  have hscheduler :=
                    BlockingIPCContext.send_accepted_unreleased_scheduler_unchanged
                      state.blockingIPCContext
                      state.execution.core.context.currentSubject resolution.handle.slot
                      payload haccepted hunreleased
                  have hblocked :=
                    BlockingIPCContext.send_accepted_unreleased_blocked_unchanged
                      state.blockingIPCContext
                      state.execution.core.context.currentSubject resolution.handle.slot
                      payload haccepted hunreleased
                  have hwaiter :=
                    BlockingIPCContext.send_accepted_unreleased_waiterEndpoint_unchanged
                      state.blockingIPCContext
                      state.execution.core.context.currentSubject resolution.handle.slot
                      payload haccepted hunreleased
                  rw [houtcome] at hblocked hwaiter hscheduler
                  have hblocked' : blocking.blocked = state.blockingContexts := by
                    simpa [CompositeState.blockingIPCContext] using hblocked
                  have hwaiter' :
                      blocking.ipc.waiterEndpoint =
                        state.blockingIPC.waiterEndpoint := by
                    simpa [CompositeState.blockingIPCContext] using hwaiter
                  have hscheduler' :
                      blocking.ipc.scheduler = state.blockingIPC.scheduler := by
                    simpa [CompositeState.blockingIPCContext] using hscheduler
                  simp only [dispatchBlockingSend, hresolve, payload, houtcome]
                  simp [publishBlockingIPCContext, hblocked', hwaiter', hscheduler']

/-- Every outcome of the authoritative blocking send constructor preserves
the dormant-cancellation classification.  Rejections are atomic, mailbox-only
sends leave all observed control projections exact, and wakes affect only the
proved non-retained receiver. -/
theorem blockingSend_authoritativeOperationCompatible state handleWord word0 word1
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeOperationCompatible state
      (.blocking (.send handleWord word0 word1)) := by
  cases hmode : state.execution.mode with
  | handling active =>
      apply dormantCancellationCompatible_of_exact_projections state _ hstate
      all_goals simp [authoritativeGate, hmode]
  | halted record =>
      apply dormantCancellationCompatible_of_exact_projections state _ hstate
      all_goals simp [authoritativeGate, hmode]
  | running =>
      have hgate :
          (authoritativeGate state
            (.blocking (.send handleWord word0 word1))).state =
              (dispatchBlockingSend state handleWord word0 word1).state := by
        simp [authoritativeGate, hmode, applyAuthoritativeOperation,
          applyBlockingOperation]
      change DormantCancellationCompatible state
        (authoritativeGate state
          (.blocking (.send handleWord word0 word1))).state
      rw [hgate]
      cases hreply : (dispatchBlockingSend state handleWord word0 word1).reply with
      | handleRejected reason =>
          rw [dispatchBlockingSend_rejected_atomic state handleWord word0 word1 _
            (.handle reason) hreply]
          exact dormantCancellationCompatible_of_exact_projections
            state state hstate rfl rfl rfl rfl
      | contextRejected reason =>
          rw [dispatchBlockingSend_rejected_atomic state handleWord word0 word1 _
            (.context reason) hreply]
          exact dormantCancellationCompatible_of_exact_projections
            state state hstate rfl rfl rfl rfl
      | restoreRejected reason =>
          rw [dispatchBlockingSend_rejected_atomic state handleWord word0 word1 _
            (.restore reason) hreply]
          exact dormantCancellationCompatible_of_exact_projections
            state state hstate rfl rfl rfl rfl
      | rejected reason =>
          rw [dispatchBlockingSend_rejected_atomic state handleWord word0 word1 _
            (.ipc reason) hreply]
          exact dormantCancellationCompatible_of_exact_projections
            state state hstate rfl rfl rfl rfl
      | sent =>
          have hshape := dispatchBlockingSend_sent_dormant_projections_exact
            state handleWord word0 word1 hreply
          dsimp only at hshape
          rcases hshape with ⟨hdeferred, hblocked, hcontexts, hwaiter, hscheduler⟩
          refine ⟨hdeferred, ?_, ?_, ?_⟩
          · intro subject hsome
            rw [hblocked] at hsome
            rw [hdeferred]
            exact hstate.2.1.2.1 subject hsome
          · intro subject saved hsaved
            rw [hblocked] at hsaved
            rw [hcontexts]
            exact hstate.2.2.1 subject saved hsaved
          · intro subject saved hretained
            have hvalid := hstate.2.1.2.2 subject saved hretained
            rw [hwaiter, hscheduler, hcontexts]
            exact ⟨hvalid.2.1, hvalid.2.2.1, hvalid.2.2.2.1,
              hvalid.2.2.2.2.1, hvalid.2.2.2.2.2.1,
              hvalid.2.2.2.2.2.2, hstate.2.2.2 subject saved hretained⟩
      | woke saved =>
          have hcoherent : state.BlockingIPCCoherent := by
            rcases hstate.blocking.1 with
              ⟨_, _, _, _, _, _, _, _, _, _, _, _, hblocking, _⟩
            exact hblocking
          have hshape := dispatchBlockingSend_woke_projection_exact
            state handleWord word0 word1 saved
              ⟨hstate.blocking.2, hcoherent⟩ hreply
          dsimp only at hshape
          obtain ⟨endpoint, receiver, rest, hstored, howner, hdeferred,
            hblocked, hipc, hcontexts, hqueue⟩ := hshape
          refine ⟨hdeferred, ?_, ?_, ?_⟩
          · intro candidate hsome
            rw [hblocked] at hsome
            by_cases heq : candidate = receiver
            · subst candidate
              simp [BlockingIPCContext.setBlocked] at hsome
            · rw [hdeferred]
              apply hstate.2.1.2.1 candidate
              change (state.blockingContexts candidate).isSome = true
              simpa [BlockingIPCContext.setBlocked, heq] using hsome
          · intro candidate blockedSaved hsome
            rw [hblocked] at hsome
            by_cases heq : candidate = receiver
            · subst candidate
              simp [BlockingIPCContext.setBlocked] at hsome
            · have hbefore :
                  state.blockingContexts candidate = some blockedSaved := by
                simpa [BlockingIPCContext.setBlocked, heq] using hsome
              rw [hcontexts]
              simpa [ResumablePreemption.contextFor, howner, heq, Ne.symm heq] using
                hstate.2.2.1 candidate blockedSaved hbefore
          · intro candidate retained hretained
            have hvalid := hstate.2.1.2.2 candidate retained hretained
            have hnotReceiver : receiver ≠ candidate := by
              intro heq
              have hnotOwner := dispatchBlockingSend_woke_not_retained
                state handleWord word0 word1 saved candidate retained
                  hstate hretained hreply
              exact hnotOwner (howner.trans heq)
            rw [hipc, hcontexts]
            have hbefore :
                state.blockingIPC.waiterEndpoint candidate = none ∧
                  state.blockingIPC.scheduler.lifecycle.capabilities.subjects candidate =
                    true ∧
                  state.blockingIPC.scheduler.lifecycle.runnable candidate = false ∧
                  state.blockingIPC.scheduler.lifecycle.current ≠ some candidate ∧
                  candidate ∉ state.blockingIPC.scheduler.ready ∧
                  Scheduler.ownsAddressSpace state.blockingIPC.scheduler candidate =
                    some candidate ∧
                  ResumablePreemption.contextFor state.resumable.contexts candidate =
                    none := by
              simpa [CompositeState.blockingIPCContext] using
                And.intro hvalid.2.1
                  (And.intro hvalid.2.2.1
                    (And.intro hvalid.2.2.2.1
                      (And.intro hvalid.2.2.2.2.1
                        (And.intro hvalid.2.2.2.2.2.1
                          (And.intro hvalid.2.2.2.2.2.2
                            (hstate.2.2.2 candidate retained hretained))))))
            simpa [BlockingIPC.wakeState, BlockingIPC.setWaiterEndpoint,
              SubjectLifecycle.setBool, Scheduler.ownsAddressSpace_eq_some_iff,
              ResumablePreemption.contextFor, howner, hnotReceiver,
              Ne.symm hnotReceiver] using hbefore

/-- Blocking send has a closed preservation theorem at the folded
authoritative boundary; callers need no post-state compatibility witness. -/
theorem authoritativeGate_blockingSend_preserves_authoritativeRuntimeWellFormed
    state handleWord word0 word1
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeGate state
        (.blocking (.send handleWord word0 word1))).state :=
  authoritativeGate_preserves_authoritativeRuntimeWellFormed_of_compatible state
    (.blocking (.send handleWord word0 word1)) hstate
    (blockingSend_authoritativeOperationCompatible
      state handleWord word0 word1 hstate)

/-- Cancelling a dormant retained identity is exactly atomic.  The retained
classification supplies the missing-waiter fact consumed directly by the
blocking cancellation transition. -/
theorem dispatchBlockingCancel_retained_unchanged state subject retained
    (hstate : AuthoritativeRuntimeWellFormed state)
    (hretained : state.deferredCancels.retained subject = some retained) :
    (dispatchBlockingCancel state subject).state = state := by
  have hwaiter :=
    (hstate.2.1.2.2 subject retained hretained).2.1
  change state.blockingIPC.waiterEndpoint subject = none at hwaiter
  simp [dispatchBlockingCancel, BlockingIPCContext.cancel,
    CompositeState.blockingIPCContext, hwaiter]

/-- A successful blocking cancellation changes only the cancelled identity's
blocking indexes and scheduler state, then prepends its released context. -/
theorem dispatchBlockingCancel_cancelled_projection_exact state subject saved
    (hstate : BlockingReceiveWellFormed state)
    (hcancelled : (dispatchBlockingCancel state subject).reply = .cancelled saved) :
    let next := (dispatchBlockingCancel state subject).state
    next.deferredCancels = state.deferredCancels ∧
      next.blockingContexts =
        BlockingIPCContext.setBlocked state.blockingContexts subject none ∧
      next.blockingIPC = BlockingIPC.cancelSubject state.blockingIPC subject ∧
      next.resumable.contexts = saved :: state.resumable.contexts ∧
      saved.owner = subject := by
  cases houtcome : BlockingIPCContext.cancel state.blockingIPCContext subject with
  | mk blocking result released =>
      cases result with
      | notWaiting => simp [dispatchBlockingCancel, houtcome] at hcancelled
      | ipcRejected reason => simp [dispatchBlockingCancel, houtcome] at hcancelled
      | contextRejected reason => simp [dispatchBlockingCancel, houtcome] at hcancelled
      | cancelled =>
          cases released with
          | none => simp [dispatchBlockingCancel, houtcome] at hcancelled
          | some actual =>
              cases hrestore : publishReleasedBlockingContext state blocking actual with
              | error reason =>
                  simp [dispatchBlockingCancel, houtcome, hrestore] at hcancelled
              | ok published =>
                  simp [dispatchBlockingCancel, houtcome, hrestore] at hcancelled
                  subst actual
                  have hcontext := BlockingIPCContext.cancel_cancelled_exact
                    state.blockingIPCContext subject saved (by simp [houtcome])
                      (by simp [houtcome])
                  have hipc :
                      blocking.ipc = BlockingIPC.cancelSubject state.blockingIPC subject := by
                    have hraw := BlockingIPC.cancelSubjectTyped_cancelled_exact
                      state.blockingIPC subject (by
                        have := (BlockingIPCContext.cancel_cancelled_ipc_exact
                          state.blockingIPCContext subject (by simp [houtcome])).2
                        exact this)
                    have hblocking :=
                      (BlockingIPCContext.cancel_cancelled_ipc_exact
                        state.blockingIPCContext subject (by simp [houtcome])).1
                    simpa [houtcome] using hblocking.trans hraw
                  have hblocked :
                      blocking.blocked =
                        BlockingIPCContext.setBlocked state.blockingContexts subject none := by
                    have hshape := houtcome
                    unfold BlockingIPCContext.cancel at hshape
                    split at hshape <;> try simp_all
                    split at hshape <;> try simp_all
                    exact congrArg BlockingIPCContext.State.blocked hshape.symm
                  have howner : saved.owner = subject :=
                    BlockingIPCContext.validSaved_owner subject saved
                      (hstate.1.2.2 subject saved hcontext.1)
                  have hrestoreExact := hrestore
                  unfold publishReleasedBlockingContext at hrestoreExact
                  split at hrestoreExact <;> try contradiction
                  split at hrestoreExact <;> try contradiction
                  split at hrestoreExact <;> try contradiction
                  split at hrestoreExact <;> try contradiction
                  simp only [Except.ok.injEq] at hrestoreExact
                  subst published
                  simp [dispatchBlockingCancel, houtcome,
                    hrestore, publishBlockingIPCContext, hipc, hblocked, howner]

/-- Blocking cancellation preserves every dormant retained cancellation.
Targeting a retained identity is atomic; targeting another waiter changes only
that waiter's blocking, scheduler, and restored-context projections. -/
theorem blockingCancel_authoritativeOperationCompatible state subject
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeOperationCompatible state (.blocking (.cancel subject)) := by
  cases hmode : state.execution.mode with
  | handling active =>
      apply dormantCancellationCompatible_of_exact_projections state _ hstate
      all_goals simp [authoritativeGate, hmode]
  | halted record =>
      apply dormantCancellationCompatible_of_exact_projections state _ hstate
      all_goals simp [authoritativeGate, hmode]
  | running =>
      have hgate :
          (authoritativeGate state (.blocking (.cancel subject))).state =
            (dispatchBlockingCancel state subject).state := by
        simp [authoritativeGate, hmode, applyAuthoritativeOperation,
          applyBlockingOperation]
      change DormantCancellationCompatible state
        (authoritativeGate state (.blocking (.cancel subject))).state
      rw [hgate]
      cases hreply : (dispatchBlockingCancel state subject).reply with
      | notWaiting =>
          rw [dispatchBlockingCancel_rejected_atomic state subject _
            .notWaiting hreply]
          exact dormantCancellationCompatible_of_exact_projections
            state state hstate rfl rfl rfl rfl
      | contextRejected reason =>
          rw [dispatchBlockingCancel_rejected_atomic state subject _
            (.context reason) hreply]
          exact dormantCancellationCompatible_of_exact_projections
            state state hstate rfl rfl rfl rfl
      | restoreRejected reason =>
          rw [dispatchBlockingCancel_rejected_atomic state subject _
            (.restore reason) hreply]
          exact dormantCancellationCompatible_of_exact_projections
            state state hstate rfl rfl rfl rfl
      | rejected reason =>
          rw [dispatchBlockingCancel_rejected_atomic state subject _
            (.ipc reason) hreply]
          exact dormantCancellationCompatible_of_exact_projections
            state state hstate rfl rfl rfl rfl
      | cancelled restored =>
          have hcoherent : state.BlockingIPCCoherent := by
            rcases hstate.blocking.1 with
              ⟨_, _, _, _, _, _, _, _, _, _, _, _, hblocking, _⟩
            exact hblocking
          have hshape := dispatchBlockingCancel_cancelled_projection_exact
            state subject restored
              ⟨hstate.blocking.2, hcoherent⟩ hreply
          dsimp only at hshape
          rcases hshape with ⟨hdeferred, hblocked, hipc, hcontexts, howner⟩
          refine ⟨hdeferred, ?_, ?_, ?_⟩
          · intro candidate hsome
            rw [hblocked] at hsome
            by_cases heq : candidate = subject
            · subst candidate
              simp [BlockingIPCContext.setBlocked] at hsome
            · rw [hdeferred]
              apply hstate.2.1.2.1 candidate
              change (state.blockingContexts candidate).isSome = true
              simpa [BlockingIPCContext.setBlocked, heq] using hsome
          · intro candidate saved hsome
            rw [hblocked] at hsome
            by_cases heq : candidate = subject
            · subst candidate
              simp [BlockingIPCContext.setBlocked] at hsome
            · have hbefore : state.blockingContexts candidate = some saved := by
                simpa [BlockingIPCContext.setBlocked, heq] using hsome
              rw [hcontexts]
              simpa [ResumablePreemption.contextFor, howner, heq, Ne.symm heq] using
                hstate.2.2.1 candidate saved hbefore
          · intro candidate saved hretained
            by_cases heq : candidate = subject
            · subst candidate
              have hatomic := dispatchBlockingCancel_retained_unchanged
                state subject saved hstate hretained
              rw [hatomic]
              exact ⟨(hstate.2.1.2.2 subject saved hretained).2.1,
                (hstate.2.1.2.2 subject saved hretained).2.2.1,
                (hstate.2.1.2.2 subject saved hretained).2.2.2.1,
                (hstate.2.1.2.2 subject saved hretained).2.2.2.2.1,
                (hstate.2.1.2.2 subject saved hretained).2.2.2.2.2.1,
                (hstate.2.1.2.2 subject saved hretained).2.2.2.2.2.2,
                hstate.2.2.2 subject saved hretained⟩
            · have hvalid := hstate.2.1.2.2 candidate saved hretained
              simp only [CompositeState.blockingIPCContext] at hvalid
              rw [hipc, hcontexts]
              have hbefore := And.intro hvalid.2.1
                (And.intro hvalid.2.2.1
                  (And.intro hvalid.2.2.2.1
                    (And.intro hvalid.2.2.2.2.1
                      (And.intro hvalid.2.2.2.2.2.1
                        (And.intro hvalid.2.2.2.2.2.2
                          (hstate.2.2.2 candidate saved hretained))))))
              simp only [BlockingIPC.cancelSubject]
              split
              · simpa [ResumablePreemption.contextFor, howner, heq, Ne.symm heq] using
                  hbefore
              · split
                · simpa [ResumablePreemption.contextFor, howner, heq, Ne.symm heq] using
                    hbefore
                · by_cases hlive :
                      state.blockingIPC.scheduler.lifecycle.capabilities.subjects subject =
                        true
                  · simpa [hlive, BlockingIPC.setWaiterEndpoint,
                      BlockingIPC.removeWaiter, BlockingIPC.setCompletion,
                      SubjectLifecycle.setBool, Scheduler.ownsAddressSpace,
                      ResumablePreemption.contextFor,
                      howner, heq, Ne.symm heq] using hbefore
                  · simpa [hlive, BlockingIPC.setWaiterEndpoint,
                      BlockingIPC.removeWaiter, BlockingIPC.setCompletion,
                      SubjectLifecycle.setBool, Scheduler.ownsAddressSpace,
                      ResumablePreemption.contextFor,
                      howner, heq, Ne.symm heq] using hbefore

/-- Blocking cancellation has a closed preservation theorem at the folded
authoritative boundary; callers need no post-state compatibility witness. -/
theorem authoritativeGate_blockingCancel_preserves_authoritativeRuntimeWellFormed
    state subject (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeGate state (.blocking (.cancel subject))).state :=
  authoritativeGate_preserves_authoritativeRuntimeWellFormed_of_compatible state
    (.blocking (.cancel subject)) hstate
    (blockingCancel_authoritativeOperationCompatible state subject hstate)

/-- Return-authority selection changes only the execution projection.  Its
public constructor therefore derives dormant-cancellation compatibility
directly from the folded invariant, with no caller-supplied post-state law. -/
theorem selectUserReturn_authoritativeOperationCompatible state purpose
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeOperationCompatible state
      (.ordinary (.selectUserReturn purpose)) := by
  apply dormantCancellationCompatible_of_exact_projections state _ hstate
  all_goals
    cases hmode : state.execution.mode <;>
      simp [authoritativeGate, hmode, applyAuthoritativeOperation,
        applyOperation, selectLiveReturnAuthority]
    all_goals split <;> rfl

/-- Outgoing return completion may change execution mode and the resumable
fatal latch, but it cannot change the waiter, deferred-cancellation, or saved
context stores. -/
theorem userReturn_authoritativeOperationCompatible state request
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeOperationCompatible state
      (.ordinary (.userReturn request)) := by
  apply dormantCancellationCompatible_of_exact_projections state _ hstate
  all_goals
    cases hmode : state.execution.mode <;>
      simp [authoritativeGate, hmode, applyAuthoritativeOperation, applyOperation]
    all_goals split <;> simp

/-- Restart is the identity constructor under every gate mode, so its
compatibility obligation follows from exact projection preservation. -/
theorem restart_authoritativeOperationCompatible state
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeOperationCompatible state (.ordinary .restart) := by
  apply dormantCancellationCompatible_of_exact_projections state _ hstate
  all_goals
    cases hmode : state.execution.mode <;>
      simp [authoritativeGate, hmode, applyAuthoritativeOperation, applyOperation]

/-- Return-authority selection unconditionally preserves the complete folded
authoritative invariant. -/
theorem authoritativeGate_selectUserReturn_preserves_authoritativeRuntimeWellFormed
    state purpose (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeGate state
        (.ordinary (.selectUserReturn purpose))).state :=
  authoritativeGate_preserves_authoritativeRuntimeWellFormed_of_compatible state
    (.ordinary (.selectUserReturn purpose)) hstate
    (selectUserReturn_authoritativeOperationCompatible state purpose hstate)

/-- Outgoing user-return completion unconditionally preserves the complete
folded authoritative invariant. -/
theorem authoritativeGate_userReturn_preserves_authoritativeRuntimeWellFormed
    state request (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeGate state (.ordinary (.userReturn request))).state :=
  authoritativeGate_preserves_authoritativeRuntimeWellFormed_of_compatible state
    (.ordinary (.userReturn request)) hstate
    (userReturn_authoritativeOperationCompatible state request hstate)

/-- Restart unconditionally preserves the complete folded authoritative
invariant. -/
theorem authoritativeGate_restart_preserves_authoritativeRuntimeWellFormed
    state (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeGate state (.ordinary .restart)).state :=
  authoritativeGate_preserves_authoritativeRuntimeWellFormed_of_compatible state
    (.ordinary .restart) hstate
    (restart_authoritativeOperationCompatible state hstate)

/-- Legacy admission vocabulary retained for source compatibility.  It is
vacuous for every operation and is not part of the published gate contract. -/
def AuthoritativeOperationAdmissible (_state : CompositeState) :
    AuthoritativeOperation → Prop
  | _ => True

/-- Every post-state compatibility obligation is derived from the
authoritative pre-invariant.  The contained-interrupt branch consumes only its
explicit trusted identity admission fact; every other ordinary, blocking, and
deferred-drain constructor is closed. -/
theorem authoritativeOperationCompatible_of_admissible state operation
    (hstate : AuthoritativeRuntimeWellFormed state)
    (hadmissible : AuthoritativeOperationAdmissible state operation) :
    AuthoritativeOperationCompatible state operation := by
  cases operation with
  | ordinary operation =>
      cases operation with
      | interrupt frame =>
          exact interrupt_authoritativeOperationCompatible state frame
      | nmi raw context => trivial
      | selectUserReturn purpose =>
          exact selectUserReturn_authoritativeOperationCompatible state purpose hstate
      | userReturn request =>
          exact userReturn_authoritativeOperationCompatible state request hstate
      | syscall call =>
          exact syscall_authoritativeOperationCompatible state call hstate
      | ipc call =>
          exact blockingStateNeutral_authoritativeOperationCompatible state
            (.ipc call) (.ipc call) hstate
      | resumePreempt frame registers =>
          exact resumePreempt_authoritativeOperationCompatible
            state frame registers hstate
      | transferOffer endpointWord sourceWord sourceKind payload rights =>
          exact transferOffer_authoritativeOperationCompatible state endpointWord
            sourceWord sourceKind payload rights hstate
      | transferAccept endpointWord destinationSlot =>
          exact transferAccept_authoritativeOperationCompatible
            state endpointWord destinationSlot hstate
      | capabilityCopy source destination destinationSlot rights =>
          exact capabilityCopy_authoritativeOperationCompatible state source
            destination destinationSlot rights hstate
      | capabilityRevoke authoritySlot victim victimSlot =>
          exact capabilityRevoke_authoritativeOperationCompatible state authoritySlot
            victim victimSlot hstate
      | capabilityRevokeSubtree authoritySlot victim victimSlot =>
          exact capabilityRevokeSubtree_authoritativeOperationCompatible state
            authoritySlot victim victimSlot hstate
      | map slot page permissions =>
          exact map_authoritativeOperationCompatible state slot page permissions hstate
      | unmap page =>
          exact unmap_authoritativeOperationCompatible state page hstate
      | protect page permissions =>
          exact protect_authoritativeOperationCompatible
            state page permissions hstate
      | createSubject subject =>
          exact createSubject_authoritativeOperationCompatible state subject hstate
      | terminateSubject subject => trivial
      | scheduleAdd subject =>
          exact scheduleAdd_authoritativeOperationCompatible state subject hstate
      | scheduleRemove subject =>
          exact scheduleRemove_authoritativeOperationCompatible state subject hstate
      | scheduleNext =>
          exact blockingStateNeutral_authoritativeOperationCompatible state
            .scheduleNext .scheduleNext hstate
      | scheduleYield =>
          exact blockingStateNeutral_authoritativeOperationCompatible state
            .scheduleYield .scheduleYield hstate
      | scheduleTick =>
          exact blockingStateNeutral_authoritativeOperationCompatible state
            .scheduleTick .scheduleTick hstate
      | terminateCurrent => trivial
      | restart =>
          exact restart_authoritativeOperationCompatible state hstate
  | blocking operation =>
      cases operation with
      | receive handleWord frame registers =>
          exact blockingReceive_authoritativeOperationCompatible state handleWord
            frame registers hstate
      | send handleWord word0 word1 =>
          exact blockingSend_authoritativeOperationCompatible state handleWord
            word0 word1 hstate
      | cancel subject =>
          exact blockingCancel_authoritativeOperationCompatible state subject hstate
  | drainDeferred subject => trivial

/-- The strengthened authoritative gate preserves the complete folded runtime
invariant from pre-state evidence alone, with no operation-local premise. -/
theorem authoritativeGate_preserves_authoritativeRuntimeWellFormed_of_admissible
    state operation (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeGate state operation).state :=
  authoritativeGate_preserves_authoritativeRuntimeWellFormed_of_compatible
    state operation hstate
    (authoritativeOperationCompatible_of_admissible
      state operation hstate trivial)

/-- Final public gate contract: every authoritative operation preserves the
complete folded invariant from pre-state evidence alone. -/
theorem authoritativeGate_preserves_authoritativeRuntimeWellFormed
    state operation (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeGate state operation).state :=
  authoritativeGate_preserves_authoritativeRuntimeWellFormed_of_admissible
    state operation hstate

/-- The self-contained neutral-constructor compatibility laws preserve the
authoritative DMA conjunct as a consequence of complete global preservation.
No compatibility premise for any unfinished constructor enters this slice. -/
theorem authoritativeGate_neutralConstructors_preserve_dmaQuarantined
    state (hstate : AuthoritativeRuntimeWellFormed state) :
    (∀ purpose,
      (authoritativeGate state
        (.ordinary (.selectUserReturn purpose))).state.DMAQuarantined) ∧
    (∀ request,
      (authoritativeGate state
        (.ordinary (.userReturn request))).state.DMAQuarantined) ∧
    (authoritativeGate state (.ordinary .restart)).state.DMAQuarantined := by
  refine ⟨?_, ?_, ?_⟩
  · intro purpose
    exact
      (authoritativeGate_selectUserReturn_preserves_authoritativeRuntimeWellFormed
        state purpose hstate).dmaQuarantined
  · intro request
    exact
      (authoritativeGate_userReturn_preserves_authoritativeRuntimeWellFormed
        state request hstate).dmaQuarantined
  · exact
      (authoritativeGate_restart_preserves_authoritativeRuntimeWellFormed
        state hstate).dmaQuarantined

def runAuthoritativeOperations (state : CompositeState) :
    List AuthoritativeOperation → CompositeState
  | [] => state
  | operation :: rest =>
      runAuthoritativeOperations (authoritativeGate state operation).state rest

/-- Arbitrary finite interleavings from the readiness-free mixed language
preserve the complete global/scheduler/mailbox/waiter/context invariant.
Consequently every later blocking member consumes the invariant established
by the preceding transition rather than a legacy per-state readiness gate. -/
theorem runAuthoritativeReadinessFreeMixedTrace_preserves_blockingRuntimeWellFormed
    state operations
    (hoperations : ReadinessFreeMixedTrace operations)
    (hstate : BlockingRuntimeWellFormed state) :
    BlockingRuntimeWellFormed
      (runAuthoritativeOperations state operations) := by
  induction hoperations generalizing state with
  | nil => exact hstate
  | ordinary hoperation hrest ih =>
      exact ih _
        (authoritativeGate_blockingRuntimePreserving_preserves_blockingRuntimeWellFormed
          state _ hoperation hstate)
  | blocking hrest ih =>
      exact ih _
        (authoritativeGate_blocking_preserves_blockingRuntimeWellFormed
          state _ hstate)

/-- The readiness-free language is inhabited by a heterogeneous trace with
ordinary lifecycle and revocation mutations on both sides of a blocking
cancellation.  This keeps the general preservation theorem's trace premise
independently auditable rather than relying on an abstract inhabitant. -/
theorem readinessFreeMixedTrace_nonvacuous :
    ReadinessFreeMixedTrace
      [.ordinary (.createSubject 1), .blocking (.cancel 1),
        .ordinary (.capabilityRevoke 0 1 0)] := by
  exact .ordinary (.createSubject 1)
    (.blocking
      (.ordinary (.capabilityRevoke 0 1 0) .nil))

/-- Recursive operation-specific compatibility for a finite mixed trace.
Unlike the removed postcondition contract, each member records only the
independently stated input premise consumed by that operation. -/
def AuthoritativeTraceCompatible (state : CompositeState) :
    List AuthoritativeOperation → Prop
  | [] => True
  | operation :: rest =>
      AuthoritativeOperationCompatible state operation ∧
      AuthoritativeTraceCompatible (authoritativeGate state operation).state rest

/-- Legacy trace-admission vocabulary retained for source compatibility.  It
is vacuous and is not part of the published arbitrary-trace theorem. -/
def AuthoritativeTraceAdmissible (_state : CompositeState) :
    List AuthoritativeOperation → Prop := fun _ => True

/-- Every compatibility-certified finite interleaving of ordinary and blocking
operations preserves the complete authoritative global invariant without
assuming any intermediate preservation conclusion.  This is intentionally not
a universal trace theorem: no inhabitant is provided for an arbitrary
operation list. -/
theorem runAuthoritativeOperations_preserves_authoritativeRuntimeWellFormed_of_compatible
    state operations (hstate : AuthoritativeRuntimeWellFormed state)
    (hcompatible : AuthoritativeTraceCompatible state operations) :
    AuthoritativeRuntimeWellFormed (runAuthoritativeOperations state operations) := by
  induction operations generalizing state with
  | nil => exact hstate
  | cons operation rest ih =>
      exact ih (authoritativeGate state operation).state
        (authoritativeGate_preserves_authoritativeRuntimeWellFormed_of_compatible
          state operation hstate hcompatible.1) hcompatible.2

/-- Arbitrary admitted finite traces preserve the authoritative invariant.
Unlike `AuthoritativeTraceCompatible`, callers never prove a fact about a
gate-selected post-state: compatibility for each member is reconstructed from
the invariant established by its predecessor. -/
theorem runAuthoritativeOperations_preserves_authoritativeRuntimeWellFormed_of_admissible
    state operations (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed (runAuthoritativeOperations state operations) := by
  induction operations generalizing state with
  | nil => exact hstate
  | cons operation rest ih =>
      have hnext :=
        authoritativeGate_preserves_authoritativeRuntimeWellFormed_of_admissible
          state operation hstate
      exact ih (authoritativeGate state operation).state hnext

/-- Final public trace contract: every finite authoritative operation list
preserves the folded invariant from the initial pre-invariant alone. -/
theorem runAuthoritativeOperations_preserves_authoritativeRuntimeWellFormed
    state operations (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (runAuthoritativeOperations state operations) :=
  runAuthoritativeOperations_preserves_authoritativeRuntimeWellFormed_of_admissible
    state operations hstate

/-- A sealed capability send followed by revocation is an ordinary
authoritative trace, with no trace-local admission or post-state premise. -/
theorem runAuthoritativeRevokeAfterSend_preserves_authoritativeRuntimeWellFormed
    state endpointWord sourceWord sourceKind payload rights
    authoritySlot victim victimSlot
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (runAuthoritativeOperations state
        [.ordinary (.transferOffer endpointWord sourceWord sourceKind payload rights),
          .ordinary (.capabilityRevoke authoritySlot victim victimSlot)]) :=
  runAuthoritativeOperations_preserves_authoritativeRuntimeWellFormed_of_admissible
    state _ hstate

/-- Retiring an identity before an attempted resumable-context restore is an
explicit authoritative trace.  Any resulting stale-context denial is covered
by the same unconditional preservation boundary and is therefore atomic. -/
theorem runAuthoritativeStaleResumableContextTrace_preserves_authoritativeRuntimeWellFormed
    state subject frame registers
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (runAuthoritativeOperations state
        [.ordinary (.terminateSubject subject),
          .ordinary (.resumePreempt frame registers)]) :=
  runAuthoritativeOperations_preserves_authoritativeRuntimeWellFormed_of_admissible
    state _ hstate

/-- Any finite sequence of resumable-preemption attempts has a closed
recursive compatibility certificate.  Each successor certificate is derived
from the invariant preserved by the preceding switch, so no intermediate
post-state law or readiness witness is supplied by the caller. -/
theorem authoritativeTraceCompatible_resumePreempts state
    (steps : List (Interrupt.HardwareFrame × ResumablePreemption.Registers))
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeTraceCompatible state
      (steps.map fun step =>
        AuthoritativeOperation.ordinary
          (.resumePreempt step.1 step.2)) := by
  induction steps generalizing state with
  | nil => trivial
  | cons step rest ih =>
      simp only [List.map_cons, AuthoritativeTraceCompatible]
      exact
        ⟨resumePreempt_authoritativeOperationCompatible
            state step.1 step.2 hstate,
          ih (authoritativeGate state
              (.ordinary (.resumePreempt step.1 step.2))).state
            (authoritativeGate_resumePreempt_preserves_authoritativeRuntimeWellFormed
              state step.1 step.2 hstate)⟩

/-- The authoritative trace runner unconditionally preserves the complete
folded runtime invariant across arbitrary finite resumable-preemption
sequences, including accepted switches, typed denials, and fatal suffixes. -/
theorem runAuthoritativeResumePreempts_preserves_authoritativeRuntimeWellFormed
    state
    (steps : List (Interrupt.HardwareFrame × ResumablePreemption.Registers))
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (runAuthoritativeOperations state
        (steps.map fun step =>
          AuthoritativeOperation.ordinary
            (.resumePreempt step.1 step.2))) := by
  exact runAuthoritativeOperations_preserves_authoritativeRuntimeWellFormed_of_compatible
    state _ hstate
    (authoritativeTraceCompatible_resumePreempts state steps hstate)

/-- Arbitrary finite scheduler-admission sequences have a closed recursive
compatibility certificate.  Each undrained candidate is rejected atomically;
every accepted member establishes the invariant consumed by the next member. -/
theorem authoritativeTraceCompatible_scheduleAdds state
    (subjects : List Scheduler.SubjectId)
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeTraceCompatible state
      (subjects.map fun subject =>
        AuthoritativeOperation.ordinary (.scheduleAdd subject)) := by
  induction subjects generalizing state with
  | nil => trivial
  | cons subject rest ih =>
      simp only [List.map_cons, AuthoritativeTraceCompatible]
      exact
        ⟨scheduleAdd_authoritativeOperationCompatible state subject hstate,
          ih (authoritativeGate state
              (.ordinary (.scheduleAdd subject))).state
            (authoritativeGate_scheduleAdd_preserves_authoritativeRuntimeWellFormed
              state subject hstate)⟩

/-- The authoritative runner unconditionally preserves the complete folded
runtime invariant across arbitrary scheduler-admission traces, including any
number of typed undrained-cancellation denials. -/
theorem runAuthoritativeScheduleAdds_preserves_authoritativeRuntimeWellFormed
    state (subjects : List Scheduler.SubjectId)
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (runAuthoritativeOperations state
        (subjects.map fun subject =>
          AuthoritativeOperation.ordinary (.scheduleAdd subject))) := by
  exact runAuthoritativeOperations_preserves_authoritativeRuntimeWellFormed_of_compatible
    state _ hstate
    (authoritativeTraceCompatible_scheduleAdds state subjects hstate)

/-- Arbitrary authoritative successor traces retain the exact boot-accepted
PCI observation.  This proof ranges over ordinary, blocking, and deferred
drain constructors directly and therefore needs neither the stronger global
invariant nor its still-partial operation compatibility certificate. -/
theorem runAuthoritativeOperations_preserves_dmaQuarantined
    state operations (hstate : state.DMAQuarantined) :
    let next := runAuthoritativeOperations state operations
    next.DMAQuarantined ∧
      DMAQuarantine.quarantine next.dmaObserved = true := by
  induction operations generalizing state with
  | nil => exact ⟨hstate, hstate.quarantine⟩
  | cons operation rest ih =>
      simp only [runAuthoritativeOperations]
      exact ih (authoritativeGate state operation).state
        (authoritativeGate_preserves_dmaQuarantined state operation hstate)

/-- Arbitrary finite ordinary traces need no reconstructed blocking or drain
readiness.  Their recursive compatibility evidence composes operation-local
premises without assuming the authoritative invariant at an intermediate
gate-selected post-state. -/
theorem runAuthoritativeOrdinaryOperations_preserves_authoritativeRuntimeWellFormed
    state (operations : List Operation)
    (hstate : AuthoritativeRuntimeWellFormed state)
    (hcompatible : AuthoritativeTraceCompatible state
      (operations.map AuthoritativeOperation.ordinary)) :
    AuthoritativeRuntimeWellFormed
      (runAuthoritativeOperations state
        (operations.map AuthoritativeOperation.ordinary)) := by
  exact runAuthoritativeOperations_preserves_authoritativeRuntimeWellFormed_of_compatible
    state (operations.map AuthoritativeOperation.ordinary) hstate hcompatible

/-- A public deferred-drain step preserves the full retained-context
classification under every outer-latch result. -/
theorem authoritativeGate_drainDeferred_preserves_deferredBlockingRuntimeWellFormed
    state subject (hstate : DeferredBlockingRuntimeWellFormed state) :
    DeferredBlockingRuntimeWellFormed
      (authoritativeGate state (.drainDeferred subject)).state := by
  cases hmode : state.execution.mode with
  | running =>
      simpa [authoritativeGate, hmode, applyAuthoritativeOperation] using
        drainDeferredCancellation_preserves_deferredBlockingRuntimeWellFormed
          state subject hstate
  | handling active => simpa [authoritativeGate, hmode] using hstate
  | halted record => simpa [authoritativeGate, hmode] using hstate

/-- Explicit identity termination crosses the public successor gate while
preserving the complete deferred classification needed by later checked
cancellation drains. -/
theorem authoritativeGate_terminateSubject_preserves_deferredBlockingRuntimeWellFormed
    state subject (hstate : DeferredBlockingRuntimeWellFormed state) :
    DeferredBlockingRuntimeWellFormed
      (authoritativeGate state (.ordinary (.terminateSubject subject))).state := by
  rw [authoritativeGate_ordinary_state]
  exact gate_terminateSubject_preserves_deferredBlockingRuntimeWellFormed
    state subject hstate

/-- Scheduler-selected termination crosses the successor gate without
weakening the retained-context classification needed by a following deferred
drain. -/
theorem authoritativeGate_terminateCurrent_preserves_deferredBlockingRuntimeWellFormed
    state (hstate : DeferredBlockingRuntimeWellFormed state) :
    DeferredBlockingRuntimeWellFormed
      (authoritativeGate state (.ordinary .terminateCurrent)).state := by
  rw [authoritativeGate_ordinary_state]
  exact gate_terminateCurrent_preserves_deferredBlockingRuntimeWellFormed
    state hstate

/-- The public successor gate retains the complete deferred blocking runtime
across every inbound interrupt result without an external identity premise. -/
theorem authoritativeGate_interrupt_preserves_deferredBlockingRuntimeWellFormed
    state frame
    (hstate : DeferredBlockingRuntimeWellFormed state) :
    DeferredBlockingRuntimeWellFormed
      (authoritativeGate state (.ordinary (.interrupt frame))).state := by
  rw [authoritativeGate_ordinary_state]
  exact gate_interrupt_preserves_deferredBlockingRuntimeWellFormed
    state frame hstate

/-- Interrupt identity validation is internal to the authoritative transition:
matching identity cleans up, mismatch rejects atomically, and every outcome
preserves the complete folded runtime invariant. -/
theorem authoritativeGate_interrupt_preserves_authoritativeRuntimeWellFormed
    state frame
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeGate state (.ordinary (.interrupt frame))).state :=
  authoritativeGate_preserves_authoritativeRuntimeWellFormed_of_compatible state
    (.ordinary (.interrupt frame)) hstate
    (interrupt_authoritativeOperationCompatible state frame)

/-- The successor gate preserves the strongest deferred invariant across its
out-of-band NMI operation, including the handling-mode path unavailable to
ordinary operations. -/
theorem authoritativeGate_nmi_preserves_deferredBlockingRuntimeWellFormed
    state raw context
    (hstate : DeferredBlockingRuntimeWellFormed state) :
    DeferredBlockingRuntimeWellFormed
      (authoritativeGate state (.ordinary (.nmi raw context))).state := by
  rw [authoritativeGate_ordinary_state]
  exact gate_nmi_preserves_deferredBlockingRuntimeWellFormed
    state raw context hstate

/-- Finite public traces containing only capacity-checked deferred drains keep
the complete deferred-cancellation invariant.  Each successful member removes
one retained entry, while every typed denial and every terminal suffix is
state-preserving. -/
theorem runAuthoritativeDeferredDrains_preserves_deferredBlockingRuntimeWellFormed
    state (subjects : List BlockingIPC.SubjectId)
    (hstate : DeferredBlockingRuntimeWellFormed state) :
    DeferredBlockingRuntimeWellFormed
      (runAuthoritativeOperations state
        (subjects.map AuthoritativeOperation.drainDeferred)) := by
  induction subjects generalizing state with
  | nil => simpa [runAuthoritativeOperations] using hstate
  | cons subject rest ih =>
      simp only [List.map_cons, runAuthoritativeOperations]
      exact ih _
        (authoritativeGate_drainDeferred_preserves_deferredBlockingRuntimeWellFormed
          state subject hstate)

/-- Explicit termination of any live, blocked, deferred, or rejected identity
and an arbitrary finite deferred-drain continuation form one readiness-free
public trace. -/
theorem runAuthoritativeTerminateSubjectThenDeferredDrains_preserves
    state subject (subjects : List BlockingIPC.SubjectId)
    (hstate : DeferredBlockingRuntimeWellFormed state) :
    DeferredBlockingRuntimeWellFormed
      (runAuthoritativeOperations state
        (.ordinary (.terminateSubject subject) ::
          subjects.map AuthoritativeOperation.drainDeferred)) := by
  simp only [runAuthoritativeOperations]
  exact runAuthoritativeDeferredDrains_preserves_deferredBlockingRuntimeWellFormed
    (authoritativeGate state (.ordinary (.terminateSubject subject))).state subjects
    (authoritativeGate_terminateSubject_preserves_deferredBlockingRuntimeWellFormed
      state subject hstate)

/-- Scheduler-selected termination and an arbitrary finite deferred-drain
continuation form one readiness-free public trace.  The terminating step
establishes the exact retained-context classification consumed by every
capacity-checked suffix step. -/
theorem runAuthoritativeTerminateCurrentThenDeferredDrains_preserves
    state (subjects : List BlockingIPC.SubjectId)
    (hstate : DeferredBlockingRuntimeWellFormed state) :
    DeferredBlockingRuntimeWellFormed
      (runAuthoritativeOperations state
        (.ordinary .terminateCurrent ::
          subjects.map AuthoritativeOperation.drainDeferred)) := by
  simp only [runAuthoritativeOperations]
  exact runAuthoritativeDeferredDrains_preserves_deferredBlockingRuntimeWellFormed
    (authoritativeGate state (.ordinary .terminateCurrent)).state subjects
    (authoritativeGate_terminateCurrent_preserves_deferredBlockingRuntimeWellFormed
      state hstate)

/-- Every inbound interrupt result can be followed by an arbitrary finite
deferred-drain suffix without leaving the public authoritative gate or
weakening the deferred blocking invariant between steps. -/
theorem runAuthoritativeInterruptThenDeferredDrains_preserves
    state frame (subjects : List BlockingIPC.SubjectId)
    (hstate : DeferredBlockingRuntimeWellFormed state) :
    DeferredBlockingRuntimeWellFormed
      (runAuthoritativeOperations state
        (.ordinary (.interrupt frame) ::
          subjects.map AuthoritativeOperation.drainDeferred)) := by
  simp only [runAuthoritativeOperations]
  exact runAuthoritativeDeferredDrains_preserves_deferredBlockingRuntimeWellFormed
    (authoritativeGate state (.ordinary (.interrupt frame))).state subjects
    (authoritativeGate_interrupt_preserves_deferredBlockingRuntimeWellFormed
      state frame hstate)

/-- Every finite deferred-drain suffix carries a recursive compatibility
certificate independently of its starting state.  Capacity-checked drains
have no caller-supplied post-state law, so this certificate can be reused
after any constructor whose own operation-local compatibility is closed. -/
theorem authoritativeTraceCompatible_deferredDrains
    state (subjects : List BlockingIPC.SubjectId) :
    AuthoritativeTraceCompatible state
      (subjects.map AuthoritativeOperation.drainDeferred) := by
  induction subjects generalizing state with
  | nil => trivial
  | cons subject rest ih =>
      exact ⟨trivial, ih _⟩

/-- Any operation-local compatibility certificate composes with an arbitrary
capacity-checked deferred-drain suffix.  The suffix consumes the invariant
established by the head transition through the common trace runner. -/
theorem authoritativeTraceCompatible_thenDeferredDrains
    state operation (subjects : List BlockingIPC.SubjectId)
    (hoperation : AuthoritativeOperationCompatible state operation) :
    AuthoritativeTraceCompatible state
      (operation :: subjects.map AuthoritativeOperation.drainDeferred) :=
  ⟨hoperation, authoritativeTraceCompatible_deferredDrains _ subjects⟩

/-- Interrupt validation and premise-free deferred-drain constructors form a
compatibility certificate for the complete public mixed trace. -/
theorem authoritativeTraceCompatible_interruptThenDeferredDrains
    state frame (subjects : List BlockingIPC.SubjectId) :
    AuthoritativeTraceCompatible state
      (.ordinary (.interrupt frame) ::
        subjects.map AuthoritativeOperation.drainDeferred) := by
  exact authoritativeTraceCompatible_thenDeferredDrains state
    (.ordinary (.interrupt frame)) subjects
    (interrupt_authoritativeOperationCompatible state frame)

/-- Explicit termination and any capacity-checked drain continuation form a
closed compatibility certificate.  Termination needs no independently
supplied post-state law, and each drain member is likewise premise-free. -/
theorem authoritativeTraceCompatible_terminateSubjectThenDeferredDrains
    state subject (subjects : List BlockingIPC.SubjectId) :
    AuthoritativeTraceCompatible state
      (.ordinary (.terminateSubject subject) ::
        subjects.map AuthoritativeOperation.drainDeferred) := by
  exact authoritativeTraceCompatible_thenDeferredDrains state
    (.ordinary (.terminateSubject subject)) subjects trivial

/-- Scheduler-selected termination has the same closed mixed-trace
compatibility certificate as explicit identity termination. -/
theorem authoritativeTraceCompatible_terminateCurrentThenDeferredDrains
    state (subjects : List BlockingIPC.SubjectId) :
    AuthoritativeTraceCompatible state
      (.ordinary .terminateCurrent ::
        subjects.map AuthoritativeOperation.drainDeferred) := by
  exact authoritativeTraceCompatible_thenDeferredDrains state
    (.ordinary .terminateCurrent) subjects trivial

/-- NMI fail-stop followed by proposed deferred drains is a closed
compatibility-certified trace.  The outer execution latch absorbs the suffix,
while the general runner retains the complete folded invariant. -/
theorem authoritativeTraceCompatible_nmiThenDeferredDrains
    state raw context (subjects : List BlockingIPC.SubjectId) :
    AuthoritativeTraceCompatible state
      (.ordinary (.nmi raw context) ::
        subjects.map AuthoritativeOperation.drainDeferred) := by
  exact authoritativeTraceCompatible_thenDeferredDrains state
    (.ordinary (.nmi raw context)) subjects trivial

/-- The general trace theorem covers every interrupt followed by any finite
sequence of capacity-checked deferred drains while retaining the complete
authoritative invariant. -/
theorem runAuthoritativeCompatibleInterruptThenDeferredDrains_preserves
    state frame (subjects : List BlockingIPC.SubjectId)
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (runAuthoritativeOperations state
        (.ordinary (.interrupt frame) ::
          subjects.map AuthoritativeOperation.drainDeferred)) := by
  exact runAuthoritativeOperations_preserves_authoritativeRuntimeWellFormed_of_compatible
    state _ hstate
    (authoritativeTraceCompatible_interruptThenDeferredDrains
      state frame subjects)

/-- Explicit termination followed by arbitrary capacity-checked drains now
crosses the general compatibility-certified trace theorem and preserves the
complete folded authoritative invariant, not only its deferred projection. -/
theorem runAuthoritativeCompatibleTerminateSubjectThenDeferredDrains_preserves
    state subject (subjects : List BlockingIPC.SubjectId)
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (runAuthoritativeOperations state
        (.ordinary (.terminateSubject subject) ::
          subjects.map AuthoritativeOperation.drainDeferred)) := by
  exact runAuthoritativeOperations_preserves_authoritativeRuntimeWellFormed_of_compatible
    state _ hstate
    (authoritativeTraceCompatible_terminateSubjectThenDeferredDrains
      state subject subjects)

/-- Scheduler-selected termination followed by arbitrary capacity-checked
drains likewise preserves the complete folded authoritative invariant. -/
theorem runAuthoritativeCompatibleTerminateCurrentThenDeferredDrains_preserves
    state (subjects : List BlockingIPC.SubjectId)
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (runAuthoritativeOperations state
        (.ordinary .terminateCurrent ::
          subjects.map AuthoritativeOperation.drainDeferred)) := by
  exact runAuthoritativeOperations_preserves_authoritativeRuntimeWellFormed_of_compatible
    state _ hstate
    (authoritativeTraceCompatible_terminateCurrentThenDeferredDrains
      state subjects)

/-- NMI fail-stop followed by arbitrary capacity-checked drains is covered by
the same general authoritative trace theorem; terminal absorption is no
longer proved only through a weaker parallel runner. -/
theorem runAuthoritativeCompatibleNmiThenDeferredDrains_preserves
    state raw context (subjects : List BlockingIPC.SubjectId)
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (runAuthoritativeOperations state
        (.ordinary (.nmi raw context) ::
          subjects.map AuthoritativeOperation.drainDeferred)) := by
  exact runAuthoritativeOperations_preserves_authoritativeRuntimeWellFormed_of_compatible
    state _ hstate
    (authoritativeTraceCompatible_nmiThenDeferredDrains
      state raw context subjects)

/-- NMI fail-stop and any proposed deferred-drain suffix form one public
authoritative trace.  The first step preserves the strongest invariant and
latches terminal mode, so the entire suffix is absorbed without manufacturing
an apparently coherent repair. -/
theorem runAuthoritativeNmiThenDeferredDrains_preserves
    state raw context (subjects : List BlockingIPC.SubjectId)
    (hstate : DeferredBlockingRuntimeWellFormed state) :
    DeferredBlockingRuntimeWellFormed
      (runAuthoritativeOperations state
        (.ordinary (.nmi raw context) ::
          subjects.map AuthoritativeOperation.drainDeferred)) := by
  simp only [runAuthoritativeOperations]
  exact runAuthoritativeDeferredDrains_preserves_deferredBlockingRuntimeWellFormed
    (authoritativeGate state (.ordinary (.nmi raw context))).state subjects
    (authoritativeGate_nmi_preserves_deferredBlockingRuntimeWellFormed
      state raw context hstate)

/-- A contained interrupt and its capacity-checked deferred-cancellation
continuation form one public mixed trace.  The trusted execution/lifecycle
binding establishes the cleanup post-state directly, after which every finite
drain suffix is carried by the execution-latched authoritative gate without
rebuilding waiter, saved-context, or resumable-bank facts between steps. -/
theorem runAuthoritativeContainedInterruptThenDeferredDrains_preserves
    state frame faulting (subjects : List BlockingIPC.SubjectId)
    (hstate : DeferredBlockingRuntimeWellFormed state)
    (hbound : ContainedFaultIdentityBound state)
    (hcontained : (dispatchHardware state.execution frame).action = .contained faulting) :
    DeferredBlockingRuntimeWellFormed
      (runAuthoritativeOperations state
        (.ordinary (.interrupt frame) ::
          subjects.map AuthoritativeOperation.drainDeferred)) := by
  have hmode : state.execution.mode = .running := by
    cases hmode : state.execution.mode with
    | handling active => simp [dispatchHardware, hmode, halt] at hcontained
    | halted record => simp [dispatchHardware, hmode] at hcontained
    | running => rfl
  have hcleaned := interrupt_contained_preserves_deferredBlockingRuntimeWellFormed
    state frame faulting hstate hbound hcontained
  simp only [runAuthoritativeOperations]
  have hgate :
      (authoritativeGate state (.ordinary (.interrupt frame))).state =
        applyOperation state (.interrupt frame) := by
    simp [authoritativeGate, hmode, applyAuthoritativeOperation]
  rw [hgate]
  exact runAuthoritativeDeferredDrains_preserves_deferredBlockingRuntimeWellFormed
    (applyOperation state (.interrupt frame)) subjects hcleaned

/-- Fatal mode is a separate result class and absorbs arbitrary suffixes that
mix ordinary operations with blocking delivery, sleep, wake, and cancellation. -/
theorem authoritative_halted_suffix_absorbing state record operations
    (hmode : state.execution.mode = .halted record) :
    runAuthoritativeOperations state operations = state := by
  induction operations generalizing state with
  | nil => rfl
  | cons operation rest ih =>
      simp only [runAuthoritativeOperations]
      have hgate : authoritativeGate state operation =
          { state, result := .rejectedHalted record } := by
        cases operation with
        | ordinary operation => cases operation <;> simp [authoritativeGate, hmode]
        | blocking operation => simp [authoritativeGate, hmode]
        | drainDeferred subject => simp [authoritativeGate, hmode]
      rw [hgate]
      exact ih state hmode

/-- A validator-rejected live PCI observation is absorbed by the complete
successor vocabulary, including blocking operations and deferred drains. -/
theorem observeDMAControl_invalid_authoritative_suffix_absorbing
    state snapshot reason operations
    (hrunning : state.execution.mode = .running)
    (hinvalid : DMAQuarantine.validate snapshot = .rejected reason) :
    let next := (observeDMAControl state snapshot).state
    next.execution.mode =
        .halted (dmaHaltRecord .dmaInvalidControlSnapshot) ∧
      runAuthoritativeOperations next operations = next := by
  rw [observeDMAControl_invalid_exact_fatal state snapshot reason hrunning hinvalid]
  dsimp [latchDMAControlFailure]
  constructor
  · rfl
  · exact authoritative_halted_suffix_absorbing _ _ operations rfl

/-- A valid but changed PCI observation receives its distinct fatal reason and
is likewise absorbed by every authoritative successor operation. -/
theorem observeDMAControl_changed_authoritative_suffix_absorbing
    state snapshot accepted operations
    (hrunning : state.execution.mode = .running)
    (hvalid : DMAQuarantine.validate snapshot = .accepted accepted)
    (hchanged : snapshot ≠ state.dmaAccepted.snapshot) :
    let next := (observeDMAControl state snapshot).state
    next.execution.mode =
        .halted (dmaHaltRecord .dmaControlSnapshotChanged) ∧
      runAuthoritativeOperations next operations = next := by
  rw [observeDMAControl_changed_exact_fatal state snapshot accepted
    hrunning hvalid hchanged]
  dsimp [latchDMAControlFailure]
  constructor
  · rfl
  · exact authoritative_halted_suffix_absorbing _ _ operations rfl

/-- Concrete reachability for the successor rejection class: the boot-produced
empty waiter store rejects cancellation without mutation. -/
theorem authoritativeGate_rejection_reachable_witness plan :
    AuthoritativeGateRejection
        (authoritativeGate (bootRuntime plan) (.blocking (.cancel 1))).result ∧
      (authoritativeGate (bootRuntime plan) (.blocking (.cancel 1))).state =
        bootRuntime plan := by
  exact ⟨.blocking (.cancel .notWaiting), rfl⟩

/-- An accepted normalized NMI is one complete composite terminal step.  No
lifecycle synchronization helper, scheduler/preemption transition, CR3/return
selection, or ordinary handler runs after the latch is written. -/
theorem accepted_nmi_composite_atomicity state raw context event proposals
    (hmode : state.execution.mode = .running ∨
      ∃ active, state.execution.mode = .handling active)
    (hcontext : context.interruptedMode = interruptedModeOf state.execution.mode)
    (haccepted : InterruptEntry.normalizeNmi raw context
      state.execution.core.context.currentSubject
      state.execution.core.context.activeAddressSpace = .accepted event) :
    let next := (gate state (.nmi raw context)).state
    next.execution.mode = .halted (acceptedNmiRecord state.execution event) ∧
      next.execution.core.lifecycle = state.execution.core.lifecycle ∧
      next.execution.core.context.currentSubject =
        state.execution.core.context.currentSubject ∧
      next.execution.core.context.activeAddressSpace =
        state.execution.core.context.activeAddressSpace ∧
      next.execution.core.context.kernelStack = state.execution.core.context.kernelStack ∧
      next.execution.returnAddressSpace = state.execution.returnAddressSpace ∧
      next.execution.returnPlan = state.execution.returnPlan ∧
      next.execution.returnAuthority = state.execution.returnAuthority ∧
      next.execution.returnAuthorityArmed = false ∧
      next.execution.copyOverride = false ∧
      next.scheduler = state.scheduler ∧
      next.preemption = state.preemption ∧
      next.virtualMemory = state.virtualMemory ∧
      next.ipc = state.ipc ∧
      next.capabilities = state.capabilities ∧
      next.lifecycle = state.lifecycle ∧
      runOperations next proposals = next := by
  dsimp only
  have hdispatch := accepted_nmi_terminal state.execution raw context event
    hmode hcontext haccepted
  have hgate : (gate state (.nmi raw context)).state =
      { state with
        execution := (dispatchNmi state.execution raw context).state
        resumable := { state.resumable with halted := true } } := by
    rcases hmode with hmode | ⟨active, hmode⟩
    · simp [gate, applyOperation, hmode]
    · simp [gate, applyOperation, hmode]
  rw [hgate]
  rcases hdispatch with ⟨_, hnextMode, hlifecycle, hsubject, haddressSpace,
    hstack, hreturnAddressSpace, hreturnPlan, hreturnAuthority, harmed, hcopy⟩
  refine ⟨hnextMode, hlifecycle, hsubject, haddressSpace, hstack,
    hreturnAddressSpace, hreturnPlan, hreturnAuthority, harmed, hcopy,
    rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact halted_suffix_absorbing
    { state with
      execution := (dispatchNmi state.execution raw context).state
      resumable := { state.resumable with halted := true } }
    (acceptedNmiRecord state.execution event) proposals hnextMode

/-- Outgoing-return rejection is one atomic composite step: it records the
typed terminal reason, changes no lifecycle/authority/scheduler/resource view,
and absorbs every later typed operation. -/
theorem rejected_user_return_composite_atomicity state request reason proposals
    (hmode : state.execution.mode = .running)
    (harmed : state.execution.returnAuthorityArmed = true)
    (hlive : state.ReturnPlanLive = true)
    (hrejected : Interrupt.validateUserReturn
      (authoritativeReturnRequest state.execution request) = .rejected reason) :
    let record : HaltRecord :=
      { reason := .invalidUserReturn state.execution.returnAuthority.purpose reason
        active := none
        incomingVector := request.hardware.vector
        incomingOrigin := request.hardware.savedPrivilege }
    let next := (gate state (.userReturn request)).state
    next.execution.mode = .halted record ∧
      next.execution.core.lifecycle = state.execution.core.lifecycle ∧
      next.scheduler = state.scheduler ∧
      next.preemption = state.preemption ∧
      next.virtualMemory = state.virtualMemory ∧
      next.ipc = state.ipc ∧
      next.capabilities = state.capabilities ∧
      next.lifecycle = state.lifecycle ∧
      runOperations next proposals = next := by
  dsimp only
  have hfatal : (completeUserReturn state.execution request).action =
      .fatal
        { reason := .invalidUserReturn state.execution.returnAuthority.purpose reason
          active := none
          incomingVector := request.hardware.vector
          incomingOrigin := request.hardware.savedPrivilege } := by
    simp only [completeUserReturn, hmode, harmed]
    rw [hrejected]
    rfl
  have hterminal :
      ((gate state (.userReturn request)).state.execution.mode =
        .halted
          { reason := .invalidUserReturn state.execution.returnAuthority.purpose reason
            active := none
            incomingVector := request.hardware.vector
            incomingOrigin := request.hardware.savedPrivilege }) := by
    simp only [gate, hmode, applyOperation, hlive, ite_true, completeUserReturn, harmed]
    rw [hrejected]
    simp [latchInvalidUserReturn, authoritativeReturnRequest]
  refine ⟨hterminal, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gate, hmode, applyOperation, hlive, ite_true, completeUserReturn, harmed]
    rw [hrejected]
    simp [latchInvalidUserReturn, authoritativeReturnRequest]
  · simp [gate, hmode, applyOperation, hlive, hfatal]
  · simp [gate, hmode, applyOperation, hlive, hfatal]
  · simp [gate, hmode, applyOperation, hlive, hfatal]
  · simp [gate, hmode, applyOperation, hlive, hfatal]
  · simp [gate, hmode, applyOperation, hlive, hfatal]
  · simp [gate, hmode, applyOperation, hlive, hfatal]
  · exact halted_suffix_absorbing _ _ proposals hterminal

theorem halted_never_accepts state record operation
    (hmode : state.execution.mode = .halted record) :
    ∀ reply, (gate state operation).result ≠ .completed reply := by
  cases operation <;> simp [gate, hmode]

/-- Terminal non-resumption over the complete typed composite step: no
subsystem transition is accepted and no component of the terminal state can
change. -/
theorem halted_terminal_non_resumption state record operation
    (hmode : state.execution.mode = .halted record) :
    (gate state operation).state = state ∧
      ∀ reply, (gate state operation).result ≠ .completed reply := by
  cases operation <;> simp [gate, hmode]

theorem fatal_atomicity state frame reason
    (hfatal : (dispatchHardware state frame).action = .fatal reason) :
    (dispatchHardware state frame).state.core.lifecycle = state.core.lifecycle := by
  cases hmode : state.mode with
  | handling active => simp [dispatchHardware, hmode, halt]
  | halted record => simp [dispatchHardware, hmode] at hfatal
  | running =>
    simp only [dispatchHardware, hmode, beginEntry, finishEntry] at hfatal ⊢
    generalize hd : Interrupt.dispatchHardware
      { state.core with context := { state.core.context with entryActive := false } }
      frame = outcome at hfatal ⊢
    cases outcome with
    | mk next action => cases action <;> simp_all [activeEntry, hd, halt]

theorem fatal_clears_copy_override state frame reason
    (hfatal : (dispatchHardware state frame).action = .fatal reason) :
    (dispatchHardware state frame).state.copyOverride = false := by
  cases hmode : state.mode with
  | handling active => simp [dispatchHardware, hmode, halt]
  | halted record => simp [dispatchHardware, hmode] at hfatal
  | running =>
      simp only [dispatchHardware, hmode, beginEntry, finishEntry] at hfatal ⊢
      generalize hd : Interrupt.dispatchHardware
        { state.core with context := { state.core.context with entryActive := false } }
        frame = outcome at hfatal ⊢
      cases outcome with
      | mk next action => cases action <;> simp_all [activeEntry, hd, halt]

private theorem interrupt_contained_requires_user core frame subject
    (h : (Interrupt.dispatchHardware core frame).action = .contained subject) :
    frame.savedPrivilege = .user := by
  unfold Interrupt.dispatchHardware at h
  split at h <;> simp_all
  cases hv : Interrupt.decodeVector frame.vector with
  | none => simp [hv] at h
  | some vector =>
      cases vector with
      | pageFault => cases hp : frame.savedPrivilege <;> simp_all
      | timer => simp [hv] at h
      | syscall => cases hp : frame.savedPrivilege <;> simp_all

theorem contained_requires_user_origin state frame subject
    (hcontained : (dispatchHardware state frame).action = .contained subject) :
    frame.savedPrivilege = .user := by
  cases hmode : state.mode with
  | handling active => simp [dispatchHardware, hmode, halt] at hcontained
  | halted record => simp [dispatchHardware, hmode] at hcontained
  | running =>
    simp only [dispatchHardware, hmode, beginEntry, finishEntry] at hcontained
    generalize hd : Interrupt.dispatchHardware
      { state.core with context := { state.core.context with entryActive := false } }
      frame = outcome at hcontained
    cases outcome with
    | mk next action =>
      cases action with
      | contained actual =>
          have hh : (Interrupt.dispatchHardware
              { state.core with context := { state.core.context with entryActive := false } }
              frame).action = .contained actual := by rw [hd]
          exact interrupt_contained_requires_user _ _ _ hh
      | fatal reason => simp [activeEntry, hd, halt] at hcontained
      | timer => simp [activeEntry, hd] at hcontained
      | syscall => simp [activeEntry, hd] at hcontained
      | rejected reason => simp [activeEntry, hd] at hcontained

theorem double_fault_escalation state active frame
    (hmode : state.mode = .handling active)
    (hactive : active.vector = 14) (hincoming : frame.vector = 14) :
    (dispatchHardware state frame).action = .fatal .doubleFault := by
  simp [dispatchHardware, hmode, escalation, hactive, hincoming, halt]

theorem kernel_fault_never_contained state frame
    (horigin : frame.savedPrivilege = .kernel) :
    ¬ ∃ subject, (dispatchHardware state frame).action = .contained subject := by
  intro h
  rcases h with ⟨subject, hsubject⟩
  have := contained_requires_user_origin state frame subject hsubject
  simp [horigin] at this

/-- Negative regression: the legacy action-only model leaves the state usable. -/
theorem legacy_fatal_not_absorbing (core : Interrupt.State)
    (hidle : core.context.entryActive = false) (kernelFault syscall : Interrupt.HardwareFrame)
    (hkvector : kernelFault.vector = 14)
    (hkorigin : kernelFault.savedPrivilege = .kernel)
    (hsvector : syscall.vector = 128)
    (_hsvalid : Interrupt.validSavedUserFrame syscall = true) :
    (Interrupt.dispatchHardware core kernelFault).action = .fatal .kernelFault ∧
      (Interrupt.dispatchHardware core syscall).action = .syscall := by
  constructor
  · exact Interrupt.kernel_page_fault_is_fatal core kernelFault hidle hkvector hkorigin
  · have horigin : syscall.savedPrivilege = .user := by
      have hsvalid := _hsvalid
      simp [Interrupt.validSavedUserFrame] at hsvalid
      exact hsvalid.1.1.1.1.1
    simp [Interrupt.dispatchHardware, hidle, hsvector, Interrupt.decodeVector, horigin]

end LeanOS.FailStop
