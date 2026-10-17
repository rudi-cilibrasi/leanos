import LeanOS.SecurityClaims

open LeanOS

/- A load rejected after a spawn rolls the loader back to the loader before
the spawn.  A weakened claim in which the loader keeps the child it was
handed must not follow from SC-LOADER-JOINT-ROLLBACK, which says the loader
is exactly the loader before the spawn. -/
example (pre : FailStop.CompositeState) (idle : ChildLoader.State)
    (request : FailStop.SpawnRequest) (grants : List Nat)
    (requests : List ChildLoader.Request) (last : ChildLoader.Request)
    (child addressSpace : Nat) (control : UInt64) (reason : ChildLoader.Rejection)
    (running : pre.execution.mode = .running) (holds : FailStop.ResourceRuntimeWellFormed pre)
    (accounting : FailStop.ChildAccountingWellFormed pre)
    (noChild : ChildLoader.rollback idle = idle)
    (spawned : (FailStop.childGate pre (.spawn request)).result =
      .completed (.spawned child addressSpace control))
    (rolledBack : (ChildLoaderJoint.loaderStep (ChildLoaderJoint.runLoader
      (ChildLoaderJoint.grantSteps (ChildLoaderJoint.spawnStep ⟨pre, idle⟩ request) control
        grants) requests) last).2 = .rolledBack reason) :
    (ChildLoaderJoint.loaderStep (ChildLoaderJoint.runLoader (ChildLoaderJoint.grantSteps
      (ChildLoaderJoint.spawnStep ⟨pre, idle⟩ request) control grants) requests) last).1.loader =
        ChildLoaderJoint.attach idle control := by
  exact (SecurityClaims.loader_joint_rollback_restores pre idle request grants requests last child
    addressSpace control reason running holds accounting noChild spawned rolledBack).1
