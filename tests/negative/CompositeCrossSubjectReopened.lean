import LeanOS.CompositeSubjectGate

open LeanOS LeanOS.FailStop LeanOS.CompositeChannels LeanOS.CompositeSubjectGate

/- `#542` proved that the replies to creating, terminating and queueing
another subject, and to delegating into or revoking another subject's slot,
reveal that subject's liveness and slot occupancy (`LeanOS.CompositeChannels`
keeps that record for the raw `authoritativeGate`).  A scheduled subject now
asks through `subjectGate`, which refuses every such request with one fixed
result.  Restating the old channels for the subject gate must fail: on the
canonical sample plan the kernel evaluates both sides to the same reply. -/

/- Creating another subject no longer reveals whether it is live. -/
example :
    (match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
      | .ok plan => subjectReply (seed plan) createThree != subjectReply (created plan) createThree
      | .error _ => false) = true := by
  decide +kernel

/- Terminating another subject no longer reveals whether it was issued. -/
example :
    (match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
      | .ok plan =>
          subjectReply (seed plan) (.terminateSubject 3) !=
            subjectReply (created plan) (.terminateSubject 3)
      | .error _ => false) = true := by
  decide +kernel

/- Delegating into another subject's slot no longer reveals its occupancy. -/
example :
    (match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
      | .ok plan =>
          subjectReply (toSlotThree plan) CompositeUnwinding.Channels.delegateToOther !=
            subjectReply (toSlotTwo plan) CompositeUnwinding.Channels.delegateToOther
      | .error _ => false) = true := by
  decide +kernel
