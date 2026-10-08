import LeanOS.SecurityClaims

open LeanOS

/- A fault handler must not gain the faulting subject's authority.  A
weakened delivery claim in which the handler's slots after delivery are the
faulting subject's slots must not follow from the no-amplification theorem,
which only says the capability state is unchanged. -/
example (sys : FaultHandler.System) (entry : InterruptEntry.Result)
    (handler : Capability.SubjectId) (record : FaultHandler.FaultRecord)
    (b : FaultHandler.Binding) (_hb : sys.binding = some b)
    (h : (FaultHandler.fault sys entry).2 = .delivered handler record) :
    ∀ slot, (FaultHandler.fault sys entry).1.core.scheduler.lifecycle.capabilities.slots
        b.handler slot = sys.core.scheduler.lifecycle.capabilities.slots b.faulting slot := by
  exact FaultHandler.delivered_no_amplification sys entry handler record h
