import LeanOS.SecurityClaims

open LeanOS

/- The containment claim cannot silently drop its cleanup conjunct or the
running-state hypothesis on the kernel-origin fatal conjunct. -/
example state frame reason
    (hsuccess : (FaultDispatch.dispatch state (.accepted frame)).action = .idle reason ∨
      ∃ context,
        (FaultDispatch.dispatch state (.accepted frame)).action = .dispatch reason context) :
    (InterruptEntry.containedReason? frame.vector = some reason ∧
      frame.vector = reason.vector ∧
      frame.purpose = .userFault ∧
      frame.origin = .user ∧
      frame.errorCode.isSome = reason.hasErrorWord ∧
      frame.cs % 4 = 3) ∧
    (∀ kernelFrame : InterruptEntry.NormalizedFrame,
      kernelFrame.origin = .kernel →
        FaultDispatch.dispatch state (.accepted kernelFrame) =
          FaultDispatch.halt state .kernelOrigin) := by
  exact SecurityClaims.user_fault_class_containment state frame reason hsuccess
