import LeanOS.SecurityClaims

/-!
Pinned statements of the refinement-ladder claims (issue #475). A weakened
conclusion or an added hypothesis changes the printed type, so the
`#guard_msgs` contract below fails; `scripts/check-refinement-mutants.sh`
shows a weakened `boot_transition_refinement` is rejected this way.
-/

/--
info: LeanOS.SecurityClaims.boot_transition_refinement (state : LeanOS.KernelTransition.State) (command : UInt64) :
  LeanOS.Refinement.CSubset.call LeanOS.Refinement.BootTransitionC.bootTransitionC
      [LeanOS.KernelTransition.encodeState state, command] =
    some
      (LeanOS.KernelTransition.encodeResult
        (LeanOS.KernelTransition.transition state (LeanOS.KernelTransition.decodeCommand command)).result)
-/
#guard_msgs in
#check LeanOS.SecurityClaims.boot_transition_refinement

/--
info: LeanOS.SecurityClaims.boot_transition_agreement (state : LeanOS.KernelTransition.State) (command : UInt64) :
  LeanOS.KernelTransition.bootTransition (LeanOS.KernelTransition.encodeState state) command =
    LeanOS.KernelTransition.encodeResult
      (LeanOS.KernelTransition.transition state (LeanOS.KernelTransition.decodeCommand command)).result
-/
#guard_msgs in
#check LeanOS.SecurityClaims.boot_transition_agreement
