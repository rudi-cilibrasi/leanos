import LeanOS.SecurityClaims

open LeanOS

/- A contracted copy claim cannot silently drop the actor-authority alternative. -/
example state actor source destination destinationSlot requested candidate object right
    (hauthority : Capability.HasAuthority
      (Capability.copy state actor source destination destinationSlot requested).state
      candidate object right) :
    Capability.HasAuthority state candidate object right := by
  exact SecurityClaims.capability_copy_no_authority_amplification state actor source destination
    destinationSlot requested candidate object right hauthority
