import LeanOS.UserCopyPrefix
open LeanOS LeanOS.VirtualMapping LeanOS.UserCopy LeanOS.UserCopyPrefix

private def demoVirtual : VirtualMapping.State :=
  { memory :=
      { capabilities :=
          { subjects := fun subject => subject = 0
            objects := fun object => object = 10 || object = 11
            kinds := fun object => if object = 10 || object = 11 then some .memory else none
            slots := fun _ _ => none }
        allocator :=
          { frames := [4, 5]
            status := fun frame => if frame = 4 then .owned 10
              else if frame = 5 then .owned 11 else .reserved }
        binding := fun object => if object = 10 then some 4 else if object = 11 then some 5 else none
        issued := fun object => object = 10 || object = 11 }
    owner := fun space => if space = 7 then some 0 else none
    mappings := fun space page =>
      if space = 7 ∧ page = 0 then some { object := 10, permissions := { read := true, write := true } }
      else if space = 7 ∧ page = 1 then some { object := 11, permissions := { read := true, write := true } }
      else none
    issuedAddressSpace := fun space => space = 7 }

private def demo : UserCopy.State :=
  { virtual := demoVirtual
    userBytes := fun frame offset => UInt8.ofNat (frame * 16 + offset)
    kernelBytes := fun buffer offset => UInt8.ofNat (buffer + offset + 1) }
private def ctx : TrustedContext := { caller := 0, activeAddressSpace := 7 }

-- Interrupt at the page boundary: the first byte changes, the second does not.
example : (copyToPrefix demo ctx 4095 2 8 1).userBytes 4 4095 = 9 := by rfl
example : (copyToPrefix demo ctx 4095 2 8 1).userBytes 5 0 = demo.userBytes 5 0 := by rfl
example : (copyToPrefix demo ctx 4095 2 8 1).userBytes 4 4094 = demo.userBytes 4 4094 := by rfl
example : (copyToPrefix demo ctx 4095 2 8 0).userBytes 4 4095 = demo.userBytes 4 4095 := by rfl
example : (copyToPrefix demo ctx 4095 2 8 2).userBytes 5 0 = 10 := by rfl
example : (copyToPrefix demo ctx 4095 2 8 100).userBytes 5 1 = demo.userBytes 5 1 := by rfl
-- The second byte is unmapped: validation prevents even the first write.
example : (copyToPrefix demo ctx 8191 2 8 1).userBytes 5 4095 = demo.userBytes 5 4095 := by rfl
example : copyToPrefix demo ctx 4095 17 8 1 = demo := by rfl
example : copyToPrefix demo ctx 4095 2 8 100 = (copyToUser demo ctx 4095 2 8).state := by
  exact complete_agrees _ _ _ _ _ _ (by decide)
