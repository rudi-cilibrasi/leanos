import LeanOS.SecurityClaims

open LeanOS

/- A copied (writable) segment reads zero past its file size.  A weakened
claim in which the child reads the file's following byte there instead (a
copy without the zero fill) must not follow from SC-LOADER-CONTENTS, which
says the byte is zero. -/
example (state : ChildLoader.State) (control : UInt64)
    (layout : ChildLoader.PlanLayout state.plan) (exact : ChildLoader.Exact state)
    (contents : ChildLoader.Contents state)
    (started : (ChildLoader.step state (.start control)).2 = .started)
    (segment : ElfAdmission.Segment) (member : segment ∈ state.plan)
    (writable : segment.writable = true) (address : Nat) (low : segment.vaddr ≤ address)
    (high : address < segment.pageEnd) (past : segment.vaddr + segment.fileBytes ≤ address) :
    ChildLoader.childByte (ChildLoader.step state (.start control)).1 address =
      some (state.file (segment.fileOffset + (address - segment.vaddr))) := by
  exact (SecurityClaims.loader_copied_contents.2 state control layout exact contents started
    segment member writable address low high).2 past
