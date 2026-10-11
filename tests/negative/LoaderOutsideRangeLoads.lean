import LeanOS.SecurityClaims

open LeanOS

/- A load claiming a source outside the loader's read authority must roll the
spawn back.  A weakened claim in which such a load still installs the
segment (the reply is `.loaded`) must not follow from
SC-LOADER-RESERVED-RANGE, which says the reply is a rollback. -/
example (state : ChildLoader.State) (child : ChildLoader.Child) (control : UInt64)
    (index source : Nat) (segment : ElfAdmission.Segment)
    (live : ChildLoader.liveChild state control = some child)
    (named : state.plan[index]? = some segment) (fresh : state.loaded index = false)
    (outside : source < state.start) :
    (ChildLoader.step state (.load control index source)).2 = .loaded := by
  rw [SecurityClaims.loader_reserved_range_only.2.2 state child control index source segment live
    named fresh (Or.inl outside)]
