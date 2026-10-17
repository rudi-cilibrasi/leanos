import LeanOS.SecurityClaims

/-!
Pinned statements of the refinement-ladder claims (issues #475, #570). A weakened
conclusion or an added hypothesis changes the printed type, so the
`#guard_msgs` contract below fails; `scripts/check-refinement-mutants.sh`
shows a weakened statement of each refinement claim is rejected this way.
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

/--
info: LeanOS.SecurityClaims.loader_source_refinement :
  (∀ (source start stop fileOffset span : UInt64),
      LeanOS.Refinement.CSubset.call LeanOS.Refinement.ChildLoaderC.loaderSourceC
          [source, start, stop, fileOffset, span] =
        some (LeanOS.ChildLoader.loaderSource source start stop fileOffset span)) ∧
    ∀ (source start stop fileOffset span : Nat),
      source < 2 ^ 62 →
        start < 2 ^ 62 →
          stop < 2 ^ 62 →
            fileOffset < 2 ^ 62 →
              span < 2 ^ 62 →
                LeanOS.Refinement.CSubset.call LeanOS.Refinement.ChildLoaderC.loaderSourceC
                    [UInt64.ofNat source, UInt64.ofNat start, UInt64.ofNat stop, UInt64.ofNat fileOffset,
                      UInt64.ofNat span] =
                  some
                    (if (!(decide (start ≤ source) && decide (source + span ≤ stop))) = true then 5
                    else if source ≠ start + fileOffset then 6 else 0)
-/
#guard_msgs in
#check LeanOS.SecurityClaims.loader_source_refinement

/--
info: LeanOS.SecurityClaims.loader_decide_refinement (state : LeanOS.ChildLoader.State) (control : UInt64) :
  (∀ (sourceCode pages frames used : UInt64),
      LeanOS.Refinement.CSubset.call LeanOS.Refinement.ChildLoaderC.loaderDecideC
          [2, LeanOS.ChildLoader.flagsWord state (LeanOS.ChildLoader.Request.start control), sourceCode, pages, frames,
            used] =
        some
          (LeanOS.ChildLoader.encodeReply false
            (LeanOS.ChildLoader.step state (LeanOS.ChildLoader.Request.start control)).snd)) ∧
    ∀ (index source : Nat),
      LeanOS.ChildLoader.Small state →
        source < 2 ^ 62 →
          ((match state.plan[index]? with
                | some s =>
                  LeanOS.Refinement.CSubset.call LeanOS.Refinement.ChildLoaderC.loaderSourceC
                    [UInt64.ofNat source, UInt64.ofNat state.start, UInt64.ofNat state.stop, UInt64.ofNat s.fileOffset,
                      UInt64.ofNat (LeanOS.ChildLoader.pageCount s * LeanOS.ElfAdmission.pageBytes)]
                | none => some 0).bind
              fun sourceCode =>
              LeanOS.Refinement.CSubset.call LeanOS.Refinement.ChildLoaderC.loaderDecideC
                [1, LeanOS.ChildLoader.flagsWord state (LeanOS.ChildLoader.Request.load control index source),
                  sourceCode, UInt64.ofNat ((Option.map LeanOS.ChildLoader.pageCount state.plan[index]?).getD 0),
                  UInt64.ofNat ((Option.map (fun c => c.frames) state.child).getD 0), UInt64.ofNat state.used]) =
            some
              (LeanOS.ChildLoader.encodeReply
                (LeanOS.ChildLoader.requestWritable state (LeanOS.ChildLoader.Request.load control index source))
                (LeanOS.ChildLoader.step state (LeanOS.ChildLoader.Request.load control index source)).snd)
-/
#guard_msgs in
#check LeanOS.SecurityClaims.loader_decide_refinement

/--
info: LeanOS.SecurityClaims.frame_copy_check_refinement (ext : LeanOS.Refinement.CSubset.Ext) :
  (∀ (subject request addr len base limit : UInt64),
      LeanOS.Refinement.CSubset.callWith (LeanOS.Refinement.NetworkSubjectC.link ext)
          LeanOS.Refinement.NetworkSubjectC.frameCopyCheckC [subject, request, addr, len, base, limit] =
        some (LeanOS.NetworkSubject.frameCopyCheck subject request addr len base limit)) ∧
    (∀ (w : LeanOS.NetworkSubject.Window) (s : LeanOS.NetworkSubject.State) (addr base limit : UInt64),
        w = { base := base.toNat, limit := limit.toNat } →
          s.rx.length < 2 ^ 64 →
            (LeanOS.Refinement.CSubset.callWith (LeanOS.Refinement.NetworkSubjectC.link ext)
                  LeanOS.Refinement.NetworkSubjectC.frameCopyCheckC
                  [3, LeanOS.NetworkSubject.fetchRequest s.rxPending, addr, s.rx.length.toUInt64, base, limit] =
                some 0 ↔
              LeanOS.NetworkSubject.fetchOk w s LeanOS.NetworkSubject.network addr.toNat = true)) ∧
      (∀ (w : LeanOS.NetworkSubject.Window) (s : LeanOS.NetworkSubject.State) (addr len base limit : UInt64),
          w = { base := base.toNat, limit := limit.toNat } →
            (LeanOS.Refinement.CSubset.callWith (LeanOS.Refinement.NetworkSubjectC.link ext)
                  LeanOS.Refinement.NetworkSubjectC.frameCopyCheckC
                  [3, LeanOS.NetworkSubject.sendRequest s.txPending, addr, len, base, limit] =
                some 0 ↔
              LeanOS.NetworkSubject.sendOk w s LeanOS.NetworkSubject.network addr.toNat len.toNat = true)) ∧
        ∀ (subject request addr len base limit : UInt64),
          subject ≠ 3 →
            LeanOS.Refinement.CSubset.callWith (LeanOS.Refinement.NetworkSubjectC.link ext)
                LeanOS.Refinement.NetworkSubjectC.frameCopyCheckC [subject, request, addr, len, base, limit] =
              some 1
-/
#guard_msgs in
#check LeanOS.SecurityClaims.frame_copy_check_refinement

/--
info: LeanOS.SecurityClaims.frame_port_check_refinement :
  (∀ (subject req addr len base limit : UInt64),
      LeanOS.Refinement.CSubset.call LeanOS.Refinement.DhcpSubjectC.framePortCheckC
          [subject, req, addr, len, base, limit] =
        some (LeanOS.DhcpSubject.framePortCheck subject req addr len base limit)) ∧
    (∀ (subject req addr len base limit : UInt64),
        LeanOS.Refinement.CSubset.call LeanOS.Refinement.DhcpSubjectC.framePortCheckC
              [subject, req, addr, len, base, limit] =
            some 0 →
          (subject = 2 ∨ subject = 3) ∧
            req >>> 24 &&& 255 = subject ∧
              req >>> 16 &&& 255 = subject ∧
                { base := base.toNat, limit := limit.toNat }.covers addr.toNat len.toNat = true) ∧
      ∀ (subject req addr len base limit : UInt64),
        subject ≠ 2 →
          subject ≠ 3 →
            LeanOS.Refinement.CSubset.call LeanOS.Refinement.DhcpSubjectC.framePortCheckC
                [subject, req, addr, len, base, limit] =
              some 1
-/
#guard_msgs in
#check LeanOS.SecurityClaims.frame_port_check_refinement
