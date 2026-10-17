import LeanOS.Refinement.CSymbolic
import LeanOS.NetworkSubject

/-!
# Rung 3 for `leanos_frame_copy_check` (issue #570)

`frameCopyCheckC` is the C function the pinned Lean toolchain emits for the
`@[export leanos_frame_copy_check]` witness of #548, and `frameCopyDecideC`
the emitted helper it calls, both extracted from the generated
`NetworkSubject.c` by `scripts/extract-generated-c.py`. The build re-runs the
extractor and fails if the emitted C no longer matches these ASTs.

Under the C-subset semantics of `LeanOS.Refinement.CSubset`, with the helper
linked as the emitted C calls it (`link`), the export returns exactly
`NetworkSubject.frameCopyCheck` on every six words, and so, through
`frameCopyCheck_fetch` and `frameCopyCheck_send`, accepts a copy exactly when
the model's `fetchOk`/`sendOk` does. The theorems do not cover the calling
convention, the compiler, the linker, the boot path or QEMU (ADR 0029).
-/
namespace LeanOS.Refinement.NetworkSubjectC

open LeanOS.Refinement.CSubset LeanOS.Refinement.CSymbolic LeanOS.NetworkSubject


-- BEGIN GENERATED AST l_LeanOS_NetworkSubject_frameCopyDecide
def frameCopyDecideC : Func :=
  { params := [("v_subject_631_", .u64), ("v_op_632_", .u64), ("v_addr_633_", .u64), ("v_len_634_", .u64), ("v_pending_635_", .u64), ("v_base_636_", .u64), ("v_limit_637_", .u64)]
    result := .u64
    body := [
      (.decl .u8 "v___y_639_"),
      (.decl .u64 "v___x_645_"),
      (.decl .u8 "v___x_651_"),
      (.assign "v___x_645_" (.lit 3)),
      (.assign "v___x_651_" (.bin .decEq (.var "v_subject_631_") (.var "v___x_645_"))),
      (.ifZero "v___x_651_" [(.decl .u64 "v___x_652_"), (.assign "v___x_652_" (.lit 1)), (.ret (.var "v___x_652_"))] [(.decl .u64 "v___x_653_"), (.decl .u8 "v___x_654_"), (.assign "v___x_653_" (.lit 1)), (.assign "v___x_654_" (.bin .decEq (.var "v_op_632_") (.var "v___x_653_"))), (.ifZero "v___x_654_" [(.decl .u64 "v___x_655_"), (.decl .u8 "v___x_656_"), (.assign "v___x_655_" (.lit 2)), (.assign "v___x_656_" (.bin .decEq (.var "v_op_632_") (.var "v___x_655_"))), (.ifZero "v___x_656_" [(.decl .u64 "v___x_657_"), (.assign "v___x_657_" (.lit 5)), (.ret (.var "v___x_657_"))] [(.decl .u64 "v___x_658_"), (.decl .u8 "v___y_660_"), (.decl .u8 "v___y_666_"), (.decl .u8 "v___x_673_"), (.assign "v___x_658_" (.lit 0)), (.assign "v___x_673_" (.bin .decEq (.var "v_pending_635_") (.var "v___x_658_"))), (.ifZero "v___x_673_" [(.assign "v___y_666_" (.var "v___x_656_")), (.goto "v___jp_665_")] [(.assign "v___y_666_" (.var "v___x_654_")), (.goto "v___jp_665_")]), (.block "v___jp_659_" [(.ifZero "v___y_660_" [(.decl .u64 "v___x_661_"), (.assign "v___x_661_" (.lit 4)), (.ret (.var "v___x_661_"))] [(.decl .u64 "v___x_662_"), (.decl .u8 "v___x_663_"), (.assign "v___x_662_" (.bin .sub (.var "v_limit_637_") (.var "v_addr_633_"))), (.assign "v___x_663_" (.bin .decLe (.var "v_len_634_") (.var "v___x_662_"))), (.ifZero "v___x_663_" [(.decl .u64 "v___x_664_"), (.assign "v___x_664_" (.lit 4)), (.ret (.var "v___x_664_"))] [(.ret (.var "v___x_658_"))])])]), (.block "v___jp_665_" [(.ifZero "v___y_666_" [(.decl .u64 "v___x_667_"), (.decl .u8 "v___x_668_"), (.assign "v___x_667_" (.lit 14)), (.assign "v___x_668_" (.bin .decLt (.var "v_len_634_") (.var "v___x_667_"))), (.ifZero "v___x_668_" [(.decl .u64 "v___x_669_"), (.decl .u8 "v___x_670_"), (.assign "v___x_669_" (.lit 1514)), (.assign "v___x_670_" (.bin .decLt (.var "v___x_669_") (.var "v_len_634_"))), (.ifZero "v___x_670_" [(.decl .u8 "v___x_671_"), (.decl .u8 "v___x_672_"), (.assign "v___x_671_" (.bin .decLe (.var "v_addr_633_") (.var "v_limit_637_"))), (.assign "v___x_672_" (.bin .decLe (.var "v_base_636_") (.var "v_addr_633_"))), (.ifZero "v___x_672_" [(.assign "v___y_660_" (.var "v___x_672_")), (.goto "v___jp_659_")] [(.assign "v___y_660_" (.var "v___x_671_")), (.goto "v___jp_659_")])] [(.ret (.var "v___x_645_"))])] [(.ret (.var "v___x_645_"))])] [(.ret (.var "v___x_655_"))])])])] [(.decl .u8 "v___x_674_"), (.assign "v___x_674_" (.bin .decEq (.var "v_pending_635_") (.var "v___x_653_"))), (.ifZero "v___x_674_" [(.ifZero "v___x_654_" [(.goto "v___jp_646_")] [(.decl .u64 "v___x_675_"), (.assign "v___x_675_" (.lit 2)), (.ret (.var "v___x_675_"))])] [(.goto "v___jp_646_")])])]),
      (.block "v___jp_638_" [(.ifZero "v___y_639_" [(.decl .u64 "v___x_640_"), (.assign "v___x_640_" (.lit 4)), (.ret (.var "v___x_640_"))] [(.decl .u64 "v___x_641_"), (.decl .u8 "v___x_642_"), (.assign "v___x_641_" (.bin .sub (.var "v_limit_637_") (.var "v_addr_633_"))), (.assign "v___x_642_" (.bin .decLe (.var "v_len_634_") (.var "v___x_641_"))), (.ifZero "v___x_642_" [(.decl .u64 "v___x_643_"), (.assign "v___x_643_" (.lit 4)), (.ret (.var "v___x_643_"))] [(.decl .u64 "v___x_644_"), (.assign "v___x_644_" (.lit 0)), (.ret (.var "v___x_644_"))])])]),
      (.block "v___jp_646_" [(.decl .u64 "v___x_647_"), (.decl .u8 "v___x_648_"), (.assign "v___x_647_" (.lit 1514)), (.assign "v___x_648_" (.bin .decLt (.var "v___x_647_") (.var "v_len_634_"))), (.ifZero "v___x_648_" [(.decl .u8 "v___x_649_"), (.decl .u8 "v___x_650_"), (.assign "v___x_649_" (.bin .decLe (.var "v_addr_633_") (.var "v_limit_637_"))), (.assign "v___x_650_" (.bin .decLe (.var "v_base_636_") (.var "v_addr_633_"))), (.ifZero "v___x_650_" [(.assign "v___y_639_" (.var "v___x_650_")), (.goto "v___jp_638_")] [(.assign "v___y_639_" (.var "v___x_649_")), (.goto "v___jp_638_")])] [(.ret (.var "v___x_645_"))])])] }
-- END GENERATED AST

-- BEGIN GENERATED AST leanos_frame_copy_check
def frameCopyCheckC : Func :=
  { params := [("v_subject_706_", .u64), ("v_request_707_", .u64), ("v_addr_708_", .u64), ("v_len_709_", .u64), ("v_base_710_", .u64), ("v_limit_711_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___x_712_"),
      (.decl .u64 "v___x_713_"),
      (.decl .u64 "v___x_714_"),
      (.decl .u64 "v___x_715_"),
      (.decl .u64 "v___x_716_"),
      (.assign "v___x_712_" (.lit 255)),
      (.assign "v___x_713_" (.bin .land (.var "v_request_707_") (.var "v___x_712_"))),
      (.assign "v___x_714_" (.lit 8)),
      (.assign "v___x_715_" (.bin .shiftRight (.var "v_request_707_") (.var "v___x_714_"))),
      (.assign "v___x_716_" (.call "l_LeanOS_NetworkSubject_frameCopyDecide" ["v_subject_706_", "v___x_713_", "v_addr_708_", "v_len_709_", "v___x_715_", "v_base_710_", "v_limit_711_"])),
      (.ret (.var "v___x_716_"))] }
-- END GENERATED AST


/-- The emitted helper computes `frameCopyDecide` on every seven words,
whatever the functions around it. -/
theorem frameCopyDecideC_refines (ext : Ext)
    (subject op addr len pending base limit : UInt64) :
    callWith ext frameCopyDecideC [subject, op, addr, len, pending, base, limit] =
      some (frameCopyDecide subject op addr len pending base limit) := by
  apply callWith_of_tree ext _ frameCopyDecideC rfl
  csym_refine [rangeOk]

/-- The functions the export calls, as the emitted C names them. -/
def link (ext : Ext) : Ext :=
  ext.add "l_LeanOS_NetworkSubject_frameCopyDecide" frameCopyDecideC

/-- Rung 3: the emitted C of `leanos_frame_copy_check`, calling the emitted
helper, computes the Lean witness on every six words. -/
theorem frameCopyCheckC_refines (ext : Ext) (subject request addr len base limit : UInt64) :
    callWith (link ext) frameCopyCheckC [subject, request, addr, len, base, limit] =
      some (frameCopyCheck subject request addr len base limit) := by
  apply callWith_of_tree (link ext) _ frameCopyCheckC rfl
  csym_refine [link, Ext.add, frameCopyDecideC_refines]

/-- The emitted C accepts the network subject's fetch exactly when the
model's `fetchOk` does. -/
theorem frameCopyCheckC_fetch (ext : Ext) (w : Window) (s : State) (addr base limit : UInt64)
    (hw : w = ⟨base.toNat, limit.toNat⟩) (hlen : s.rx.length < 2 ^ 64) :
    callWith (link ext) frameCopyCheckC
        [3, fetchRequest s.rxPending, addr, s.rx.length.toUInt64, base, limit] = some 0 ↔
      fetchOk w s network addr.toNat = true := by
  rw [frameCopyCheckC_refines, Option.some_inj]
  exact frameCopyCheck_fetch w s addr base limit hw hlen

/-- The emitted C accepts the network subject's send exactly when the model's
`sendOk` does. -/
theorem frameCopyCheckC_send (ext : Ext) (w : Window) (s : State) (addr len base limit : UInt64)
    (hw : w = ⟨base.toNat, limit.toNat⟩) :
    callWith (link ext) frameCopyCheckC
        [3, sendRequest s.txPending, addr, len, base, limit] = some 0 ↔
      sendOk w s network addr.toNat len.toNat = true := by
  rw [frameCopyCheckC_refines, Option.some_inj]
  exact frameCopyCheck_send w s addr len base limit hw

/-- The emitted C refuses every other subject whatever it asks. -/
theorem frameCopyCheckC_nonholder (ext : Ext) (subject request addr len base limit : UInt64)
    (h : subject ≠ 3) :
    callWith (link ext) frameCopyCheckC [subject, request, addr, len, base, limit] = some 1 := by
  rw [frameCopyCheckC_refines, frameCopyCheck_nonholder subject request addr len base limit h]

end LeanOS.Refinement.NetworkSubjectC
