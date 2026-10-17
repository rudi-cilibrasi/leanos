import LeanOS.Refinement.CSymbolic
import LeanOS.ChildLoader

/-!
# Rung 3 for `leanos_loader_source` and `leanos_loader_decide` (issue #570)

`loaderSourceC` and `loaderDecideC` are the C functions the pinned Lean
toolchain emits for the `@[export leanos_loader_source]` and
`@[export leanos_loader_decide]` witnesses of #555, as extracted from the
generated `ChildLoader.c` by `scripts/extract-generated-c.py`. The build
re-runs the extractor and fails if the emitted C no longer matches these ASTs.

Under the C-subset semantics of `LeanOS.Refinement.CSubset`, calling either on
any fixed-width words returns exactly the Lean witness, and so, through
`ChildLoader.loader_witness_agrees_load` and
`ChildLoader.loader_witness_agrees_start`, the encoded reply of the model's
`ChildLoader.step`. The theorems do not cover the calling convention, the
compiler, the linker, the boot path or QEMU (ADR 0029).
-/
namespace LeanOS.Refinement.ChildLoaderC

open LeanOS.Refinement.CSubset LeanOS.Refinement.CSymbolic LeanOS.ChildLoader


-- BEGIN GENERATED AST leanos_loader_source
def loaderSourceC : Func :=
  { params := [("v_source_1613_", .u64), ("v_start_1614_", .u64), ("v_stop_1615_", .u64), ("v_fileOffset_1616_", .u64), ("v_span_1617_", .u64)]
    result := .u64
    body := [
      (.decl .u8 "v___y_1619_"),
      (.decl .u8 "v___x_1628_"),
      (.assign "v___x_1628_" (.bin .decLt (.var "v_source_1613_") (.var "v_start_1614_"))),
      (.ifZero "v___x_1628_" [(.decl .u8 "v___x_1629_"), (.assign "v___x_1629_" (.bin .decLt (.var "v_stop_1615_") (.var "v_span_1617_"))), (.assign "v___y_1619_" (.var "v___x_1629_")), (.goto "v___jp_1618_")] [(.assign "v___y_1619_" (.var "v___x_1628_")), (.goto "v___jp_1618_")]),
      (.block "v___jp_1618_" [(.ifZero "v___y_1619_" [(.decl .u64 "v___x_1620_"), (.decl .u8 "v___x_1621_"), (.assign "v___x_1620_" (.bin .sub (.var "v_stop_1615_") (.var "v_span_1617_"))), (.assign "v___x_1621_" (.bin .decLt (.var "v___x_1620_") (.var "v_source_1613_"))), (.ifZero "v___x_1621_" [(.decl .u64 "v___x_1622_"), (.decl .u8 "v___x_1623_"), (.assign "v___x_1622_" (.bin .add (.var "v_start_1614_") (.var "v_fileOffset_1616_"))), (.assign "v___x_1623_" (.bin .decEq (.var "v_source_1613_") (.var "v___x_1622_"))), (.ifZero "v___x_1623_" [(.decl .u64 "v___x_1624_"), (.assign "v___x_1624_" (.lit 6)), (.ret (.var "v___x_1624_"))] [(.decl .u64 "v___x_1625_"), (.assign "v___x_1625_" (.lit 0)), (.ret (.var "v___x_1625_"))])] [(.decl .u64 "v___x_1626_"), (.assign "v___x_1626_" (.lit 5)), (.ret (.var "v___x_1626_"))])] [(.decl .u64 "v___x_1627_"), (.assign "v___x_1627_" (.lit 5)), (.ret (.var "v___x_1627_"))])])] }
-- END GENERATED AST

-- BEGIN GENERATED AST leanos_loader_decide
def loaderDecideC : Func :=
  { params := [("v_op_1642_", .u64), ("v_flags_1643_", .u64), ("v_sourceCode_1644_", .u64), ("v_pages_1645_", .u64), ("v_frames_1646_", .u64), ("v_used_1647_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___x_1648_"),
      (.decl .u8 "v___y_1650_"),
      (.decl .u8 "v___x_1657_"),
      (.assign "v___x_1648_" (.lit 1)),
      (.assign "v___x_1657_" (.bin .decEq (.var "v_op_1642_") (.var "v___x_1648_"))),
      (.ifZero "v___x_1657_" [(.decl .u64 "v___x_1658_"), (.decl .u8 "v___x_1659_"), (.assign "v___x_1658_" (.lit 2)), (.assign "v___x_1659_" (.bin .decEq (.var "v_op_1642_") (.var "v___x_1658_"))), (.ifZero "v___x_1659_" [(.decl .u64 "v___x_1660_"), (.assign "v___x_1660_" (.lit 511)), (.ret (.var "v___x_1660_"))] [(.decl .u64 "v___x_1661_"), (.decl .u64 "v___x_1662_"), (.decl .u8 "v___x_1663_"), (.assign "v___x_1661_" (.bin .land (.var "v_flags_1643_") (.var "v___x_1648_"))), (.assign "v___x_1662_" (.lit 0)), (.assign "v___x_1663_" (.bin .decEq (.var "v___x_1661_") (.var "v___x_1662_"))), (.ifZero "v___x_1663_" [(.decl .u64 "v___x_1664_"), (.decl .u64 "v___x_1665_"), (.decl .u8 "v___x_1666_"), (.assign "v___x_1664_" (.lit 64)), (.assign "v___x_1665_" (.bin .land (.var "v_flags_1643_") (.var "v___x_1664_"))), (.assign "v___x_1666_" (.bin .decEq (.var "v___x_1665_") (.var "v___x_1662_"))), (.ifZero "v___x_1666_" [(.decl .u64 "v___x_1667_"), (.assign "v___x_1667_" (.lit 3)), (.ret (.var "v___x_1667_"))] [(.decl .u64 "v___x_1668_"), (.assign "v___x_1668_" (.lit 521)), (.ret (.var "v___x_1668_"))])] [(.decl .u64 "v___x_1669_"), (.decl .u8 "v___x_1670_"), (.assign "v___x_1669_" (.bin .land (.var "v_flags_1643_") (.var "v___x_1658_"))), (.assign "v___x_1670_" (.bin .decEq (.var "v___x_1669_") (.var "v___x_1662_"))), (.ifZero "v___x_1670_" [(.decl .u64 "v___x_1671_"), (.assign "v___x_1671_" (.lit 258)), (.ret (.var "v___x_1671_"))] [(.decl .u64 "v___x_1672_"), (.assign "v___x_1672_" (.lit 257)), (.ret (.var "v___x_1672_"))])])])] [(.decl .u64 "v___x_1673_"), (.decl .u64 "v___x_1674_"), (.decl .u64 "v___y_1676_"), (.decl .u8 "v___y_1677_"), (.decl .u64 "v___y_1680_"), (.decl .u8 "v___y_1681_"), (.decl .u8 "v___y_1684_"), (.decl .u8 "v___y_1693_"), (.decl .u8 "v___x_1699_"), (.assign "v___x_1673_" (.bin .land (.var "v_flags_1643_") (.var "v___x_1648_"))), (.assign "v___x_1674_" (.lit 0)), (.assign "v___x_1699_" (.bin .decEq (.var "v___x_1673_") (.var "v___x_1674_"))), (.ifZero "v___x_1699_" [(.decl .u64 "v___x_1700_"), (.decl .u64 "v___x_1701_"), (.decl .u8 "v___x_1702_"), (.assign "v___x_1700_" (.lit 4)), (.assign "v___x_1701_" (.bin .land (.var "v_flags_1643_") (.var "v___x_1700_"))), (.assign "v___x_1702_" (.bin .decEq (.var "v___x_1701_") (.var "v___x_1674_"))), (.ifZero "v___x_1702_" [(.decl .u64 "v___x_1703_"), (.decl .u64 "v___x_1704_"), (.decl .u8 "v___x_1705_"), (.assign "v___x_1703_" (.lit 8)), (.assign "v___x_1704_" (.bin .land (.var "v_flags_1643_") (.var "v___x_1703_"))), (.assign "v___x_1705_" (.bin .decEq (.var "v___x_1704_") (.var "v___x_1674_"))), (.ifZero "v___x_1705_" [(.assign "v___y_1693_" (.var "v___x_1657_")), (.goto "v___jp_1692_")] [(.assign "v___y_1693_" (.var "v___x_1702_")), (.goto "v___jp_1692_")])] [(.decl .u64 "v___x_1706_"), (.assign "v___x_1706_" (.lit 515)), (.ret (.var "v___x_1706_"))])] [(.decl .u64 "v___x_1707_"), (.decl .u64 "v___x_1708_"), (.decl .u8 "v___x_1709_"), (.assign "v___x_1707_" (.lit 2)), (.assign "v___x_1708_" (.bin .land (.var "v_flags_1643_") (.var "v___x_1707_"))), (.assign "v___x_1709_" (.bin .decEq (.var "v___x_1708_") (.var "v___x_1674_"))), (.ifZero "v___x_1709_" [(.decl .u64 "v___x_1710_"), (.assign "v___x_1710_" (.lit 258)), (.ret (.var "v___x_1710_"))] [(.decl .u64 "v___x_1711_"), (.assign "v___x_1711_" (.lit 257)), (.ret (.var "v___x_1711_"))])]), (.block "v___jp_1675_" [(.decl .u8 "v___x_1678_"), (.assign "v___x_1678_" (.bin .decEq (.var "v___y_1676_") (.var "v___x_1674_"))), (.ifZero "v___x_1678_" [(.assign "v___y_1650_" (.var "v___x_1657_")), (.goto "v___jp_1649_")] [(.assign "v___y_1650_" (.var "v___y_1677_")), (.goto "v___jp_1649_")])]), (.block "v___jp_1679_" [(.ifZero "v___y_1681_" [(.assign "v___y_1676_" (.var "v___y_1680_")), (.assign "v___y_1677_" (.var "v___y_1681_")), (.goto "v___jp_1675_")] [(.decl .u64 "v___x_1682_"), (.assign "v___x_1682_" (.lit 519)), (.ret (.var "v___x_1682_"))])]), (.block "v___jp_1683_" [(.ifZero "v___y_1684_" [(.decl .u64 "v___x_1685_"), (.decl .u64 "v___x_1686_"), (.decl .u8 "v___x_1687_"), (.assign "v___x_1685_" (.lit 16)), (.assign "v___x_1686_" (.bin .land (.var "v_flags_1643_") (.var "v___x_1685_"))), (.assign "v___x_1687_" (.bin .decEq (.var "v___x_1686_") (.var "v___x_1674_"))), (.ifZero "v___x_1687_" [(.assign "v___y_1680_" (.var "v___x_1686_")), (.assign "v___y_1681_" (.var "v___x_1687_")), (.goto "v___jp_1679_")] [(.decl .u64 "v___x_1688_"), (.decl .u64 "v___x_1689_"), (.decl .u8 "v___x_1690_"), (.assign "v___x_1688_" (.lit 32)), (.assign "v___x_1689_" (.bin .land (.var "v_flags_1643_") (.var "v___x_1688_"))), (.assign "v___x_1690_" (.bin .decEq (.var "v___x_1689_") (.var "v___x_1674_"))), (.ifZero "v___x_1690_" [(.assign "v___y_1680_" (.var "v___x_1686_")), (.assign "v___y_1681_" (.var "v___x_1687_")), (.goto "v___jp_1679_")] [(.assign "v___y_1676_" (.var "v___x_1686_")), (.assign "v___y_1677_" (.var "v___y_1684_")), (.goto "v___jp_1675_")])])] [(.decl .u64 "v___x_1691_"), (.assign "v___x_1691_" (.lit 518)), (.ret (.var "v___x_1691_"))])]), (.block "v___jp_1692_" [(.ifZero "v___y_1693_" [(.decl .u64 "v___x_1694_"), (.decl .u8 "v___x_1695_"), (.assign "v___x_1694_" (.lit 5)), (.assign "v___x_1695_" (.bin .decEq (.var "v_sourceCode_1644_") (.var "v___x_1694_"))), (.ifZero "v___x_1695_" [(.decl .u8 "v___x_1696_"), (.assign "v___x_1696_" (.bin .decEq (.var "v_sourceCode_1644_") (.var "v___x_1674_"))), (.ifZero "v___x_1696_" [(.assign "v___y_1684_" (.var "v___x_1657_")), (.goto "v___jp_1683_")] [(.assign "v___y_1684_" (.var "v___x_1695_")), (.goto "v___jp_1683_")])] [(.decl .u64 "v___x_1697_"), (.assign "v___x_1697_" (.lit 517)), (.ret (.var "v___x_1697_"))])] [(.decl .u64 "v___x_1698_"), (.assign "v___x_1698_" (.lit 516)), (.ret (.var "v___x_1698_"))])])]),
      (.block "v___jp_1649_" [(.ifZero "v___y_1650_" [(.ret (.var "v___x_1648_"))] [(.decl .u8 "v___x_1651_"), (.assign "v___x_1651_" (.bin .decLt (.var "v_frames_1646_") (.var "v_used_1647_"))), (.ifZero "v___x_1651_" [(.decl .u64 "v___x_1652_"), (.decl .u8 "v___x_1653_"), (.assign "v___x_1652_" (.bin .sub (.var "v_frames_1646_") (.var "v_used_1647_"))), (.assign "v___x_1653_" (.bin .decLt (.var "v___x_1652_") (.var "v_pages_1645_"))), (.ifZero "v___x_1653_" [(.decl .u64 "v___x_1654_"), (.assign "v___x_1654_" (.lit 2)), (.ret (.var "v___x_1654_"))] [(.decl .u64 "v___x_1655_"), (.assign "v___x_1655_" (.lit 520)), (.ret (.var "v___x_1655_"))])] [(.decl .u64 "v___x_1656_"), (.assign "v___x_1656_" (.lit 520)), (.ret (.var "v___x_1656_"))])])])] }
-- END GENERATED AST

/-- Rung 3: the emitted C of `leanos_loader_source` computes the Lean witness
on every five words. -/
theorem loaderSourceC_refines (source start stop fileOffset span : UInt64) :
    call loaderSourceC [source, start, stop, fileOffset, span] =
      some (loaderSource source start stop fileOffset span) := by
  apply callWith_of_tree noCalls _ loaderSourceC rfl
  csym_refine

/-- Rung 3: the emitted C of `leanos_loader_decide` computes the Lean witness
on every six words. -/
theorem loaderDecideC_refines (op flags sourceCode pages frames used : UInt64) :
    call loaderDecideC [op, flags, sourceCode, pages, frames, used] =
      some (loaderDecide op flags sourceCode pages frames used) := by
  apply callWith_of_tree noCalls _ loaderDecideC rfl
  csym_refine

/-- The two emitted C witnesses answer a start with the model: for every
state and control word, the C decision on the kernel's words returns the
encoded reply of `ChildLoader.step`. -/
theorem loaderC_refines_start (state : State) (control : UInt64)
    (sourceCode pages frames used : UInt64) :
    call loaderDecideC [2, flagsWord state (.start control), sourceCode, pages, frames, used] =
      some (encodeReply false (step state (.start control)).2) := by
  rw [loaderDecideC_refines, loader_witness_agrees_start]

/-- The two emitted C witnesses answer a load with the model: for a state
whose words are small and a small claimed source, the C source check on the
named segment's words, fed with the flags and frame counts into the C
decision, returns the encoded reply of `ChildLoader.step`. -/
theorem loaderC_refines_load (state : State) (control : UInt64) (index source : Nat)
    (small : Small state) (sourceSmall : source < 2 ^ 62) :
    ((match state.plan[index]? with
        | some s => call loaderSourceC [UInt64.ofNat source, UInt64.ofNat state.start,
            UInt64.ofNat state.stop, UInt64.ofNat s.fileOffset,
            UInt64.ofNat (pageCount s * ElfAdmission.pageBytes)]
        | none => some 0).bind fun sourceCode =>
      call loaderDecideC [1, flagsWord state (.load control index source), sourceCode,
        UInt64.ofNat ((state.plan[index]?.map pageCount).getD 0),
        UInt64.ofNat ((state.child.map (fun c : Child => c.frames)).getD 0), UInt64.ofNat state.used]) =
      some (encodeReply (requestWritable state (.load control index source))
        (step state (.load control index source)).2) := by
  have agrees := loader_witness_agrees_load state control index source small sourceSmall
  simp only at agrees
  rw [← agrees]
  cases state.plan[index]? <;> simp only [Option.bind_some, loaderSourceC_refines, loaderDecideC_refines]

end LeanOS.Refinement.ChildLoaderC
