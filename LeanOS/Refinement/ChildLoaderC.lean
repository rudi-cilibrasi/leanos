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
  { params := [("v_source_1446_", .u64), ("v_start_1447_", .u64), ("v_stop_1448_", .u64), ("v_fileOffset_1449_", .u64), ("v_span_1450_", .u64)]
    result := .u64
    body := [
      (.decl .u8 "v___y_1452_"),
      (.decl .u8 "v___x_1461_"),
      (.assign "v___x_1461_" (.bin .decLt (.var "v_source_1446_") (.var "v_start_1447_"))),
      (.ifZero "v___x_1461_" [(.decl .u8 "v___x_1462_"), (.assign "v___x_1462_" (.bin .decLt (.var "v_stop_1448_") (.var "v_span_1450_"))), (.assign "v___y_1452_" (.var "v___x_1462_")), (.goto "v___jp_1451_")] [(.assign "v___y_1452_" (.var "v___x_1461_")), (.goto "v___jp_1451_")]),
      (.block "v___jp_1451_" [(.ifZero "v___y_1452_" [(.decl .u64 "v___x_1453_"), (.decl .u8 "v___x_1454_"), (.assign "v___x_1453_" (.bin .sub (.var "v_stop_1448_") (.var "v_span_1450_"))), (.assign "v___x_1454_" (.bin .decLt (.var "v___x_1453_") (.var "v_source_1446_"))), (.ifZero "v___x_1454_" [(.decl .u64 "v___x_1455_"), (.decl .u8 "v___x_1456_"), (.assign "v___x_1455_" (.bin .add (.var "v_start_1447_") (.var "v_fileOffset_1449_"))), (.assign "v___x_1456_" (.bin .decEq (.var "v_source_1446_") (.var "v___x_1455_"))), (.ifZero "v___x_1456_" [(.decl .u64 "v___x_1457_"), (.assign "v___x_1457_" (.lit 6)), (.ret (.var "v___x_1457_"))] [(.decl .u64 "v___x_1458_"), (.assign "v___x_1458_" (.lit 0)), (.ret (.var "v___x_1458_"))])] [(.decl .u64 "v___x_1459_"), (.assign "v___x_1459_" (.lit 5)), (.ret (.var "v___x_1459_"))])] [(.decl .u64 "v___x_1460_"), (.assign "v___x_1460_" (.lit 5)), (.ret (.var "v___x_1460_"))])])] }
-- END GENERATED AST

-- BEGIN GENERATED AST leanos_loader_decide
def loaderDecideC : Func :=
  { params := [("v_op_1475_", .u64), ("v_flags_1476_", .u64), ("v_sourceCode_1477_", .u64), ("v_pages_1478_", .u64), ("v_frames_1479_", .u64), ("v_used_1480_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___x_1481_"),
      (.decl .u8 "v___y_1483_"),
      (.decl .u8 "v___x_1490_"),
      (.assign "v___x_1481_" (.lit 1)),
      (.assign "v___x_1490_" (.bin .decEq (.var "v_op_1475_") (.var "v___x_1481_"))),
      (.ifZero "v___x_1490_" [(.decl .u64 "v___x_1491_"), (.decl .u8 "v___x_1492_"), (.assign "v___x_1491_" (.lit 2)), (.assign "v___x_1492_" (.bin .decEq (.var "v_op_1475_") (.var "v___x_1491_"))), (.ifZero "v___x_1492_" [(.decl .u64 "v___x_1493_"), (.assign "v___x_1493_" (.lit 511)), (.ret (.var "v___x_1493_"))] [(.decl .u64 "v___x_1494_"), (.decl .u64 "v___x_1495_"), (.decl .u8 "v___x_1496_"), (.assign "v___x_1494_" (.bin .land (.var "v_flags_1476_") (.var "v___x_1481_"))), (.assign "v___x_1495_" (.lit 0)), (.assign "v___x_1496_" (.bin .decEq (.var "v___x_1494_") (.var "v___x_1495_"))), (.ifZero "v___x_1496_" [(.decl .u64 "v___x_1497_"), (.decl .u64 "v___x_1498_"), (.decl .u8 "v___x_1499_"), (.assign "v___x_1497_" (.lit 64)), (.assign "v___x_1498_" (.bin .land (.var "v_flags_1476_") (.var "v___x_1497_"))), (.assign "v___x_1499_" (.bin .decEq (.var "v___x_1498_") (.var "v___x_1495_"))), (.ifZero "v___x_1499_" [(.decl .u64 "v___x_1500_"), (.assign "v___x_1500_" (.lit 3)), (.ret (.var "v___x_1500_"))] [(.decl .u64 "v___x_1501_"), (.assign "v___x_1501_" (.lit 521)), (.ret (.var "v___x_1501_"))])] [(.decl .u64 "v___x_1502_"), (.decl .u8 "v___x_1503_"), (.assign "v___x_1502_" (.bin .land (.var "v_flags_1476_") (.var "v___x_1491_"))), (.assign "v___x_1503_" (.bin .decEq (.var "v___x_1502_") (.var "v___x_1495_"))), (.ifZero "v___x_1503_" [(.decl .u64 "v___x_1504_"), (.assign "v___x_1504_" (.lit 258)), (.ret (.var "v___x_1504_"))] [(.decl .u64 "v___x_1505_"), (.assign "v___x_1505_" (.lit 257)), (.ret (.var "v___x_1505_"))])])])] [(.decl .u64 "v___x_1506_"), (.decl .u64 "v___x_1507_"), (.decl .u64 "v___y_1509_"), (.decl .u8 "v___y_1510_"), (.decl .u64 "v___y_1513_"), (.decl .u8 "v___y_1514_"), (.decl .u8 "v___y_1517_"), (.decl .u8 "v___y_1526_"), (.decl .u8 "v___x_1532_"), (.assign "v___x_1506_" (.bin .land (.var "v_flags_1476_") (.var "v___x_1481_"))), (.assign "v___x_1507_" (.lit 0)), (.assign "v___x_1532_" (.bin .decEq (.var "v___x_1506_") (.var "v___x_1507_"))), (.ifZero "v___x_1532_" [(.decl .u64 "v___x_1533_"), (.decl .u64 "v___x_1534_"), (.decl .u8 "v___x_1535_"), (.assign "v___x_1533_" (.lit 4)), (.assign "v___x_1534_" (.bin .land (.var "v_flags_1476_") (.var "v___x_1533_"))), (.assign "v___x_1535_" (.bin .decEq (.var "v___x_1534_") (.var "v___x_1507_"))), (.ifZero "v___x_1535_" [(.decl .u64 "v___x_1536_"), (.decl .u64 "v___x_1537_"), (.decl .u8 "v___x_1538_"), (.assign "v___x_1536_" (.lit 8)), (.assign "v___x_1537_" (.bin .land (.var "v_flags_1476_") (.var "v___x_1536_"))), (.assign "v___x_1538_" (.bin .decEq (.var "v___x_1537_") (.var "v___x_1507_"))), (.ifZero "v___x_1538_" [(.assign "v___y_1526_" (.var "v___x_1490_")), (.goto "v___jp_1525_")] [(.assign "v___y_1526_" (.var "v___x_1535_")), (.goto "v___jp_1525_")])] [(.decl .u64 "v___x_1539_"), (.assign "v___x_1539_" (.lit 515)), (.ret (.var "v___x_1539_"))])] [(.decl .u64 "v___x_1540_"), (.decl .u64 "v___x_1541_"), (.decl .u8 "v___x_1542_"), (.assign "v___x_1540_" (.lit 2)), (.assign "v___x_1541_" (.bin .land (.var "v_flags_1476_") (.var "v___x_1540_"))), (.assign "v___x_1542_" (.bin .decEq (.var "v___x_1541_") (.var "v___x_1507_"))), (.ifZero "v___x_1542_" [(.decl .u64 "v___x_1543_"), (.assign "v___x_1543_" (.lit 258)), (.ret (.var "v___x_1543_"))] [(.decl .u64 "v___x_1544_"), (.assign "v___x_1544_" (.lit 257)), (.ret (.var "v___x_1544_"))])]), (.block "v___jp_1508_" [(.decl .u8 "v___x_1511_"), (.assign "v___x_1511_" (.bin .decEq (.var "v___y_1509_") (.var "v___x_1507_"))), (.ifZero "v___x_1511_" [(.assign "v___y_1483_" (.var "v___x_1490_")), (.goto "v___jp_1482_")] [(.assign "v___y_1483_" (.var "v___y_1510_")), (.goto "v___jp_1482_")])]), (.block "v___jp_1512_" [(.ifZero "v___y_1514_" [(.assign "v___y_1509_" (.var "v___y_1513_")), (.assign "v___y_1510_" (.var "v___y_1514_")), (.goto "v___jp_1508_")] [(.decl .u64 "v___x_1515_"), (.assign "v___x_1515_" (.lit 519)), (.ret (.var "v___x_1515_"))])]), (.block "v___jp_1516_" [(.ifZero "v___y_1517_" [(.decl .u64 "v___x_1518_"), (.decl .u64 "v___x_1519_"), (.decl .u8 "v___x_1520_"), (.assign "v___x_1518_" (.lit 16)), (.assign "v___x_1519_" (.bin .land (.var "v_flags_1476_") (.var "v___x_1518_"))), (.assign "v___x_1520_" (.bin .decEq (.var "v___x_1519_") (.var "v___x_1507_"))), (.ifZero "v___x_1520_" [(.assign "v___y_1513_" (.var "v___x_1519_")), (.assign "v___y_1514_" (.var "v___x_1520_")), (.goto "v___jp_1512_")] [(.decl .u64 "v___x_1521_"), (.decl .u64 "v___x_1522_"), (.decl .u8 "v___x_1523_"), (.assign "v___x_1521_" (.lit 32)), (.assign "v___x_1522_" (.bin .land (.var "v_flags_1476_") (.var "v___x_1521_"))), (.assign "v___x_1523_" (.bin .decEq (.var "v___x_1522_") (.var "v___x_1507_"))), (.ifZero "v___x_1523_" [(.assign "v___y_1513_" (.var "v___x_1519_")), (.assign "v___y_1514_" (.var "v___x_1520_")), (.goto "v___jp_1512_")] [(.assign "v___y_1509_" (.var "v___x_1519_")), (.assign "v___y_1510_" (.var "v___y_1517_")), (.goto "v___jp_1508_")])])] [(.decl .u64 "v___x_1524_"), (.assign "v___x_1524_" (.lit 518)), (.ret (.var "v___x_1524_"))])]), (.block "v___jp_1525_" [(.ifZero "v___y_1526_" [(.decl .u64 "v___x_1527_"), (.decl .u8 "v___x_1528_"), (.assign "v___x_1527_" (.lit 5)), (.assign "v___x_1528_" (.bin .decEq (.var "v_sourceCode_1477_") (.var "v___x_1527_"))), (.ifZero "v___x_1528_" [(.decl .u8 "v___x_1529_"), (.assign "v___x_1529_" (.bin .decEq (.var "v_sourceCode_1477_") (.var "v___x_1507_"))), (.ifZero "v___x_1529_" [(.assign "v___y_1517_" (.var "v___x_1490_")), (.goto "v___jp_1516_")] [(.assign "v___y_1517_" (.var "v___x_1528_")), (.goto "v___jp_1516_")])] [(.decl .u64 "v___x_1530_"), (.assign "v___x_1530_" (.lit 517)), (.ret (.var "v___x_1530_"))])] [(.decl .u64 "v___x_1531_"), (.assign "v___x_1531_" (.lit 516)), (.ret (.var "v___x_1531_"))])])]),
      (.block "v___jp_1482_" [(.ifZero "v___y_1483_" [(.ret (.var "v___x_1481_"))] [(.decl .u8 "v___x_1484_"), (.assign "v___x_1484_" (.bin .decLt (.var "v_frames_1479_") (.var "v_used_1480_"))), (.ifZero "v___x_1484_" [(.decl .u64 "v___x_1485_"), (.decl .u8 "v___x_1486_"), (.assign "v___x_1485_" (.bin .sub (.var "v_frames_1479_") (.var "v_used_1480_"))), (.assign "v___x_1486_" (.bin .decLt (.var "v___x_1485_") (.var "v_pages_1478_"))), (.ifZero "v___x_1486_" [(.decl .u64 "v___x_1487_"), (.assign "v___x_1487_" (.lit 2)), (.ret (.var "v___x_1487_"))] [(.decl .u64 "v___x_1488_"), (.assign "v___x_1488_" (.lit 520)), (.ret (.var "v___x_1488_"))])] [(.decl .u64 "v___x_1489_"), (.assign "v___x_1489_" (.lit 520)), (.ret (.var "v___x_1489_"))])])])] }
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
