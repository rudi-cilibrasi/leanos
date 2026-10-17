import LeanOS.Refinement.CSymbolic
import LeanOS.SpawnSyscall

/-!
# Rung 3 for `leanos_spawn_syscall` and `leanos_spawn_syscall_value` (issue #570)

The ASTs below are the C functions the pinned Lean toolchain emits for the
`@[export leanos_spawn_syscall]` and `@[export leanos_spawn_syscall_value]`
witnesses of #554 and for the five scalar helpers they call, extracted from
the generated `SpawnSyscall.c` by `scripts/extract-generated-c.py`. The build
re-runs the extractor and fails if the emitted C no longer matches them.

The witnesses also call `leanos_composite_dispatch` and
`leanos_composite_dispatch_value`, the generated table of
`CompositeDispatcher`. Their emitted C is not proved here: the theorems take
as a hypothesis (`DispatchSpec`) that the environment answers those two calls
with the Lean definitions. Under that hypothesis and the C-subset semantics
of `LeanOS.Refinement.CSubset`, with the helpers linked as the emitted C calls
them (`link`), both exports compute exactly the Lean witnesses on every six
words, and so every theorem about `SpawnSyscall.spawnSyscall` (refusals, the
gate step, rollback, the whole-trace invariants) holds of the emitted C. The
theorems do not cover the calling convention, the compiler, the linker, the
boot path or QEMU (ADR 0029).
-/
namespace LeanOS.Refinement.SpawnSyscallC

open LeanOS.Refinement.CSubset LeanOS.Refinement.CSymbolic LeanOS.SpawnSyscall

-- BEGIN GENERATED AST l_LeanOS_SpawnSyscall_syscallTag
def syscallTagC : Func :=
  { params := [("v_number_6_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___x_7_"),
      (.decl .u8 "v___x_8_"),
      (.assign "v___x_7_" (.lit 100)),
      (.assign "v___x_8_" (.bin .decEq (.var "v_number_6_") (.var "v___x_7_"))),
      (.ifZero "v___x_8_" [(.decl .u64 "v___x_9_"), (.decl .u8 "v___x_10_"), (.assign "v___x_9_" (.lit 101)), (.assign "v___x_10_" (.bin .decEq (.var "v_number_6_") (.var "v___x_9_"))), (.ifZero "v___x_10_" [(.decl .u64 "v___x_11_"), (.decl .u8 "v___x_12_"), (.assign "v___x_11_" (.lit 102)), (.assign "v___x_12_" (.bin .decEq (.var "v_number_6_") (.var "v___x_11_"))), (.ifZero "v___x_12_" [(.decl .u64 "v___x_13_"), (.decl .u8 "v___x_14_"), (.assign "v___x_13_" (.lit 103)), (.assign "v___x_14_" (.bin .decEq (.var "v_number_6_") (.var "v___x_13_"))), (.ifZero "v___x_14_" [(.decl .u64 "v___x_15_"), (.decl .u8 "v___x_16_"), (.assign "v___x_15_" (.lit 104)), (.assign "v___x_16_" (.bin .decEq (.var "v_number_6_") (.var "v___x_15_"))), (.ifZero "v___x_16_" [(.decl .u64 "v___x_17_"), (.assign "v___x_17_" (.lit 0)), (.ret (.var "v___x_17_"))] [(.decl .u64 "v___x_18_"), (.assign "v___x_18_" (.lit 29697)), (.ret (.var "v___x_18_"))])] [(.decl .u64 "v___x_19_"), (.assign "v___x_19_" (.lit 29441)), (.ret (.var "v___x_19_"))])] [(.decl .u64 "v___x_20_"), (.assign "v___x_20_" (.lit 29185)), (.ret (.var "v___x_20_"))])] [(.decl .u64 "v___x_21_"), (.assign "v___x_21_" (.lit 28929)), (.ret (.var "v___x_21_"))])] [(.decl .u64 "v___x_22_"), (.assign "v___x_22_" (.lit 28673)), (.ret (.var "v___x_22_"))])] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnSyscall_canonical
def canonicalC : Func :=
  { params := [("v_tag_43_", .u64), ("v_rbx_44_", .u64), ("v_rcx_45_", .u64), ("v_rdx_46_", .u64)]
    result := .u8
    body := [
      (.decl .u8 "v___y_52_"),
      (.decl .u64 "v___x_55_"),
      (.decl .u8 "v___x_56_"),
      (.assign "v___x_55_" (.lit 28673)),
      (.assign "v___x_56_" (.bin .decEq (.var "v_tag_43_") (.var "v___x_55_"))),
      (.ifZero "v___x_56_" [(.decl .u64 "v___x_57_"), (.decl .u8 "v___x_58_"), (.assign "v___x_57_" (.lit 28929)), (.assign "v___x_58_" (.bin .decEq (.var "v_tag_43_") (.var "v___x_57_"))), (.ifZero "v___x_58_" [(.decl .u64 "v___x_59_"), (.decl .u8 "v___x_60_"), (.assign "v___x_59_" (.lit 29185)), (.assign "v___x_60_" (.bin .decEq (.var "v_tag_43_") (.var "v___x_59_"))), (.ifZero "v___x_60_" [(.decl .u64 "v___x_61_"), (.decl .u8 "v___x_62_"), (.assign "v___x_61_" (.lit 29441)), (.assign "v___x_62_" (.bin .decEq (.var "v_tag_43_") (.var "v___x_61_"))), (.assign "v___y_52_" (.var "v___x_62_")), (.goto "v___jp_51_")] [(.assign "v___y_52_" (.var "v___x_60_")), (.goto "v___jp_51_")])] [(.decl .u64 "v___x_63_"), (.decl .u8 "v___x_64_"), (.assign "v___x_63_" (.lit 0)), (.assign "v___x_64_" (.bin .decEq (.var "v_rcx_45_") (.var "v___x_63_"))), (.ifZero "v___x_64_" [(.decl .u8 "v___x_65_"), (.assign "v___x_65_" (.bin .decEq (.var "v_rdx_46_") (.var "v___x_63_"))), (.ret (.var "v___x_65_"))] [(.ret (.var "v___x_56_"))])])] [(.decl .u64 "v___x_66_"), (.decl .u8 "v___x_67_"), (.assign "v___x_66_" (.lit 0)), (.assign "v___x_67_" (.bin .decEq (.var "v_rbx_44_") (.var "v___x_66_"))), (.ifZero "v___x_67_" [(.decl .u64 "v___x_68_"), (.decl .u8 "v___x_69_"), (.assign "v___x_68_" (.lit 64)), (.assign "v___x_69_" (.bin .decLt (.var "v_rdx_46_") (.var "v___x_68_"))), (.ret (.var "v___x_69_"))] [(.decl .u8 "v___x_70_"), (.assign "v___x_70_" (.lit 0)), (.ret (.var "v___x_70_"))])]),
      (.block "v___jp_47_" [(.decl .u64 "v___x_48_"), (.decl .u8 "v___x_49_"), (.assign "v___x_48_" (.lit 0)), (.assign "v___x_49_" (.bin .decEq (.var "v_rcx_45_") (.var "v___x_48_"))), (.ifZero "v___x_49_" [(.ret (.var "v___x_49_"))] [(.decl .u8 "v___x_50_"), (.assign "v___x_50_" (.bin .decEq (.var "v_rdx_46_") (.var "v___x_48_"))), (.ret (.var "v___x_50_"))])]),
      (.block "v___jp_51_" [(.ifZero "v___y_52_" [(.decl .u64 "v___x_53_"), (.decl .u8 "v___x_54_"), (.assign "v___x_53_" (.lit 29697)), (.assign "v___x_54_" (.bin .decEq (.var "v_tag_43_") (.var "v___x_53_"))), (.ifZero "v___x_54_" [(.ret (.var "v___x_54_"))] [(.goto "v___jp_47_")])] [(.goto "v___jp_47_")])])] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnSyscall_familyToken
def familyTokenC : Func :=
  { params := [("v_state_81_", .u64)]
    result := .u8
    body := [
      (.decl .u8 "v___y_83_"),
      (.decl .u64 "v___x_88_"),
      (.decl .u8 "v___x_89_"),
      (.assign "v___x_88_" (.lit 28673)),
      (.assign "v___x_89_" (.bin .decLe (.var "v___x_88_") (.var "v_state_81_"))),
      (.ifZero "v___x_89_" [(.assign "v___y_83_" (.var "v___x_89_")), (.goto "v___jp_82_")] [(.decl .u64 "v___x_90_"), (.decl .u8 "v___x_91_"), (.assign "v___x_90_" (.lit 33793)), (.assign "v___x_91_" (.bin .decLe (.var "v_state_81_") (.var "v___x_90_"))), (.assign "v___y_83_" (.var "v___x_91_")), (.goto "v___jp_82_")]),
      (.block "v___jp_82_" [(.ifZero "v___y_83_" [(.ret (.var "v___y_83_"))] [(.decl .u64 "v___x_84_"), (.decl .u64 "v___x_85_"), (.decl .u64 "v___x_86_"), (.decl .u8 "v___x_87_"), (.assign "v___x_84_" (.lit 256)), (.assign "v___x_85_" (.bin .mod (.var "v_state_81_") (.var "v___x_84_"))), (.assign "v___x_86_" (.lit 1)), (.assign "v___x_87_" (.bin .decEq (.var "v___x_85_") (.var "v___x_86_"))), (.ret (.var "v___x_87_"))])])] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnSyscall_stateActor
def stateActorC : Func :=
  { params := [("v_state_96_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___x_97_"),
      (.decl .u8 "v___x_98_"),
      (.assign "v___x_97_" (.lit 30977)),
      (.assign "v___x_98_" (.bin .decEq (.var "v_state_96_") (.var "v___x_97_"))),
      (.ifZero "v___x_98_" [(.decl .u64 "v___x_99_"), (.assign "v___x_99_" (.lit 2)), (.ret (.var "v___x_99_"))] [(.decl .u64 "v___x_100_"), (.assign "v___x_100_" (.lit 1)), (.ret (.var "v___x_100_"))])] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnSyscall_isEdgeReply
def isEdgeReplyC : Func :=
  { params := [("v_reply_105_", .u64)]
    result := .u8
    body := [
      (.decl .u8 "v___y_107_"),
      (.decl .u64 "v___x_110_"),
      (.decl .u64 "v___x_111_"),
      (.decl .u64 "v___x_112_"),
      (.decl .u8 "v___x_113_"),
      (.assign "v___x_110_" (.lit 256)),
      (.assign "v___x_111_" (.bin .mod (.var "v_reply_105_") (.var "v___x_110_"))),
      (.assign "v___x_112_" (.lit 1)),
      (.assign "v___x_113_" (.bin .decEq (.var "v___x_111_") (.var "v___x_112_"))),
      (.ifZero "v___x_113_" [(.assign "v___y_107_" (.var "v___x_113_")), (.goto "v___jp_106_")] [(.decl .u64 "v___x_114_"), (.decl .u8 "v___x_115_"), (.assign "v___x_114_" (.lit 65536)), (.assign "v___x_115_" (.bin .decLe (.var "v___x_114_") (.var "v_reply_105_"))), (.assign "v___y_107_" (.var "v___x_115_")), (.goto "v___jp_106_")]),
      (.block "v___jp_106_" [(.ifZero "v___y_107_" [(.ret (.var "v___y_107_"))] [(.decl .u64 "v___x_108_"), (.decl .u8 "v___x_109_"), (.assign "v___x_108_" (.lit 16777216)), (.assign "v___x_109_" (.bin .decLt (.var "v_reply_105_") (.var "v___x_108_"))), (.ret (.var "v___x_109_"))])])] }
-- END GENERATED AST

-- BEGIN GENERATED AST leanos_spawn_syscall
def spawnSyscallC : Func :=
  { params := [("v_state_120_", .u64), ("v_actor_121_", .u64), ("v_number_122_", .u64), ("v_rbx_123_", .u64), ("v_rcx_124_", .u64), ("v_rdx_125_", .u64)]
    result := .u64
    body := [
      (.decl .u8 "v___x_126_"),
      (.assign "v___x_126_" (.call "l_LeanOS_SpawnSyscall_familyToken" ["v_state_120_"])),
      (.ifZero "v___x_126_" [(.decl .u64 "v___x_127_"), (.assign "v___x_127_" (.lit 65056)), (.ret (.var "v___x_127_"))] [(.decl .u64 "v___x_128_"), (.decl .u8 "v___x_129_"), (.assign "v___x_128_" (.call "l_LeanOS_SpawnSyscall_stateActor" ["v_state_120_"])), (.assign "v___x_129_" (.bin .decEq (.var "v_actor_121_") (.var "v___x_128_"))), (.ifZero "v___x_129_" [(.decl .u64 "v___x_130_"), (.assign "v___x_130_" (.lit 65057)), (.ret (.var "v___x_130_"))] [(.decl .u64 "v___x_131_"), (.decl .u64 "v___x_132_"), (.decl .u8 "v___x_133_"), (.assign "v___x_131_" (.call "l_LeanOS_SpawnSyscall_syscallTag" ["v_number_122_"])), (.assign "v___x_132_" (.lit 0)), (.assign "v___x_133_" (.bin .decEq (.var "v___x_131_") (.var "v___x_132_"))), (.ifZero "v___x_133_" [(.decl .u8 "v___x_134_"), (.assign "v___x_134_" (.call "l_LeanOS_SpawnSyscall_canonical" ["v___x_131_", "v_rbx_123_", "v_rcx_124_", "v_rdx_125_"])), (.ifZero "v___x_134_" [(.decl .u64 "v___x_135_"), (.assign "v___x_135_" (.lit 65059)), (.ret (.var "v___x_135_"))] [(.ifZero "v___x_133_" [(.decl .u64 "v_reply_136_"), (.decl .u8 "v___x_137_"), (.assign "v_reply_136_" (.call "leanos_composite_dispatch" ["v_state_120_", "v___x_131_", "v_rbx_123_", "v_rcx_124_", "v_rdx_125_", "v___x_132_"])), (.assign "v___x_137_" (.call "l_LeanOS_SpawnSyscall_isEdgeReply" ["v_reply_136_"])), (.ifZero "v___x_137_" [(.decl .u64 "v___x_138_"), (.assign "v___x_138_" (.lit 65060)), (.ret (.var "v___x_138_"))] [(.ret (.var "v_reply_136_"))])] [(.decl .u64 "v___x_139_"), (.assign "v___x_139_" (.lit 65059)), (.ret (.var "v___x_139_"))])])] [(.decl .u64 "v___x_140_"), (.assign "v___x_140_" (.lit 65058)), (.ret (.var "v___x_140_"))])])])] }
-- END GENERATED AST

-- BEGIN GENERATED AST leanos_spawn_syscall_value
def spawnSyscallValueC : Func :=
  { params := [("v_state_155_", .u64), ("v_actor_156_", .u64), ("v_number_157_", .u64), ("v_rbx_158_", .u64), ("v_rcx_159_", .u64), ("v_rdx_160_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___x_161_"),
      (.decl .u8 "v___x_162_"),
      (.assign "v___x_161_" (.call "leanos_spawn_syscall" ["v_state_155_", "v_actor_156_", "v_number_157_", "v_rbx_158_", "v_rcx_159_", "v_rdx_160_"])),
      (.assign "v___x_162_" (.call "l_LeanOS_SpawnSyscall_isEdgeReply" ["v___x_161_"])),
      (.ifZero "v___x_162_" [(.decl .u64 "v___x_163_"), (.assign "v___x_163_" (.lit 0)), (.ret (.var "v___x_163_"))] [(.decl .u64 "v___x_164_"), (.decl .u64 "v___x_165_"), (.decl .u64 "v___x_166_"), (.assign "v___x_164_" (.call "l_LeanOS_SpawnSyscall_syscallTag" ["v_number_157_"])), (.assign "v___x_165_" (.lit 0)), (.assign "v___x_166_" (.call "leanos_composite_dispatch_value" ["v_state_155_", "v___x_164_", "v_rbx_158_", "v_rcx_159_", "v_rdx_160_", "v___x_165_"])), (.ret (.var "v___x_166_"))])] }
-- END GENERATED AST


/-! ## The helpers -/

theorem syscallTagC_refines (ext : Ext) (number : UInt64) :
    callWith ext syscallTagC [number] = some (syscallTag number) := by
  apply callWith_of_tree ext _ syscallTagC rfl
  csym_refine [syscallTag]

theorem canonicalC_refines (ext : Ext) (tag rbx rcx rdx : UInt64) :
    callWith ext canonicalC [tag, rbx, rcx, rdx] = some (boolWord (canonical tag rbx rcx rdx)) := by
  apply callWith_of_tree_bool ext _ canonicalC rfl rfl
  csym_refine [canonical]

theorem familyTokenC_refines (ext : Ext) (state : UInt64) :
    callWith ext familyTokenC [state] = some (boolWord (familyToken state)) := by
  apply callWith_of_tree_bool ext _ familyTokenC rfl rfl
  csym_refine [familyToken]

theorem stateActorC_refines (ext : Ext) (state : UInt64) :
    callWith ext stateActorC [state] = some (stateActor state) := by
  apply callWith_of_tree ext _ stateActorC rfl
  csym_refine [stateActor]

theorem isEdgeReplyC_refines (ext : Ext) (reply : UInt64) :
    callWith ext isEdgeReplyC [reply] = some (boolWord (isEdgeReply reply)) := by
  apply callWith_of_tree_bool ext _ isEdgeReplyC rfl rfl
  csym_refine [isEdgeReply]

/-! ## The exports -/

/-- The trusted callees: the environment answers the two generated dispatcher
exports with their Lean definitions. -/
structure DispatchSpec (ext : Ext) : Prop where
  dispatch : ∀ state tag arg0 arg1 arg2 arg3,
    ext "leanos_composite_dispatch" [state, tag, arg0, arg1, arg2, arg3] =
      some (CompositeDispatcher.dispatch state tag arg0 arg1 arg2 arg3)
  dispatchValue : ∀ state tag arg0 arg1 arg2 arg3,
    ext "leanos_composite_dispatch_value" [state, tag, arg0, arg1, arg2, arg3] =
      some (CompositeDispatcher.dispatchValue state tag arg0 arg1 arg2 arg3)

/-- The five helpers, as the emitted C names them, over `ext`. -/
def helpers (ext : Ext) : Ext :=
  ((((ext.add "l_LeanOS_SpawnSyscall_syscallTag" syscallTagC).add
    "l_LeanOS_SpawnSyscall_canonical" canonicalC).add
    "l_LeanOS_SpawnSyscall_familyToken" familyTokenC).add
    "l_LeanOS_SpawnSyscall_stateActor" stateActorC).add
    "l_LeanOS_SpawnSyscall_isEdgeReply" isEdgeReplyC

/-- Every function the exports call, as the emitted C names them. -/
def link (ext : Ext) : Ext :=
  (helpers ext).add "leanos_spawn_syscall" spawnSyscallC

/-- Rung 3: the emitted C of `leanos_spawn_syscall`, calling the emitted
helpers and a dispatcher that meets `DispatchSpec`, computes the Lean witness
on every six words. -/
theorem spawnSyscallC_refines (ext : Ext) (spec : DispatchSpec ext)
    (state actor number rbx rcx rdx : UInt64) :
    callWith (helpers ext) spawnSyscallC [state, actor, number, rbx, rcx, rdx] =
      some (spawnSyscall state actor number rbx rcx rdx) := by
  apply callWith_of_tree (helpers ext) _ spawnSyscallC rfl
  csym_refine [helpers, Ext.add, syscallTagC_refines, canonicalC_refines,
    familyTokenC_refines, stateActorC_refines, isEdgeReplyC_refines, spec.dispatch]

/-- Rung 3: the emitted C of `leanos_spawn_syscall_value`, calling the
emitted `leanos_spawn_syscall` and helpers and a dispatcher that meets
`DispatchSpec`, computes the Lean witness on every six words. -/
theorem spawnSyscallValueC_refines (ext : Ext) (spec : DispatchSpec ext)
    (state actor number rbx rcx rdx : UInt64) :
    callWith (link ext) spawnSyscallValueC [state, actor, number, rbx, rcx, rdx] =
      some (spawnSyscallValue state actor number rbx rcx rdx) := by
  apply callWith_of_tree (link ext) _ spawnSyscallValueC rfl
  csym_tree
  csym_den
  -- Resolve the call of the export first, then the helpers it shares.
  simp +decide only [↓reduceIte, link, Ext.add]
  simp only [spawnSyscallC_refines ext spec]
  simp +decide only [↓reduceIte, helpers, Ext.add, syscallTagC_refines, isEdgeReplyC_refines,
    spec.dispatchValue]
  csym_norm
  all_goals csym_close

end LeanOS.Refinement.SpawnSyscallC
