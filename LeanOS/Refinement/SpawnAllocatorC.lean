import LeanOS.Refinement.CSymbolic
import LeanOS.SpawnAllocatorBootRefinement

/-!
# Rung 3 for the spawn allocator's seven exports (issue #593)

The kernel decides the spawn family with seven exports of
`LeanOS.SpawnAllocatorWords` (#575):

| Export | Lean definition |
| --- | --- |
| `leanos_spawn_allocator_seed` | `SpawnAllocatorBoot.seed` |
| `leanos_spawn_allocator_syscall` | `SpawnAllocatorBoot.syscall` |
| `leanos_spawn_allocator_syscall_value` | `SpawnAllocatorBoot.syscallValue` |
| `leanos_spawn_allocator_syscall_next` | `SpawnAllocatorBoot.syscallNext` |
| `leanos_spawn_allocator_kernel` | `SpawnAllocatorBoot.kernel` |
| `leanos_spawn_allocator_kernel_value` | `SpawnAllocatorBoot.kernelValue` |
| `leanos_spawn_allocator_kernel_next` | `SpawnAllocatorBoot.kernelNext` |

The pinned toolchain emits each of them, and each of the 31 scalar functions
they call (`stepReply`, `decideW`, `canonical`, …), as its own C function of
the generated `SpawnAllocatorWords.c`. The 38 ASTs below are those functions
as `scripts/extract-generated-c.py` extracts them. The build re-runs the
extractor for every one (`scripts/refinement-exports.tsv`) and fails if the
emitted C no longer matches its AST.

The proof is compositional, one theorem per C function:

* `link ext` resolves a call of a helper's C name by running that helper's
  AST (`helper?`, `linkAt`). A helper that calls helpers at most `k` calls
  deep is proved under `linkAt ext (n + k)`, and its C name answers in
  `linkAt ext (n + k + 1)` (`link_*`). Every helper call chain is at most five
  calls deep, so `link ext` is `linkAt ext 5`.
* `*C_refines`: under the C-subset semantics of `LeanOS.Refinement.CSubset`,
  each AST computes its Lean definition on every input, for every `ext`: the
  ASTs call only helpers of their own module, and those are proved too.
* `syscallWordsC_spec` and `kernelWordsC_spec` compose the exports with
  `SpawnAllocatorBoot.syscall_spec` and `kernel_spec`: called as the kernel
  calls them, the emitted C computes decode, `SpawnAllocator.step`, encode on
  every record of words. `seedWordsC_eq` gives the seed's words, and
  `seedWordsC_spec`, through `seed_refines`, the encoded family seed.

The theorems do not cover the calling convention, the compiler, the linker,
the boot path, QEMU, or the kernel's own handling of the words it passes in
and gets back (ADR 0029).
-/
namespace LeanOS.Refinement.SpawnAllocatorC

open LeanOS.Refinement.CSubset LeanOS.Refinement.CSymbolic LeanOS.SpawnAllocatorWords
  LeanOS.SpawnAllocatorBoot

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorWords_childCanonical
def childCanonicalC : Func :=
  { params := [("v_word_659_", .u64)]
    result := .u8
    body := [
      (.decl .u64 "v___x_660_"),
      (.decl .u8 "v___x_661_"),
      (.assign "v___x_660_" (.lit 0)),
      (.assign "v___x_661_" (.bin .decEq (.var "v_word_659_") (.var "v___x_660_"))),
      (.ifZero "v___x_661_" [(.decl .u64 "v___x_662_"), (.decl .u64 "v___x_663_"), (.decl .u8 "v___x_664_"), (.assign "v___x_662_" (.lit 16)), (.assign "v___x_663_" (.bin .shiftRight (.var "v_word_659_") (.var "v___x_662_"))), (.assign "v___x_664_" (.bin .decEq (.var "v___x_663_") (.var "v___x_660_"))), (.ifZero "v___x_664_" [(.decl .u64 "v___x_665_"), (.decl .u8 "v___x_666_"), (.assign "v___x_665_" (.lit 281474976710655)), (.assign "v___x_666_" (.bin .decLt (.var "v___x_663_") (.var "v___x_665_"))), (.ret (.var "v___x_666_"))] [(.ret (.var "v___x_661_"))])] [(.ret (.var "v___x_661_"))])] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorWords_occupied
def occupiedC : Func :=
  { params := [("v_word_671_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___x_672_"),
      (.decl .u8 "v___x_673_"),
      (.assign "v___x_672_" (.lit 0)),
      (.assign "v___x_673_" (.bin .decEq (.var "v_word_671_") (.var "v___x_672_"))),
      (.ifZero "v___x_673_" [(.decl .u64 "v___x_674_"), (.assign "v___x_674_" (.lit 1)), (.ret (.var "v___x_674_"))] [(.ret (.var "v___x_672_"))])] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorWords_chargeOf
def chargeOfC : Func :=
  { params := [("v_word_679_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___x_680_"),
      (.decl .u64 "v___x_681_"),
      (.assign "v___x_680_" (.lit 65535)),
      (.assign "v___x_681_" (.bin .land (.var "v_word_679_") (.var "v___x_680_"))),
      (.ret (.var "v___x_681_"))] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorWords_generationOf
def generationOfC : Func :=
  { params := [("v_word_686_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___x_687_"),
      (.decl .u64 "v___x_688_"),
      (.assign "v___x_687_" (.lit 16)),
      (.assign "v___x_688_" (.bin .shiftRight (.var "v_word_686_") (.var "v___x_687_"))),
      (.ret (.var "v___x_688_"))] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorWords_canonical
def canonicalC : Func :=
  { params := [("v_w4_693_", .u64), ("v_c0_694_", .u64), ("v_c1_695_", .u64), ("v_c2_696_", .u64), ("v_c3_697_", .u64), ("v_f_698_", .u64)]
    result := .u8
    body := [
      (.decl .u64 "v___x_699_"),
      (.decl .u8 "v___x_700_"),
      (.assign "v___x_699_" (.lit 0)),
      (.assign "v___x_700_" (.bin .decEq (.var "v_w4_693_") (.var "v___x_699_"))),
      (.ifZero "v___x_700_" [(.decl .u8 "v___x_701_"), (.assign "v___x_701_" (.call "l_LeanOS_SpawnAllocatorWords_childCanonical" ["v_c0_694_"])), (.ifZero "v___x_701_" [(.ret (.var "v___x_701_"))] [(.decl .u8 "v___x_702_"), (.assign "v___x_702_" (.call "l_LeanOS_SpawnAllocatorWords_childCanonical" ["v_c1_695_"])), (.ifZero "v___x_702_" [(.ret (.var "v___x_702_"))] [(.decl .u8 "v___x_703_"), (.assign "v___x_703_" (.call "l_LeanOS_SpawnAllocatorWords_childCanonical" ["v_c2_696_"])), (.ifZero "v___x_703_" [(.ret (.var "v___x_703_"))] [(.decl .u8 "v___x_704_"), (.assign "v___x_704_" (.call "l_LeanOS_SpawnAllocatorWords_childCanonical" ["v_c3_697_"])), (.ifZero "v___x_704_" [(.ret (.var "v___x_704_"))] [(.decl .u64 "v___x_705_"), (.decl .u64 "v___x_706_"), (.decl .u8 "v___x_707_"), (.assign "v___x_705_" (.lit 32)), (.assign "v___x_706_" (.bin .shiftRight (.var "v_f_698_") (.var "v___x_705_"))), (.assign "v___x_707_" (.bin .decEq (.var "v___x_706_") (.var "v___x_699_"))), (.ifZero "v___x_707_" [(.ret (.var "v___x_707_"))] [(.decl .u64 "v___x_708_"), (.decl .u64 "v___x_709_"), (.decl .u64 "v___x_710_"), (.decl .u8 "v___x_711_"), (.assign "v___x_708_" (.lit 65535)), (.assign "v___x_709_" (.bin .land (.var "v_f_698_") (.var "v___x_708_"))), (.assign "v___x_710_" (.lit 4)), (.assign "v___x_711_" (.bin .decLe (.var "v___x_709_") (.var "v___x_710_"))), (.ifZero "v___x_711_" [(.ret (.var "v___x_711_"))] [(.decl .u64 "v___x_712_"), (.decl .u64 "v___x_713_"), (.decl .u64 "v___x_714_"), (.decl .u64 "v___x_715_"), (.decl .u64 "v___x_716_"), (.decl .u64 "v___x_717_"), (.decl .u64 "v___x_718_"), (.decl .u64 "v___x_719_"), (.decl .u64 "v___x_720_"), (.decl .u64 "v___x_721_"), (.decl .u64 "v___x_722_"), (.decl .u8 "v___x_723_"), (.assign "v___x_712_" (.lit 16)), (.assign "v___x_713_" (.bin .shiftRight (.var "v_f_698_") (.var "v___x_712_"))), (.assign "v___x_714_" (.call "l_LeanOS_SpawnAllocatorWords_chargeOf" ["v_c0_694_"])), (.assign "v___x_715_" (.bin .add (.var "v___x_713_") (.var "v___x_714_"))), (.assign "v___x_716_" (.call "l_LeanOS_SpawnAllocatorWords_chargeOf" ["v_c1_695_"])), (.assign "v___x_717_" (.bin .add (.var "v___x_715_") (.var "v___x_716_"))), (.assign "v___x_718_" (.call "l_LeanOS_SpawnAllocatorWords_chargeOf" ["v_c2_696_"])), (.assign "v___x_719_" (.bin .add (.var "v___x_717_") (.var "v___x_718_"))), (.assign "v___x_720_" (.call "l_LeanOS_SpawnAllocatorWords_chargeOf" ["v_c3_697_"])), (.assign "v___x_721_" (.bin .add (.var "v___x_719_") (.var "v___x_720_"))), (.assign "v___x_722_" (.lit 65536)), (.assign "v___x_723_" (.bin .decLt (.var "v___x_721_") (.var "v___x_722_"))), (.ret (.var "v___x_723_"))])])])])])])] [(.decl .u8 "v___x_724_"), (.assign "v___x_724_" (.lit 0)), (.ret (.var "v___x_724_"))])] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorWords_identityExhaustedW
def identityExhaustedWC : Func :=
  { params := [("v_next_739_", .u64)]
    result := .u8
    body := [
      (.decl .u64 "v___x_740_"),
      (.decl .u8 "v___x_741_"),
      (.assign "v___x_740_" (.lit 0)),
      (.assign "v___x_741_" (.bin .decEq (.var "v_next_739_") (.var "v___x_740_"))),
      (.ifZero "v___x_741_" [(.decl .u64 "v___x_742_"), (.decl .u8 "v___x_743_"), (.assign "v___x_742_" (.lit 18446744073709551615)), (.assign "v___x_743_" (.bin .decEq (.var "v_next_739_") (.var "v___x_742_"))), (.ret (.var "v___x_743_"))] [(.ret (.var "v___x_741_"))])] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorWords_capabilityExhaustedW
def capabilityExhaustedWC : Func :=
  { params := [("v_next_748_", .u64)]
    result := .u8
    body := [
      (.decl .u64 "v___x_749_"),
      (.decl .u8 "v___x_750_"),
      (.assign "v___x_749_" (.lit 0)),
      (.assign "v___x_750_" (.bin .decEq (.var "v_next_748_") (.var "v___x_749_"))),
      (.ifZero "v___x_750_" [(.decl .u64 "v___x_751_"), (.decl .u8 "v___x_752_"), (.assign "v___x_751_" (.lit 281474976710655)), (.assign "v___x_752_" (.bin .decLe (.var "v___x_751_") (.var "v_next_748_"))), (.ret (.var "v___x_752_"))] [(.ret (.var "v___x_750_"))])] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorWords_controlAvailableW
def controlAvailableWC : Func :=
  { params := [("v_next_757_", .u64)]
    result := .u8
    body := [
      (.decl .u64 "v___x_758_"),
      (.decl .u8 "v___x_759_"),
      (.assign "v___x_758_" (.lit 0)),
      (.assign "v___x_759_" (.bin .decEq (.var "v_next_757_") (.var "v___x_758_"))),
      (.ifZero "v___x_759_" [(.decl .u64 "v___x_760_"), (.decl .u8 "v___x_761_"), (.assign "v___x_760_" (.lit 281474976710655)), (.assign "v___x_761_" (.bin .decLt (.var "v_next_757_") (.var "v___x_760_"))), (.ret (.var "v___x_761_"))] [(.decl .u8 "v___x_762_"), (.assign "v___x_762_" (.lit 0)), (.ret (.var "v___x_762_"))])] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorWords_childCountW
def childCountWC : Func :=
  { params := [("v_c0_767_", .u64), ("v_c1_768_", .u64), ("v_c2_769_", .u64), ("v_c3_770_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___x_771_"),
      (.decl .u64 "v___x_772_"),
      (.decl .u64 "v___x_773_"),
      (.decl .u64 "v___x_774_"),
      (.decl .u64 "v___x_775_"),
      (.decl .u64 "v___x_776_"),
      (.decl .u64 "v___x_777_"),
      (.assign "v___x_771_" (.call "l_LeanOS_SpawnAllocatorWords_occupied" ["v_c0_767_"])),
      (.assign "v___x_772_" (.call "l_LeanOS_SpawnAllocatorWords_occupied" ["v_c1_768_"])),
      (.assign "v___x_773_" (.bin .add (.var "v___x_771_") (.var "v___x_772_"))),
      (.assign "v___x_774_" (.call "l_LeanOS_SpawnAllocatorWords_occupied" ["v_c2_769_"])),
      (.assign "v___x_775_" (.bin .add (.var "v___x_773_") (.var "v___x_774_"))),
      (.assign "v___x_776_" (.call "l_LeanOS_SpawnAllocatorWords_occupied" ["v_c3_770_"])),
      (.assign "v___x_777_" (.bin .add (.var "v___x_775_") (.var "v___x_776_"))),
      (.ret (.var "v___x_777_"))] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorWords_freeSlotW
def freeSlotWC : Func :=
  { params := [("v_c0_788_", .u64), ("v_c1_789_", .u64), ("v_c2_790_", .u64), ("v_c3_791_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___x_792_"),
      (.decl .u8 "v___x_793_"),
      (.assign "v___x_792_" (.lit 0)),
      (.assign "v___x_793_" (.bin .decEq (.var "v_c0_788_") (.var "v___x_792_"))),
      (.ifZero "v___x_793_" [(.decl .u8 "v___x_794_"), (.assign "v___x_794_" (.bin .decEq (.var "v_c1_789_") (.var "v___x_792_"))), (.ifZero "v___x_794_" [(.decl .u8 "v___x_795_"), (.assign "v___x_795_" (.bin .decEq (.var "v_c2_790_") (.var "v___x_792_"))), (.ifZero "v___x_795_" [(.decl .u8 "v___x_796_"), (.assign "v___x_796_" (.bin .decEq (.var "v_c3_791_") (.var "v___x_792_"))), (.ifZero "v___x_796_" [(.decl .u64 "v___x_797_"), (.assign "v___x_797_" (.lit 4)), (.ret (.var "v___x_797_"))] [(.decl .u64 "v___x_798_"), (.assign "v___x_798_" (.lit 3)), (.ret (.var "v___x_798_"))])] [(.decl .u64 "v___x_799_"), (.assign "v___x_799_" (.lit 2)), (.ret (.var "v___x_799_"))])] [(.decl .u64 "v___x_800_"), (.assign "v___x_800_" (.lit 1)), (.ret (.var "v___x_800_"))])] [(.ret (.var "v___x_792_"))])] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorWords_childWordAt
def childWordAtC : Func :=
  { params := [("v_slot_811_", .u64), ("v_c0_812_", .u64), ("v_c1_813_", .u64), ("v_c2_814_", .u64), ("v_c3_815_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___x_816_"),
      (.decl .u8 "v___x_817_"),
      (.assign "v___x_816_" (.lit 0)),
      (.assign "v___x_817_" (.bin .decEq (.var "v_slot_811_") (.var "v___x_816_"))),
      (.ifZero "v___x_817_" [(.decl .u64 "v___x_818_"), (.decl .u8 "v___x_819_"), (.assign "v___x_818_" (.lit 1)), (.assign "v___x_819_" (.bin .decEq (.var "v_slot_811_") (.var "v___x_818_"))), (.ifZero "v___x_819_" [(.decl .u64 "v___x_820_"), (.decl .u8 "v___x_821_"), (.assign "v___x_820_" (.lit 2)), (.assign "v___x_821_" (.bin .decEq (.var "v_slot_811_") (.var "v___x_820_"))), (.ifZero "v___x_821_" [(.decl .u64 "v___x_822_"), (.decl .u8 "v___x_823_"), (.assign "v___x_822_" (.lit 3)), (.assign "v___x_823_" (.bin .decEq (.var "v_slot_811_") (.var "v___x_822_"))), (.ifZero "v___x_823_" [(.ret (.var "v___x_816_"))] [(.ret (.var "v_c3_815_"))])] [(.ret (.var "v_c2_814_"))])] [(.ret (.var "v_c1_813_"))])] [(.ret (.var "v_c0_812_"))])] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorWords_memoryWordAt
def memoryWordAtC : Func :=
  { params := [("v_slot_836_", .u64), ("v_m2_837_", .u64), ("v_m3_838_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___x_839_"),
      (.decl .u8 "v___x_840_"),
      (.assign "v___x_839_" (.lit 2)),
      (.assign "v___x_840_" (.bin .decEq (.var "v_slot_836_") (.var "v___x_839_"))),
      (.ifZero "v___x_840_" [(.decl .u64 "v___x_841_"), (.decl .u8 "v___x_842_"), (.assign "v___x_841_" (.lit 3)), (.assign "v___x_842_" (.bin .decEq (.var "v_slot_836_") (.var "v___x_841_"))), (.ifZero "v___x_842_" [(.decl .u64 "v___x_843_"), (.assign "v___x_843_" (.lit 0)), (.ret (.var "v___x_843_"))] [(.ret (.var "v_m3_838_"))])] [(.ret (.var "v_m2_837_"))])] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorWords_budgetW
def budgetWC : Func :=
  { params := [("v_f_852_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___x_853_"),
      (.decl .u64 "v___x_854_"),
      (.assign "v___x_853_" (.lit 65535)),
      (.assign "v___x_854_" (.bin .land (.var "v_f_852_") (.var "v___x_853_"))),
      (.ret (.var "v___x_854_"))] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorWords_parentFramesW
def parentFramesWC : Func :=
  { params := [("v_f_859_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___x_860_"),
      (.decl .u64 "v___x_861_"),
      (.assign "v___x_860_" (.lit 16)),
      (.assign "v___x_861_" (.bin .shiftRight (.var "v_f_859_") (.var "v___x_860_"))),
      (.ret (.var "v___x_861_"))] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorWords_availableW
def availableWC : Func :=
  { params := [("v_f_866_", .u64), ("v_m2_867_", .u64), ("v_m3_868_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___x_869_"),
      (.decl .u64 "v___x_870_"),
      (.decl .u64 "v___x_871_"),
      (.decl .u64 "v___x_872_"),
      (.decl .u8 "v___x_873_"),
      (.assign "v___x_869_" (.call "l_LeanOS_SpawnAllocatorWords_occupied" ["v_m2_867_"])),
      (.assign "v___x_870_" (.call "l_LeanOS_SpawnAllocatorWords_occupied" ["v_m3_868_"])),
      (.assign "v___x_871_" (.bin .add (.var "v___x_869_") (.var "v___x_870_"))),
      (.assign "v___x_872_" (.call "l_LeanOS_SpawnAllocatorWords_parentFramesW" ["v_f_866_"])),
      (.assign "v___x_873_" (.bin .decLe (.var "v___x_871_") (.var "v___x_872_"))),
      (.ifZero "v___x_873_" [(.decl .u64 "v___x_874_"), (.assign "v___x_874_" (.lit 0)), (.ret (.var "v___x_874_"))] [(.decl .u64 "v___x_875_"), (.assign "v___x_875_" (.bin .sub (.var "v___x_872_") (.var "v___x_871_"))), (.ret (.var "v___x_875_"))])] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorWords_resolveEndpointW
def resolveEndpointWC : Func :=
  { params := [("v_m2_884_", .u64), ("v_m3_885_", .u64), ("v_word_886_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___x_887_"),
      (.decl .u64 "v_slot_888_"),
      (.decl .u8 "v___x_889_"),
      (.assign "v___x_887_" (.lit 65535)),
      (.assign "v_slot_888_" (.bin .land (.var "v_word_886_") (.var "v___x_887_"))),
      (.assign "v___x_889_" (.bin .decEq (.var "v_slot_888_") (.var "v___x_887_"))),
      (.ifZero "v___x_889_" [(.decl .u64 "v___x_890_"), (.decl .u64 "v_identity_891_"), (.decl .u64 "v___x_892_"), (.decl .u8 "v___x_893_"), (.assign "v___x_890_" (.lit 16)), (.assign "v_identity_891_" (.bin .shiftRight (.var "v_word_886_") (.var "v___x_890_"))), (.assign "v___x_892_" (.lit 0)), (.assign "v___x_893_" (.bin .decEq (.var "v_identity_891_") (.var "v___x_892_"))), (.ifZero "v___x_893_" [(.decl .u64 "v___x_894_"), (.decl .u8 "v___x_895_"), (.assign "v___x_894_" (.lit 281474976710655)), (.assign "v___x_895_" (.bin .decEq (.var "v_identity_891_") (.var "v___x_894_"))), (.ifZero "v___x_895_" [(.decl .u64 "v___x_896_"), (.decl .u8 "v___x_897_"), (.assign "v___x_896_" (.lit 4)), (.assign "v___x_897_" (.bin .decLe (.var "v___x_896_") (.var "v_slot_888_"))), (.ifZero "v___x_897_" [(.decl .u8 "v___x_898_"), (.assign "v___x_898_" (.bin .decEq (.var "v_slot_888_") (.var "v___x_892_"))), (.ifZero "v___x_898_" [(.decl .u64 "v___x_899_"), (.decl .u8 "v___x_900_"), (.assign "v___x_899_" (.lit 1)), (.assign "v___x_900_" (.bin .decEq (.var "v_slot_888_") (.var "v___x_899_"))), (.ifZero "v___x_900_" [(.decl .u64 "v___x_901_"), (.decl .u8 "v___x_902_"), (.assign "v___x_901_" (.call "l_LeanOS_SpawnAllocatorWords_memoryWordAt" ["v_slot_888_", "v_m2_884_", "v_m3_885_"])), (.assign "v___x_902_" (.bin .decEq (.var "v___x_901_") (.var "v___x_892_"))), (.ifZero "v___x_902_" [(.decl .u8 "v___x_903_"), (.assign "v___x_903_" (.bin .decEq (.var "v_identity_891_") (.var "v___x_901_"))), (.ifZero "v___x_903_" [(.decl .u64 "v___x_904_"), (.assign "v___x_904_" (.lit 36)), (.ret (.var "v___x_904_"))] [(.decl .u64 "v___x_905_"), (.assign "v___x_905_" (.lit 37)), (.ret (.var "v___x_905_"))])] [(.decl .u64 "v___x_906_"), (.assign "v___x_906_" (.lit 36)), (.ret (.var "v___x_906_"))])] [(.decl .u8 "v___x_907_"), (.assign "v___x_907_" (.bin .decEq (.var "v_identity_891_") (.var "v___x_896_"))), (.ifZero "v___x_907_" [(.decl .u64 "v___x_908_"), (.assign "v___x_908_" (.lit 36)), (.ret (.var "v___x_908_"))] [(.decl .u64 "v___x_909_"), (.assign "v___x_909_" (.lit 37)), (.ret (.var "v___x_909_"))])])] [(.decl .u64 "v___x_910_"), (.decl .u8 "v___x_911_"), (.assign "v___x_910_" (.lit 3)), (.assign "v___x_911_" (.bin .decEq (.var "v_identity_891_") (.var "v___x_910_"))), (.ifZero "v___x_911_" [(.decl .u64 "v___x_912_"), (.assign "v___x_912_" (.lit 36)), (.ret (.var "v___x_912_"))] [(.ret (.var "v___x_892_"))])])] [(.decl .u64 "v___x_913_"), (.assign "v___x_913_" (.lit 35)), (.ret (.var "v___x_913_"))])] [(.decl .u64 "v___x_914_"), (.assign "v___x_914_" (.lit 33)), (.ret (.var "v___x_914_"))])] [(.decl .u64 "v___x_915_"), (.assign "v___x_915_" (.lit 33)), (.ret (.var "v___x_915_"))])] [(.decl .u64 "v___x_916_"), (.assign "v___x_916_" (.lit 32)), (.ret (.var "v___x_916_"))])] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorWords_resolveControlW
def resolveControlWC : Func :=
  { params := [("v_c0_925_", .u64), ("v_c1_926_", .u64), ("v_c2_927_", .u64), ("v_c3_928_", .u64), ("v_word_929_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___x_930_"),
      (.decl .u64 "v_slot_931_"),
      (.decl .u8 "v___x_932_"),
      (.assign "v___x_930_" (.lit 65535)),
      (.assign "v_slot_931_" (.bin .land (.var "v_word_929_") (.var "v___x_930_"))),
      (.assign "v___x_932_" (.bin .decEq (.var "v_slot_931_") (.var "v___x_930_"))),
      (.ifZero "v___x_932_" [(.decl .u64 "v___x_933_"), (.decl .u64 "v_identity_934_"), (.decl .u64 "v___x_935_"), (.decl .u8 "v___x_936_"), (.assign "v___x_933_" (.lit 16)), (.assign "v_identity_934_" (.bin .shiftRight (.var "v_word_929_") (.var "v___x_933_"))), (.assign "v___x_935_" (.lit 0)), (.assign "v___x_936_" (.bin .decEq (.var "v_identity_934_") (.var "v___x_935_"))), (.ifZero "v___x_936_" [(.decl .u64 "v___x_937_"), (.decl .u8 "v___x_938_"), (.assign "v___x_937_" (.lit 281474976710655)), (.assign "v___x_938_" (.bin .decEq (.var "v_identity_934_") (.var "v___x_937_"))), (.ifZero "v___x_938_" [(.decl .u64 "v___x_939_"), (.decl .u8 "v___x_940_"), (.assign "v___x_939_" (.call "l_LeanOS_SpawnAllocatorWords_childWordAt" ["v_slot_931_", "v_c0_925_", "v_c1_926_", "v_c2_927_", "v_c3_928_"])), (.assign "v___x_940_" (.bin .decEq (.var "v___x_939_") (.var "v___x_935_"))), (.ifZero "v___x_940_" [(.decl .u64 "v___x_941_"), (.decl .u8 "v___x_942_"), (.assign "v___x_941_" (.call "l_LeanOS_SpawnAllocatorWords_generationOf" ["v___x_939_"])), (.assign "v___x_942_" (.bin .decEq (.var "v___x_941_") (.var "v_identity_934_"))), (.ifZero "v___x_942_" [(.decl .u64 "v___x_943_"), (.assign "v___x_943_" (.lit 67)), (.ret (.var "v___x_943_"))] [(.ret (.var "v___x_935_"))])] [(.decl .u64 "v___x_944_"), (.assign "v___x_944_" (.lit 67)), (.ret (.var "v___x_944_"))])] [(.decl .u64 "v___x_945_"), (.assign "v___x_945_" (.lit 66)), (.ret (.var "v___x_945_"))])] [(.decl .u64 "v___x_946_"), (.assign "v___x_946_" (.lit 66)), (.ret (.var "v___x_946_"))])] [(.decl .u64 "v___x_947_"), (.assign "v___x_947_" (.lit 65)), (.ret (.var "v___x_947_"))])] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorWords_rightsValidW
def rightsValidWC : Func :=
  { params := [("v_rights_960_", .u64)]
    result := .u8
    body := [
      (.decl .u64 "v___x_961_"),
      (.decl .u64 "v___x_962_"),
      (.decl .u64 "v___x_963_"),
      (.decl .u8 "v___x_964_"),
      (.assign "v___x_961_" (.lit 3)),
      (.assign "v___x_962_" (.bin .land (.var "v_rights_960_") (.var "v___x_961_"))),
      (.assign "v___x_963_" (.lit 0)),
      (.assign "v___x_964_" (.bin .decEq (.var "v___x_962_") (.var "v___x_963_"))),
      (.ifZero "v___x_964_" [(.ret (.var "v___x_964_"))] [(.decl .u64 "v___x_965_"), (.decl .u64 "v___x_966_"), (.decl .u8 "v___x_967_"), (.assign "v___x_965_" (.lit 60)), (.assign "v___x_966_" (.bin .land (.var "v_rights_960_") (.var "v___x_965_"))), (.assign "v___x_967_" (.bin .decEq (.var "v___x_966_") (.var "v___x_963_"))), (.ifZero "v___x_967_" [(.ret (.var "v___x_964_"))] [(.decl .u8 "v___x_968_"), (.assign "v___x_968_" (.lit 0)), (.ret (.var "v___x_968_"))])])] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorWords_commandErrorW
def commandErrorWC : Func :=
  { params := [("v_tag_973_", .u64), ("v_a0_974_", .u64), ("v_a1_975_", .u64), ("v_a2_976_", .u64), ("v_a3_977_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___y_979_"),
      (.decl .u8 "v___y_980_"),
      (.decl .u64 "v___x_986_"),
      (.decl .u8 "v___x_987_"),
      (.assign "v___x_986_" (.lit 28673)),
      (.assign "v___x_987_" (.bin .decEq (.var "v_tag_973_") (.var "v___x_986_"))),
      (.ifZero "v___x_987_" [(.decl .u64 "v___x_988_"), (.decl .u8 "v___x_989_"), (.decl .u8 "v___y_991_"), (.assign "v___x_988_" (.lit 28929)), (.assign "v___x_989_" (.bin .decEq (.var "v_tag_973_") (.var "v___x_988_"))), (.ifZero "v___x_989_" [(.decl .u8 "v___x_994_"), (.decl .u64 "v___x_995_"), (.decl .u8 "v___x_996_"), (.assign "v___x_994_" (.lit 1)), (.assign "v___x_995_" (.lit 29185)), (.assign "v___x_996_" (.bin .decEq (.var "v_tag_973_") (.var "v___x_995_"))), (.ifZero "v___x_996_" [(.decl .u64 "v___x_997_"), (.decl .u8 "v___x_998_"), (.assign "v___x_997_" (.lit 29441)), (.assign "v___x_998_" (.bin .decEq (.var "v_tag_973_") (.var "v___x_997_"))), (.ifZero "v___x_998_" [(.decl .u64 "v___x_999_"), (.decl .u8 "v___x_1000_"), (.assign "v___x_999_" (.lit 29697)), (.assign "v___x_1000_" (.bin .decEq (.var "v_tag_973_") (.var "v___x_999_"))), (.ifZero "v___x_1000_" [(.decl .u64 "v___x_1001_"), (.decl .u8 "v___x_1002_"), (.assign "v___x_1001_" (.lit 30209)), (.assign "v___x_1002_" (.bin .decEq (.var "v_tag_973_") (.var "v___x_1001_"))), (.ifZero "v___x_1002_" [(.decl .u64 "v___x_1003_"), (.decl .u8 "v___x_1004_"), (.assign "v___x_1003_" (.lit 29953)), (.assign "v___x_1004_" (.bin .decEq (.var "v_tag_973_") (.var "v___x_1003_"))), (.ifZero "v___x_1004_" [(.decl .u64 "v___x_1005_"), (.assign "v___x_1005_" (.lit 65284)), (.ret (.var "v___x_1005_"))] [(.decl .u64 "v___x_1006_"), (.decl .u8 "v___x_1010_"), (.assign "v___x_1006_" (.lit 0)), (.assign "v___x_1010_" (.bin .decEq (.var "v_a2_976_") (.var "v___x_1006_"))), (.ifZero "v___x_1010_" [(.ifZero "v___x_1004_" [(.goto "v___jp_1007_")] [(.decl .u64 "v___x_1011_"), (.assign "v___x_1011_" (.lit 65282)), (.ret (.var "v___x_1011_"))])] [(.goto "v___jp_1007_")]), (.block "v___jp_1007_" [(.decl .u8 "v___x_1008_"), (.assign "v___x_1008_" (.bin .decEq (.var "v_a3_977_") (.var "v___x_1006_"))), (.ifZero "v___x_1008_" [(.ifZero "v___x_1004_" [(.ret (.var "v___x_1006_"))] [(.decl .u64 "v___x_1009_"), (.assign "v___x_1009_" (.lit 65282)), (.ret (.var "v___x_1009_"))])] [(.ret (.var "v___x_1006_"))])])])] [(.assign "v___y_991_" (.var "v___x_1002_")), (.goto "v___jp_990_")])] [(.assign "v___y_991_" (.var "v___x_994_")), (.goto "v___jp_990_")])] [(.assign "v___y_991_" (.var "v___x_994_")), (.goto "v___jp_990_")])] [(.assign "v___y_991_" (.var "v___x_994_")), (.goto "v___jp_990_")])] [(.decl .u64 "v___x_1012_"), (.decl .u8 "v___y_1017_"), (.decl .u8 "v___x_1021_"), (.assign "v___x_1012_" (.lit 0)), (.assign "v___x_1021_" (.bin .decEq (.var "v_a2_976_") (.var "v___x_1012_"))), (.ifZero "v___x_1021_" [(.assign "v___y_1017_" (.var "v___x_989_")), (.goto "v___jp_1016_")] [(.assign "v___y_1017_" (.var "v___x_987_")), (.goto "v___jp_1016_")]), (.block "v___jp_1013_" [(.decl .u8 "v___x_1014_"), (.assign "v___x_1014_" (.bin .decEq (.var "v_a1_975_") (.var "v___x_1012_"))), (.ifZero "v___x_1014_" [(.ret (.var "v___x_1012_"))] [(.decl .u64 "v___x_1015_"), (.assign "v___x_1015_" (.lit 65285)), (.ret (.var "v___x_1015_"))])]), (.block "v___jp_1016_" [(.ifZero "v___y_1017_" [(.decl .u8 "v___x_1018_"), (.assign "v___x_1018_" (.bin .decEq (.var "v_a3_977_") (.var "v___x_1012_"))), (.ifZero "v___x_1018_" [(.ifZero "v___x_989_" [(.goto "v___jp_1013_")] [(.decl .u64 "v___x_1019_"), (.assign "v___x_1019_" (.lit 65282)), (.ret (.var "v___x_1019_"))])] [(.goto "v___jp_1013_")])] [(.decl .u64 "v___x_1020_"), (.assign "v___x_1020_" (.lit 65282)), (.ret (.var "v___x_1020_"))])])]), (.block "v___jp_990_" [(.decl .u64 "v___x_992_"), (.decl .u8 "v___x_993_"), (.assign "v___x_992_" (.lit 0)), (.assign "v___x_993_" (.bin .decEq (.var "v_a1_975_") (.var "v___x_992_"))), (.ifZero "v___x_993_" [(.assign "v___y_979_" (.var "v___x_992_")), (.assign "v___y_980_" (.var "v___y_991_")), (.goto "v___jp_978_")] [(.assign "v___y_979_" (.var "v___x_992_")), (.assign "v___y_980_" (.var "v___x_989_")), (.goto "v___jp_978_")])])] [(.decl .u64 "v___x_1022_"), (.decl .u8 "v___x_1029_"), (.assign "v___x_1022_" (.lit 0)), (.assign "v___x_1029_" (.bin .decEq (.var "v_a3_977_") (.var "v___x_1022_"))), (.ifZero "v___x_1029_" [(.ifZero "v___x_987_" [(.goto "v___jp_1023_")] [(.decl .u64 "v___x_1030_"), (.assign "v___x_1030_" (.lit 65282)), (.ret (.var "v___x_1030_"))])] [(.goto "v___jp_1023_")]), (.block "v___jp_1023_" [(.decl .u8 "v___x_1024_"), (.assign "v___x_1024_" (.bin .decEq (.var "v_a0_974_") (.var "v___x_1022_"))), (.ifZero "v___x_1024_" [(.decl .u64 "v___x_1025_"), (.decl .u8 "v___x_1026_"), (.assign "v___x_1025_" (.lit 64)), (.assign "v___x_1026_" (.bin .decLe (.var "v___x_1025_") (.var "v_a2_976_"))), (.ifZero "v___x_1026_" [(.ret (.var "v___x_1022_"))] [(.decl .u64 "v___x_1027_"), (.assign "v___x_1027_" (.lit 65282)), (.ret (.var "v___x_1027_"))])] [(.decl .u64 "v___x_1028_"), (.assign "v___x_1028_" (.lit 65285)), (.ret (.var "v___x_1028_"))])])]),
      (.block "v___jp_978_" [(.ifZero "v___y_980_" [(.decl .u8 "v___x_981_"), (.assign "v___x_981_" (.bin .decEq (.var "v_a2_976_") (.var "v___y_979_"))), (.ifZero "v___x_981_" [(.decl .u64 "v___x_982_"), (.assign "v___x_982_" (.lit 65282)), (.ret (.var "v___x_982_"))] [(.decl .u8 "v___x_983_"), (.assign "v___x_983_" (.bin .decEq (.var "v_a3_977_") (.var "v___y_979_"))), (.ifZero "v___x_983_" [(.decl .u64 "v___x_984_"), (.assign "v___x_984_" (.lit 65282)), (.ret (.var "v___x_984_"))] [(.ret (.var "v___y_979_"))])])] [(.decl .u64 "v___x_985_"), (.assign "v___x_985_" (.lit 65282)), (.ret (.var "v___x_985_"))])])] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorWords_decideW
def decideWC : Func :=
  { params := [("v_w0_1045_", .u64), ("v_w1_1046_", .u64), ("v_w2_1047_", .u64), ("v_w3_1048_", .u64), ("v_w4_1049_", .u64), ("v_w5_1050_", .u64), ("v_c0_1051_", .u64), ("v_c1_1052_", .u64), ("v_c2_1053_", .u64), ("v_c3_1054_", .u64), ("v_m2_1055_", .u64), ("v_m3_1056_", .u64), ("v_f_1057_", .u64), ("v_tag_1058_", .u64), ("v_a0_1059_", .u64), ("v_a1_1060_", .u64), ("v_a2_1061_", .u64)]
    result := .u64
    body := [
      (.decl .u8 "v___y_1063_"),
      (.decl .u8 "v___y_1073_"),
      (.decl .u64 "v___y_1083_"),
      (.decl .u8 "v___y_1084_"),
      (.decl .u64 "v___x_1090_"),
      (.decl .u8 "v___x_1091_"),
      (.assign "v___x_1090_" (.lit 28673)),
      (.assign "v___x_1091_" (.bin .decEq (.var "v_tag_1058_") (.var "v___x_1090_"))),
      (.ifZero "v___x_1091_" [(.decl .u64 "v___x_1092_"), (.decl .u8 "v___x_1093_"), (.assign "v___x_1092_" (.lit 28929)), (.assign "v___x_1093_" (.bin .decEq (.var "v_tag_1058_") (.var "v___x_1092_"))), (.ifZero "v___x_1093_" [(.decl .u64 "v___x_1094_"), (.decl .u8 "v___x_1095_"), (.assign "v___x_1094_" (.lit 29185)), (.assign "v___x_1095_" (.bin .decEq (.var "v_tag_1058_") (.var "v___x_1094_"))), (.ifZero "v___x_1095_" [(.decl .u64 "v___x_1096_"), (.decl .u8 "v___x_1097_"), (.assign "v___x_1096_" (.lit 29441)), (.assign "v___x_1097_" (.bin .decEq (.var "v_tag_1058_") (.var "v___x_1096_"))), (.ifZero "v___x_1097_" [(.decl .u64 "v___x_1098_"), (.decl .u8 "v___x_1099_"), (.assign "v___x_1098_" (.lit 29697)), (.assign "v___x_1099_" (.bin .decEq (.var "v_tag_1058_") (.var "v___x_1098_"))), (.ifZero "v___x_1099_" [(.decl .u64 "v___x_1100_"), (.decl .u8 "v___x_1101_"), (.assign "v___x_1100_" (.lit 29953)), (.assign "v___x_1101_" (.bin .decEq (.var "v_tag_1058_") (.var "v___x_1100_"))), (.ifZero "v___x_1101_" [(.decl .u64 "v___x_1102_"), (.assign "v___x_1102_" (.lit 1)), (.ret (.var "v___x_1102_"))] [(.decl .u64 "v___x_1103_"), (.decl .u8 "v___x_1104_"), (.assign "v___x_1103_" (.lit 2)), (.assign "v___x_1104_" (.bin .decEq (.var "v_a0_1059_") (.var "v___x_1103_"))), (.ifZero "v___x_1104_" [(.decl .u64 "v___x_1105_"), (.decl .u8 "v___x_1106_"), (.assign "v___x_1105_" (.lit 1)), (.assign "v___x_1106_" (.bin .decEq (.var "v_a0_1059_") (.var "v___x_1105_"))), (.ifZero "v___x_1106_" [(.decl .u64 "v___x_1107_"), (.assign "v___x_1107_" (.lit 128)), (.ret (.var "v___x_1107_"))] [(.decl .u64 "v___x_1108_"), (.decl .u8 "v___x_1109_"), (.assign "v___x_1108_" (.lit 64)), (.assign "v___x_1109_" (.bin .decLe (.var "v_a1_1060_") (.var "v___x_1108_"))), (.ifZero "v___x_1109_" [(.decl .u64 "v___x_1110_"), (.assign "v___x_1110_" (.lit 128)), (.ret (.var "v___x_1110_"))] [(.decl .u64 "v___x_1111_"), (.assign "v___x_1111_" (.lit 65287)), (.ret (.var "v___x_1111_"))])])] [(.decl .u64 "v___x_1112_"), (.decl .u8 "v___x_1113_"), (.assign "v___x_1112_" (.lit 64)), (.assign "v___x_1113_" (.bin .decLe (.var "v_a1_1060_") (.var "v___x_1112_"))), (.ifZero "v___x_1113_" [(.assign "v___y_1063_" (.var "v___x_1113_")), (.goto "v___jp_1062_")] [(.decl .u64 "v___x_1114_"), (.decl .u8 "v___x_1115_"), (.assign "v___x_1114_" (.call "l_LeanOS_SpawnAllocatorWords_childCountW" ["v_c0_1051_", "v_c1_1052_", "v_c2_1053_", "v_c3_1054_"])), (.assign "v___x_1115_" (.bin .decLe (.var "v___x_1114_") (.var "v_a1_1060_"))), (.assign "v___y_1063_" (.var "v___x_1115_")), (.goto "v___jp_1062_")])])])] [(.decl .u64 "v___x_1116_"), (.decl .u8 "v___x_1117_"), (.assign "v___x_1116_" (.lit 4)), (.assign "v___x_1117_" (.bin .decLe (.var "v___x_1116_") (.var "v_a0_1059_"))), (.ifZero "v___x_1117_" [(.decl .u64 "v___x_1118_"), (.decl .u8 "v___x_1119_"), (.assign "v___x_1118_" (.lit 2)), (.assign "v___x_1119_" (.bin .decLt (.var "v_a0_1059_") (.var "v___x_1118_"))), (.ifZero "v___x_1119_" [(.decl .u64 "v___x_1120_"), (.decl .u64 "v___x_1121_"), (.decl .u8 "v___x_1122_"), (.assign "v___x_1120_" (.call "l_LeanOS_SpawnAllocatorWords_memoryWordAt" ["v_a0_1059_", "v_m2_1055_", "v_m3_1056_"])), (.assign "v___x_1121_" (.lit 0)), (.assign "v___x_1122_" (.bin .decEq (.var "v___x_1120_") (.var "v___x_1121_"))), (.ifZero "v___x_1122_" [(.decl .u64 "v___x_1123_"), (.assign "v___x_1123_" (.lit 1)), (.ret (.var "v___x_1123_"))] [(.decl .u64 "v___x_1124_"), (.assign "v___x_1124_" (.lit 137)), (.ret (.var "v___x_1124_"))])] [(.decl .u64 "v___x_1125_"), (.assign "v___x_1125_" (.lit 138)), (.ret (.var "v___x_1125_"))])] [(.decl .u64 "v___x_1126_"), (.assign "v___x_1126_" (.lit 137)), (.ret (.var "v___x_1126_"))])])] [(.decl .u64 "v___x_1127_"), (.decl .u8 "v___x_1128_"), (.assign "v___x_1127_" (.lit 65535)), (.assign "v___x_1128_" (.bin .decLe (.var "v___x_1127_") (.var "v_a0_1059_"))), (.ifZero "v___x_1128_" [(.decl .u64 "v___x_1129_"), (.decl .u8 "v___x_1130_"), (.assign "v___x_1129_" (.lit 4)), (.assign "v___x_1130_" (.bin .decLe (.var "v___x_1129_") (.var "v_a0_1059_"))), (.ifZero "v___x_1130_" [(.decl .u8 "v___x_1131_"), (.assign "v___x_1131_" (.call "l_LeanOS_SpawnAllocatorWords_capabilityExhaustedW" ["v_w2_1047_"])), (.ifZero "v___x_1131_" [(.decl .u64 "v___x_1132_"), (.decl .u8 "v___x_1133_"), (.assign "v___x_1132_" (.lit 2)), (.assign "v___x_1133_" (.bin .decLt (.var "v_a0_1059_") (.var "v___x_1132_"))), (.ifZero "v___x_1133_" [(.decl .u64 "v___x_1134_"), (.decl .u64 "v___x_1135_"), (.decl .u8 "v___x_1136_"), (.assign "v___x_1134_" (.call "l_LeanOS_SpawnAllocatorWords_memoryWordAt" ["v_a0_1059_", "v_m2_1055_", "v_m3_1056_"])), (.assign "v___x_1135_" (.lit 0)), (.assign "v___x_1136_" (.bin .decEq (.var "v___x_1134_") (.var "v___x_1135_"))), (.ifZero "v___x_1136_" [(.assign "v___y_1073_" (.var "v___x_1097_")), (.goto "v___jp_1072_")] [(.assign "v___y_1073_" (.var "v___x_1133_")), (.goto "v___jp_1072_")])] [(.decl .u64 "v___x_1137_"), (.assign "v___x_1137_" (.lit 132)), (.ret (.var "v___x_1137_"))])] [(.decl .u64 "v___x_1138_"), (.assign "v___x_1138_" (.lit 131)), (.ret (.var "v___x_1138_"))])] [(.decl .u64 "v___x_1139_"), (.assign "v___x_1139_" (.lit 130)), (.ret (.var "v___x_1139_"))])] [(.decl .u64 "v___x_1140_"), (.assign "v___x_1140_" (.lit 130)), (.ret (.var "v___x_1140_"))])])] [(.decl .u64 "v___x_1141_"), (.decl .u8 "v___y_1143_"), (.decl .u64 "v___x_1147_"), (.decl .u8 "v___x_1148_"), (.assign "v___x_1141_" (.call "l_LeanOS_SpawnAllocatorWords_resolveControlW" ["v_c0_1051_", "v_c1_1052_", "v_c2_1053_", "v_c3_1054_", "v_a0_1059_"])), (.assign "v___x_1147_" (.lit 0)), (.assign "v___x_1148_" (.bin .decEq (.var "v___x_1141_") (.var "v___x_1147_"))), (.ifZero "v___x_1148_" [(.assign "v___y_1143_" (.var "v___x_1095_")), (.goto "v___jp_1142_")] [(.assign "v___y_1143_" (.var "v___x_1093_")), (.goto "v___jp_1142_")]), (.block "v___jp_1142_" [(.ifZero "v___y_1143_" [(.decl .u64 "v___x_1144_"), (.assign "v___x_1144_" (.lit 1)), (.ret (.var "v___x_1144_"))] [(.decl .u64 "v___x_1145_"), (.decl .u64 "v___x_1146_"), (.assign "v___x_1145_" (.lit 128)), (.assign "v___x_1146_" (.bin .add (.var "v___x_1145_") (.var "v___x_1141_"))), (.ret (.var "v___x_1146_"))])])])] [(.decl .u64 "v___x_1149_"), (.decl .u8 "v___y_1151_"), (.decl .u64 "v___x_1158_"), (.decl .u8 "v___x_1159_"), (.assign "v___x_1149_" (.call "l_LeanOS_SpawnAllocatorWords_resolveControlW" ["v_c0_1051_", "v_c1_1052_", "v_c2_1053_", "v_c3_1054_", "v_a0_1059_"])), (.assign "v___x_1158_" (.lit 0)), (.assign "v___x_1159_" (.bin .decEq (.var "v___x_1149_") (.var "v___x_1158_"))), (.ifZero "v___x_1159_" [(.assign "v___y_1151_" (.var "v___x_1093_")), (.goto "v___jp_1150_")] [(.assign "v___y_1151_" (.var "v___x_1091_")), (.goto "v___jp_1150_")]), (.block "v___jp_1150_" [(.ifZero "v___y_1151_" [(.decl .u64 "v___x_1152_"), (.decl .u8 "v___x_1153_"), (.assign "v___x_1152_" (.call "l_LeanOS_SpawnAllocatorWords_availableW" ["v_f_1057_", "v_m2_1055_", "v_m3_1056_"])), (.assign "v___x_1153_" (.bin .decLt (.var "v___x_1152_") (.var "v_a1_1060_"))), (.ifZero "v___x_1153_" [(.decl .u64 "v___x_1154_"), (.assign "v___x_1154_" (.lit 1)), (.ret (.var "v___x_1154_"))] [(.decl .u64 "v___x_1155_"), (.assign "v___x_1155_" (.lit 197)), (.ret (.var "v___x_1155_"))])] [(.decl .u64 "v___x_1156_"), (.decl .u64 "v___x_1157_"), (.assign "v___x_1156_" (.lit 128)), (.assign "v___x_1157_" (.bin .add (.var "v___x_1156_") (.var "v___x_1149_"))), (.ret (.var "v___x_1157_"))])])])] [(.decl .u64 "v___x_1160_"), (.decl .u8 "v___y_1162_"), (.decl .u8 "v___y_1173_"), (.decl .u8 "v___x_1184_"), (.assign "v___x_1160_" (.lit 0)), (.assign "v___x_1184_" (.bin .decEq (.var "v_w5_1050_") (.var "v___x_1160_"))), (.ifZero "v___x_1184_" [(.decl .u8 "v___x_1185_"), (.assign "v___x_1185_" (.bin .decEq (.var "v_w5_1050_") (.var "v_a0_1059_"))), (.ifZero "v___x_1185_" [(.assign "v___y_1173_" (.var "v___x_1091_")), (.goto "v___jp_1172_")] [(.assign "v___y_1173_" (.var "v___x_1184_")), (.goto "v___jp_1172_")])] [(.decl .u64 "v___x_1186_"), (.assign "v___x_1186_" (.lit 129)), (.ret (.var "v___x_1186_"))]), (.block "v___jp_1161_" [(.ifZero "v___y_1162_" [(.decl .u8 "v___x_1163_"), (.assign "v___x_1163_" (.call "l_LeanOS_SpawnAllocatorWords_identityExhaustedW" ["v_w0_1045_"])), (.ifZero "v___x_1163_" [(.decl .u8 "v___x_1164_"), (.assign "v___x_1164_" (.call "l_LeanOS_SpawnAllocatorWords_identityExhaustedW" ["v_w1_1046_"])), (.ifZero "v___x_1164_" [(.decl .u8 "v___x_1165_"), (.assign "v___x_1165_" (.call "l_LeanOS_SpawnAllocatorWords_capabilityExhaustedW" ["v_w2_1047_"])), (.ifZero "v___x_1165_" [(.decl .u64 "v___x_1166_"), (.decl .u8 "v___x_1167_"), (.assign "v___x_1166_" (.call "l_LeanOS_SpawnAllocatorWords_resolveEndpointW" ["v_m2_1055_", "v_m3_1056_", "v_a1_1060_"])), (.assign "v___x_1167_" (.bin .decEq (.var "v___x_1166_") (.var "v___x_1160_"))), (.ifZero "v___x_1167_" [(.assign "v___y_1083_" (.var "v___x_1166_")), (.assign "v___y_1084_" (.var "v___x_1091_")), (.goto "v___jp_1082_")] [(.assign "v___y_1083_" (.var "v___x_1166_")), (.assign "v___y_1084_" (.var "v___x_1165_")), (.goto "v___jp_1082_")])] [(.decl .u64 "v___x_1168_"), (.assign "v___x_1168_" (.lit 146)), (.ret (.var "v___x_1168_"))])] [(.decl .u64 "v___x_1169_"), (.assign "v___x_1169_" (.lit 135)), (.ret (.var "v___x_1169_"))])] [(.decl .u64 "v___x_1170_"), (.assign "v___x_1170_" (.lit 131)), (.ret (.var "v___x_1170_"))])] [(.decl .u64 "v___x_1171_"), (.assign "v___x_1171_" (.lit 141)), (.ret (.var "v___x_1171_"))])]), (.block "v___jp_1172_" [(.ifZero "v___y_1173_" [(.decl .u64 "v___x_1174_"), (.decl .u64 "v___x_1175_"), (.decl .u8 "v___x_1176_"), (.assign "v___x_1174_" (.call "l_LeanOS_SpawnAllocatorWords_budgetW" ["v_f_1057_"])), (.assign "v___x_1175_" (.call "l_LeanOS_SpawnAllocatorWords_childCountW" ["v_c0_1051_", "v_c1_1052_", "v_c2_1053_", "v_c3_1054_"])), (.assign "v___x_1176_" (.bin .decLe (.var "v___x_1174_") (.var "v___x_1175_"))), (.ifZero "v___x_1176_" [(.decl .u64 "v___x_1177_"), (.decl .u64 "v___x_1178_"), (.decl .u8 "v___x_1179_"), (.assign "v___x_1177_" (.call "l_LeanOS_SpawnAllocatorWords_freeSlotW" ["v_c0_1051_", "v_c1_1052_", "v_c2_1053_", "v_c3_1054_"])), (.assign "v___x_1178_" (.lit 4)), (.assign "v___x_1179_" (.bin .decEq (.var "v___x_1177_") (.var "v___x_1178_"))), (.ifZero "v___x_1179_" [(.decl .u8 "v___x_1180_"), (.assign "v___x_1180_" (.call "l_LeanOS_SpawnAllocatorWords_controlAvailableW" ["v_w3_1048_"])), (.ifZero "v___x_1180_" [(.assign "v___y_1162_" (.var "v___x_1091_")), (.goto "v___jp_1161_")] [(.assign "v___y_1162_" (.var "v___x_1179_")), (.goto "v___jp_1161_")])] [(.decl .u64 "v___x_1181_"), (.assign "v___x_1181_" (.lit 140)), (.ret (.var "v___x_1181_"))])] [(.decl .u64 "v___x_1182_"), (.assign "v___x_1182_" (.lit 140)), (.ret (.var "v___x_1182_"))])] [(.decl .u64 "v___x_1183_"), (.assign "v___x_1183_" (.lit 130)), (.ret (.var "v___x_1183_"))])])]),
      (.block "v___jp_1062_" [(.ifZero "v___y_1063_" [(.decl .u64 "v___x_1064_"), (.assign "v___x_1064_" (.lit 128)), (.ret (.var "v___x_1064_"))] [(.decl .u64 "v___x_1065_"), (.decl .u8 "v___x_1066_"), (.assign "v___x_1065_" (.lit 4)), (.assign "v___x_1066_" (.bin .decLt (.var "v___x_1065_") (.var "v_a1_1060_"))), (.ifZero "v___x_1066_" [(.decl .u64 "v___x_1067_"), (.decl .u8 "v___x_1068_"), (.assign "v___x_1067_" (.lit 18446744073709551615)), (.assign "v___x_1068_" (.bin .decEq (.var "v_w4_1049_") (.var "v___x_1067_"))), (.ifZero "v___x_1068_" [(.decl .u64 "v___x_1069_"), (.assign "v___x_1069_" (.lit 1)), (.ret (.var "v___x_1069_"))] [(.decl .u64 "v___x_1070_"), (.assign "v___x_1070_" (.lit 65287)), (.ret (.var "v___x_1070_"))])] [(.decl .u64 "v___x_1071_"), (.assign "v___x_1071_" (.lit 65287)), (.ret (.var "v___x_1071_"))])])]),
      (.block "v___jp_1072_" [(.ifZero "v___y_1073_" [(.decl .u8 "v___x_1074_"), (.assign "v___x_1074_" (.call "l_LeanOS_SpawnAllocatorWords_identityExhaustedW" ["v_w1_1046_"])), (.ifZero "v___x_1074_" [(.decl .u64 "v___x_1075_"), (.decl .u64 "v___x_1076_"), (.decl .u8 "v___x_1077_"), (.assign "v___x_1075_" (.call "l_LeanOS_SpawnAllocatorWords_availableW" ["v_f_1057_", "v_m2_1055_", "v_m3_1056_"])), (.assign "v___x_1076_" (.lit 0)), (.assign "v___x_1077_" (.bin .decEq (.var "v___x_1075_") (.var "v___x_1076_"))), (.ifZero "v___x_1077_" [(.decl .u64 "v___x_1078_"), (.assign "v___x_1078_" (.lit 1)), (.ret (.var "v___x_1078_"))] [(.decl .u64 "v___x_1079_"), (.assign "v___x_1079_" (.lit 135)), (.ret (.var "v___x_1079_"))])] [(.decl .u64 "v___x_1080_"), (.assign "v___x_1080_" (.lit 133)), (.ret (.var "v___x_1080_"))])] [(.decl .u64 "v___x_1081_"), (.assign "v___x_1081_" (.lit 132)), (.ret (.var "v___x_1081_"))])]),
      (.block "v___jp_1082_" [(.ifZero "v___y_1084_" [(.decl .u8 "v___x_1085_"), (.assign "v___x_1085_" (.call "l_LeanOS_SpawnAllocatorWords_rightsValidW" ["v_a2_1061_"])), (.ifZero "v___x_1085_" [(.decl .u64 "v___x_1086_"), (.assign "v___x_1086_" (.lit 138)), (.ret (.var "v___x_1086_"))] [(.decl .u64 "v___x_1087_"), (.assign "v___x_1087_" (.lit 1)), (.ret (.var "v___x_1087_"))])] [(.decl .u64 "v___x_1088_"), (.decl .u64 "v___x_1089_"), (.assign "v___x_1088_" (.lit 128)), (.assign "v___x_1089_" (.bin .add (.var "v___x_1088_") (.var "v___y_1083_"))), (.ret (.var "v___x_1089_"))])])] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorWords_stepReply
def stepReplyC : Func :=
  { params := [("v_w0_1223_", .u64), ("v_w1_1224_", .u64), ("v_w2_1225_", .u64), ("v_w3_1226_", .u64), ("v_w4_1227_", .u64), ("v_w5_1228_", .u64), ("v_c0_1229_", .u64), ("v_c1_1230_", .u64), ("v_c2_1231_", .u64), ("v_c3_1232_", .u64), ("v_m2_1233_", .u64), ("v_m3_1234_", .u64), ("v_f_1235_", .u64), ("v_tag_1236_", .u64), ("v_a0_1237_", .u64), ("v_a1_1238_", .u64), ("v_a2_1239_", .u64), ("v_a3_1240_", .u64)]
    result := .u64
    body := [
      (.decl .u8 "v___x_1241_"),
      (.assign "v___x_1241_" (.call "l_LeanOS_SpawnAllocatorWords_canonical" ["v_w4_1227_", "v_c0_1229_", "v_c1_1230_", "v_c2_1231_", "v_c3_1232_", "v_f_1235_"])),
      (.ifZero "v___x_1241_" [(.decl .u64 "v___x_1242_"), (.assign "v___x_1242_" (.lit 65283)), (.ret (.var "v___x_1242_"))] [(.decl .u64 "v___x_1243_"), (.decl .u64 "v___x_1244_"), (.decl .u8 "v___x_1245_"), (.assign "v___x_1243_" (.call "l_LeanOS_SpawnAllocatorWords_commandErrorW" ["v_tag_1236_", "v_a0_1237_", "v_a1_1238_", "v_a2_1239_", "v_a3_1240_"])), (.assign "v___x_1244_" (.lit 0)), (.assign "v___x_1245_" (.bin .decEq (.var "v___x_1243_") (.var "v___x_1244_"))), (.ifZero "v___x_1245_" [(.ret (.var "v___x_1243_"))] [(.decl .u64 "v___x_1246_"), (.assign "v___x_1246_" (.call "l_LeanOS_SpawnAllocatorWords_decideW" ["v_w0_1223_", "v_w1_1224_", "v_w2_1225_", "v_w3_1226_", "v_w4_1227_", "v_w5_1228_", "v_c0_1229_", "v_c1_1230_", "v_c2_1231_", "v_c3_1232_", "v_m2_1233_", "v_m3_1234_", "v_f_1235_", "v_tag_1236_", "v_a0_1237_", "v_a1_1238_", "v_a2_1239_"])), (.ret (.var "v___x_1246_"))])])] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorWords_stepValue
def stepValueC : Func :=
  { params := [("v_w0_1285_", .u64), ("v_w1_1286_", .u64), ("v_w2_1287_", .u64), ("v_w3_1288_", .u64), ("v_w4_1289_", .u64), ("v_w5_1290_", .u64), ("v_c0_1291_", .u64), ("v_c1_1292_", .u64), ("v_c2_1293_", .u64), ("v_c3_1294_", .u64), ("v_m2_1295_", .u64), ("v_m3_1296_", .u64), ("v_f_1297_", .u64), ("v_tag_1298_", .u64), ("v_a0_1299_", .u64), ("v_a1_1300_", .u64), ("v_a2_1301_", .u64), ("v_a3_1302_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___x_1303_"),
      (.decl .u64 "v___x_1304_"),
      (.decl .u8 "v___x_1305_"),
      (.assign "v___x_1303_" (.call "l_LeanOS_SpawnAllocatorWords_stepReply" ["v_w0_1285_", "v_w1_1286_", "v_w2_1287_", "v_w3_1288_", "v_w4_1289_", "v_w5_1290_", "v_c0_1291_", "v_c1_1292_", "v_c2_1293_", "v_c3_1294_", "v_m2_1295_", "v_m3_1296_", "v_f_1297_", "v_tag_1298_", "v_a0_1299_", "v_a1_1300_", "v_a2_1301_", "v_a3_1302_"])),
      (.assign "v___x_1304_" (.lit 1)),
      (.assign "v___x_1305_" (.bin .decEq (.var "v___x_1303_") (.var "v___x_1304_"))),
      (.ifZero "v___x_1305_" [(.decl .u64 "v___x_1306_"), (.assign "v___x_1306_" (.lit 0)), (.ret (.var "v___x_1306_"))] [(.decl .u64 "v___x_1307_"), (.decl .u8 "v___x_1308_"), (.assign "v___x_1307_" (.lit 28673)), (.assign "v___x_1308_" (.bin .decEq (.var "v_tag_1298_") (.var "v___x_1307_"))), (.ifZero "v___x_1308_" [(.decl .u64 "v___x_1309_"), (.decl .u8 "v___x_1310_"), (.assign "v___x_1309_" (.lit 28929)), (.assign "v___x_1310_" (.bin .decEq (.var "v_tag_1298_") (.var "v___x_1309_"))), (.ifZero "v___x_1310_" [(.decl .u64 "v___x_1311_"), (.decl .u8 "v___x_1312_"), (.assign "v___x_1311_" (.lit 29185)), (.assign "v___x_1312_" (.bin .decEq (.var "v_tag_1298_") (.var "v___x_1311_"))), (.ifZero "v___x_1312_" [(.decl .u64 "v___x_1313_"), (.decl .u8 "v___x_1314_"), (.assign "v___x_1313_" (.lit 29953)), (.assign "v___x_1314_" (.bin .decEq (.var "v_tag_1298_") (.var "v___x_1313_"))), (.ifZero "v___x_1314_" [(.decl .u64 "v___x_1315_"), (.assign "v___x_1315_" (.lit 0)), (.ret (.var "v___x_1315_"))] [(.ret (.var "v_w4_1289_"))])] [(.decl .u64 "v___x_1316_"), (.decl .u64 "v___x_1317_"), (.decl .u64 "v___x_1318_"), (.decl .u64 "v___x_1319_"), (.assign "v___x_1316_" (.lit 65535)), (.assign "v___x_1317_" (.bin .land (.var "v_a0_1299_") (.var "v___x_1316_"))), (.assign "v___x_1318_" (.call "l_LeanOS_SpawnAllocatorWords_childWordAt" ["v___x_1317_", "v_c0_1291_", "v_c1_1292_", "v_c2_1293_", "v_c3_1294_"])), (.assign "v___x_1319_" (.call "l_LeanOS_SpawnAllocatorWords_chargeOf" ["v___x_1318_"])), (.ret (.var "v___x_1319_"))])] [(.ret (.var "v_a1_1300_"))])] [(.decl .u64 "v___x_1320_"), (.decl .u64 "v___x_1321_"), (.decl .u64 "v___x_1322_"), (.decl .u64 "v___x_1323_"), (.assign "v___x_1320_" (.call "l_LeanOS_SpawnAllocatorWords_freeSlotW" ["v_c0_1291_", "v_c1_1292_", "v_c2_1293_", "v_c3_1294_"])), (.assign "v___x_1321_" (.lit 16)), (.assign "v___x_1322_" (.bin .shiftLeft (.var "v_w3_1288_") (.var "v___x_1321_"))), (.assign "v___x_1323_" (.bin .add (.var "v___x_1320_") (.var "v___x_1322_"))), (.ret (.var "v___x_1323_"))])])] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorWords_nextChild
def nextChildC : Func :=
  { params := [("v_index_1362_", .u64), ("v_w3_1363_", .u64), ("v_c0_1364_", .u64), ("v_c1_1365_", .u64), ("v_c2_1366_", .u64), ("v_c3_1367_", .u64), ("v_tag_1368_", .u64), ("v_a0_1369_", .u64), ("v_a1_1370_", .u64), ("v_current_1371_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___x_1372_"),
      (.decl .u8 "v___x_1373_"),
      (.assign "v___x_1372_" (.lit 28673)),
      (.assign "v___x_1373_" (.bin .decEq (.var "v_tag_1368_") (.var "v___x_1372_"))),
      (.ifZero "v___x_1373_" [(.decl .u64 "v___x_1374_"), (.decl .u8 "v___x_1375_"), (.assign "v___x_1374_" (.lit 28929)), (.assign "v___x_1375_" (.bin .decEq (.var "v_tag_1368_") (.var "v___x_1374_"))), (.ifZero "v___x_1375_" [(.decl .u64 "v___x_1376_"), (.decl .u8 "v___x_1377_"), (.assign "v___x_1376_" (.lit 29185)), (.assign "v___x_1377_" (.bin .decEq (.var "v_tag_1368_") (.var "v___x_1376_"))), (.ifZero "v___x_1377_" [(.ret (.var "v_current_1371_"))] [(.decl .u64 "v___x_1378_"), (.decl .u64 "v___x_1379_"), (.decl .u8 "v___x_1380_"), (.assign "v___x_1378_" (.lit 65535)), (.assign "v___x_1379_" (.bin .land (.var "v_a0_1369_") (.var "v___x_1378_"))), (.assign "v___x_1380_" (.bin .decEq (.var "v___x_1379_") (.var "v_index_1362_"))), (.ifZero "v___x_1380_" [(.ret (.var "v_current_1371_"))] [(.decl .u64 "v___x_1381_"), (.assign "v___x_1381_" (.lit 0)), (.ret (.var "v___x_1381_"))])])] [(.decl .u64 "v___x_1382_"), (.decl .u64 "v___x_1383_"), (.decl .u8 "v___x_1384_"), (.assign "v___x_1382_" (.lit 65535)), (.assign "v___x_1383_" (.bin .land (.var "v_a0_1369_") (.var "v___x_1382_"))), (.assign "v___x_1384_" (.bin .decEq (.var "v___x_1383_") (.var "v_index_1362_"))), (.ifZero "v___x_1384_" [(.ret (.var "v_current_1371_"))] [(.decl .u64 "v___x_1385_"), (.assign "v___x_1385_" (.bin .add (.var "v_current_1371_") (.var "v_a1_1370_"))), (.ret (.var "v___x_1385_"))])])] [(.decl .u64 "v___x_1386_"), (.decl .u8 "v___x_1387_"), (.assign "v___x_1386_" (.call "l_LeanOS_SpawnAllocatorWords_freeSlotW" ["v_c0_1364_", "v_c1_1365_", "v_c2_1366_", "v_c3_1367_"])), (.assign "v___x_1387_" (.bin .decEq (.var "v___x_1386_") (.var "v_index_1362_"))), (.ifZero "v___x_1387_" [(.ret (.var "v_current_1371_"))] [(.decl .u64 "v___x_1388_"), (.decl .u64 "v___x_1389_"), (.assign "v___x_1388_" (.lit 16)), (.assign "v___x_1389_" (.bin .shiftLeft (.var "v_w3_1363_") (.var "v___x_1388_"))), (.ret (.var "v___x_1389_"))])])] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorWords_nextMemory
def nextMemoryC : Func :=
  { params := [("v_slot_1412_", .u64), ("v_w2_1413_", .u64), ("v_tag_1414_", .u64), ("v_a0_1415_", .u64), ("v_current_1416_", .u64)]
    result := .u64
    body := [
      (.decl .u8 "v___y_1418_"),
      (.decl .u8 "v___y_1421_"),
      (.decl .u64 "v___x_1425_"),
      (.decl .u8 "v___x_1426_"),
      (.assign "v___x_1425_" (.lit 29441)),
      (.assign "v___x_1426_" (.bin .decEq (.var "v_tag_1414_") (.var "v___x_1425_"))),
      (.ifZero "v___x_1426_" [(.assign "v___y_1421_" (.var "v___x_1426_")), (.goto "v___jp_1420_")] [(.decl .u8 "v___x_1427_"), (.assign "v___x_1427_" (.bin .decEq (.var "v_a0_1415_") (.var "v_slot_1412_"))), (.assign "v___y_1421_" (.var "v___x_1427_")), (.goto "v___jp_1420_")]),
      (.block "v___jp_1417_" [(.ifZero "v___y_1418_" [(.ret (.var "v_current_1416_"))] [(.decl .u64 "v___x_1419_"), (.assign "v___x_1419_" (.lit 0)), (.ret (.var "v___x_1419_"))])]),
      (.block "v___jp_1420_" [(.ifZero "v___y_1421_" [(.decl .u64 "v___x_1422_"), (.decl .u8 "v___x_1423_"), (.assign "v___x_1422_" (.lit 29697)), (.assign "v___x_1423_" (.bin .decEq (.var "v_tag_1414_") (.var "v___x_1422_"))), (.ifZero "v___x_1423_" [(.assign "v___y_1418_" (.var "v___x_1423_")), (.goto "v___jp_1417_")] [(.decl .u8 "v___x_1424_"), (.assign "v___x_1424_" (.bin .decEq (.var "v_a0_1415_") (.var "v_slot_1412_"))), (.assign "v___y_1418_" (.var "v___x_1424_")), (.goto "v___jp_1417_")])] [(.ret (.var "v_w2_1413_"))])])] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorWords_nextFrames
def nextFramesC : Func :=
  { params := [("v_c0_1440_", .u64), ("v_c1_1441_", .u64), ("v_c2_1442_", .u64), ("v_c3_1443_", .u64), ("v_f_1444_", .u64), ("v_tag_1445_", .u64), ("v_a0_1446_", .u64), ("v_a1_1447_", .u64)]
    result := .u64
    body := [
      (.decl .u8 "v___y_1449_"),
      (.decl .u64 "v___x_1453_"),
      (.decl .u8 "v___x_1454_"),
      (.assign "v___x_1453_" (.lit 28929)),
      (.assign "v___x_1454_" (.bin .decEq (.var "v_tag_1445_") (.var "v___x_1453_"))),
      (.ifZero "v___x_1454_" [(.decl .u64 "v___x_1455_"), (.decl .u8 "v___x_1456_"), (.assign "v___x_1455_" (.lit 29185)), (.assign "v___x_1456_" (.bin .decEq (.var "v_tag_1445_") (.var "v___x_1455_"))), (.ifZero "v___x_1456_" [(.decl .u64 "v___x_1457_"), (.decl .u8 "v___x_1458_"), (.assign "v___x_1457_" (.lit 29953)), (.assign "v___x_1458_" (.bin .decEq (.var "v_tag_1445_") (.var "v___x_1457_"))), (.ifZero "v___x_1458_" [(.decl .u64 "v___x_1459_"), (.decl .u8 "v___x_1460_"), (.assign "v___x_1459_" (.lit 30209)), (.assign "v___x_1460_" (.bin .decEq (.var "v_tag_1445_") (.var "v___x_1459_"))), (.ifZero "v___x_1460_" [(.assign "v___y_1449_" (.var "v___x_1460_")), (.goto "v___jp_1448_")] [(.decl .u64 "v___x_1461_"), (.decl .u8 "v___x_1462_"), (.assign "v___x_1461_" (.lit 2)), (.assign "v___x_1462_" (.bin .decEq (.var "v_a0_1446_") (.var "v___x_1461_"))), (.assign "v___y_1449_" (.var "v___x_1462_")), (.goto "v___jp_1448_")])] [(.decl .u64 "v___x_1463_"), (.decl .u64 "v___x_1464_"), (.decl .u64 "v___x_1465_"), (.decl .u64 "v___x_1466_"), (.assign "v___x_1463_" (.call "l_LeanOS_SpawnAllocatorWords_parentFramesW" ["v_f_1444_"])), (.assign "v___x_1464_" (.lit 16)), (.assign "v___x_1465_" (.bin .shiftLeft (.var "v___x_1463_") (.var "v___x_1464_"))), (.assign "v___x_1466_" (.bin .add (.var "v_a1_1447_") (.var "v___x_1465_"))), (.ret (.var "v___x_1466_"))])] [(.decl .u64 "v___x_1467_"), (.decl .u64 "v___x_1468_"), (.decl .u64 "v___x_1469_"), (.decl .u64 "v___x_1470_"), (.decl .u64 "v___x_1471_"), (.decl .u64 "v___x_1472_"), (.decl .u64 "v___x_1473_"), (.decl .u64 "v___x_1474_"), (.decl .u64 "v___x_1475_"), (.decl .u64 "v___x_1476_"), (.assign "v___x_1467_" (.call "l_LeanOS_SpawnAllocatorWords_budgetW" ["v_f_1444_"])), (.assign "v___x_1468_" (.call "l_LeanOS_SpawnAllocatorWords_parentFramesW" ["v_f_1444_"])), (.assign "v___x_1469_" (.lit 65535)), (.assign "v___x_1470_" (.bin .land (.var "v_a0_1446_") (.var "v___x_1469_"))), (.assign "v___x_1471_" (.call "l_LeanOS_SpawnAllocatorWords_childWordAt" ["v___x_1470_", "v_c0_1440_", "v_c1_1441_", "v_c2_1442_", "v_c3_1443_"])), (.assign "v___x_1472_" (.call "l_LeanOS_SpawnAllocatorWords_chargeOf" ["v___x_1471_"])), (.assign "v___x_1473_" (.bin .add (.var "v___x_1468_") (.var "v___x_1472_"))), (.assign "v___x_1474_" (.lit 16)), (.assign "v___x_1475_" (.bin .shiftLeft (.var "v___x_1473_") (.var "v___x_1474_"))), (.assign "v___x_1476_" (.bin .add (.var "v___x_1467_") (.var "v___x_1475_"))), (.ret (.var "v___x_1476_"))])] [(.decl .u64 "v___x_1477_"), (.decl .u64 "v___x_1478_"), (.decl .u64 "v___x_1479_"), (.decl .u64 "v___x_1480_"), (.decl .u64 "v___x_1481_"), (.decl .u64 "v___x_1482_"), (.assign "v___x_1477_" (.call "l_LeanOS_SpawnAllocatorWords_budgetW" ["v_f_1444_"])), (.assign "v___x_1478_" (.call "l_LeanOS_SpawnAllocatorWords_parentFramesW" ["v_f_1444_"])), (.assign "v___x_1479_" (.bin .sub (.var "v___x_1478_") (.var "v_a1_1447_"))), (.assign "v___x_1480_" (.lit 16)), (.assign "v___x_1481_" (.bin .shiftLeft (.var "v___x_1479_") (.var "v___x_1480_"))), (.assign "v___x_1482_" (.bin .add (.var "v___x_1477_") (.var "v___x_1481_"))), (.ret (.var "v___x_1482_"))]),
      (.block "v___jp_1448_" [(.ifZero "v___y_1449_" [(.ret (.var "v_f_1444_"))] [(.decl .u64 "v___x_1450_"), (.decl .u64 "v___x_1451_"), (.decl .u64 "v___x_1452_"), (.assign "v___x_1450_" (.call "l_LeanOS_SpawnAllocatorWords_parentFramesW" ["v_f_1444_"])), (.assign "v___x_1451_" (.lit 16)), (.assign "v___x_1452_" (.bin .shiftLeft (.var "v___x_1450_") (.var "v___x_1451_"))), (.ret (.var "v___x_1452_"))])])] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorWords_stepNextWord
def stepNextWordC : Func :=
  { params := [("v_index_1501_", .u64), ("v_w0_1502_", .u64), ("v_w1_1503_", .u64), ("v_w2_1504_", .u64), ("v_w3_1505_", .u64), ("v_w4_1506_", .u64), ("v_w5_1507_", .u64), ("v_c0_1508_", .u64), ("v_c1_1509_", .u64), ("v_c2_1510_", .u64), ("v_c3_1511_", .u64), ("v_m2_1512_", .u64), ("v_m3_1513_", .u64), ("v_f_1514_", .u64), ("v_tag_1515_", .u64), ("v_a0_1516_", .u64), ("v_a1_1517_", .u64), ("v_a2_1518_", .u64), ("v_a3_1519_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___x_1520_"),
      (.decl .u64 "v___x_1521_"),
      (.decl .u8 "v___y_1523_"),
      (.decl .u8 "v___y_1526_"),
      (.decl .u8 "v___y_1529_"),
      (.decl .u8 "v___y_1532_"),
      (.decl .u8 "v___y_1535_"),
      (.decl .u8 "v_accepted_1537_"),
      (.decl .u64 "v___x_1538_"),
      (.decl .u8 "v___x_1539_"),
      (.assign "v___x_1520_" (.call "l_LeanOS_SpawnAllocatorWords_stepReply" ["v_w0_1502_", "v_w1_1503_", "v_w2_1504_", "v_w3_1505_", "v_w4_1506_", "v_w5_1507_", "v_c0_1508_", "v_c1_1509_", "v_c2_1510_", "v_c3_1511_", "v_m2_1512_", "v_m3_1513_", "v_f_1514_", "v_tag_1515_", "v_a0_1516_", "v_a1_1517_", "v_a2_1518_", "v_a3_1519_"])),
      (.assign "v___x_1521_" (.lit 1)),
      (.assign "v_accepted_1537_" (.bin .decEq (.var "v___x_1520_") (.var "v___x_1521_"))),
      (.assign "v___x_1538_" (.lit 0)),
      (.assign "v___x_1539_" (.bin .decEq (.var "v_index_1501_") (.var "v___x_1538_"))),
      (.ifZero "v___x_1539_" [(.decl .u8 "v___x_1540_"), (.assign "v___x_1540_" (.bin .decEq (.var "v_index_1501_") (.var "v___x_1521_"))), (.ifZero "v___x_1540_" [(.decl .u64 "v___x_1541_"), (.decl .u8 "v___y_1543_"), (.decl .u8 "v___y_1548_"), (.decl .u8 "v___y_1551_"), (.decl .u8 "v___x_1554_"), (.assign "v___x_1541_" (.lit 2)), (.assign "v___x_1554_" (.bin .decEq (.var "v_index_1501_") (.var "v___x_1541_"))), (.ifZero "v___x_1554_" [(.decl .u64 "v___x_1555_"), (.decl .u8 "v___x_1556_"), (.assign "v___x_1555_" (.lit 3)), (.assign "v___x_1556_" (.bin .decEq (.var "v_index_1501_") (.var "v___x_1555_"))), (.ifZero "v___x_1556_" [(.decl .u64 "v___x_1557_"), (.decl .u8 "v___x_1558_"), (.assign "v___x_1557_" (.lit 4)), (.assign "v___x_1558_" (.bin .decEq (.var "v_index_1501_") (.var "v___x_1557_"))), (.ifZero "v___x_1558_" [(.decl .u64 "v___x_1559_"), (.decl .u8 "v___x_1560_"), (.assign "v___x_1559_" (.lit 5)), (.assign "v___x_1560_" (.bin .decEq (.var "v_index_1501_") (.var "v___x_1559_"))), (.ifZero "v___x_1560_" [(.decl .u64 "v___x_1561_"), (.decl .u8 "v___x_1562_"), (.assign "v___x_1561_" (.lit 6)), (.assign "v___x_1562_" (.bin .decEq (.var "v_index_1501_") (.var "v___x_1561_"))), (.ifZero "v___x_1562_" [(.decl .u64 "v___x_1563_"), (.decl .u8 "v___x_1564_"), (.assign "v___x_1563_" (.lit 7)), (.assign "v___x_1564_" (.bin .decEq (.var "v_index_1501_") (.var "v___x_1563_"))), (.ifZero "v___x_1564_" [(.decl .u64 "v___x_1565_"), (.decl .u8 "v___x_1566_"), (.assign "v___x_1565_" (.lit 8)), (.assign "v___x_1566_" (.bin .decEq (.var "v_index_1501_") (.var "v___x_1565_"))), (.ifZero "v___x_1566_" [(.decl .u64 "v___x_1567_"), (.decl .u8 "v___x_1568_"), (.assign "v___x_1567_" (.lit 9)), (.assign "v___x_1568_" (.bin .decEq (.var "v_index_1501_") (.var "v___x_1567_"))), (.ifZero "v___x_1568_" [(.decl .u64 "v___x_1569_"), (.decl .u8 "v___x_1570_"), (.assign "v___x_1569_" (.lit 10)), (.assign "v___x_1570_" (.bin .decEq (.var "v_index_1501_") (.var "v___x_1569_"))), (.ifZero "v___x_1570_" [(.decl .u64 "v___x_1571_"), (.decl .u8 "v___x_1572_"), (.assign "v___x_1571_" (.lit 11)), (.assign "v___x_1572_" (.bin .decEq (.var "v_index_1501_") (.var "v___x_1571_"))), (.ifZero "v___x_1572_" [(.decl .u64 "v___x_1573_"), (.decl .u8 "v___x_1574_"), (.assign "v___x_1573_" (.lit 12)), (.assign "v___x_1574_" (.bin .decEq (.var "v_index_1501_") (.var "v___x_1573_"))), (.ifZero "v___x_1574_" [(.ret (.var "v___x_1538_"))] [(.ifZero "v_accepted_1537_" [(.ret (.var "v_f_1514_"))] [(.decl .u64 "v___x_1575_"), (.assign "v___x_1575_" (.call "l_LeanOS_SpawnAllocatorWords_nextFrames" ["v_c0_1508_", "v_c1_1509_", "v_c2_1510_", "v_c3_1511_", "v_f_1514_", "v_tag_1515_", "v_a0_1516_", "v_a1_1517_"])), (.ret (.var "v___x_1575_"))])])] [(.ifZero "v_accepted_1537_" [(.ret (.var "v_m3_1513_"))] [(.decl .u64 "v___x_1576_"), (.assign "v___x_1576_" (.call "l_LeanOS_SpawnAllocatorWords_nextMemory" ["v___x_1555_", "v_w2_1504_", "v_tag_1515_", "v_a0_1516_", "v_m3_1513_"])), (.ret (.var "v___x_1576_"))])])] [(.ifZero "v_accepted_1537_" [(.ret (.var "v_m2_1512_"))] [(.decl .u64 "v___x_1577_"), (.assign "v___x_1577_" (.call "l_LeanOS_SpawnAllocatorWords_nextMemory" ["v___x_1541_", "v_w2_1504_", "v_tag_1515_", "v_a0_1516_", "v_m2_1512_"])), (.ret (.var "v___x_1577_"))])])] [(.ifZero "v_accepted_1537_" [(.ret (.var "v_c3_1511_"))] [(.decl .u64 "v___x_1578_"), (.assign "v___x_1578_" (.call "l_LeanOS_SpawnAllocatorWords_nextChild" ["v___x_1555_", "v_w3_1505_", "v_c0_1508_", "v_c1_1509_", "v_c2_1510_", "v_c3_1511_", "v_tag_1515_", "v_a0_1516_", "v_a1_1517_", "v_c3_1511_"])), (.ret (.var "v___x_1578_"))])])] [(.ifZero "v_accepted_1537_" [(.ret (.var "v_c2_1510_"))] [(.decl .u64 "v___x_1579_"), (.assign "v___x_1579_" (.call "l_LeanOS_SpawnAllocatorWords_nextChild" ["v___x_1541_", "v_w3_1505_", "v_c0_1508_", "v_c1_1509_", "v_c2_1510_", "v_c3_1511_", "v_tag_1515_", "v_a0_1516_", "v_a1_1517_", "v_c2_1510_"])), (.ret (.var "v___x_1579_"))])])] [(.ifZero "v_accepted_1537_" [(.ret (.var "v_c1_1509_"))] [(.decl .u64 "v___x_1580_"), (.assign "v___x_1580_" (.call "l_LeanOS_SpawnAllocatorWords_nextChild" ["v___x_1521_", "v_w3_1505_", "v_c0_1508_", "v_c1_1509_", "v_c2_1510_", "v_c3_1511_", "v_tag_1515_", "v_a0_1516_", "v_a1_1517_", "v_c1_1509_"])), (.ret (.var "v___x_1580_"))])])] [(.ifZero "v_accepted_1537_" [(.ret (.var "v_c0_1508_"))] [(.decl .u64 "v___x_1581_"), (.assign "v___x_1581_" (.call "l_LeanOS_SpawnAllocatorWords_nextChild" ["v___x_1538_", "v_w3_1505_", "v_c0_1508_", "v_c1_1509_", "v_c2_1510_", "v_c3_1511_", "v_tag_1515_", "v_a0_1516_", "v_a1_1517_", "v_c0_1508_"])), (.ret (.var "v___x_1581_"))])])] [(.ifZero "v_accepted_1537_" [(.assign "v___y_1551_" (.var "v_accepted_1537_")), (.goto "v___jp_1550_")] [(.decl .u64 "v___x_1582_"), (.decl .u8 "v___x_1583_"), (.assign "v___x_1582_" (.lit 29953)), (.assign "v___x_1583_" (.bin .decEq (.var "v_tag_1515_") (.var "v___x_1582_"))), (.assign "v___y_1551_" (.var "v___x_1583_")), (.goto "v___jp_1550_")])])] [(.ifZero "v_accepted_1537_" [(.assign "v___y_1535_" (.var "v_accepted_1537_")), (.goto "v___jp_1534_")] [(.decl .u64 "v___x_1584_"), (.decl .u8 "v___x_1585_"), (.assign "v___x_1584_" (.lit 29953)), (.assign "v___x_1585_" (.bin .decEq (.var "v_tag_1515_") (.var "v___x_1584_"))), (.assign "v___y_1535_" (.var "v___x_1585_")), (.goto "v___jp_1534_")])])] [(.ifZero "v_accepted_1537_" [(.assign "v___y_1532_" (.var "v_accepted_1537_")), (.goto "v___jp_1531_")] [(.decl .u64 "v___x_1586_"), (.decl .u8 "v___x_1587_"), (.assign "v___x_1586_" (.lit 28673)), (.assign "v___x_1587_" (.bin .decEq (.var "v_tag_1515_") (.var "v___x_1586_"))), (.assign "v___y_1532_" (.var "v___x_1587_")), (.goto "v___jp_1531_")])])] [(.ifZero "v_accepted_1537_" [(.assign "v___y_1543_" (.var "v_accepted_1537_")), (.goto "v___jp_1542_")] [(.decl .u64 "v___x_1588_"), (.decl .u8 "v___x_1589_"), (.assign "v___x_1588_" (.lit 28673)), (.assign "v___x_1589_" (.bin .decEq (.var "v_tag_1515_") (.var "v___x_1588_"))), (.assign "v___y_1543_" (.var "v___x_1589_")), (.goto "v___jp_1542_")])]), (.block "v___jp_1542_" [(.ifZero "v___y_1543_" [(.ifZero "v_accepted_1537_" [(.assign "v___y_1529_" (.var "v_accepted_1537_")), (.goto "v___jp_1528_")] [(.decl .u64 "v___x_1544_"), (.decl .u8 "v___x_1545_"), (.assign "v___x_1544_" (.lit 29441)), (.assign "v___x_1545_" (.bin .decEq (.var "v_tag_1515_") (.var "v___x_1544_"))), (.assign "v___y_1529_" (.var "v___x_1545_")), (.goto "v___jp_1528_")])] [(.decl .u64 "v___x_1546_"), (.assign "v___x_1546_" (.bin .add (.var "v_w2_1504_") (.var "v___x_1541_"))), (.ret (.var "v___x_1546_"))])]), (.block "v___jp_1547_" [(.ifZero "v___y_1548_" [(.ret (.var "v_w5_1507_"))] [(.decl .u8 "v___x_1549_"), (.assign "v___x_1549_" (.bin .decEq (.var "v_a0_1516_") (.var "v___x_1541_"))), (.ifZero "v___x_1549_" [(.ret (.var "v_w5_1507_"))] [(.ret (.var "v___x_1538_"))])])]), (.block "v___jp_1550_" [(.ifZero "v___y_1551_" [(.ifZero "v_accepted_1537_" [(.assign "v___y_1548_" (.var "v_accepted_1537_")), (.goto "v___jp_1547_")] [(.decl .u64 "v___x_1552_"), (.decl .u8 "v___x_1553_"), (.assign "v___x_1552_" (.lit 30209)), (.assign "v___x_1553_" (.bin .decEq (.var "v_tag_1515_") (.var "v___x_1552_"))), (.assign "v___y_1548_" (.var "v___x_1553_")), (.goto "v___jp_1547_")])] [(.ret (.var "v_w4_1506_"))])])] [(.ifZero "v_accepted_1537_" [(.assign "v___y_1526_" (.var "v_accepted_1537_")), (.goto "v___jp_1525_")] [(.decl .u64 "v___x_1590_"), (.decl .u8 "v___x_1591_"), (.assign "v___x_1590_" (.lit 28673)), (.assign "v___x_1591_" (.bin .decEq (.var "v_tag_1515_") (.var "v___x_1590_"))), (.ifZero "v___x_1591_" [(.decl .u64 "v___x_1592_"), (.decl .u8 "v___x_1593_"), (.assign "v___x_1592_" (.lit 29441)), (.assign "v___x_1593_" (.bin .decEq (.var "v_tag_1515_") (.var "v___x_1592_"))), (.assign "v___y_1526_" (.var "v___x_1593_")), (.goto "v___jp_1525_")] [(.decl .u64 "v___x_1594_"), (.assign "v___x_1594_" (.bin .add (.var "v_w1_1503_") (.var "v___x_1521_"))), (.ret (.var "v___x_1594_"))])])])] [(.ifZero "v_accepted_1537_" [(.assign "v___y_1523_" (.var "v_accepted_1537_")), (.goto "v___jp_1522_")] [(.decl .u64 "v___x_1595_"), (.decl .u8 "v___x_1596_"), (.assign "v___x_1595_" (.lit 28673)), (.assign "v___x_1596_" (.bin .decEq (.var "v_tag_1515_") (.var "v___x_1595_"))), (.assign "v___y_1523_" (.var "v___x_1596_")), (.goto "v___jp_1522_")])]),
      (.block "v___jp_1522_" [(.ifZero "v___y_1523_" [(.ret (.var "v_w0_1502_"))] [(.decl .u64 "v___x_1524_"), (.assign "v___x_1524_" (.bin .add (.var "v_w0_1502_") (.var "v___x_1521_"))), (.ret (.var "v___x_1524_"))])]),
      (.block "v___jp_1525_" [(.ifZero "v___y_1526_" [(.ret (.var "v_w1_1503_"))] [(.decl .u64 "v___x_1527_"), (.assign "v___x_1527_" (.bin .add (.var "v_w1_1503_") (.var "v___x_1521_"))), (.ret (.var "v___x_1527_"))])]),
      (.block "v___jp_1528_" [(.ifZero "v___y_1529_" [(.ret (.var "v_w2_1504_"))] [(.decl .u64 "v___x_1530_"), (.assign "v___x_1530_" (.bin .add (.var "v_w2_1504_") (.var "v___x_1521_"))), (.ret (.var "v___x_1530_"))])]),
      (.block "v___jp_1531_" [(.ifZero "v___y_1532_" [(.ret (.var "v_w3_1505_"))] [(.decl .u64 "v___x_1533_"), (.assign "v___x_1533_" (.bin .add (.var "v_w3_1505_") (.var "v___x_1521_"))), (.ret (.var "v___x_1533_"))])]),
      (.block "v___jp_1534_" [(.ifZero "v___y_1535_" [(.ret (.var "v_w4_1506_"))] [(.decl .u64 "v___x_1536_"), (.assign "v___x_1536_" (.bin .add (.var "v_w4_1506_") (.var "v___x_1521_"))), (.ret (.var "v___x_1536_"))])])] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorBoot_syscallTag
def syscallTagC : Func :=
  { params := [("v_number_1800_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___x_1801_"),
      (.decl .u8 "v___x_1802_"),
      (.assign "v___x_1801_" (.lit 100)),
      (.assign "v___x_1802_" (.bin .decEq (.var "v_number_1800_") (.var "v___x_1801_"))),
      (.ifZero "v___x_1802_" [(.decl .u64 "v___x_1803_"), (.decl .u8 "v___x_1804_"), (.assign "v___x_1803_" (.lit 101)), (.assign "v___x_1804_" (.bin .decEq (.var "v_number_1800_") (.var "v___x_1803_"))), (.ifZero "v___x_1804_" [(.decl .u64 "v___x_1805_"), (.decl .u8 "v___x_1806_"), (.assign "v___x_1805_" (.lit 102)), (.assign "v___x_1806_" (.bin .decEq (.var "v_number_1800_") (.var "v___x_1805_"))), (.ifZero "v___x_1806_" [(.decl .u64 "v___x_1807_"), (.decl .u8 "v___x_1808_"), (.assign "v___x_1807_" (.lit 103)), (.assign "v___x_1808_" (.bin .decEq (.var "v_number_1800_") (.var "v___x_1807_"))), (.ifZero "v___x_1808_" [(.decl .u64 "v___x_1809_"), (.decl .u8 "v___x_1810_"), (.assign "v___x_1809_" (.lit 104)), (.assign "v___x_1810_" (.bin .decEq (.var "v_number_1800_") (.var "v___x_1809_"))), (.ifZero "v___x_1810_" [(.decl .u64 "v___x_1811_"), (.assign "v___x_1811_" (.lit 0)), (.ret (.var "v___x_1811_"))] [(.decl .u64 "v___x_1812_"), (.assign "v___x_1812_" (.lit 29697)), (.ret (.var "v___x_1812_"))])] [(.decl .u64 "v___x_1813_"), (.assign "v___x_1813_" (.lit 29441)), (.ret (.var "v___x_1813_"))])] [(.decl .u64 "v___x_1814_"), (.assign "v___x_1814_" (.lit 29185)), (.ret (.var "v___x_1814_"))])] [(.decl .u64 "v___x_1815_"), (.assign "v___x_1815_" (.lit 28929)), (.ret (.var "v___x_1815_"))])] [(.decl .u64 "v___x_1816_"), (.assign "v___x_1816_" (.lit 28673)), (.ret (.var "v___x_1816_"))])] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorBoot_registersCanonical
def registersCanonicalC : Func :=
  { params := [("v_tag_1821_", .u64), ("v_rbx_1822_", .u64), ("v_rcx_1823_", .u64), ("v_rdx_1824_", .u64)]
    result := .u8
    body := [
      (.decl .u8 "v___y_1830_"),
      (.decl .u64 "v___x_1833_"),
      (.decl .u8 "v___x_1834_"),
      (.assign "v___x_1833_" (.lit 28673)),
      (.assign "v___x_1834_" (.bin .decEq (.var "v_tag_1821_") (.var "v___x_1833_"))),
      (.ifZero "v___x_1834_" [(.decl .u64 "v___x_1835_"), (.decl .u8 "v___x_1836_"), (.assign "v___x_1835_" (.lit 28929)), (.assign "v___x_1836_" (.bin .decEq (.var "v_tag_1821_") (.var "v___x_1835_"))), (.ifZero "v___x_1836_" [(.decl .u64 "v___x_1837_"), (.decl .u8 "v___x_1838_"), (.assign "v___x_1837_" (.lit 29185)), (.assign "v___x_1838_" (.bin .decEq (.var "v_tag_1821_") (.var "v___x_1837_"))), (.ifZero "v___x_1838_" [(.decl .u64 "v___x_1839_"), (.decl .u8 "v___x_1840_"), (.assign "v___x_1839_" (.lit 29441)), (.assign "v___x_1840_" (.bin .decEq (.var "v_tag_1821_") (.var "v___x_1839_"))), (.assign "v___y_1830_" (.var "v___x_1840_")), (.goto "v___jp_1829_")] [(.assign "v___y_1830_" (.var "v___x_1838_")), (.goto "v___jp_1829_")])] [(.decl .u64 "v___x_1841_"), (.decl .u8 "v___x_1842_"), (.assign "v___x_1841_" (.lit 0)), (.assign "v___x_1842_" (.bin .decEq (.var "v_rcx_1823_") (.var "v___x_1841_"))), (.ifZero "v___x_1842_" [(.decl .u8 "v___x_1843_"), (.assign "v___x_1843_" (.bin .decEq (.var "v_rdx_1824_") (.var "v___x_1841_"))), (.ret (.var "v___x_1843_"))] [(.ret (.var "v___x_1834_"))])])] [(.decl .u64 "v___x_1844_"), (.decl .u8 "v___x_1845_"), (.assign "v___x_1844_" (.lit 0)), (.assign "v___x_1845_" (.bin .decEq (.var "v_rbx_1822_") (.var "v___x_1844_"))), (.ifZero "v___x_1845_" [(.decl .u64 "v___x_1846_"), (.decl .u8 "v___x_1847_"), (.assign "v___x_1846_" (.lit 64)), (.assign "v___x_1847_" (.bin .decLt (.var "v_rdx_1824_") (.var "v___x_1846_"))), (.ret (.var "v___x_1847_"))] [(.decl .u8 "v___x_1848_"), (.assign "v___x_1848_" (.lit 0)), (.ret (.var "v___x_1848_"))])]),
      (.block "v___jp_1825_" [(.decl .u64 "v___x_1826_"), (.decl .u8 "v___x_1827_"), (.assign "v___x_1826_" (.lit 0)), (.assign "v___x_1827_" (.bin .decEq (.var "v_rcx_1823_") (.var "v___x_1826_"))), (.ifZero "v___x_1827_" [(.ret (.var "v___x_1827_"))] [(.decl .u8 "v___x_1828_"), (.assign "v___x_1828_" (.bin .decEq (.var "v_rdx_1824_") (.var "v___x_1826_"))), (.ret (.var "v___x_1828_"))])]),
      (.block "v___jp_1829_" [(.ifZero "v___y_1830_" [(.decl .u64 "v___x_1831_"), (.decl .u8 "v___x_1832_"), (.assign "v___x_1831_" (.lit 29697)), (.assign "v___x_1832_" (.bin .decEq (.var "v_tag_1821_") (.var "v___x_1831_"))), (.ifZero "v___x_1832_" [(.ret (.var "v___x_1832_"))] [(.goto "v___jp_1825_")])] [(.goto "v___jp_1825_")])])] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorBoot_refusal
def refusalC : Func :=
  { params := [("v_w4_1859_", .u64), ("v_c0_1860_", .u64), ("v_c1_1861_", .u64), ("v_c2_1862_", .u64), ("v_c3_1863_", .u64), ("v_f_1864_", .u64), ("v_actor_1865_", .u64), ("v_number_1866_", .u64), ("v_rbx_1867_", .u64), ("v_rcx_1868_", .u64), ("v_rdx_1869_", .u64)]
    result := .u64
    body := [
      (.decl .u8 "v___x_1870_"),
      (.assign "v___x_1870_" (.call "l_LeanOS_SpawnAllocatorWords_canonical" ["v_w4_1859_", "v_c0_1860_", "v_c1_1861_", "v_c2_1862_", "v_c3_1863_", "v_f_1864_"])),
      (.ifZero "v___x_1870_" [(.decl .u64 "v___x_1871_"), (.assign "v___x_1871_" (.lit 65056)), (.ret (.var "v___x_1871_"))] [(.decl .u64 "v___x_1872_"), (.decl .u8 "v___x_1873_"), (.assign "v___x_1872_" (.lit 2)), (.assign "v___x_1873_" (.bin .decEq (.var "v_actor_1865_") (.var "v___x_1872_"))), (.ifZero "v___x_1873_" [(.decl .u64 "v___x_1874_"), (.assign "v___x_1874_" (.lit 65057)), (.ret (.var "v___x_1874_"))] [(.decl .u64 "v___x_1875_"), (.decl .u64 "v___x_1876_"), (.decl .u8 "v___x_1877_"), (.assign "v___x_1875_" (.call "l_LeanOS_SpawnAllocatorBoot_syscallTag" ["v_number_1866_"])), (.assign "v___x_1876_" (.lit 0)), (.assign "v___x_1877_" (.bin .decEq (.var "v___x_1875_") (.var "v___x_1876_"))), (.ifZero "v___x_1877_" [(.decl .u8 "v___x_1878_"), (.assign "v___x_1878_" (.call "l_LeanOS_SpawnAllocatorBoot_registersCanonical" ["v___x_1875_", "v_rbx_1867_", "v_rcx_1868_", "v_rdx_1869_"])), (.ifZero "v___x_1878_" [(.decl .u64 "v___x_1879_"), (.assign "v___x_1879_" (.lit 65059)), (.ret (.var "v___x_1879_"))] [(.ret (.var "v___x_1876_"))])] [(.decl .u64 "v___x_1880_"), (.assign "v___x_1880_" (.lit 65058)), (.ret (.var "v___x_1880_"))])])])] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorBoot_replyOf
def replyOfC : Func :=
  { params := [("v_status_1905_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___x_1906_"),
      (.decl .u64 "v___x_1907_"),
      (.decl .u64 "v___x_1908_"),
      (.decl .u64 "v___x_1909_"),
      (.assign "v___x_1906_" (.lit 1)),
      (.assign "v___x_1907_" (.lit 16)),
      (.assign "v___x_1908_" (.bin .shiftLeft (.var "v_status_1905_") (.var "v___x_1907_"))),
      (.assign "v___x_1909_" (.bin .lor (.var "v___x_1906_") (.var "v___x_1908_"))),
      (.ret (.var "v___x_1909_"))] }
-- END GENERATED AST

-- BEGIN GENERATED AST l_LeanOS_SpawnAllocatorBoot_wordAt
def wordAtC : Func :=
  { params := [("v_index_1914_", .u64), ("v_w0_1915_", .u64), ("v_w1_1916_", .u64), ("v_w2_1917_", .u64), ("v_w3_1918_", .u64), ("v_w4_1919_", .u64), ("v_w5_1920_", .u64), ("v_c0_1921_", .u64), ("v_c1_1922_", .u64), ("v_c2_1923_", .u64), ("v_c3_1924_", .u64), ("v_m2_1925_", .u64), ("v_m3_1926_", .u64), ("v_f_1927_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___x_1928_"),
      (.decl .u8 "v___x_1929_"),
      (.assign "v___x_1928_" (.lit 0)),
      (.assign "v___x_1929_" (.bin .decEq (.var "v_index_1914_") (.var "v___x_1928_"))),
      (.ifZero "v___x_1929_" [(.decl .u64 "v___x_1930_"), (.decl .u8 "v___x_1931_"), (.assign "v___x_1930_" (.lit 1)), (.assign "v___x_1931_" (.bin .decEq (.var "v_index_1914_") (.var "v___x_1930_"))), (.ifZero "v___x_1931_" [(.decl .u64 "v___x_1932_"), (.decl .u8 "v___x_1933_"), (.assign "v___x_1932_" (.lit 2)), (.assign "v___x_1933_" (.bin .decEq (.var "v_index_1914_") (.var "v___x_1932_"))), (.ifZero "v___x_1933_" [(.decl .u64 "v___x_1934_"), (.decl .u8 "v___x_1935_"), (.assign "v___x_1934_" (.lit 3)), (.assign "v___x_1935_" (.bin .decEq (.var "v_index_1914_") (.var "v___x_1934_"))), (.ifZero "v___x_1935_" [(.decl .u64 "v___x_1936_"), (.decl .u8 "v___x_1937_"), (.assign "v___x_1936_" (.lit 4)), (.assign "v___x_1937_" (.bin .decEq (.var "v_index_1914_") (.var "v___x_1936_"))), (.ifZero "v___x_1937_" [(.decl .u64 "v___x_1938_"), (.decl .u8 "v___x_1939_"), (.assign "v___x_1938_" (.lit 5)), (.assign "v___x_1939_" (.bin .decEq (.var "v_index_1914_") (.var "v___x_1938_"))), (.ifZero "v___x_1939_" [(.decl .u64 "v___x_1940_"), (.decl .u8 "v___x_1941_"), (.assign "v___x_1940_" (.lit 6)), (.assign "v___x_1941_" (.bin .decEq (.var "v_index_1914_") (.var "v___x_1940_"))), (.ifZero "v___x_1941_" [(.decl .u64 "v___x_1942_"), (.decl .u8 "v___x_1943_"), (.assign "v___x_1942_" (.lit 7)), (.assign "v___x_1943_" (.bin .decEq (.var "v_index_1914_") (.var "v___x_1942_"))), (.ifZero "v___x_1943_" [(.decl .u64 "v___x_1944_"), (.decl .u8 "v___x_1945_"), (.assign "v___x_1944_" (.lit 8)), (.assign "v___x_1945_" (.bin .decEq (.var "v_index_1914_") (.var "v___x_1944_"))), (.ifZero "v___x_1945_" [(.decl .u64 "v___x_1946_"), (.decl .u8 "v___x_1947_"), (.assign "v___x_1946_" (.lit 9)), (.assign "v___x_1947_" (.bin .decEq (.var "v_index_1914_") (.var "v___x_1946_"))), (.ifZero "v___x_1947_" [(.decl .u64 "v___x_1948_"), (.decl .u8 "v___x_1949_"), (.assign "v___x_1948_" (.lit 10)), (.assign "v___x_1949_" (.bin .decEq (.var "v_index_1914_") (.var "v___x_1948_"))), (.ifZero "v___x_1949_" [(.decl .u64 "v___x_1950_"), (.decl .u8 "v___x_1951_"), (.assign "v___x_1950_" (.lit 11)), (.assign "v___x_1951_" (.bin .decEq (.var "v_index_1914_") (.var "v___x_1950_"))), (.ifZero "v___x_1951_" [(.decl .u64 "v___x_1952_"), (.decl .u8 "v___x_1953_"), (.assign "v___x_1952_" (.lit 12)), (.assign "v___x_1953_" (.bin .decEq (.var "v_index_1914_") (.var "v___x_1952_"))), (.ifZero "v___x_1953_" [(.ret (.var "v___x_1928_"))] [(.ret (.var "v_f_1927_"))])] [(.ret (.var "v_m3_1926_"))])] [(.ret (.var "v_m2_1925_"))])] [(.ret (.var "v_c3_1924_"))])] [(.ret (.var "v_c2_1923_"))])] [(.ret (.var "v_c1_1922_"))])] [(.ret (.var "v_c0_1921_"))])] [(.ret (.var "v_w5_1920_"))])] [(.ret (.var "v_w4_1919_"))])] [(.ret (.var "v_w3_1918_"))])] [(.ret (.var "v_w2_1917_"))])] [(.ret (.var "v_w1_1916_"))])] [(.ret (.var "v_w0_1915_"))])] }
-- END GENERATED AST

-- BEGIN GENERATED AST leanos_spawn_allocator_seed
def seedC : Func :=
  { params := [("v_index_1984_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___x_1985_"),
      (.decl .u64 "v___x_1986_"),
      (.decl .u64 "v___x_1987_"),
      (.decl .u64 "v___x_1988_"),
      (.decl .u64 "v___x_1989_"),
      (.decl .u64 "v___x_1990_"),
      (.decl .u64 "v___x_1991_"),
      (.decl .u64 "v___x_1992_"),
      (.assign "v___x_1985_" (.lit 3)),
      (.assign "v___x_1986_" (.lit 21)),
      (.assign "v___x_1987_" (.lit 6)),
      (.assign "v___x_1988_" (.lit 1)),
      (.assign "v___x_1989_" (.lit 0)),
      (.assign "v___x_1990_" (.lit 5)),
      (.assign "v___x_1991_" (.lit 65536)),
      (.assign "v___x_1992_" (.call "l_LeanOS_SpawnAllocatorBoot_wordAt" ["v_index_1984_", "v___x_1985_", "v___x_1986_", "v___x_1987_", "v___x_1988_", "v___x_1988_", "v___x_1989_", "v___x_1989_", "v___x_1989_", "v___x_1989_", "v___x_1989_", "v___x_1990_", "v___x_1989_", "v___x_1991_"])),
      (.ret (.var "v___x_1992_"))] }
-- END GENERATED AST

-- BEGIN GENERATED AST leanos_spawn_allocator_syscall
def syscallC : Func :=
  { params := [("v_w0_1997_", .u64), ("v_w1_1998_", .u64), ("v_w2_1999_", .u64), ("v_w3_2000_", .u64), ("v_w4_2001_", .u64), ("v_w5_2002_", .u64), ("v_c0_2003_", .u64), ("v_c1_2004_", .u64), ("v_c2_2005_", .u64), ("v_c3_2006_", .u64), ("v_m2_2007_", .u64), ("v_m3_2008_", .u64), ("v_f_2009_", .u64), ("v_actor_2010_", .u64), ("v_number_2011_", .u64), ("v_rbx_2012_", .u64), ("v_rcx_2013_", .u64), ("v_rdx_2014_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v_refused_2015_"),
      (.decl .u64 "v___x_2016_"),
      (.decl .u8 "v___x_2017_"),
      (.assign "v_refused_2015_" (.call "l_LeanOS_SpawnAllocatorBoot_refusal" ["v_w4_2001_", "v_c0_2003_", "v_c1_2004_", "v_c2_2005_", "v_c3_2006_", "v_f_2009_", "v_actor_2010_", "v_number_2011_", "v_rbx_2012_", "v_rcx_2013_", "v_rdx_2014_"])),
      (.assign "v___x_2016_" (.lit 0)),
      (.assign "v___x_2017_" (.bin .decEq (.var "v_refused_2015_") (.var "v___x_2016_"))),
      (.ifZero "v___x_2017_" [(.ret (.var "v_refused_2015_"))] [(.decl .u64 "v___x_2018_"), (.decl .u64 "v___x_2019_"), (.decl .u64 "v___x_2020_"), (.assign "v___x_2018_" (.call "l_LeanOS_SpawnAllocatorBoot_syscallTag" ["v_number_2011_"])), (.assign "v___x_2019_" (.call "l_LeanOS_SpawnAllocatorWords_stepReply" ["v_w0_1997_", "v_w1_1998_", "v_w2_1999_", "v_w3_2000_", "v_w4_2001_", "v_w5_2002_", "v_c0_2003_", "v_c1_2004_", "v_c2_2005_", "v_c3_2006_", "v_m2_2007_", "v_m3_2008_", "v_f_2009_", "v___x_2018_", "v_rbx_2012_", "v_rcx_2013_", "v_rdx_2014_", "v___x_2016_"])), (.assign "v___x_2020_" (.call "l_LeanOS_SpawnAllocatorBoot_replyOf" ["v___x_2019_"])), (.ret (.var "v___x_2020_"))])] }
-- END GENERATED AST

-- BEGIN GENERATED AST leanos_spawn_allocator_syscall_value
def syscallValueC : Func :=
  { params := [("v_w0_2059_", .u64), ("v_w1_2060_", .u64), ("v_w2_2061_", .u64), ("v_w3_2062_", .u64), ("v_w4_2063_", .u64), ("v_w5_2064_", .u64), ("v_c0_2065_", .u64), ("v_c1_2066_", .u64), ("v_c2_2067_", .u64), ("v_c3_2068_", .u64), ("v_m2_2069_", .u64), ("v_m3_2070_", .u64), ("v_f_2071_", .u64), ("v_actor_2072_", .u64), ("v_number_2073_", .u64), ("v_rbx_2074_", .u64), ("v_rcx_2075_", .u64), ("v_rdx_2076_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___x_2077_"),
      (.decl .u64 "v___x_2078_"),
      (.decl .u8 "v___x_2079_"),
      (.assign "v___x_2077_" (.call "l_LeanOS_SpawnAllocatorBoot_refusal" ["v_w4_2063_", "v_c0_2065_", "v_c1_2066_", "v_c2_2067_", "v_c3_2068_", "v_f_2071_", "v_actor_2072_", "v_number_2073_", "v_rbx_2074_", "v_rcx_2075_", "v_rdx_2076_"])),
      (.assign "v___x_2078_" (.lit 0)),
      (.assign "v___x_2079_" (.bin .decEq (.var "v___x_2077_") (.var "v___x_2078_"))),
      (.ifZero "v___x_2079_" [(.ret (.var "v___x_2078_"))] [(.decl .u64 "v___x_2080_"), (.decl .u64 "v___x_2081_"), (.assign "v___x_2080_" (.call "l_LeanOS_SpawnAllocatorBoot_syscallTag" ["v_number_2073_"])), (.assign "v___x_2081_" (.call "l_LeanOS_SpawnAllocatorWords_stepValue" ["v_w0_2059_", "v_w1_2060_", "v_w2_2061_", "v_w3_2062_", "v_w4_2063_", "v_w5_2064_", "v_c0_2065_", "v_c1_2066_", "v_c2_2067_", "v_c3_2068_", "v_m2_2069_", "v_m3_2070_", "v_f_2071_", "v___x_2080_", "v_rbx_2074_", "v_rcx_2075_", "v_rdx_2076_", "v___x_2078_"])), (.ret (.var "v___x_2081_"))])] }
-- END GENERATED AST

-- BEGIN GENERATED AST leanos_spawn_allocator_syscall_next
def syscallNextC : Func :=
  { params := [("v_index_2120_", .u64), ("v_w0_2121_", .u64), ("v_w1_2122_", .u64), ("v_w2_2123_", .u64), ("v_w3_2124_", .u64), ("v_w4_2125_", .u64), ("v_w5_2126_", .u64), ("v_c0_2127_", .u64), ("v_c1_2128_", .u64), ("v_c2_2129_", .u64), ("v_c3_2130_", .u64), ("v_m2_2131_", .u64), ("v_m3_2132_", .u64), ("v_f_2133_", .u64), ("v_actor_2134_", .u64), ("v_number_2135_", .u64), ("v_rbx_2136_", .u64), ("v_rcx_2137_", .u64), ("v_rdx_2138_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___x_2139_"),
      (.decl .u64 "v___x_2140_"),
      (.decl .u8 "v___x_2141_"),
      (.assign "v___x_2139_" (.call "l_LeanOS_SpawnAllocatorBoot_refusal" ["v_w4_2125_", "v_c0_2127_", "v_c1_2128_", "v_c2_2129_", "v_c3_2130_", "v_f_2133_", "v_actor_2134_", "v_number_2135_", "v_rbx_2136_", "v_rcx_2137_", "v_rdx_2138_"])),
      (.assign "v___x_2140_" (.lit 0)),
      (.assign "v___x_2141_" (.bin .decEq (.var "v___x_2139_") (.var "v___x_2140_"))),
      (.ifZero "v___x_2141_" [(.decl .u64 "v___x_2142_"), (.assign "v___x_2142_" (.call "l_LeanOS_SpawnAllocatorBoot_wordAt" ["v_index_2120_", "v_w0_2121_", "v_w1_2122_", "v_w2_2123_", "v_w3_2124_", "v_w4_2125_", "v_w5_2126_", "v_c0_2127_", "v_c1_2128_", "v_c2_2129_", "v_c3_2130_", "v_m2_2131_", "v_m3_2132_", "v_f_2133_"])), (.ret (.var "v___x_2142_"))] [(.decl .u64 "v___x_2143_"), (.decl .u64 "v___x_2144_"), (.assign "v___x_2143_" (.call "l_LeanOS_SpawnAllocatorBoot_syscallTag" ["v_number_2135_"])), (.assign "v___x_2144_" (.call "l_LeanOS_SpawnAllocatorWords_stepNextWord" ["v_index_2120_", "v_w0_2121_", "v_w1_2122_", "v_w2_2123_", "v_w3_2124_", "v_w4_2125_", "v_w5_2126_", "v_c0_2127_", "v_c1_2128_", "v_c2_2129_", "v_c3_2130_", "v_m2_2131_", "v_m3_2132_", "v_f_2133_", "v___x_2143_", "v_rbx_2136_", "v_rcx_2137_", "v_rdx_2138_", "v___x_2140_"])), (.ret (.var "v___x_2144_"))])] }
-- END GENERATED AST

-- BEGIN GENERATED AST leanos_spawn_allocator_kernel
def kernelC : Func :=
  { params := [("v_w0_2185_", .u64), ("v_w1_2186_", .u64), ("v_w2_2187_", .u64), ("v_w3_2188_", .u64), ("v_w4_2189_", .u64), ("v_w5_2190_", .u64), ("v_c0_2191_", .u64), ("v_c1_2192_", .u64), ("v_c2_2193_", .u64), ("v_c3_2194_", .u64), ("v_m2_2195_", .u64), ("v_m3_2196_", .u64), ("v_f_2197_", .u64), ("v_tag_2198_", .u64), ("v_a0_2199_", .u64), ("v_a1_2200_", .u64), ("v_a2_2201_", .u64), ("v_a3_2202_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___x_2203_"),
      (.assign "v___x_2203_" (.call "l_LeanOS_SpawnAllocatorWords_stepReply" ["v_w0_2185_", "v_w1_2186_", "v_w2_2187_", "v_w3_2188_", "v_w4_2189_", "v_w5_2190_", "v_c0_2191_", "v_c1_2192_", "v_c2_2193_", "v_c3_2194_", "v_m2_2195_", "v_m3_2196_", "v_f_2197_", "v_tag_2198_", "v_a0_2199_", "v_a1_2200_", "v_a2_2201_", "v_a3_2202_"])),
      (.ret (.var "v___x_2203_"))] }
-- END GENERATED AST

-- BEGIN GENERATED AST leanos_spawn_allocator_kernel_value
def kernelValueC : Func :=
  { params := [("v_w0_2242_", .u64), ("v_w1_2243_", .u64), ("v_w2_2244_", .u64), ("v_w3_2245_", .u64), ("v_w4_2246_", .u64), ("v_w5_2247_", .u64), ("v_c0_2248_", .u64), ("v_c1_2249_", .u64), ("v_c2_2250_", .u64), ("v_c3_2251_", .u64), ("v_m2_2252_", .u64), ("v_m3_2253_", .u64), ("v_f_2254_", .u64), ("v_tag_2255_", .u64), ("v_a0_2256_", .u64), ("v_a1_2257_", .u64), ("v_a2_2258_", .u64), ("v_a3_2259_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___x_2260_"),
      (.assign "v___x_2260_" (.call "l_LeanOS_SpawnAllocatorWords_stepValue" ["v_w0_2242_", "v_w1_2243_", "v_w2_2244_", "v_w3_2245_", "v_w4_2246_", "v_w5_2247_", "v_c0_2248_", "v_c1_2249_", "v_c2_2250_", "v_c3_2251_", "v_m2_2252_", "v_m3_2253_", "v_f_2254_", "v_tag_2255_", "v_a0_2256_", "v_a1_2257_", "v_a2_2258_", "v_a3_2259_"])),
      (.ret (.var "v___x_2260_"))] }
-- END GENERATED AST

-- BEGIN GENERATED AST leanos_spawn_allocator_kernel_next
def kernelNextC : Func :=
  { params := [("v_index_2299_", .u64), ("v_w0_2300_", .u64), ("v_w1_2301_", .u64), ("v_w2_2302_", .u64), ("v_w3_2303_", .u64), ("v_w4_2304_", .u64), ("v_w5_2305_", .u64), ("v_c0_2306_", .u64), ("v_c1_2307_", .u64), ("v_c2_2308_", .u64), ("v_c3_2309_", .u64), ("v_m2_2310_", .u64), ("v_m3_2311_", .u64), ("v_f_2312_", .u64), ("v_tag_2313_", .u64), ("v_a0_2314_", .u64), ("v_a1_2315_", .u64), ("v_a2_2316_", .u64), ("v_a3_2317_", .u64)]
    result := .u64
    body := [
      (.decl .u64 "v___x_2318_"),
      (.assign "v___x_2318_" (.call "l_LeanOS_SpawnAllocatorWords_stepNextWord" ["v_index_2299_", "v_w0_2300_", "v_w1_2301_", "v_w2_2302_", "v_w3_2303_", "v_w4_2304_", "v_w5_2305_", "v_c0_2306_", "v_c1_2307_", "v_c2_2308_", "v_c3_2309_", "v_m2_2310_", "v_m3_2311_", "v_f_2312_", "v_tag_2313_", "v_a0_2314_", "v_a1_2315_", "v_a2_2316_", "v_a3_2317_"])),
      (.ret (.var "v___x_2318_"))] }
-- END GENERATED AST


/-! ## Linking the emitted helpers -/

/-- The emitted helper of `SpawnAllocatorWords.c` that a call names, by its
number of argument words and its C name; `none` for every other callee. -/
def helper? (arity : Nat) (fn : String) : Option Func :=
  match arity with
  | 1 =>
      if fn = "l_LeanOS_SpawnAllocatorWords_childCanonical" then some childCanonicalC
      else if fn = "l_LeanOS_SpawnAllocatorWords_occupied" then some occupiedC
      else if fn = "l_LeanOS_SpawnAllocatorWords_chargeOf" then some chargeOfC
      else if fn = "l_LeanOS_SpawnAllocatorWords_generationOf" then some generationOfC
      else if fn = "l_LeanOS_SpawnAllocatorWords_identityExhaustedW" then some identityExhaustedWC
      else if fn = "l_LeanOS_SpawnAllocatorWords_capabilityExhaustedW" then
        some capabilityExhaustedWC
      else if fn = "l_LeanOS_SpawnAllocatorWords_controlAvailableW" then some controlAvailableWC
      else if fn = "l_LeanOS_SpawnAllocatorWords_budgetW" then some budgetWC
      else if fn = "l_LeanOS_SpawnAllocatorWords_parentFramesW" then some parentFramesWC
      else if fn = "l_LeanOS_SpawnAllocatorWords_rightsValidW" then some rightsValidWC
      else if fn = "l_LeanOS_SpawnAllocatorBoot_syscallTag" then some syscallTagC
      else if fn = "l_LeanOS_SpawnAllocatorBoot_replyOf" then some replyOfC
      else none
  | 3 =>
      if fn = "l_LeanOS_SpawnAllocatorWords_memoryWordAt" then some memoryWordAtC
      else if fn = "l_LeanOS_SpawnAllocatorWords_availableW" then some availableWC
      else if fn = "l_LeanOS_SpawnAllocatorWords_resolveEndpointW" then some resolveEndpointWC
      else none
  | 4 =>
      if fn = "l_LeanOS_SpawnAllocatorWords_childCountW" then some childCountWC
      else if fn = "l_LeanOS_SpawnAllocatorWords_freeSlotW" then some freeSlotWC
      else if fn = "l_LeanOS_SpawnAllocatorBoot_registersCanonical" then some registersCanonicalC
      else none
  | 5 =>
      if fn = "l_LeanOS_SpawnAllocatorWords_childWordAt" then some childWordAtC
      else if fn = "l_LeanOS_SpawnAllocatorWords_resolveControlW" then some resolveControlWC
      else if fn = "l_LeanOS_SpawnAllocatorWords_commandErrorW" then some commandErrorWC
      else if fn = "l_LeanOS_SpawnAllocatorWords_nextMemory" then some nextMemoryC
      else none
  | 6 => if fn = "l_LeanOS_SpawnAllocatorWords_canonical" then some canonicalC else none
  | 8 => if fn = "l_LeanOS_SpawnAllocatorWords_nextFrames" then some nextFramesC else none
  | 10 => if fn = "l_LeanOS_SpawnAllocatorWords_nextChild" then some nextChildC else none
  | 11 => if fn = "l_LeanOS_SpawnAllocatorBoot_refusal" then some refusalC else none
  | 14 => if fn = "l_LeanOS_SpawnAllocatorBoot_wordAt" then some wordAtC else none
  | 17 => if fn = "l_LeanOS_SpawnAllocatorWords_decideW" then some decideWC else none
  | 18 =>
      if fn = "l_LeanOS_SpawnAllocatorWords_stepReply" then some stepReplyC
      else if fn = "l_LeanOS_SpawnAllocatorWords_stepValue" then some stepValueC
      else none
  | 19 => if fn = "l_LeanOS_SpawnAllocatorWords_stepNextWord" then some stepNextWordC else none
  | _ => none

/-- The emitted helpers linked `depth` calls deep: a call of a helper runs its
AST with the helpers linked one call less deep; every other call, and every
call at depth zero, goes to `ext`. -/
def linkAt (ext : Ext) : Nat → Ext
  | 0 => ext
  | depth + 1 => fun fn args =>
      match helper? args.length fn with
      | some func => callWith (linkAt ext depth) func args
      | none => ext fn args

/-- The emitted helpers as the exports call them. No call chain from an export
is more than five calls deep (`syscallNext`, `stepNextWord`, `stepReply`,
`decideW`, `resolveControlW`, `childWordAt`), so every helper call resolves to
its AST. -/
def link (ext : Ext) : Ext := linkAt ext 5

/-- A call of a helper's C name, one level deeper, runs its AST. -/
theorem linkAt_helper (ext : Ext) (n : Nat) (fn : String) (args : List UInt64) (func : Func)
    (h : helper? args.length fn = some func) :
    linkAt ext (n + 1) fn args = callWith (linkAt ext n) func args := by
  simp only [linkAt, h]

/-- Look a helper up by its arity and C name. -/
macro "helper_lookup" : tactic => `(tactic|
  (simp only [List.length_cons, List.length_nil, Nat.reduceAdd]; unfold helper?;
    simp only [String.reduceEq, ↓reduceIte]))

/-! ## Helpers that call nothing

Each AST computes its Lean definition on every input, whatever `ext` answers
(it calls nothing), and so does its C name in every linking at least one
call deep. -/

theorem childCanonicalC_refines (ext : Ext) (word : UInt64) :
    callWith ext childCanonicalC [word] = some (boolWord (childCanonical word)) := by
  apply callWith_of_tree_bool ext _ childCanonicalC rfl rfl
  csym_refine [childCanonical, generationLimit]

theorem link_childCanonical (ext : Ext) (n : Nat) (word : UInt64) :
    linkAt ext (n + 1) "l_LeanOS_SpawnAllocatorWords_childCanonical" [word] =
      some (boolWord (childCanonical word)) :=
  (linkAt_helper ext n _ _ _ (by helper_lookup)).trans (childCanonicalC_refines _ word)

theorem occupiedC_refines (ext : Ext) (word : UInt64) :
    callWith ext occupiedC [word] = some (occupied word) := by
  apply callWith_of_tree ext _ occupiedC rfl
  csym_refine [occupied]

theorem link_occupied (ext : Ext) (n : Nat) (word : UInt64) :
    linkAt ext (n + 1) "l_LeanOS_SpawnAllocatorWords_occupied" [word] = some (occupied word) :=
  (linkAt_helper ext n _ _ _ (by helper_lookup)).trans (occupiedC_refines _ word)

theorem chargeOfC_refines (ext : Ext) (word : UInt64) :
    callWith ext chargeOfC [word] = some (chargeOf word) := by
  apply callWith_of_tree ext _ chargeOfC rfl
  csym_refine [chargeOf]

theorem link_chargeOf (ext : Ext) (n : Nat) (word : UInt64) :
    linkAt ext (n + 1) "l_LeanOS_SpawnAllocatorWords_chargeOf" [word] = some (chargeOf word) :=
  (linkAt_helper ext n _ _ _ (by helper_lookup)).trans (chargeOfC_refines _ word)

theorem generationOfC_refines (ext : Ext) (word : UInt64) :
    callWith ext generationOfC [word] = some (generationOf word) := by
  apply callWith_of_tree ext _ generationOfC rfl
  csym_refine [generationOf]

theorem link_generationOf (ext : Ext) (n : Nat) (word : UInt64) :
    linkAt ext (n + 1) "l_LeanOS_SpawnAllocatorWords_generationOf" [word] =
      some (generationOf word) :=
  (linkAt_helper ext n _ _ _ (by helper_lookup)).trans (generationOfC_refines _ word)

theorem identityExhaustedWC_refines (ext : Ext) (next : UInt64) :
    callWith ext identityExhaustedWC [next] = some (boolWord (identityExhaustedW next)) := by
  apply callWith_of_tree_bool ext _ identityExhaustedWC rfl rfl
  csym_refine [identityExhaustedW, maxWord]

theorem link_identityExhaustedW (ext : Ext) (n : Nat) (next : UInt64) :
    linkAt ext (n + 1) "l_LeanOS_SpawnAllocatorWords_identityExhaustedW" [next] =
      some (boolWord (identityExhaustedW next)) :=
  (linkAt_helper ext n _ _ _ (by helper_lookup)).trans (identityExhaustedWC_refines _ next)

theorem capabilityExhaustedWC_refines (ext : Ext) (next : UInt64) :
    callWith ext capabilityExhaustedWC [next] = some (boolWord (capabilityExhaustedW next)) := by
  apply callWith_of_tree_bool ext _ capabilityExhaustedWC rfl rfl
  csym_refine [capabilityExhaustedW, generationLimit]

theorem link_capabilityExhaustedW (ext : Ext) (n : Nat) (next : UInt64) :
    linkAt ext (n + 1) "l_LeanOS_SpawnAllocatorWords_capabilityExhaustedW" [next] =
      some (boolWord (capabilityExhaustedW next)) :=
  (linkAt_helper ext n _ _ _ (by helper_lookup)).trans (capabilityExhaustedWC_refines _ next)

theorem controlAvailableWC_refines (ext : Ext) (next : UInt64) :
    callWith ext controlAvailableWC [next] = some (boolWord (controlAvailableW next)) := by
  apply callWith_of_tree_bool ext _ controlAvailableWC rfl rfl
  csym_refine [controlAvailableW, generationLimit]

theorem link_controlAvailableW (ext : Ext) (n : Nat) (next : UInt64) :
    linkAt ext (n + 1) "l_LeanOS_SpawnAllocatorWords_controlAvailableW" [next] =
      some (boolWord (controlAvailableW next)) :=
  (linkAt_helper ext n _ _ _ (by helper_lookup)).trans (controlAvailableWC_refines _ next)

theorem freeSlotWC_refines (ext : Ext) (c0 c1 c2 c3 : UInt64) :
    callWith ext freeSlotWC [c0, c1, c2, c3] = some (freeSlotW c0 c1 c2 c3) := by
  apply callWith_of_tree ext _ freeSlotWC rfl
  csym_refine [freeSlotW]

theorem link_freeSlotW (ext : Ext) (n : Nat) (c0 c1 c2 c3 : UInt64) :
    linkAt ext (n + 1) "l_LeanOS_SpawnAllocatorWords_freeSlotW" [c0, c1, c2, c3] =
      some (freeSlotW c0 c1 c2 c3) :=
  (linkAt_helper ext n _ _ _ (by helper_lookup)).trans (freeSlotWC_refines _ c0 c1 c2 c3)

theorem childWordAtC_refines (ext : Ext) (slot c0 c1 c2 c3 : UInt64) :
    callWith ext childWordAtC [slot, c0, c1, c2, c3] = some (childWordAt slot c0 c1 c2 c3) := by
  apply callWith_of_tree ext _ childWordAtC rfl
  csym_refine [childWordAt]

theorem link_childWordAt (ext : Ext) (n : Nat) (slot c0 c1 c2 c3 : UInt64) :
    linkAt ext (n + 1) "l_LeanOS_SpawnAllocatorWords_childWordAt" [slot, c0, c1, c2, c3] =
      some (childWordAt slot c0 c1 c2 c3) :=
  (linkAt_helper ext n _ _ _ (by helper_lookup)).trans (childWordAtC_refines _ slot c0 c1 c2 c3)

theorem memoryWordAtC_refines (ext : Ext) (slot m2 m3 : UInt64) :
    callWith ext memoryWordAtC [slot, m2, m3] = some (memoryWordAt slot m2 m3) := by
  apply callWith_of_tree ext _ memoryWordAtC rfl
  csym_refine [memoryWordAt]

theorem link_memoryWordAt (ext : Ext) (n : Nat) (slot m2 m3 : UInt64) :
    linkAt ext (n + 1) "l_LeanOS_SpawnAllocatorWords_memoryWordAt" [slot, m2, m3] =
      some (memoryWordAt slot m2 m3) :=
  (linkAt_helper ext n _ _ _ (by helper_lookup)).trans (memoryWordAtC_refines _ slot m2 m3)

theorem budgetWC_refines (ext : Ext) (f : UInt64) :
    callWith ext budgetWC [f] = some (budgetW f) := by
  apply callWith_of_tree ext _ budgetWC rfl
  csym_refine [budgetW]

theorem link_budgetW (ext : Ext) (n : Nat) (f : UInt64) :
    linkAt ext (n + 1) "l_LeanOS_SpawnAllocatorWords_budgetW" [f] = some (budgetW f) :=
  (linkAt_helper ext n _ _ _ (by helper_lookup)).trans (budgetWC_refines _ f)

theorem parentFramesWC_refines (ext : Ext) (f : UInt64) :
    callWith ext parentFramesWC [f] = some (parentFramesW f) := by
  apply callWith_of_tree ext _ parentFramesWC rfl
  csym_refine [parentFramesW]

theorem link_parentFramesW (ext : Ext) (n : Nat) (f : UInt64) :
    linkAt ext (n + 1) "l_LeanOS_SpawnAllocatorWords_parentFramesW" [f] = some (parentFramesW f) :=
  (linkAt_helper ext n _ _ _ (by helper_lookup)).trans (parentFramesWC_refines _ f)

theorem rightsValidWC_refines (ext : Ext) (rights : UInt64) :
    callWith ext rightsValidWC [rights] = some (boolWord (rightsValidW rights)) := by
  apply callWith_of_tree_bool ext _ rightsValidWC rfl rfl
  csym_refine [rightsValidW]

theorem link_rightsValidW (ext : Ext) (n : Nat) (rights : UInt64) :
    linkAt ext (n + 1) "l_LeanOS_SpawnAllocatorWords_rightsValidW" [rights] =
      some (boolWord (rightsValidW rights)) :=
  (linkAt_helper ext n _ _ _ (by helper_lookup)).trans (rightsValidWC_refines _ rights)

theorem commandErrorWC_refines (ext : Ext) (tag a0 a1 a2 a3 : UInt64) :
    callWith ext commandErrorWC [tag, a0, a1, a2, a3] = some (commandErrorW tag a0 a1 a2 a3) := by
  apply callWith_of_tree ext _ commandErrorWC rfl
  csym_refine [commandErrorW]

theorem link_commandErrorW (ext : Ext) (n : Nat) (tag a0 a1 a2 a3 : UInt64) :
    linkAt ext (n + 1) "l_LeanOS_SpawnAllocatorWords_commandErrorW" [tag, a0, a1, a2, a3] =
      some (commandErrorW tag a0 a1 a2 a3) :=
  (linkAt_helper ext n _ _ _ (by helper_lookup)).trans (commandErrorWC_refines _ tag a0 a1 a2 a3)

theorem nextMemoryC_refines (ext : Ext) (slot w2 tag a0 current : UInt64) :
    callWith ext nextMemoryC [slot, w2, tag, a0, current] =
      some (nextMemory slot w2 tag a0 current) := by
  apply callWith_of_tree ext _ nextMemoryC rfl
  csym_refine [nextMemory]

theorem link_nextMemory (ext : Ext) (n : Nat) (slot w2 tag a0 current : UInt64) :
    linkAt ext (n + 1) "l_LeanOS_SpawnAllocatorWords_nextMemory" [slot, w2, tag, a0, current] =
      some (nextMemory slot w2 tag a0 current) :=
  (linkAt_helper ext n _ _ _ (by helper_lookup)).trans
    (nextMemoryC_refines _ slot w2 tag a0 current)

theorem syscallTagC_refines (ext : Ext) (number : UInt64) :
    callWith ext syscallTagC [number] = some (syscallTag number) := by
  apply callWith_of_tree ext _ syscallTagC rfl
  csym_refine [syscallTag]

theorem link_syscallTag (ext : Ext) (n : Nat) (number : UInt64) :
    linkAt ext (n + 1) "l_LeanOS_SpawnAllocatorBoot_syscallTag" [number] =
      some (syscallTag number) :=
  (linkAt_helper ext n _ _ _ (by helper_lookup)).trans (syscallTagC_refines _ number)

theorem registersCanonicalC_refines (ext : Ext) (tag rbx rcx rdx : UInt64) :
    callWith ext registersCanonicalC [tag, rbx, rcx, rdx] =
      some (boolWord (registersCanonical tag rbx rcx rdx)) := by
  apply callWith_of_tree_bool ext _ registersCanonicalC rfl rfl
  csym_refine [registersCanonical]

theorem link_registersCanonical (ext : Ext) (n : Nat) (tag rbx rcx rdx : UInt64) :
    linkAt ext (n + 1) "l_LeanOS_SpawnAllocatorBoot_registersCanonical" [tag, rbx, rcx, rdx] =
      some (boolWord (registersCanonical tag rbx rcx rdx)) :=
  (linkAt_helper ext n _ _ _ (by helper_lookup)).trans
    (registersCanonicalC_refines _ tag rbx rcx rdx)

theorem replyOfC_refines (ext : Ext) (status : UInt64) :
    callWith ext replyOfC [status] = some (replyOf status) := by
  apply callWith_of_tree ext _ replyOfC rfl
  csym_refine [replyOf]

theorem link_replyOf (ext : Ext) (n : Nat) (status : UInt64) :
    linkAt ext (n + 1) "l_LeanOS_SpawnAllocatorBoot_replyOf" [status] = some (replyOf status) :=
  (linkAt_helper ext n _ _ _ (by helper_lookup)).trans (replyOfC_refines _ status)

theorem wordAtC_refines (ext : Ext) (index w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f : UInt64) :
    callWith ext wordAtC [index, w0, w1, w2, w3, w4, w5, c0, c1, c2, c3, m2, m3, f] =
      some (wordAt index w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f) := by
  apply callWith_of_tree ext _ wordAtC rfl
  csym_refine [wordAt]

theorem link_wordAt (ext : Ext) (n : Nat) (index w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f : UInt64) :
    linkAt ext (n + 1) "l_LeanOS_SpawnAllocatorBoot_wordAt"
        [index, w0, w1, w2, w3, w4, w5, c0, c1, c2, c3, m2, m3, f] =
      some (wordAt index w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f) :=
  (linkAt_helper ext n _ _ _ (by helper_lookup)).trans
    (wordAtC_refines _ index w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f)

/-! ## Helpers one call deep -/

theorem canonicalC_refines (ext : Ext) (n : Nat) (w4 c0 c1 c2 c3 f : UInt64) :
    callWith (linkAt ext (n + 1)) canonicalC [w4, c0, c1, c2, c3, f] =
      some (boolWord (canonical w4 c0 c1 c2 c3 f)) := by
  apply callWith_of_tree_bool _ _ canonicalC rfl rfl
  csym_refine [link_childCanonical, link_chargeOf, canonical]

theorem link_canonical (ext : Ext) (n : Nat) (w4 c0 c1 c2 c3 f : UInt64) :
    linkAt ext (n + 2) "l_LeanOS_SpawnAllocatorWords_canonical" [w4, c0, c1, c2, c3, f] =
      some (boolWord (canonical w4 c0 c1 c2 c3 f)) :=
  (linkAt_helper ext (n + 1) _ _ _ (by helper_lookup)).trans
    (canonicalC_refines ext n w4 c0 c1 c2 c3 f)

theorem childCountWC_refines (ext : Ext) (n : Nat) (c0 c1 c2 c3 : UInt64) :
    callWith (linkAt ext (n + 1)) childCountWC [c0, c1, c2, c3] =
      some (childCountW c0 c1 c2 c3) := by
  apply callWith_of_tree _ _ childCountWC rfl
  csym_refine [link_occupied, childCountW]

theorem link_childCountW (ext : Ext) (n : Nat) (c0 c1 c2 c3 : UInt64) :
    linkAt ext (n + 2) "l_LeanOS_SpawnAllocatorWords_childCountW" [c0, c1, c2, c3] =
      some (childCountW c0 c1 c2 c3) :=
  (linkAt_helper ext (n + 1) _ _ _ (by helper_lookup)).trans
    (childCountWC_refines ext n c0 c1 c2 c3)

theorem availableWC_refines (ext : Ext) (n : Nat) (f m2 m3 : UInt64) :
    callWith (linkAt ext (n + 1)) availableWC [f, m2, m3] = some (availableW f m2 m3) := by
  apply callWith_of_tree _ _ availableWC rfl
  csym_refine [link_occupied, link_parentFramesW, availableW]

theorem link_availableW (ext : Ext) (n : Nat) (f m2 m3 : UInt64) :
    linkAt ext (n + 2) "l_LeanOS_SpawnAllocatorWords_availableW" [f, m2, m3] =
      some (availableW f m2 m3) :=
  (linkAt_helper ext (n + 1) _ _ _ (by helper_lookup)).trans (availableWC_refines ext n f m2 m3)

theorem resolveEndpointWC_refines (ext : Ext) (n : Nat) (m2 m3 word : UInt64) :
    callWith (linkAt ext (n + 1)) resolveEndpointWC [m2, m3, word] =
      some (resolveEndpointW m2 m3 word) := by
  apply callWith_of_tree _ _ resolveEndpointWC rfl
  csym_refine [link_memoryWordAt, resolveEndpointW, generationLimit]

theorem link_resolveEndpointW (ext : Ext) (n : Nat) (m2 m3 word : UInt64) :
    linkAt ext (n + 2) "l_LeanOS_SpawnAllocatorWords_resolveEndpointW" [m2, m3, word] =
      some (resolveEndpointW m2 m3 word) :=
  (linkAt_helper ext (n + 1) _ _ _ (by helper_lookup)).trans
    (resolveEndpointWC_refines ext n m2 m3 word)

theorem resolveControlWC_refines (ext : Ext) (n : Nat) (c0 c1 c2 c3 word : UInt64) :
    callWith (linkAt ext (n + 1)) resolveControlWC [c0, c1, c2, c3, word] =
      some (resolveControlW c0 c1 c2 c3 word) := by
  apply callWith_of_tree _ _ resolveControlWC rfl
  csym_refine [link_childWordAt, link_generationOf, resolveControlW, generationLimit]

theorem link_resolveControlW (ext : Ext) (n : Nat) (c0 c1 c2 c3 word : UInt64) :
    linkAt ext (n + 2) "l_LeanOS_SpawnAllocatorWords_resolveControlW" [c0, c1, c2, c3, word] =
      some (resolveControlW c0 c1 c2 c3 word) :=
  (linkAt_helper ext (n + 1) _ _ _ (by helper_lookup)).trans
    (resolveControlWC_refines ext n c0 c1 c2 c3 word)

theorem nextChildC_refines (ext : Ext) (n : Nat)
    (index w3 c0 c1 c2 c3 tag a0 a1 current : UInt64) :
    callWith (linkAt ext (n + 1)) nextChildC [index, w3, c0, c1, c2, c3, tag, a0, a1, current] =
      some (nextChild index w3 c0 c1 c2 c3 tag a0 a1 current) := by
  apply callWith_of_tree _ _ nextChildC rfl
  csym_refine [link_freeSlotW, nextChild]

theorem link_nextChild (ext : Ext) (n : Nat) (index w3 c0 c1 c2 c3 tag a0 a1 current : UInt64) :
    linkAt ext (n + 2) "l_LeanOS_SpawnAllocatorWords_nextChild"
        [index, w3, c0, c1, c2, c3, tag, a0, a1, current] =
      some (nextChild index w3 c0 c1 c2 c3 tag a0 a1 current) :=
  (linkAt_helper ext (n + 1) _ _ _ (by helper_lookup)).trans
    (nextChildC_refines ext n index w3 c0 c1 c2 c3 tag a0 a1 current)

theorem nextFramesC_refines (ext : Ext) (n : Nat) (c0 c1 c2 c3 f tag a0 a1 : UInt64) :
    callWith (linkAt ext (n + 1)) nextFramesC [c0, c1, c2, c3, f, tag, a0, a1] =
      some (nextFrames c0 c1 c2 c3 f tag a0 a1) := by
  apply callWith_of_tree _ _ nextFramesC rfl
  csym_refine [link_budgetW, link_parentFramesW, link_chargeOf, link_childWordAt, nextFrames]

theorem link_nextFrames (ext : Ext) (n : Nat) (c0 c1 c2 c3 f tag a0 a1 : UInt64) :
    linkAt ext (n + 2) "l_LeanOS_SpawnAllocatorWords_nextFrames" [c0, c1, c2, c3, f, tag, a0, a1] =
      some (nextFrames c0 c1 c2 c3 f tag a0 a1) :=
  (linkAt_helper ext (n + 1) _ _ _ (by helper_lookup)).trans
    (nextFramesC_refines ext n c0 c1 c2 c3 f tag a0 a1)

/-! ## Helpers two to four calls deep -/

theorem decideWC_refines (ext : Ext) (n : Nat)
    (w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2 : UInt64) :
    callWith (linkAt ext (n + 2)) decideWC
        [w0, w1, w2, w3, w4, w5, c0, c1, c2, c3, m2, m3, f, tag, a0, a1, a2] =
      some (decideW w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2) := by
  apply callWith_of_tree _ _ decideWC rfl
  csym_refine [link_availableW, link_budgetW, link_capabilityExhaustedW, link_childCountW,
    link_controlAvailableW, link_freeSlotW, link_identityExhaustedW, link_memoryWordAt,
    link_resolveControlW, link_resolveEndpointW, link_rightsValidW, decideW, uncoveredWord,
    maxWord]

theorem link_decideW (ext : Ext) (n : Nat)
    (w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2 : UInt64) :
    linkAt ext (n + 3) "l_LeanOS_SpawnAllocatorWords_decideW"
        [w0, w1, w2, w3, w4, w5, c0, c1, c2, c3, m2, m3, f, tag, a0, a1, a2] =
      some (decideW w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2) :=
  (linkAt_helper ext (n + 2) _ _ _ (by helper_lookup)).trans
    (decideWC_refines ext n w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2)

theorem refusalC_refines (ext : Ext) (n : Nat)
    (w4 c0 c1 c2 c3 f actor number rbx rcx rdx : UInt64) :
    callWith (linkAt ext (n + 2)) refusalC [w4, c0, c1, c2, c3, f, actor, number, rbx, rcx, rdx] =
      some (refusal w4 c0 c1 c2 c3 f actor number rbx rcx rdx) := by
  apply callWith_of_tree _ _ refusalC rfl
  csym_refine [link_canonical, link_syscallTag, link_registersCanonical, refusal]

theorem link_refusal (ext : Ext) (n : Nat) (w4 c0 c1 c2 c3 f actor number rbx rcx rdx : UInt64) :
    linkAt ext (n + 3) "l_LeanOS_SpawnAllocatorBoot_refusal"
        [w4, c0, c1, c2, c3, f, actor, number, rbx, rcx, rdx] =
      some (refusal w4 c0 c1 c2 c3 f actor number rbx rcx rdx) :=
  (linkAt_helper ext (n + 2) _ _ _ (by helper_lookup)).trans
    (refusalC_refines ext n w4 c0 c1 c2 c3 f actor number rbx rcx rdx)

theorem stepReplyC_refines (ext : Ext) (n : Nat)
    (w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2 a3 : UInt64) :
    callWith (linkAt ext (n + 3)) stepReplyC
        [w0, w1, w2, w3, w4, w5, c0, c1, c2, c3, m2, m3, f, tag, a0, a1, a2, a3] =
      some (stepReply w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2 a3) := by
  apply callWith_of_tree _ _ stepReplyC rfl
  csym_refine [link_canonical, link_commandErrorW, link_decideW, stepReply, stateErrorWord]

theorem link_stepReply (ext : Ext) (n : Nat)
    (w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2 a3 : UInt64) :
    linkAt ext (n + 4) "l_LeanOS_SpawnAllocatorWords_stepReply"
        [w0, w1, w2, w3, w4, w5, c0, c1, c2, c3, m2, m3, f, tag, a0, a1, a2, a3] =
      some (stepReply w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2 a3) :=
  (linkAt_helper ext (n + 3) _ _ _ (by helper_lookup)).trans
    (stepReplyC_refines ext n w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2 a3)

theorem stepValueC_refines (ext : Ext) (n : Nat)
    (w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2 a3 : UInt64) :
    callWith (linkAt ext (n + 4)) stepValueC
        [w0, w1, w2, w3, w4, w5, c0, c1, c2, c3, m2, m3, f, tag, a0, a1, a2, a3] =
      some (stepValue w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2 a3) := by
  apply callWith_of_tree _ _ stepValueC rfl
  csym_refine [link_stepReply, link_freeSlotW, link_chargeOf, link_childWordAt, stepValue]

theorem link_stepValue (ext : Ext) (n : Nat)
    (w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2 a3 : UInt64) :
    linkAt ext (n + 5) "l_LeanOS_SpawnAllocatorWords_stepValue"
        [w0, w1, w2, w3, w4, w5, c0, c1, c2, c3, m2, m3, f, tag, a0, a1, a2, a3] =
      some (stepValue w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2 a3) :=
  (linkAt_helper ext (n + 4) _ _ _ (by helper_lookup)).trans
    (stepValueC_refines ext n w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2 a3)

theorem stepNextWordC_refines (ext : Ext) (n : Nat)
    (index w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2 a3 : UInt64) :
    callWith (linkAt ext (n + 4)) stepNextWordC
        [index, w0, w1, w2, w3, w4, w5, c0, c1, c2, c3, m2, m3, f, tag, a0, a1, a2, a3] =
      some (stepNextWord index w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2 a3) := by
  apply callWith_of_tree _ _ stepNextWordC rfl
  csym_refine [link_stepReply, link_nextChild, link_nextMemory, link_nextFrames, stepNextWord]

theorem link_stepNextWord (ext : Ext) (n : Nat)
    (index w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2 a3 : UInt64) :
    linkAt ext (n + 5) "l_LeanOS_SpawnAllocatorWords_stepNextWord"
        [index, w0, w1, w2, w3, w4, w5, c0, c1, c2, c3, m2, m3, f, tag, a0, a1, a2, a3] =
      some (stepNextWord index w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2 a3) :=
  (linkAt_helper ext (n + 4) _ _ _ (by helper_lookup)).trans
    (stepNextWordC_refines ext n index w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2 a3)

/-! ## The seven exports

Rung 3: with the emitted helpers linked as the emitted C calls them, each
export computes its Lean definition on every input. -/

theorem seedC_refines (ext : Ext) (index : UInt64) :
    callWith (link ext) seedC [index] = some (seed index) := by
  apply callWith_of_tree _ _ seedC rfl
  csym_refine [link, link_wordAt, seed]

theorem syscallC_refines (ext : Ext)
    (w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f actor number rbx rcx rdx : UInt64) :
    callWith (link ext) syscallC
        [w0, w1, w2, w3, w4, w5, c0, c1, c2, c3, m2, m3, f, actor, number, rbx, rcx, rdx] =
      some (syscall w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f actor number rbx rcx rdx) := by
  apply callWith_of_tree _ _ syscallC rfl
  csym_refine [link, link_refusal, link_replyOf, link_syscallTag, link_stepReply, syscall]

theorem syscallValueC_refines (ext : Ext)
    (w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f actor number rbx rcx rdx : UInt64) :
    callWith (link ext) syscallValueC
        [w0, w1, w2, w3, w4, w5, c0, c1, c2, c3, m2, m3, f, actor, number, rbx, rcx, rdx] =
      some (syscallValue w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f actor number rbx rcx rdx) := by
  apply callWith_of_tree _ _ syscallValueC rfl
  csym_refine [link, link_refusal, link_syscallTag, link_stepValue, syscallValue]

theorem syscallNextC_refines (ext : Ext)
    (index w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f actor number rbx rcx rdx : UInt64) :
    callWith (link ext) syscallNextC
        [index, w0, w1, w2, w3, w4, w5, c0, c1, c2, c3, m2, m3, f, actor, number, rbx, rcx, rdx] =
      some (syscallNext index w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f actor number rbx rcx rdx) := by
  apply callWith_of_tree _ _ syscallNextC rfl
  csym_refine [link, link_refusal, link_syscallTag, link_wordAt, link_stepNextWord, syscallNext]

theorem kernelC_refines (ext : Ext)
    (w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2 a3 : UInt64) :
    callWith (link ext) kernelC
        [w0, w1, w2, w3, w4, w5, c0, c1, c2, c3, m2, m3, f, tag, a0, a1, a2, a3] =
      some (kernel w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2 a3) := by
  apply callWith_of_tree _ _ kernelC rfl
  csym_refine [link, link_stepReply, kernel]

theorem kernelValueC_refines (ext : Ext)
    (w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2 a3 : UInt64) :
    callWith (link ext) kernelValueC
        [w0, w1, w2, w3, w4, w5, c0, c1, c2, c3, m2, m3, f, tag, a0, a1, a2, a3] =
      some (kernelValue w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2 a3) := by
  apply callWith_of_tree _ _ kernelValueC rfl
  csym_refine [link, link_stepValue, kernelValue]

theorem kernelNextC_refines (ext : Ext)
    (index w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2 a3 : UInt64) :
    callWith (link ext) kernelNextC
        [index, w0, w1, w2, w3, w4, w5, c0, c1, c2, c3, m2, m3, f, tag, a0, a1, a2, a3] =
      some (kernelNext index w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f tag a0 a1 a2 a3) := by
  apply callWith_of_tree _ _ kernelNextC rfl
  csym_refine [link, link_stepNextWord, kernelNext]

/-! ## The exports compute the specification

The kernel passes the thirteen state words of its record (`Words.toList`)
and the registers or command words, and asks the `_next` export for each of
the thirteen successor words. -/

/-- A syscall through the emitted C, as the kernel makes it: the reply, the
value and the thirteen successor words. -/
def syscallWordsC (ext : Ext) (words : Words) (actor number rbx rcx rdx : UInt64) :
    Option (UInt64 × UInt64 × Words) := do
  let input := words.toList ++ [actor, number, rbx, rcx, rdx]
  let after := fun index : UInt64 => callWith (link ext) syscallNextC (index :: input)
  pure (← callWith (link ext) syscallC input, ← callWith (link ext) syscallValueC input,
    ⟨← after 0, ← after 1, ← after 2, ← after 3, ← after 4, ← after 5, ← after 6, ← after 7,
      ← after 8, ← after 9, ← after 10, ← after 11, ← after 12⟩)

/-- A kernel command through the emitted C: the status, the value and the
thirteen successor words. -/
def kernelWordsC (ext : Ext) (words : Words) (command : CompositeDispatcher.CommandWords) :
    Option (UInt64 × UInt64 × Words) := do
  let input := words.toList ++
    [command.tag, command.arg0, command.arg1, command.arg2, command.arg3]
  let after := fun index : UInt64 => callWith (link ext) kernelNextC (index :: input)
  pure (← callWith (link ext) kernelC input, ← callWith (link ext) kernelValueC input,
    ⟨← after 0, ← after 1, ← after 2, ← after 3, ← after 4, ← after 5, ← after 6, ← after 7,
      ← after 8, ← after 9, ← after 10, ← after 11, ← after 12⟩)

/-- The seed's thirteen words through the emitted C. -/
def seedWordsC (ext : Ext) : Option Words := do
  let at_ := fun index : UInt64 => callWith (link ext) seedC [index]
  pure ⟨← at_ 0, ← at_ 1, ← at_ 2, ← at_ 3, ← at_ 4, ← at_ 5, ← at_ 6, ← at_ 7, ← at_ 8,
    ← at_ 9, ← at_ 10, ← at_ 11, ← at_ 12⟩

/-- **The emitted syscall exports compute the specification on every input**:
the refusal words in order, then decode, `SpawnAllocator.step` and encode. -/
theorem syscallWordsC_spec (ext : Ext) (words : Words) (actor number rbx rcx rdx : UInt64) :
    syscallWordsC ext words actor number rbx rcx rdx =
      some (specSyscall words actor number rbx rcx rdx) := by
  rw [← syscall_spec]
  simp only [syscallWordsC, Words.toList, List.cons_append, List.nil_append, syscallC_refines,
    syscallValueC_refines, syscallNextC_refines, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some]
  rfl

/-- **The emitted kernel-command exports compute `specStep` on every
input.** -/
theorem kernelWordsC_spec (ext : Ext) (words : Words)
    (command : CompositeDispatcher.CommandWords) :
    kernelWordsC ext words command =
      some ((specStep words command).2.1, (specStep words command).2.2,
        (specStep words command).1) := by
  rw [← kernel_spec]
  simp only [kernelWordsC, Words.toList, List.cons_append, List.nil_append, kernelC_refines,
    kernelValueC_refines, kernelNextC_refines, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some]
  rfl

/-- **The emitted seed export gives the seed's thirteen words.** -/
theorem seedWordsC_eq (ext : Ext) : seedWordsC ext = some seedWords := by
  simp only [seedWordsC, seedC_refines, Option.pure_def, Option.bind_eq_bind, Option.bind_some]
  rfl

/-- **The emitted seed export gives the words of the family seed**, for every
boot plan. Through `seed_refines` this composition inherits that theorem's
trust in `native_decide` (the q35 platform it boots on); `seedWordsC_eq`
does not. -/
theorem seedWordsC_spec (ext : Ext) (plan : BootPageTablePlan.Plan) :
    seedWordsC ext =
      some (encode (SpawnAllocator.abstraction (SpawnFamily.seedState plan .main))) := by
  rw [seedWordsC_eq, (seed_refines plan).1]

end LeanOS.Refinement.SpawnAllocatorC
