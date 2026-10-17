import LeanOS.Refinement.CSymbolic
import LeanOS.DhcpSubject

/-!
# Rung 3 for `leanos_frame_port_check` (issue #570)

`framePortCheckC` is the C function the pinned Lean toolchain emits for the
`@[export leanos_frame_port_check]` witness of #564 (with the `@[inline]`
decision `framePortDecide` inlined into it), extracted from the generated
`DhcpSubject.c` by `scripts/extract-generated-c.py`. The build re-runs the
extractor and fails if the emitted C no longer matches this AST.

Under the C-subset semantics of `LeanOS.Refinement.CSubset` it calls nothing,
and on every six words it returns exactly `DhcpSubject.framePortCheck`, and
so, through `framePortCheck_fetch` and `framePortCheck_send`, accepts a copy
exactly when the model's `fetchOk`/`sendOk` does. The theorems do not cover
the calling convention, the compiler, the linker, the boot path or QEMU
(ADR 0029).
-/
namespace LeanOS.Refinement.DhcpSubjectC

open LeanOS.Refinement.CSubset LeanOS.Refinement.CSymbolic LeanOS.DhcpSubject

-- BEGIN GENERATED AST leanos_frame_port_check
def framePortCheckC : Func :=
  { params := [("v_subject_743_", .u64), ("v_req_744_", .u64), ("v_addr_745_", .u64), ("v_len_746_", .u64), ("v_base_747_", .u64), ("v_limit_748_", .u64)]
    result := .u64
    body := [
      (.decl .u8 "v___y_750_"),
      (.decl .u64 "v___y_763_"),
      (.decl .u8 "v___y_764_"),
      (.decl .u64 "v___y_770_"),
      (.decl .u8 "v___y_771_"),
      (.decl .u64 "v___x_781_"),
      (.decl .u64 "v___x_782_"),
      (.decl .u64 "v___x_783_"),
      (.decl .u64 "v___x_784_"),
      (.decl .u64 "v___x_785_"),
      (.decl .u64 "v___x_786_"),
      (.decl .u64 "v___x_787_"),
      (.decl .u64 "v___x_788_"),
      (.decl .u64 "v___x_789_"),
      (.decl .u64 "v___x_790_"),
      (.decl .u64 "v___x_791_"),
      (.decl .u64 "v___x_792_"),
      (.decl .u8 "v___x_805_"),
      (.assign "v___x_781_" (.lit 255)),
      (.assign "v___x_782_" (.bin .land (.var "v_req_744_") (.var "v___x_781_"))),
      (.assign "v___x_783_" (.lit 8)),
      (.assign "v___x_784_" (.bin .shiftRight (.var "v_req_744_") (.var "v___x_783_"))),
      (.assign "v___x_785_" (.bin .land (.var "v___x_784_") (.var "v___x_781_"))),
      (.assign "v___x_786_" (.lit 16)),
      (.assign "v___x_787_" (.bin .shiftRight (.var "v_req_744_") (.var "v___x_786_"))),
      (.assign "v___x_788_" (.bin .land (.var "v___x_787_") (.var "v___x_781_"))),
      (.assign "v___x_789_" (.lit 24)),
      (.assign "v___x_790_" (.bin .shiftRight (.var "v_req_744_") (.var "v___x_789_"))),
      (.assign "v___x_791_" (.bin .land (.var "v___x_790_") (.var "v___x_781_"))),
      (.assign "v___x_792_" (.lit 2)),
      (.assign "v___x_805_" (.bin .decEq (.var "v_subject_743_") (.var "v___x_792_"))),
      (.ifZero "v___x_805_" [(.decl .u64 "v___x_806_"), (.decl .u8 "v___x_807_"), (.assign "v___x_806_" (.lit 3)), (.assign "v___x_807_" (.bin .decEq (.var "v_subject_743_") (.var "v___x_806_"))), (.ifZero "v___x_807_" [(.decl .u64 "v___x_808_"), (.assign "v___x_808_" (.lit 1)), (.ret (.var "v___x_808_"))] [(.goto "v___jp_793_")])] [(.goto "v___jp_793_")]),
      (.block "v___jp_749_" [(.ifZero "v___y_750_" [(.decl .u64 "v___x_751_"), (.assign "v___x_751_" (.lit 6)), (.ret (.var "v___x_751_"))] [(.decl .u64 "v___x_752_"), (.decl .u8 "v___x_753_"), (.assign "v___x_752_" (.bin .sub (.var "v_limit_748_") (.var "v_addr_745_"))), (.assign "v___x_753_" (.bin .decLe (.var "v_len_746_") (.var "v___x_752_"))), (.ifZero "v___x_753_" [(.decl .u64 "v___x_754_"), (.assign "v___x_754_" (.lit 6)), (.ret (.var "v___x_754_"))] [(.decl .u64 "v___x_755_"), (.assign "v___x_755_" (.lit 0)), (.ret (.var "v___x_755_"))])])]),
      (.block "v___jp_756_" [(.decl .u64 "v___x_757_"), (.decl .u8 "v___x_758_"), (.assign "v___x_757_" (.lit 1514)), (.assign "v___x_758_" (.bin .decLt (.var "v___x_757_") (.var "v_len_746_"))), (.ifZero "v___x_758_" [(.decl .u8 "v___x_759_"), (.decl .u8 "v___x_760_"), (.assign "v___x_759_" (.bin .decLe (.var "v_addr_745_") (.var "v_limit_748_"))), (.assign "v___x_760_" (.bin .decLe (.var "v_base_747_") (.var "v_addr_745_"))), (.ifZero "v___x_760_" [(.assign "v___y_750_" (.var "v___x_760_")), (.goto "v___jp_749_")] [(.assign "v___y_750_" (.var "v___x_759_")), (.goto "v___jp_749_")])] [(.decl .u64 "v___x_761_"), (.assign "v___x_761_" (.lit 5)), (.ret (.var "v___x_761_"))])]),
      (.block "v___jp_762_" [(.ifZero "v___y_764_" [(.decl .u64 "v___x_765_"), (.assign "v___x_765_" (.lit 6)), (.ret (.var "v___x_765_"))] [(.decl .u64 "v___x_766_"), (.decl .u8 "v___x_767_"), (.assign "v___x_766_" (.bin .sub (.var "v_limit_748_") (.var "v_addr_745_"))), (.assign "v___x_767_" (.bin .decLe (.var "v_len_746_") (.var "v___x_766_"))), (.ifZero "v___x_767_" [(.decl .u64 "v___x_768_"), (.assign "v___x_768_" (.lit 6)), (.ret (.var "v___x_768_"))] [(.ret (.var "v___y_763_"))])])]),
      (.block "v___jp_769_" [(.ifZero "v___y_771_" [(.decl .u64 "v___x_772_"), (.decl .u8 "v___x_773_"), (.assign "v___x_772_" (.lit 14)), (.assign "v___x_773_" (.bin .decLt (.var "v_len_746_") (.var "v___x_772_"))), (.ifZero "v___x_773_" [(.decl .u64 "v___x_774_"), (.decl .u8 "v___x_775_"), (.assign "v___x_774_" (.lit 1514)), (.assign "v___x_775_" (.bin .decLt (.var "v___x_774_") (.var "v_len_746_"))), (.ifZero "v___x_775_" [(.decl .u8 "v___x_776_"), (.decl .u8 "v___x_777_"), (.assign "v___x_776_" (.bin .decLe (.var "v_addr_745_") (.var "v_limit_748_"))), (.assign "v___x_777_" (.bin .decLe (.var "v_base_747_") (.var "v_addr_745_"))), (.ifZero "v___x_777_" [(.assign "v___y_763_" (.var "v___y_770_")), (.assign "v___y_764_" (.var "v___x_777_")), (.goto "v___jp_762_")] [(.assign "v___y_763_" (.var "v___y_770_")), (.assign "v___y_764_" (.var "v___x_776_")), (.goto "v___jp_762_")])] [(.decl .u64 "v___x_778_"), (.assign "v___x_778_" (.lit 5)), (.ret (.var "v___x_778_"))])] [(.decl .u64 "v___x_779_"), (.assign "v___x_779_" (.lit 5)), (.ret (.var "v___x_779_"))])] [(.decl .u64 "v___x_780_"), (.assign "v___x_780_" (.lit 4)), (.ret (.var "v___x_780_"))])]),
      (.block "v___jp_793_" [(.decl .u8 "v___x_794_"), (.assign "v___x_794_" (.bin .decEq (.var "v___x_791_") (.var "v_subject_743_"))), (.ifZero "v___x_794_" [(.ret (.var "v___x_792_"))] [(.decl .u8 "v___x_795_"), (.assign "v___x_795_" (.bin .decEq (.var "v___x_788_") (.var "v_subject_743_"))), (.ifZero "v___x_795_" [(.decl .u64 "v___x_796_"), (.assign "v___x_796_" (.lit 3)), (.ret (.var "v___x_796_"))] [(.decl .u64 "v___x_797_"), (.decl .u8 "v___x_798_"), (.assign "v___x_797_" (.lit 1)), (.assign "v___x_798_" (.bin .decEq (.var "v___x_782_") (.var "v___x_797_"))), (.ifZero "v___x_798_" [(.decl .u8 "v___x_799_"), (.assign "v___x_799_" (.bin .decEq (.var "v___x_782_") (.var "v___x_792_"))), (.ifZero "v___x_799_" [(.decl .u64 "v___x_800_"), (.assign "v___x_800_" (.lit 7)), (.ret (.var "v___x_800_"))] [(.decl .u64 "v___x_801_"), (.decl .u8 "v___x_802_"), (.assign "v___x_801_" (.lit 0)), (.assign "v___x_802_" (.bin .decEq (.var "v___x_785_") (.var "v___x_801_"))), (.ifZero "v___x_802_" [(.assign "v___y_770_" (.var "v___x_801_")), (.assign "v___y_771_" (.var "v___x_799_")), (.goto "v___jp_769_")] [(.assign "v___y_770_" (.var "v___x_801_")), (.assign "v___y_771_" (.var "v___x_798_")), (.goto "v___jp_769_")])])] [(.decl .u8 "v___x_803_"), (.assign "v___x_803_" (.bin .decEq (.var "v___x_785_") (.var "v___x_797_"))), (.ifZero "v___x_803_" [(.ifZero "v___x_798_" [(.goto "v___jp_756_")] [(.decl .u64 "v___x_804_"), (.assign "v___x_804_" (.lit 4)), (.ret (.var "v___x_804_"))])] [(.goto "v___jp_756_")])])])])])] }
-- END GENERATED AST


/-- Rung 3: the emitted C of `leanos_frame_port_check` computes the Lean
witness on every six words. -/
theorem framePortCheckC_refines (subject req addr len base limit : UInt64) :
    call framePortCheckC [subject, req, addr, len, base, limit] =
      some (framePortCheck subject req addr len base limit) := by
  apply callWith_of_tree noCalls _ framePortCheckC rfl
  csym_refine [framePortDecide, NetworkSubject.rangeOk]

/-- The emitted C admits each subject only for a window labelled its own:
whatever the request, an accepted copy names the caller as the window's
owner and as the port the endpoint serves. -/
theorem framePortCheckC_own_window (subject req addr len base limit : UInt64)
    (h : call framePortCheckC [subject, req, addr, len, base, limit] = some 0) :
    (subject = 2 ∨ subject = 3) ∧ (req >>> 24) &&& 0xff = subject ∧
      (req >>> 16) &&& 0xff = subject ∧
      NetworkSubject.Window.covers ⟨base.toNat, limit.toNat⟩ addr.toNat len.toNat = true := by
  rw [framePortCheckC_refines, Option.some_inj] at h
  exact framePortCheck_own_window subject req addr len base limit h

/-- For a port holder `who` whose window is `[base, limit)`, in a reachable
state, the emitted C accepts a fetch exactly when the model's `fetchOk`
does. -/
theorem framePortCheckC_fetch (p : Ports) (s : State) (who : Nat) (addr base limit : UInt64)
    (hwho : who = dhcp ∨ who = echo) (hw : p.window who = some ⟨base.toNat, limit.toNat⟩)
    (hlen : s.rx.length < 2 ^ 64) (hroute : Routed s) :
    call framePortCheckC [who.toUInt64,
        request NetworkSubject.opFetch s.rxPending s.route.toUInt64 who.toUInt64, addr,
        s.rx.length.toUInt64, base, limit] = some 0 ↔
      fetchOk p s who addr.toNat = true := by
  rw [framePortCheckC_refines, Option.some_inj]
  exact framePortCheck_fetch p s who addr base limit hwho hw hlen hroute

/-- For a port holder `who` whose window is `[base, limit)`, in a reachable
state, the emitted C accepts a send exactly when the model's `sendOk` does. -/
theorem framePortCheckC_send (p : Ports) (s : State) (who : Nat) (addr len base limit : UInt64)
    (hwho : who = dhcp ∨ who = echo) (hw : p.window who = some ⟨base.toNat, limit.toNat⟩)
    (hroute : Routed s) :
    call framePortCheckC [who.toUInt64,
        request NetworkSubject.opSend s.txPending s.route.toUInt64 who.toUInt64, addr, len,
        base, limit] = some 0 ↔
      sendOk p s who addr.toNat len.toNat = true := by
  rw [framePortCheckC_refines, Option.some_inj]
  exact framePortCheck_send p s who addr len base limit hwho hw hroute

/-- The emitted C refuses every subject holding no port. -/
theorem framePortCheckC_nonholder (subject req addr len base limit : UInt64)
    (h2 : subject ≠ 2) (h3 : subject ≠ 3) :
    call framePortCheckC [subject, req, addr, len, base, limit] = some 1 := by
  rw [framePortCheckC_refines, framePortCheck_nonholder subject req addr len base limit h2 h3]

end LeanOS.Refinement.DhcpSubjectC
