(* Law enumeration_exact: main's uninitialized struct device, field by field (LawSplit for its contents). *)
Require Import VST.floyd.proofauto.
Require Import LeanosEnum.harness.enumeration_exact.code.
Require Import LeanosEnum.proof.LawProg LeanosEnum.proof.LawSpecs LeanosEnum.proof.LawSplit LeanosEnum.proof.LawOut.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Lemma dev_split_: forall ctx,
  data_at_ Tsh t_device ctx =
  (field_at_ Tsh t_device (DOT _next) ctx * field_at_ Tsh t_device (DOT _word) ctx *
   field_at_ Tsh t_device (DOT _found) ctx * field_at_ Tsh t_device (DOT _stopped) ctx *
   field_at_ Tsh t_device (DOT _failed) ctx * field_at_ Tsh t_device (DOT _reads) ctx *
   field_at Tsh t_device (DOT _last_bus) Vundef ctx * field_at Tsh t_device (DOT _last_device) Vundef ctx *
   field_at Tsh t_device (DOT _last_function) Vundef ctx * field_at Tsh t_device (DOT _last_offset) Vundef ctx *
   field_at Tsh t_device (DOT _seen) seen_undef ctx)%logic.
Proof.
  intros. change (data_at_ Tsh t_device ctx) with (data_at Tsh t_device (default_val t_device) ctx).
  unfold_data_at (data_at Tsh t_device (default_val t_device) ctx).
  unfold field_at_.
  rewrite !sepcon_assoc. reflexivity.
Qed.
