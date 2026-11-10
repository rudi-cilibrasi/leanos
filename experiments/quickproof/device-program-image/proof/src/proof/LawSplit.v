(* Law image_exact: the harness's structs as their fields (VST's unfold_data_at on them is slow, so the splits
   are proved once). *)
Require Import VST.floyd.proofauto.
Require Import LeanosDeviceProgramImage.harness.image_exact.code.
Require Import LeanosDeviceProgramImage.proof.Defs.
Require Import LeanosDeviceProgramImage.proof.LawProg LeanosDeviceProgramImage.proof.LawSpecs.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

(* struct wifi_policy with its fields as values. *)
Definition pol_vals (a1 a2 a3 a4 a5 a6 a7 a8: val) (ss: list val) (dc: val) (ds: list desc_t) : policy_t :=
  (a1, (a2, (a3, (a4, (a5, (a6, (a7, (a8, (ss, (dc, ds)))))))))).

Definition pol_fields (sh: share) (p: val) (a1 a2 a3 a4 a5 a6 a7 a8: val) (ss: list val) (dc: val)
    (ds: list desc_t) : mpred :=
  (field_at sh t_policy (DOT _present) a1 p * field_at sh t_policy (DOT _dma) a2 p *
   field_at sh t_policy (DOT _window) a3 p * spacer sh 12 16 p * field_at sh t_policy (DOT _cfg_read) a4 p *
   field_at sh t_policy (DOT _cfg_write) a5 p * field_at sh t_policy (DOT _cmd_clear) a6 p *
   field_at sh t_policy (DOT _cmd_set) a7 p * field_at sh t_policy (DOT _sink_count) a8 p *
   field_at sh t_policy (DOT _sinks) ss p * field_at sh t_policy (DOT _desc_count) dc p *
   field_at sh t_policy (DOT _descs) ds p)%logic.

Lemma pol_split: forall sh p a1 a2 a3 a4 a5 a6 a7 a8 ss dc ds,
  data_at sh t_policy (pol_vals a1 a2 a3 a4 a5 a6 a7 a8 ss dc ds) p = pol_fields sh p a1 a2 a3 a4 a5 a6 a7 a8 ss dc ds.
Proof.
  intros. unfold pol_vals, pol_fields. unfold_data_at (data_at _ _ _ p). rewrite !sepcon_assoc. reflexivity.
Qed.

Definition udesc : desc_t := (Vundef, (Vundef, (Vundef, Vundef))).

Lemma pol_default: default_val t_policy = pol_vals Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef
  (Zrepeat Vundef 8) Vundef (Zrepeat udesc 16).
Proof. reflexivity. Qed.

Lemma pol_val_vals: forall P, policy_val P =
  pol_vals (Vint (Int.repr (pl_present P))) (Vint (Int.repr (pl_dma P))) (Vint (Int.repr (pl_window P)))
    (Vlong (Int64.repr (pl_cfg_read P))) (Vlong (Int64.repr (pl_cfg_write P))) (Vint (Int.repr (pl_cmd_clear P)))
    (Vint (Int.repr (pl_cmd_set P))) (Vint (Int.repr (pl_sink_count P))) (words_val (pl_sinks P))
    (Vint (Int.repr (pl_desc_count P))) (map desc_val (pl_descs P)).
Proof. reflexivity. Qed.

Lemma pol_rep_vals: forall a1 a2 a3 a4 a5 a6 a7 a8 ss dc ds, policy_rep a1 a2 a3 a4 a5 a6 a7 a8 ss dc ds =
  pol_vals (Vint (Int.repr a1)) (Vint (Int.repr a2)) (Vint (Int.repr a3)) (Vlong (Int64.repr a4))
    (Vlong (Int64.repr a5)) (Vint (Int.repr a6)) (Vint (Int.repr a7)) (Vint (Int.repr a8)) ss
    (Vint (Int.repr dc)) ds.
Proof. reflexivity. Qed.

(* struct wifi_target. *)
Definition tg_fields (sh: share) (p: val) (a1 a2 a3 a4 a5 a6: val) : mpred :=
  (field_at sh t_target (DOT _bus) a1 p * field_at sh t_target (DOT _dev) a2 p *
   field_at sh t_target (DOT _fn) a3 p * field_at sh t_target (DOT _id) a4 p *
   field_at sh t_target (DOT _window) a5 p * field_at sh t_target (DOT _bar) a6 p)%logic.

Lemma tg_split: forall sh p a1 a2 a3 a4 a5 a6,
  data_at sh t_target (a1, (a2, (a3, (a4, (a5, a6))))) p = tg_fields sh p a1 a2 a3 a4 a5 a6.
Proof.
  intros. unfold tg_fields. unfold_data_at (data_at _ _ _ p). rewrite !sepcon_assoc. reflexivity.
Qed.
