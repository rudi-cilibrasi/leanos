(* The pieces of the proof of wifi_image_header (HdHead.v, HdTarget.v, HdV3.v, HdSinks.v, HdDescs.v): the
   context, the postcondition, the tails of the body each stage file proves, the arithmetic of the C's tests and
   the model's decode stage by stage. *)
Require Import VST.floyd.proofauto.
Require Import LeanosDeviceProgramImage.device_program.code.
Require Import LeanosDeviceProgramImage.proof.Specs.
Require Import LeanosDeviceProgramImage.proof.BodyLookup.
Require Import LeanosDeviceProgramImage.proof.BodyPolicy.
Require Import LeanosDeviceProgramImage.proof.BodyAdmit.
Require Import LeanosDeviceProgramImage.proof.BodyShape.
#[local] Existing Instance Specs.CS.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* The context, the postcondition and the tails.                          *)
(* ---------------------------------------------------------------------- *)

Definition Delta_hd : tycontext := func_tycontext f_wifi_image_header Vprog Gprog nil.

Definition Post_hd sh image bs tsh tp psh pp P0 hsh hp : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint
       (EX (tv : target_t) (pv : policy_t) (hv : val),
        PROP (header_post bs P0 tv pv hv)
        RETURN (Vint (Int.repr (header_status bs)))
        SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) image;
             data_at tsh t_target tv tp; data_at psh t_policy pv pp;
             data_at hsh tuint hv hp))%argsassert)
    (stackframe_of f_wifi_image_header).

Definition ret0 : statement := Sreturn (Some (Econst_int (Int.repr 0) tint)).

Definition hd_body : statement :=
  ltac:(let b := eval cbv delta [f_wifi_image_header] beta iota zeta in (fn_body f_wifi_image_header) in exact b).

(* From the version-2/3 test on (after the version-1 return). *)
Definition s_target : statement := ltac:(
  let b := eval cbv delta [hd_body] in hd_body in
  match b with context [Ssequence (Sifthenelse (Ebinop Oeq (Etempvar _version tuint)
                          (Econst_int (Int.repr 1) tint) tint) _ Sskip) ?rest] => exact rest end).

(* The version-3 part. *)
Definition s_v3 : statement := ltac:(
  let b := eval cbv delta [hd_body] in hd_body in
  match b with context [Sifthenelse (Ebinop Oeq (Etempvar _version tuint)
                          (Econst_int (Int.repr 3) tint) tint) ?v Sskip] => exact v end).

(* From the sink loop on. *)
Definition s_sinks : statement := ltac:(
  let b := eval cbv delta [hd_body] in hd_body in
  match b with context [Ssequence (Ssequence (Sset _i (Econst_int (Int.repr 0) tint)) ?l) ?rest] =>
    exact (Ssequence (Ssequence (Sset _i (Econst_int (Int.repr 0) tint)) l) rest) end).

(* The descriptor map. *)
Definition s_desc : statement := ltac:(
  let b := eval cbv delta [hd_body] in hd_body in
  match b with context [Sifthenelse (Ebinop Oand (Etempvar _flags tuint) (Econst_int (Int.repr 2) tuint) tuint)
                          ?d Sskip] => exact d end).

(* From the descriptor loop on. *)
Definition s_dloop : statement := ltac:(
  let b := eval cbv delta [hd_body] in hd_body in
  match b with context [Ssequence (Ssequence (Sset _i__1 (Econst_int (Int.repr 0) tint)) ?l) ?rest] =>
    exact (Ssequence (Ssequence (Sset _i__1 (Econst_int (Int.repr 0) tint)) l) rest) end).

Ltac start_tail :=
  repeat match goal with
  | |- context [Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s) Sskip] => fold (Swhile e s)
  end;
  simplify_func_tycontext;
  abbreviate_semax.

(* ---------------------------------------------------------------------- *)
(* The decode, case by case.                                              *)
(* ---------------------------------------------------------------------- *)

(* Boolean facts into Prop (bprop never splits the goal; bprop_split does, on disjunctions). *)
Ltac bprop :=
  repeat match goal with
  | H: (_ || _)%bool = false |- _ => apply orb_false_iff in H; destruct H
  | H: (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H
  | H: negb _ = true |- _ => apply negb_true_iff in H
  | H: negb _ = false |- _ => apply negb_false_iff in H
  | H: (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H: (_ <? _) = false |- _ => apply Z.ltb_ge in H
  | H: (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H: (_ <=? _) = false |- _ => apply Z.leb_gt in H
  | H: (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H: (_ =? _) = false |- _ => apply Z.eqb_neq in H
  end.

Ltac bprop_split :=
  repeat (bprop; match goal with
  | H: (_ || _)%bool = true |- _ => apply orb_true_iff in H; destruct H
  | H: (_ && _)%bool = false |- _ => apply andb_false_iff in H; destruct H
  | H: _ \/ _ |- _ => destruct H
  end); bprop.

(* Decide the decode's tests one by one against the facts in the context. *)
Ltac dec_hyps :=
  repeat match goal with H: context [if ?c then _ else _] |- _ => let E := fresh "E" in destruct c eqn:E end;
  bprop_split.

Ltac dec_solve :=
  unfold decode; cbv zeta; unfold MAX_SINKS, MAX_DESCS in *;
  cbn [tg_bus tg_dev tg_fn tg_id tg_window tg_bar target_of] in *;
  dec_hyps;
  repeat (match goal with |- context [if ?c then _ else _] =>
            let E := fresh "E" in destruct c eqn:E end;
          try solve [ dec_hyps; first [ congruence | lia ] ]);
  try reflexivity; try congruence; dec_hyps; try congruence; try lia.

Lemma bool2val_b2z': forall b, bool2val b = Vint (Int.repr (Z.b2z b)).
Proof. intros [ | ]; reflexivity. Qed.

(* A comparison of two words, as the C's != or == leaves it. *)
Ltac cmp_join := rewrite ?u32_eq by (auto; unfold u32_ok; rep_lia); rewrite ?bool2val_b2z'; reflexivity.

(* Int.repr equations of words (Wr: their range) as equations of Z. *)
Ltac repr_facts Wr :=
  change Int.zero with (Int.repr 0) in *;
  repeat match goal with
  | H: Int.repr ?a = Int.repr ?b |- _ =>
      let A := fresh "R" in
      assert (A: a = b) by (apply repr_inj_unsigned; [ first [ apply Wr | rep_lia ] | first [ apply Wr | rep_lia ] | exact H ]);
      clear H
  | H: Int.repr ?a <> Int.repr ?b |- _ =>
      let A := fresh "R" in
      assert (A: a <> b) by (let E := fresh in intro E; apply H; rewrite E; reflexivity);
      clear H
  end.

(* Joins: the precondition with the temp t now v, or with the fact X added. *)
Ltac fif_t t v :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp t v :: Q) (SEPx R))) end.
Ltac fif_p X :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx (X :: P) (LOCALx Q (SEPx R))) end.

(* The policy object from its fields. *)
Lemma pol_fold: forall sh p pr dm wn cr cw cc cs sc sk dc ds, field_compatible t_policy [] p ->
  (field_at sh t_policy (DOT _present) pr p * field_at sh t_policy (DOT _dma) dm p *
   field_at sh t_policy (DOT _window) wn p * spacer sh 12 16 p * field_at sh t_policy (DOT _cfg_read) cr p *
   field_at sh t_policy (DOT _cfg_write) cw p * field_at sh t_policy (DOT _cmd_clear) cc p *
   field_at sh t_policy (DOT _cmd_set) cs p * field_at sh t_policy (DOT _sink_count) sc p *
   field_at sh t_policy (DOT _sinks) sk p * field_at sh t_policy (DOT _desc_count) dc p *
   data_at sh (tarray t_desc 16) ds (offset_val 80 p))%logic |--
  data_at sh t_policy (pol_tuple pr dm wn cr cw cc cs sc sk dc ds) p.
Proof. intros. rewrite pol_fields by auto. apply derives_refl. Qed.

Ltac pol_fold_tac :=
  match goal with |- context [field_at ?sh t_policy (DOT _present) ?pr ?p] =>
  match goal with |- context [field_at _ t_policy (DOT _dma) ?dm p] =>
  match goal with |- context [field_at _ t_policy (DOT _window) ?wn p] =>
  match goal with |- context [field_at _ t_policy (DOT _cfg_read) ?cr p] =>
  match goal with |- context [field_at _ t_policy (DOT _cfg_write) ?cw p] =>
  match goal with |- context [field_at _ t_policy (DOT _cmd_clear) ?cc p] =>
  match goal with |- context [field_at _ t_policy (DOT _cmd_set) ?cs p] =>
  match goal with |- context [field_at _ t_policy (DOT _sink_count) ?sc p] =>
  match goal with |- context [field_at _ t_policy (DOT _sinks) ?sk p] =>
  match goal with |- context [field_at _ t_policy (DOT _desc_count) ?dc p] =>
  match goal with |- context [data_at _ (tarray t_desc 16) ?ds (offset_val 80 p)] =>
  match goal with FC: field_compatible t_policy [] p |- _ =>
    sep_apply (pol_fold sh p pr dm wn cr cw cc cs sc sk dc ds FC)
  end end end end end end end end end end end end.

Lemma pol_store_none: forall P0, policy_wf P0 ->
  policy_val (store no_policy P0) =
  pol_tuple (Vint (Int.repr 0)) (Vint (Int.repr 0)) (Vint (Int.repr 0)) (Vlong (Int64.repr 0))
    (Vlong (Int64.repr 0)) (Vint (Int.repr 0)) (Vint (Int.repr 0)) (Vint (Int.repr 0))
    (words_val (pl_sinks P0)) (Vint (Int.repr 0)) (map desc_val (pl_descs P0)).
Proof.
  intros P0 PW. destruct PW as (_ & _ & _ & _ & _ & _ & _ & _ & Ls & _ & _ & Ld & _).
  unfold store, no_policy, policy_val, policy_rep, pol_tuple.
  cbn [pl_present pl_dma pl_window pl_cfg_read pl_cfg_write pl_cmd_clear pl_cmd_set pl_sink_count pl_sinks
       pl_desc_count pl_descs app].
  rewrite !sublist_same by (unfold MAX_SINKS, MAX_DESCS in *; lia). reflexivity.
Qed.

Lemma zlt_b2z: forall a b, bool2val (zlt a b) = Vint (Int.repr (Z.b2z (a <? b))).
Proof. intros. destruct (zlt a b), (Z.ltb_spec a b); try lia; reflexivity. Qed.
Lemma zgt_b2z: forall a b, bool2val (zlt b a) = Vint (Int.repr (Z.b2z (b <? a))).
Proof. intros. apply zlt_b2z. Qed.
Lemma ltu_b2z: forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  bool2val (Int.ltu (Int.repr a) (Int.repr b)) = Vint (Int.repr (Z.b2z (a <? b))).
Proof.
  intros. unfold Int.ltu. rewrite !Int.unsigned_repr by lia. destruct (zlt a b), (Z.ltb_spec a b); try lia; reflexivity.
Qed.

Lemma ltu_repr_b: forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.ltu (Int.repr a) (Int.repr b) = (a <? b).
Proof. intros. unfold Int.ltu. rewrite !Int.unsigned_repr by lia. destruct (zlt a b), (Z.ltb_spec a b); lia. Qed.

(* The joins of the C's || and && chains of tests, against the model's booleans. *)
Ltac bjoin :=
  repeat match goal with
  | H: ?a <> ?b |- context [?a =? ?b] => rewrite (proj2 (Z.eqb_neq a b) H)
  | H: ?a = ?b |- context [?a =? ?b] => rewrite (proj2 (Z.eqb_eq a b) H)
  | H: @eq bool ?o true |- context [?o] => rewrite H
  | H: @eq bool ?o false |- context [?o] => rewrite H
  | H: ?a < ?b |- context [?a <? ?b] => rewrite (proj2 (Z.ltb_lt a b) H)
  | H: ?b <= ?a |- context [?a <? ?b] => rewrite (proj2 (Z.ltb_ge a b) H)
  | H: ?a >= ?b |- context [?a <? ?b] => rewrite (proj2 (Z.ltb_ge a b) ltac:(lia))
  | H: ?a > ?b |- context [?b <? ?a] => rewrite (proj2 (Z.ltb_lt b a) ltac:(lia))
  end; cbn [orb andb negb];
  rewrite ?zneq_b2z, ?zeq_b2z, ?zlt_b2z;
  rewrite ?notbool_b2z, ?zbool_b2z by (unfold u32_ok; rep_lia);
  rewrite ?u32_eq by (unfold u32_ok; rep_lia); rewrite ?ltu_b2z by rep_lia; rewrite ?bool2val_b2z';
  rewrite ?ltu_repr_b by rep_lia; cbn [orb andb negb];
  try reflexivity.

(* A return: the outputs as they are. *)
Ltac hd_ret :=
  try pol_fold_tac;
  forward;
  match goal with |- context [data_at _ t_target ?tv _] =>
  match goal with |- context [data_at _ t_policy ?pv _] =>
  match goal with |- context [data_at _ tuint ?hv _] => Exists tv pv hv end end end;
  entailer!.

(* A return of WIFI_BAD_IMAGE: the outputs as they are, decode bs = None. *)
Ltac hd_bad D :=
  try pol_fold_tac;
  forward;
  match goal with |- context [data_at _ t_target ?tv _] =>
  match goal with |- context [data_at _ t_policy ?pv _] =>
  match goal with |- context [data_at _ tuint ?hv _] => Exists tv pv hv end end end;
  entailer!; unfold header_post, header_status; rewrite D; auto.
