(* struct wifi_policy with one descriptor descs[i] split out (at offset 80 + 16 i), proved once: the
   admission reads max->descs[k] through wifi_has_desc, and the header writes pol->descs[i] through its
   pointer d and passes it to wifi_desc_limit. *)
Require Import VST.floyd.proofauto.
Require Import LeanosDeviceProgramImage.device_program.code.
Require Import LeanosDeviceProgramImage.proof.Specs.
#[local] Existing Instance Specs.CS.
Local Open Scope Z_scope.

Definition pol_tuple (pr dm wn cr cw cc cs sc: val) (sk: list val) (dc: val) (ds: list desc_t) : policy_t :=
  (pr, (dm, (wn, (cr, (cw, (cc, (cs, (sc, (sk, (dc, ds)))))))))).

(* Everything of the policy object but descs[i]: the scalars, the sinks, descs[0..i) and descs(i..16). *)
Definition pol_hole sh (pr dm wn cr cw cc cs sc: val) (sk: list val) (dc: val) (lo hi: list desc_t) (i: Z)
    (p: val) : mpred :=
  (field_at sh t_policy (DOT _present) pr p * field_at sh t_policy (DOT _dma) dm p *
   field_at sh t_policy (DOT _window) wn p * spacer sh 12 16 p * field_at sh t_policy (DOT _cfg_read) cr p *
   field_at sh t_policy (DOT _cfg_write) cw p * field_at sh t_policy (DOT _cmd_clear) cc p *
   field_at sh t_policy (DOT _cmd_set) cs p * field_at sh t_policy (DOT _sink_count) sc p *
   field_at sh t_policy (DOT _sinks) sk p * field_at sh t_policy (DOT _desc_count) dc p *
   data_at sh (tarray t_desc i) lo (offset_val 80 p) *
   data_at sh (tarray t_desc (16 - (i + 1))) hi (offset_val (80 + 16 * (i + 1)) p))%logic.

Lemma pol_fields: forall sh pr dm wn cr cw cc cs sc sk dc ds p,
  field_compatible t_policy [] p ->
  data_at sh t_policy (pol_tuple pr dm wn cr cw cc cs sc sk dc ds) p =
  (field_at sh t_policy (DOT _present) pr p * field_at sh t_policy (DOT _dma) dm p *
   field_at sh t_policy (DOT _window) wn p * spacer sh 12 16 p * field_at sh t_policy (DOT _cfg_read) cr p *
   field_at sh t_policy (DOT _cfg_write) cw p * field_at sh t_policy (DOT _cmd_clear) cc p *
   field_at sh t_policy (DOT _cmd_set) cs p * field_at sh t_policy (DOT _sink_count) sc p *
   field_at sh t_policy (DOT _sinks) sk p * field_at sh t_policy (DOT _desc_count) dc p *
   data_at sh (tarray t_desc 16) ds (offset_val 80 p))%logic.
Proof.
  intros. unfold pol_tuple, t_policy.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh (Tstruct _wifi_policy noattr) (DOT _descs)).
  rewrite field_compatible_field_address by auto with field_compatible.
  change (nested_field_type (Tstruct _wifi_policy noattr) (DOT _descs)) with (tarray t_desc 16).
  change (nested_field_offset (Tstruct _wifi_policy noattr) (DOT _descs)) with 80.
  apply pred_ext; cancel.
Qed.

Lemma descs_split: forall sh (ds: list desc_t) i q, 0 <= i < 16 -> Zlength ds = 16 ->
  field_compatible (tarray t_desc 16) [] q ->
  data_at sh (tarray t_desc 16) ds q =
  (data_at sh (tarray t_desc i) (sublist 0 i ds) q *
   data_at sh t_desc (Znth i ds) (offset_val (16 * i) q) *
   data_at sh (tarray t_desc (16 - (i + 1))) (sublist (i + 1) 16 ds) (offset_val (16 * (i + 1)) q))%logic.
Proof.
  intros sh ds i q I L FC. unfold tarray.
  assert (L': @Zlength (reptype t_desc) ds = 16) by exact L.
  rewrite (@split3_data_at_Tarray CS sh t_desc 16 i (i + 1) ds ds (sublist 0 i ds) (sublist i (i + 1) ds)
             (sublist (i + 1) 16 ds)); try first [ lia | reflexivity ].
  2: { cbn. split; auto. }
  2: rewrite sublist_same by lia; reflexivity.
  replace (i + 1 - i) with 1 by lia.
  rewrite (@sublist_one desc_t _ i (i + 1) ds) by lia.
  rewrite (@data_at_singleton_array_eq CS sh t_desc (Znth i ds) [Znth i ds]) by reflexivity.
  rewrite !field_address0_offset by auto with field_compatible.
  change (nested_field_offset (Tarray t_desc 16 noattr) (SUB i)) with (0 + sizeof t_desc * i).
  change (nested_field_offset (Tarray t_desc 16 noattr) (SUB (i + 1))) with (0 + sizeof t_desc * (i + 1)).
  change (sizeof t_desc) with 16. rewrite !Z.add_0_l. reflexivity.
Qed.

Lemma descs_compatible: forall p, field_compatible t_policy [] p ->
  field_compatible (tarray t_desc 16) [] (offset_val 80 p).
Proof.
  intros p FC.
  assert (F: field_compatible t_policy (DOT _descs) p) by auto with field_compatible.
  pose proof (field_compatible_nested_field _ _ _ F) as N.
  exact N.
Qed.

Lemma pol_split: forall sh pr dm wn cr cw cc cs sc sk dc ds i p,
  0 <= i < 16 -> Zlength ds = 16 -> field_compatible t_policy [] p ->
  data_at sh t_policy (pol_tuple pr dm wn cr cw cc cs sc sk dc ds) p =
  (data_at sh t_desc (Znth i ds) (offset_val (80 + 16 * i) p) *
   pol_hole sh pr dm wn cr cw cc cs sc sk dc (sublist 0 i ds) (sublist (i + 1) 16 ds) i p)%logic.
Proof.
  intros. rewrite pol_fields by auto.
  rewrite (descs_split sh ds i (offset_val 80 p)) by (auto; apply descs_compatible; auto).
  rewrite !offset_offset_val. unfold pol_hole. apply pred_ext; cancel.
Qed.

(* After descs[i] is replaced by x: the hole is the same. *)
Lemma pol_join: forall sh pr dm wn cr cw cc cs sc sk dc ds i x p,
  0 <= i < 16 -> Zlength ds = 16 -> field_compatible t_policy [] p ->
  (data_at sh t_desc x (offset_val (80 + 16 * i) p) *
   pol_hole sh pr dm wn cr cw cc cs sc sk dc (sublist 0 i ds) (sublist (i + 1) 16 ds) i p)%logic =
  data_at sh t_policy (pol_tuple pr dm wn cr cw cc cs sc sk dc (upd_Znth i ds x)) p.
Proof.
  intros. rewrite (pol_split sh pr dm wn cr cw cc cs sc sk dc (upd_Znth i ds x) i p)
    by (auto; rewrite upd_Znth_Zlength; lia).
  rewrite upd_Znth_same by lia.
  rewrite sublist_upd_Znth_l by lia. rewrite sublist_upd_Znth_r by lia. reflexivity.
Qed.

(* The read-only form for a policy object. *)
Lemma policy_val_split: forall sh P i p,
  0 <= i < 16 -> Zlength (pl_descs P) = 16 -> field_compatible t_policy [] p ->
  data_at sh t_policy (policy_val P) p =
  (data_at sh t_desc (desc_val (Znth i (pl_descs P))) (offset_val (80 + 16 * i) p) *
   pol_hole sh (Vint (Int.repr (pl_present P))) (Vint (Int.repr (pl_dma P))) (Vint (Int.repr (pl_window P)))
     (Vlong (Int64.repr (pl_cfg_read P))) (Vlong (Int64.repr (pl_cfg_write P)))
     (Vint (Int.repr (pl_cmd_clear P))) (Vint (Int.repr (pl_cmd_set P))) (Vint (Int.repr (pl_sink_count P)))
     (words_val (pl_sinks P)) (Vint (Int.repr (pl_desc_count P)))
     (sublist 0 i (map desc_val (pl_descs P))) (sublist (i + 1) 16 (map desc_val (pl_descs P))) i p)%logic.
Proof.
  intros. unfold policy_val, policy_rep.
  change (data_at sh t_policy _ p) with (data_at sh t_policy (pol_tuple (Vint (Int.repr (pl_present P)))
     (Vint (Int.repr (pl_dma P))) (Vint (Int.repr (pl_window P)))
     (Vlong (Int64.repr (pl_cfg_read P))) (Vlong (Int64.repr (pl_cfg_write P)))
     (Vint (Int.repr (pl_cmd_clear P))) (Vint (Int.repr (pl_cmd_set P))) (Vint (Int.repr (pl_sink_count P)))
     (words_val (pl_sinks P)) (Vint (Int.repr (pl_desc_count P))) (map desc_val (pl_descs P))) p).
  rewrite (pol_split sh _ _ _ _ _ _ _ _ _ _ _ i p) by (auto; rewrite Zlength_map; lia).
  rewrite Znth_map by lia. reflexivity.
Qed.
