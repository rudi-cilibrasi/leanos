(* Law capabilities_complete: lemmas and tactics for the proof of main (CompMain.v). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosCaps.proof.Defs.
Require LeanosCaps.proof.CapsSpecs.
Require Import LeanosCaps.proof.CompPure.
Require Import LeanosCaps.proof.CompProg LeanosCaps.proof.CompSpecs.
Require Import LeanosCaps.harness.capabilities_complete.code.
Local Open Scope Z_scope.
#[local] Existing Instance LCS.

Definition t_header := Tstruct _pci_enumeration_header noattr.
Definition t_snapshot := Tstruct _pci_capability_snapshot noattr.
Definition t_result := Tstruct _pci_capability_result noattr.

(* ---------------------------------------------------------------------- *)
(* The walker's arguments, from the law's compspecs to the unit's.         *)
(* ---------------------------------------------------------------------- *)

Lemma header_cs: forall sh (v: val * (val * (val * list val))) p,
  @data_at LCS sh t_header v p = @data_at CapsSpecs.CS sh CapsSpecs.t_header v p.
Proof.
  intros. apply equal_f. symmetry.
  apply (@data_at_change_composite CapsSpecs.CS LCS LCR); [ apply JMeq_refl | reflexivity ].
Qed.

Lemma snapshot_cs: forall sh (v: val * list (val * val)) p,
  @data_at LCS sh t_snapshot v p = @data_at CapsSpecs.CS sh CapsSpecs.t_snapshot v p.
Proof.
  intros. apply equal_f. symmetry.
  apply (@data_at_change_composite CapsSpecs.CS LCS LCR); [ apply JMeq_refl | reflexivity ].
Qed.

Lemma snapshot__cs: forall sh p,
  @data_at_ LCS sh t_snapshot p = @data_at_ CapsSpecs.CS sh CapsSpecs.t_snapshot p.
Proof.
  intros. apply equal_f. symmetry.
  apply (@data_at__change_composite CapsSpecs.CS LCS LCR). reflexivity.
Qed.

Lemma maybe_at_ptr: forall sh t v p, isptr p -> CapsSpecs.maybe_at sh t v p = data_at sh t v p.
Proof. intros. unfold CapsSpecs.maybe_at. destruct (Val.eq p nullval); [ subst; contradiction | reflexivity ]. Qed.

Lemma maybe_at_null: forall sh t v, CapsSpecs.maybe_at sh t v nullval = emp.
Proof. intros. unfold CapsSpecs.maybe_at. destruct (Val.eq nullval nullval); [ reflexivity | contradiction ]. Qed.

Lemma maybe_read_ptr: forall Dev p, func_ptr' (CapsSpecs.read_spec Dev) p |-- CapsSpecs.maybe_read Dev p.
Proof.
  intros. unfold CapsSpecs.maybe_read. destruct (Val.eq p nullval).
  - subst. eapply derives_trans; [ apply func_ptr'_isptr | ]. apply prop_left. intro N. inversion N.
  - apply derives_refl.
Qed.

(* The device of the law, before its first read. *)
Lemma dev_intro: forall bdf W p, Zlength W = 64 -> Forall CapsSpecs.u32_ok W ->
  data_at sh_dev t_space (space_val bdf W) p |-- Dev_comp p bdf nil.
Proof. intros. unfold Dev_comp. Exists W. entailer!. Qed.

(* ---------------------------------------------------------------------- *)
(* Arithmetic.                                                             *)
(* ---------------------------------------------------------------------- *)

Lemma divu4: forall a, 0 <= a <= Int.max_unsigned -> Int.unsigned (Int.divu (Int.repr a) (Int.repr 4)) = a / 4.
Proof.
  intros a H. unfold Int.divu. rewrite (Int.unsigned_repr a), (Int.unsigned_repr 4) by rep_lia.
  assert (0 <= a / 4 <= a) by (Z.div_mod_to_equations; lia).
  rewrite Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma at_mod: forall a, at_ok a -> a mod 4 = 0.
Proof.
  intros a [_ H]. change 3 with (Z.ones 2) in H. rewrite Z.land_ones in H by lia. exact H.
Qed.

Lemma at_quot: forall x y, at_ok x -> at_ok y -> x / 4 = y / 4 -> x = y.
Proof.
  intros x y Hx Hy E. pose proof (at_mod x Hx). pose proof (at_mod y Hy).
  rewrite (Z.div_mod x 4), (Z.div_mod y 4) by lia. lia.
Qed.

Lemma at_quot_range: forall a, at_ok a -> 16 <= a / 4 < 64.
Proof. intros a [H _]. Z.div_mod_to_equations. lia. Qed.

Lemma b2z_true: forall c, Int.repr (Z.b2z c) <> Int.zero -> c = true.
Proof. intros c H. destruct c; [ reflexivity | exfalso; apply H; reflexivity ]. Qed.

(* ---------------------------------------------------------------------- *)
(* Freezing (as in the reference proofs, LeanosRoots Law3Tac).             *)
(* ---------------------------------------------------------------------- *)

(* The indices of the SEP items of R that mention neither p nor q (syntactically). *)
Ltac sep_idx_free R p q i :=
  lazymatch R with
  | nil => constr:(@nil Z)
  | ?x :: ?R' =>
      let rest := sep_idx_free R' p q (Z.succ i) in
      match x with
      | context [p] => rest
      | context [q] => rest
      | _ => constr:(i :: rest)
      end
  end.

(* Freeze every SEP item but those at p and q. *)
Ltac freeze_except p q F :=
  match goal with
  | |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
      let L := sep_idx_free R p q 0 in let L := eval cbn in L in freeze_tac L F
  | |- ENTAIL _, (PROPx _ (LOCALx _ (SEPx ?R))) |-- _ =>
      let L := sep_idx_free R p q 0 in let L := eval cbn in L in freeze_tac_entail L F
  end.

(* ---------------------------------------------------------------------- *)
(* The harness's assumes and comparisons, as facts on Z.                   *)
(* ---------------------------------------------------------------------- *)

Lemma ltu_false_le: forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.ltu (Int.repr a) (Int.repr b) = false -> b <= a.
Proof.
  intros a b Ha Hb E. unfold Int.ltu in E. rewrite !Int.unsigned_repr in E by lia.
  destruct (zlt a b); [ discriminate | lia ].
Qed.

Lemma ltu_true_lt: forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.ltu (Int.repr a) (Int.repr b) = true -> a < b.
Proof.
  intros a b Ha Hb E. unfold Int.ltu in E. rewrite !Int.unsigned_repr in E by lia.
  destruct (zlt a b); [ lia | discriminate ].
Qed.

Lemma eq_false_neq: forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.eq (Int.repr a) (Int.repr b) = false -> a <> b.
Proof. intros a b Ha Hb E N. subst. rewrite Int.eq_true in E. discriminate. Qed.

Lemma eq_true_eq: forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.eq (Int.repr a) (Int.repr b) = true -> a = b.
Proof.
  intros a b Ha Hb E. apply Int.same_if_eq in E. apply repr_inj_unsigned; auto.
Qed.

Ltac assume_hyps :=
  repeat match goal with
  | E: Int.repr (Z.b2z _) <> Int.zero |- _ => apply b2z_true in E
  | E: negb _ = true |- _ => apply negb_true_iff in E
  | E: (_ && _)%bool = true |- _ => apply andb_prop in E; destruct E
  | E: (?a <=? ?b) = true |- _ => apply Z.leb_le in E
  | E: (?a <? ?b) = true |- _ => apply Z.ltb_lt in E
  | E: (?a =? ?b) = true |- _ => apply Z.eqb_eq in E
  | E: (?a <=? ?b) = false |- _ => apply Z.leb_gt in E
  | E: (?a <? ?b) = false |- _ => apply Z.ltb_ge in E
  | E: (?a =? ?b) = false |- _ => apply Z.eqb_neq in E
  | E: Int.ltu (Int.repr ?a) (Int.repr ?b) = false |- _ =>
      let F := fresh "F" in pose proof (ltu_false_le a b ltac:(rep_lia) ltac:(rep_lia) E) as F; clear E
  | E: Int.ltu (Int.repr ?a) (Int.repr ?b) = true |- _ =>
      let F := fresh "F" in pose proof (ltu_true_lt a b ltac:(rep_lia) ltac:(rep_lia) E) as F; clear E
  | E: Int.eq (Int.repr ?a) (Int.repr ?b) = false |- _ =>
      let F := fresh "F" in pose proof (eq_false_neq a b ltac:(rep_lia) ltac:(rep_lia) E) as F; clear E
  | E: Int.eq (Int.repr ?a) (Int.repr ?b) = true |- _ =>
      let F := fresh "F" in pose proof (eq_true_eq a b ltac:(rep_lia) ltac:(rep_lia) E) as F; clear E
  end.

Lemma NoDup_snoc: forall (l: list Z) x, NoDup l -> ~ In x l -> NoDup (l ++ [x]).
Proof.
  induction l as [|a l IH]; simpl; intros x N I.
  - constructor; [ intro F; inversion F | constructor ].
  - inversion N; subst. constructor.
    + rewrite in_app_iff. simpl. intuition.
    + apply IH; auto.
Qed.

(* The offsets array: the first i planted, the rest undefined. *)
Definition vints (l: list Z) : list val := map (fun z => Vint (Int.repr z)) l.

Lemma vints_Znth: forall l k (u: list val), 0 <= k < Zlength l ->
  Znth k (vints l ++ u) = Vint (Int.repr (Znth k l)).
Proof.
  intros. unfold vints. rewrite Znth_app1 by (rewrite Zlength_map; lia). rewrite Znth_map by lia. reflexivity.
Qed.

Lemma vints_snoc: forall l x k, Zlength l + 1 + k = 48 -> 0 <= k ->
  upd_Znth (Zlength l) (vints l ++ Zrepeat Vundef (k + 1)) (Vint (Int.repr x)) = vints (l ++ [x]) ++ Zrepeat Vundef k.
Proof. intros. unfold vints. list_solve. Qed.

Lemma Znth_snoc: forall {A} {d: Inhabitant A} (l: list A) x, Znth (Zlength l) (l ++ [x]) = x.
Proof. intros. rewrite Znth_app2 by lia. rewrite Z.sub_diag. reflexivity. Qed.

Lemma Znth_app_l: forall {A} {d: Inhabitant A} (l: list A) x k, 0 <= k < Zlength l -> Znth k (l ++ [x]) = Znth k l.
Proof. intros. apply Znth_app1. lia. Qed.

Lemma Int_eq_repr: forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.eq (Int.repr a) (Int.repr b) = (a =? b).
Proof.
  intros. unfold Int.eq. rewrite !Int.unsigned_repr by lia.
  destruct (zeq a b); destruct (Z.eqb_spec a b); congruence.
Qed.

(* Goals on the boolean value of a comparison: by cases on the comparisons. *)
Ltac bcase :=
  repeat match goal with
  | E: ?c = false |- context [?c] => rewrite E
  | E: ?c = true |- context [?c] => rewrite E
  end;
  repeat (rewrite Int_eq_repr by (first [ rep_lia | apply land_range; rep_lia ]));
  repeat match goal with
  | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b)
  | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
  | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
  | |- context [zlt ?a ?b] => destruct (zlt a b)
  | |- context [zle ?a ?b] => destruct (zle a b)
  | |- context [zeq ?a ?b] => destruct (zeq a b)
  end;
  simpl; try reflexivity; try lia.

(* ---------------------------------------------------------------------- *)
(* The planting loop.                                                      *)
(* ---------------------------------------------------------------------- *)

Lemma next_of_range: forall ats k, Forall at_ok ats -> 0 <= next_of ats k < 256.
Proof.
  intros ats k F. unfold next_of. destruct (Z.ltb_spec (k + 1) (Zlength ats)); [ | lia ].
  destruct (zlt (k + 1) 0).
  - rewrite Znth_underflow by lia. unfold default, Inhabitant_Z. lia.
  - assert (A: at_ok (Znth (k + 1) ats)) by (apply Forall_Znth; [ exact F | lia ]). destruct A. lia.
Qed.

(* The value the harness stores: (w & 0xffff0000) | (next << 8) | id. *)
Lemma plant_repr: forall w nx id, 0 <= w <= Int.max_unsigned -> 0 <= nx < 256 -> 0 <= id < 256 ->
  Int.or (Int.or (Int.and (Int.repr w) (Int.repr (-65536))) (Int.shl (Int.repr nx) (Int.repr 8))) (Int.repr id) =
  Int.repr (plant w nx id).
Proof.
  intros w nx id Hw Hn Hi. rewrite repr_m65536.
  rewrite int_and by rep_lia. rewrite int_shl8 by rep_lia.
  assert (R1: 0 <= Z.land w 4294901760 <= Int.max_unsigned) by (apply land_range; rep_lia).
  assert (R2: 0 <= Z.shiftl nx 8 <= Int.max_unsigned) by (apply shiftl8_range; lia).
  rewrite int_or by assumption.
  assert (R3: 0 <= Z.lor (Z.land w 4294901760) (Z.shiftl nx 8) <= Int.max_unsigned) by (apply lor_range; assumption).
  rewrite int_or by rep_lia. reflexivity.
Qed.

Lemma plant_step: forall W ats i id,
  Zlength W = 64 -> Forall CapsSpecs.u32_ok W -> Forall at_ok ats -> NoDup ats -> 0 <= i < Zlength ats ->
  0 <= id < 256 -> id <> 255 ->
  (forall k, 0 <= k < i -> node_ok W ats k) ->
  let a := Znth i ats in
  let W' := upd_Znth (a / 4) W (plant (Znth (a / 4) W) (next_of ats i) id) in
  Zlength W' = 64 /\ Forall CapsSpecs.u32_ok W' /\ (forall k, 0 <= k < i + 1 -> node_ok W' ats k).
Proof.
  intros W ats i id LW UW AOK ND Hi Hid N255 NK a W'.
  assert (Aa: at_ok a) by (apply Forall_Znth; [ exact AOK | lia ]).
  pose proof (at_quot_range a Aa) as Qa.
  pose proof (next_of_range ats i AOK) as Rn.
  assert (Uw: CapsSpecs.u32_ok (Znth (a / 4) W)) by (apply Forall_Znth; [ exact UW | lia ]).
  unfold CapsSpecs.u32_ok in Uw.
  split; [ unfold W'; rewrite upd_Znth_Zlength; lia | split ].
  - unfold W'. apply Forall_upd_Znth; [ exact UW | ]. unfold CapsSpecs.u32_ok. apply plant_range; lia.
  - intros k Hk. destruct (zeq k i).
    + subst k. unfold node_ok. fold a. unfold W'. rewrite upd_Znth_same by lia.
      split; [ rewrite plant_id by lia; exact N255 | apply plant_next; lia ].
    + assert (Ak: at_ok (Znth k ats)) by (apply Forall_Znth; [ exact AOK | lia ]).
      pose proof (at_quot_range _ Ak) as Qk.
      assert (D: Znth k ats / 4 <> a / 4).
      { intro E. apply n. apply (NoDup_Znth_inj ats k i ND); [ lia | lia | ]. apply at_quot; auto. }
      destruct (NK k ltac:(lia)) as [N1 N2]. unfold node_ok. unfold W'.
      rewrite upd_Znth_diff by lia. auto.
Qed.

Lemma land255_range: forall y, 0 <= Z.land y 255 < 256.
Proof. intros. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.

(* Undo the unfolding of Z.div by simpl. *)
Ltac fold_div :=
  repeat match goal with
  | |- context [let (q, _) := Z.div_eucl ?a ?b in q] => change (let (q, _) := Z.div_eucl a b in q) with (Z.div a b)
  end.

(* ---------------------------------------------------------------------- *)
(* The header words.                                                       *)
(* ---------------------------------------------------------------------- *)

(* A change of a header word (below 16) keeps the planted list. *)
Lemma links_upd: forall W ats j v, Zlength W = 64 -> Forall at_ok ats -> 0 <= j < 16 ->
  links W ats -> links (upd_Znth j W v) ats.
Proof.
  intros W ats j v LW. induction ats as [|a l IH]; intros AOK Hj LK; [ exact I | ].
  inversion AOK as [| ? ? Aa AOK']; subst. pose proof (at_quot_range a Aa) as Qa.
  destruct LK as [L1 [L2 LK]]. cbn [links].
  rewrite upd_Znth_diff by lia. auto.
Qed.

Lemma list_head_eq: forall W, Zlength W = 64 ->
  list_head (sublist 0 16 W) = if Z.land (Znth 1 W) 1048576 =? 0 then 0 else Z.land (Znth 13 W) 255.
Proof. intros. unfold list_head. rewrite !Znth_sublist by lia. reflexivity. Qed.

Lemma u32_upd: forall W j v, Forall CapsSpecs.u32_ok W -> 0 <= v <= Int.max_unsigned ->
  Forall CapsSpecs.u32_ok (upd_Znth j W v).
Proof. intros. apply Forall_upd_Znth; auto. Qed.

Lemma u32_Znth: forall W j, Forall CapsSpecs.u32_ok W -> 0 <= j < Zlength W -> 0 <= Znth j W <= Int.max_unsigned.
Proof. intros. apply Forall_Znth; [ assumption | lia ]. Qed.

(* The three ways main sets the list head. *)
Definition W_set (W: list Z) (a: Z) : list Z :=
  upd_Znth 13 (upd_Znth 1 W (Z.lor (Znth 1 W) 1048576)) (Z.lor (Z.land (Znth 13 W) 4294967040) a).
Definition W_clear_bit (W: list Z) : list Z := upd_Znth 1 W (Z.land (Znth 1 W) 4293918719).
Definition W_clear_byte (W: list Z) : list Z :=
  upd_Znth 13 (upd_Znth 1 W (Z.lor (Znth 1 W) 1048576)) (Z.land (Znth 13 W) 4294967040).

(* n > 0: the status bit set, word 13's low byte the first offset. *)
Lemma head_set: forall W ats, Zlength W = 64 -> Forall CapsSpecs.u32_ok W -> Forall at_ok ats -> links W ats ->
  0 < Zlength ats ->
  let W3 := W_set W (Znth 0 ats) in
  Zlength W3 = 64 /\ Forall CapsSpecs.u32_ok W3 /\ links W3 ats /\ list_head (sublist 0 16 W3) = hd 0 ats.
Proof.
  intros W ats LW UW AOK LK NZ W3. unfold W_set in W3.
  assert (A0: at_ok (Znth 0 ats)) by (apply Forall_Znth; [ exact AOK | lia ]). pose proof A0 as [A01 A02].
  assert (U1: 0 <= Znth 1 W <= Int.max_unsigned) by (apply u32_Znth; auto; lia).
  assert (U13: 0 <= Znth 13 W <= Int.max_unsigned) by (apply u32_Znth; auto; lia).
  assert (R1: 0 <= Z.lor (Znth 1 W) 1048576 <= Int.max_unsigned) by (apply lor_range; rep_lia).
  assert (R13: 0 <= Z.lor (Z.land (Znth 13 W) 4294967040) (Znth 0 ats) <= Int.max_unsigned)
    by (apply lor_range; [ apply land_range; rep_lia | rep_lia ]).
  assert (L2: Zlength (upd_Znth 1 W (Z.lor (Znth 1 W) 1048576)) = 64) by (rewrite upd_Znth_Zlength; lia).
  split; [ unfold W3; rewrite upd_Znth_Zlength; lia | ].
  split; [ unfold W3; apply u32_upd; [ apply u32_upd; auto | auto ] | ].
  split; [ unfold W3; apply links_upd; [ exact L2 | auto | lia | apply links_upd; auto; lia ] | ].
  rewrite list_head_eq by (unfold W3; rewrite upd_Znth_Zlength; lia).
  unfold W3. rewrite upd_Znth_diff by lia. rewrite !upd_Znth_same by lia.
  rewrite (proj2 (Z.eqb_neq _ 0)) by (apply set_cap_bit; lia).
  rewrite set_head by lia.
  destruct ats; [ rewrite Zlength_nil in NZ; lia | reflexivity ].
Qed.

(* n = 0, first way: the status bit cleared. *)
Lemma head_clear_bit: forall W, Zlength W = 64 -> Forall CapsSpecs.u32_ok W ->
  let W2 := W_clear_bit W in
  Zlength W2 = 64 /\ Forall CapsSpecs.u32_ok W2 /\ links W2 [] /\ list_head (sublist 0 16 W2) = hd 0 [].
Proof.
  intros W LW UW W2. unfold W_clear_bit in W2.
  assert (U1: 0 <= Znth 1 W <= Int.max_unsigned) by (apply u32_Znth; auto; lia).
  split; [ unfold W2; rewrite upd_Znth_Zlength; lia | ].
  split; [ unfold W2; apply u32_upd; auto; apply land_range; rep_lia | ].
  split; [ exact I | ].
  rewrite list_head_eq by (unfold W2; rewrite upd_Znth_Zlength; lia).
  unfold W2. rewrite upd_Znth_same by lia. rewrite clear_cap_bit. reflexivity.
Qed.

(* n = 0, second way: the status bit set, a zero head. *)
Lemma head_clear_byte: forall W, Zlength W = 64 -> Forall CapsSpecs.u32_ok W ->
  let W3 := W_clear_byte W in
  Zlength W3 = 64 /\ Forall CapsSpecs.u32_ok W3 /\ links W3 [] /\ list_head (sublist 0 16 W3) = hd 0 [].
Proof.
  intros W LW UW W3. unfold W_clear_byte in W3.
  assert (U1: 0 <= Znth 1 W <= Int.max_unsigned) by (apply u32_Znth; auto; lia).
  assert (U13: 0 <= Znth 13 W <= Int.max_unsigned) by (apply u32_Znth; auto; lia).
  assert (L2: Zlength (upd_Znth 1 W (Z.lor (Znth 1 W) 1048576)) = 64) by (rewrite upd_Znth_Zlength; lia).
  split; [ unfold W3; rewrite upd_Znth_Zlength; lia | ].
  split; [ unfold W3; apply u32_upd; [ apply u32_upd; auto; apply lor_range; rep_lia
                                     | apply land_range; rep_lia ] | ].
  split; [ exact I | ].
  rewrite list_head_eq by (unfold W3; rewrite upd_Znth_Zlength; lia).
  unfold W3. rewrite upd_Znth_same by lia. rewrite clear_head.
  destruct (_ =? 0); reflexivity.
Qed.

(* The header type of word 3: ((w >> 16) & 0x7f), as a Z. *)
Lemma htype_repr: forall w, 0 <= w <= Int.max_unsigned ->
  Int.unsigned (Int.and (Int.shru (Int.repr w) (Int.repr 16)) (Int.repr 127)) = Z.land (Z.shiftr w 16) 127.
Proof.
  intros w Hw. pose proof (shiftr_range w 16 Hw ltac:(lia)) as R.
  rewrite int_shru16 by assumption. rewrite int_and by rep_lia.
  apply Int.unsigned_repr. apply land_range; [ assumption | lia ].
Qed.

Lemma zext8: forall b, 0 <= b <= Byte.max_unsigned -> Int.zero_ext 8 (Int.repr b) = Int.repr b.
Proof.
  intros b Hb. rewrite <- (Int.repr_unsigned (Int.zero_ext 8 (Int.repr b))).
  rewrite Int.zero_ext_mod. 2: { change Int.zwordsize with 32. lia. }
  rewrite Int.unsigned_repr by rep_lia. change (two_p 8) with 256.
  rewrite Z.mod_small by rep_lia. reflexivity.
Qed.

(* The harness's assume on the initial header: header type <= 1 and a vendor other than 0xffff. *)
Definition hdr_ok (w3 w0: Z) : bool :=
  ((Z.land (Z.shiftr w3 16) 127 <=? 1) && negb (Z.land w0 65535 =? 65535))%bool.
Arguments hdr_ok : simpl never.

(* ---------------------------------------------------------------------- *)
(* The call of the walker: its precondition from main's state, and back.   *)
(* ---------------------------------------------------------------------- *)

Definition hv (b d f: Z) (ws: list Z) : reptype t_header :=
  (Vint (Int.repr b), (Vint (Int.repr d), (Vint (Int.repr f), map (fun z => Vint (Int.repr z)) ws))).

Definition sv (b d f: Z) (W: list Z) : reptype t_space :=
  (Vint (Int.repr b), (Vint (Int.repr d), (Vint (Int.repr f), map (fun z => Vint (Int.repr z)) W))).

Lemma sv_space_val: forall b d f W, sv b d f W = space_val (b, d, f) W.
Proof. reflexivity. Qed.

Lemma header_to_maybe: forall b d f ws p, isptr p ->
  data_at Tsh t_header (hv b d f ws) p |-- CapsSpecs.maybe_at Tsh CapsSpecs.t_header (CapsSpecs.header_val b d f ws) p.
Proof. intros. rewrite maybe_at_ptr by assumption. rewrite header_cs. apply derives_refl. Qed.

Lemma header_of_maybe: forall b d f ws p, isptr p ->
  CapsSpecs.maybe_at Tsh CapsSpecs.t_header (CapsSpecs.header_val b d f ws) p |-- data_at Tsh t_header (hv b d f ws) p.
Proof. intros. rewrite maybe_at_ptr by assumption. rewrite header_cs. apply derives_refl. Qed.

Lemma snapshot_to_maybe: forall p, isptr p ->
  data_at_ Tsh t_snapshot p |--
  CapsSpecs.maybe_at Tsh CapsSpecs.t_snapshot (@default_val CapsSpecs.CS CapsSpecs.t_snapshot) p.
Proof. intros. rewrite maybe_at_ptr by assumption. rewrite snapshot__cs. apply derives_refl. Qed.

Lemma snapshot_of_maybe: forall (v: val * list (val * val)) p, isptr p ->
  CapsSpecs.maybe_at Tsh CapsSpecs.t_snapshot v p |-- data_at Tsh t_snapshot v p.
Proof. intros. rewrite maybe_at_ptr by assumption. rewrite snapshot_cs. apply derives_refl. Qed.

Lemma read_ptr_result: forall p (rold: reptype CapsSpecs.t_result),
  func_ptr' (CapsSpecs.read_spec Dev_comp) p |--
  CapsSpecs.maybe_read Dev_comp p * CapsSpecs.maybe_at Tsh CapsSpecs.t_result rold nullval.
Proof. intros. rewrite maybe_at_null, sepcon_emp. apply maybe_read_ptr. Qed.

Lemma space_split: forall b d f W p, Zlength W = 64 -> Forall CapsSpecs.u32_ok W ->
  data_at Tsh t_space (sv b d f W) p |-- Dev_comp p (b, d, f) nil * data_at sh_main t_space (sv b d f W) p.
Proof.
  intros. rewrite <- (data_at_share_join sh_dev sh_main Tsh t_space (sv b d f W) p sh_join).
  apply sepcon_derives; [ | apply derives_refl ]. rewrite sv_space_val. apply dev_intro; auto.
Qed.

(* After the call: the device's share holds the words main kept, and every answer was one of them. *)
Lemma dev_back: forall b d f W h p,
  CapsSpecs.u8_ok b -> CapsSpecs.u8_ok d -> CapsSpecs.u8_ok f -> Zlength W = 64 -> Forall CapsSpecs.u32_ok W ->
  Dev_comp p (b, d, f) h * data_at sh_main t_space (sv b d f W) p |--
  !! (Forall (served W) h) && data_at Tsh t_space (sv b d f W) p.
Proof.
  intros b d f W h p Hb Hd Hf LW UW. unfold Dev_comp.
  rewrite exp_sepcon1. apply exp_left. intro W'.
  rewrite sepcon_andp_prop'. apply derives_extract_prop. intros [L' [U' S']].
  eapply derives_trans with (!! (W' = W) && sepcon (data_at sh_dev t_space (space_val (b, d, f) W') p)
                                                   (data_at sh_main t_space (sv b d f W) p)).
  { apply andp_right; [ | apply derives_refl ].
    rewrite sv_space_val. apply space_values_eq; auto. }
  apply derives_extract_prop. intro E. subst W'.
  apply andp_right; [ apply prop_right; exact S' | ].
  rewrite <- sv_space_val. rewrite (data_at_share_join _ _ _ _ _ _ sh_join). apply derives_refl.
Qed.

Lemma isnull_ptr: forall p, isptr p -> CapsSpecs.isnull p = false.
Proof. intros. unfold CapsSpecs.isnull. destruct (Val.eq p nullval); [ subst; contradiction | reflexivity ]. Qed.

Lemma args_ok_true: forall d f W, Zlength W = 64 -> d <= 31 -> f <= 7 ->
  Z.land (Z.shiftr (Znth 3 W) 16) 127 <= 1 -> Z.land (Znth 0 W) 65535 <> 65535 ->
  args_ok d f (sublist 0 16 W) = true.
Proof.
  intros d f W LW Hd Hf H3 H0. unfold args_ok. rewrite !Znth_sublist by lia. rewrite !Z.add_0_r.
  rewrite (proj2 (Z.leb_le d 31)) by lia. rewrite (proj2 (Z.leb_le f 7)) by lia.
  rewrite (proj2 (Z.leb_le _ 1)) by lia. rewrite (proj2 (Z.eqb_neq _ 65535)) by lia. reflexivity.
Qed.

Lemma header_undef: forall p,
  data_at_ Tsh t_header p |-- data_at Tsh t_header (Vundef, (Vundef, (Vundef, Zrepeat Vundef 16))) p.
Proof. intros. unfold data_at_. apply derives_refl. Qed.

(* The published headers, as values. *)
Definition cap_vals (W: list Z) (ats: list Z) : list (val * val) :=
  map (fun a => (Vint (Int.repr a), Vint (Int.repr (Znth (a / 4) W)))) ats.

Lemma map_cap_val: forall W ats, map CapsSpecs.cap_val (map (cap_of W) ats) = cap_vals W ats.
Proof. intros. unfold cap_vals. rewrite map_map. reflexivity. Qed.

Lemma cap_vals_Znth: forall W ats (rest: list (val * val)) i, 0 <= i < Zlength ats ->
  Znth i (cap_vals W ats ++ rest) = (Vint (Int.repr (Znth i ats)), Vint (Int.repr (Znth (Znth i ats / 4) W))).
Proof.
  intros. unfold cap_vals. rewrite Znth_app1 by (rewrite Zlength_map; lia). rewrite Znth_map by lia. reflexivity.
Qed.
