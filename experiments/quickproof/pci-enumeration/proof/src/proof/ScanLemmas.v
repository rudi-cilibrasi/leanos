(* Pure lemmas and tactics for the body proof of pci_enumerate_segment (ScanSegment.v): pointer tests on maybe_at
   objects, the scan model of Defs.v (run, next_read, scan) one answer at a time in prefix form, the index of a
   function and its bus/device/function, and the casts of the C expressions.  The memory of the snapshot is in
   ScanSnap.v. *)
Require Import VST.floyd.proofauto.
Require Import LeanosEnum.enum.code.
Require Import LeanosEnum.proof.Defs.
Require Import LeanosEnum.proof.EnumSpecs.
#[local] Existing Instance EnumSpecs.CS.
Local Open Scope Z_scope.

(* ---------- NULL tests ---------- *)

Definition b2z (b: bool) : Z := if b then 1 else 0.

Lemma isnull_null: isnull nullval = true.
Proof. unfold isnull. destruct (Val.eq nullval nullval); [ reflexivity | congruence ]. Qed.

Lemma isnull_nonnull: forall p, p <> nullval -> isnull p = false.
Proof. intros. unfold isnull. destruct (Val.eq p nullval); [ congruence | reflexivity ]. Qed.

Lemma isnull_false: forall p, isnull p = false -> p <> nullval.
Proof. intros p H E. subst. rewrite isnull_null in H. discriminate. Qed.

Lemma maybe_valid: forall sh t v p Q, readable_share sh -> sizeof t > 0 ->
  maybe_at sh t v p * Q |-- valid_pointer p.
Proof.
  intros. unfold maybe_at. destruct (Val.eq p nullval).
  - subst. apply valid_pointer_null.
  - apply sepcon_valid_pointer1. apply data_at_valid_ptr; auto.
Qed.

Lemma maybe_read_valid: forall Dev p Q, maybe_read Dev p * Q |-- valid_pointer p.
Proof.
  intros. unfold maybe_read. destruct (Val.eq p nullval).
  - subst. apply valid_pointer_null.
  - apply sepcon_valid_pointer1. apply func_ptr'_valid_pointer.
Qed.

Lemma maybe_at_nonnull: forall sh t v p, p <> nullval -> maybe_at sh t v p = data_at sh t v p.
Proof. intros. unfold maybe_at. destruct (Val.eq p nullval); [ contradiction | reflexivity ]. Qed.

Lemma maybe_at_null: forall sh t v, maybe_at sh t v nullval = emp.
Proof. intros. unfold maybe_at. destruct (Val.eq nullval nullval); [ reflexivity | congruence ]. Qed.

Lemma maybe_read_nonnull: forall Dev p, p <> nullval -> maybe_read Dev p = func_ptr' (read_spec Dev) p.
Proof. intros. unfold maybe_read. destruct (Val.eq p nullval); [ contradiction | reflexivity ]. Qed.

Ltac tc_ptr :=
  match goal with |- _ |-- denote_tc_test_eq ?p _ =>
    apply denote_tc_test_eq_split;
    [ first
      [ match goal with |- context [maybe_at ?sh ?t ?v p] =>
          eapply derives_trans; [ | apply (maybe_valid sh t v p TT); [ auto | simpl; try rewrite Z.max_r by lia; try lia ] ];
          cancel end
      | match goal with |- context [maybe_read ?D p] =>
          eapply derives_trans; [ | apply (maybe_read_valid D p TT) ]; cancel end ]
    | apply valid_pointer_null ]
  end.

Lemma notbool_ptr: forall p, is_pointer_or_null p ->
  force_val (sem_cast_i2bool (force_val (option_map (fun b : bool => bool2val (negb b)) (bool_val_p p)))) =
  Vint (Int.repr (b2z (isnull p))).
Proof.
  intros. destruct p; try contradiction.
  - simpl in H. subst. change (Vlong Int64.zero) with nullval. rewrite isnull_null. reflexivity.
  - rewrite isnull_nonnull by (intro X; inv X). reflexivity.
Qed.

Lemma b2z_true: forall c, Int.repr (b2z c) <> Int.zero -> c = true.
Proof. intros [ | ] H; [ reflexivity | exfalso; apply H; reflexivity ]. Qed.
Lemma b2z_false: forall c, Int.repr (b2z c) = Int.zero -> c = false.
Proof. intros [ | ] H; [ exfalso; apply Int.one_not_zero; exact H | reflexivity ]. Qed.

Ltac bfix :=
  repeat match goal with
  | H: Int.repr (b2z _) <> Int.zero |- _ => apply b2z_true in H
  | H: Int.repr (b2z _) = Int.zero |- _ => apply b2z_false in H
  end.

(* A branch whose condition contradicts what is known. *)
Ltac dead := first [ discriminate | contradiction
  | exfalso; match goal with H: ?a <> ?b |- _ => apply H; reflexivity end | exfalso; lia ].

(* ---------- the scan model, one answer at a time ---------- *)

Lemma run_app: forall h s s' rest, run s h = Some (Go s') -> run s (h ++ rest) = run s' rest.
Proof.
  induction h as [ | a h IH]; intros s s' rest H.
  - simpl in H. inv H. reflexivity.
  - simpl in H |- *. destruct (live s && answers (request s) a)%bool; [ | discriminate ].
    destruct (step s a) as [s1 | st i o]; [ eapply IH; eauto | destruct h; discriminate ].
Qed.

(* The dword position of the scan after dword w - 1 of a header: w, or 0 once the header is whole. *)
Definition wstate (w: Z) : Z := if w =? WORDS then 0 else w.

Lemma wstate_lt: forall w, w < WORDS -> wstate w = w.
Proof. intros. unfold wstate. rewrite (proj2 (Z.eqb_neq w WORDS)) by lia. reflexivity. Qed.

Lemma wstate_16: wstate 16 = 0.
Proof. reflexivity. Qed.

Lemma n_neq: forall n, 0 <= n < FUNCTIONS -> (n =? 65536) = false.
Proof. intros. apply Z.eqb_neq. unfold FUNCTIONS in H. lia. Qed.

(* The identity read of function n. *)
Lemma next_read_id: forall h n fs, run start h = Some (Go (n, 0, fs)) -> 0 <= n < FUNCTIONS ->
  next_read h = Some (n, 0).
Proof. intros. unfold next_read. rewrite H. simpl. rewrite n_neq by auto. reflexivity. Qed.

Lemma run_id: forall h n fs ok v, run start h = Some (Go (n, 0, fs)) -> 0 <= n < FUNCTIONS ->
  run start (h ++ [(n, 0, ok, v)]) =
  if negb ok then Some (Stop S_READ_FAILED n 0)
  else if Z.land v 65535 =? 65535 then Some (Go (n + 1, 0, fs))
  else if Zlength fs =? CAPACITY then Some (Stop S_CAPACITY_EXCEEDED n 0)
  else Some (Go (n + 1, 1, (n, [v]) :: fs)).
Proof.
  intros. rewrite (run_app _ _ _ _ H). simpl. rewrite n_neq, Z.eqb_refl by auto. simpl.
  destruct ok; simpl; [ | reflexivity ].
  destruct (Z.land v 65535 =? 65535); [ reflexivity | ].
  destruct (Zlength fs =? CAPACITY); reflexivity.
Qed.

Lemma scan_id_fail: forall h n fs v, run start h = Some (Go (n, 0, fs)) -> 0 <= n < FUNCTIONS ->
  scan (h ++ [(n, 0, false, v)]) = Some (S_READ_FAILED, n, 0, nil).
Proof. intros. unfold scan. rewrite (run_id h n fs) by auto. reflexivity. Qed.

Lemma run_id_absent: forall h n fs v, run start h = Some (Go (n, 0, fs)) -> 0 <= n < FUNCTIONS ->
  Z.land v 65535 = 65535 -> run start (h ++ [(n, 0, true, v)]) = Some (Go (n + 1, 0, fs)).
Proof. intros. rewrite (run_id h n fs) by auto. simpl. rewrite H1. reflexivity. Qed.

Lemma scan_id_full: forall h n fs v, run start h = Some (Go (n, 0, fs)) -> 0 <= n < FUNCTIONS ->
  Z.land v 65535 <> 65535 -> Zlength fs = CAPACITY ->
  scan (h ++ [(n, 0, true, v)]) = Some (S_CAPACITY_EXCEEDED, n, 0, nil).
Proof.
  intros. unfold scan. rewrite (run_id h n fs) by auto. simpl.
  rewrite (proj2 (Z.eqb_neq _ _) H1), H2. reflexivity.
Qed.

Lemma run_id_found: forall h n fs v, run start h = Some (Go (n, 0, fs)) -> 0 <= n < FUNCTIONS ->
  Z.land v 65535 <> 65535 -> Zlength fs <> CAPACITY ->
  run start (h ++ [(n, 0, true, v)]) = Some (Go (n + 1, wstate 1, (n, [v]) :: fs)).
Proof.
  intros. rewrite (run_id h n fs) by auto. simpl.
  rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2). reflexivity.
Qed.

(* Dword w (1..15) of the header of function n, found at the identity read before. *)
Lemma next_read_w: forall h n w ws fs, run start h = Some (Go (n + 1, wstate w, (n, ws) :: fs)) ->
  1 <= w < WORDS -> next_read h = Some (n, 4 * w).
Proof.
  intros. rewrite wstate_lt in H by lia. unfold next_read. rewrite H. unfold live, request.
  rewrite (proj2 (Z.eqb_neq w 0)) by lia. simpl. f_equal. f_equal. lia.
Qed.

Lemma run_w: forall h n w ws fs ok v, run start h = Some (Go (n + 1, wstate w, (n, ws) :: fs)) ->
  1 <= w < WORDS ->
  run start (h ++ [(n, 4 * w, ok, v)]) =
  if ok then Some (Go (n + 1, wstate (w + 1), (n, ws ++ [v]) :: fs)) else Some (Stop S_READ_FAILED n (4 * w)).
Proof.
  intros. rewrite wstate_lt in H by lia. rewrite (run_app _ _ _ _ H). unfold run, live, answers, request, step.
  rewrite (proj2 (Z.eqb_neq w 0)) by lia. cbn [andb negb fst snd].
  replace (n + 1 - 1) with n by lia. rewrite !Z.eqb_refl. cbn [andb negb].
  destruct ok; [ | reflexivity ]. cbn [negb add_word].
  unfold wstate, WORDS. destruct (Z.eqb_spec w (16 - 1)); destruct (Z.eqb_spec (w + 1) 16); try lia; reflexivity.
Qed.

Lemma scan_w_fail: forall h n w ws fs v, run start h = Some (Go (n + 1, wstate w, (n, ws) :: fs)) ->
  1 <= w < WORDS -> scan (h ++ [(n, 4 * w, false, v)]) = Some (S_READ_FAILED, n, 4 * w, nil).
Proof. intros. unfold scan. rewrite (run_w h n w ws fs) by auto. reflexivity. Qed.

Lemma run_w_ok: forall h n w ws fs v, run start h = Some (Go (n + 1, wstate w, (n, ws) :: fs)) ->
  1 <= w < WORDS -> run start (h ++ [(n, 4 * w, true, v)]) = Some (Go (n + 1, wstate (w + 1), (n, ws ++ [v]) :: fs)).
Proof. intros. rewrite (run_w h n w ws fs) by auto. reflexivity. Qed.

Lemma scan_done: forall h fs, run start h = Some (Go (FUNCTIONS, 0, fs)) -> scan h = Some (S_OK, 0, 0, rev fs).
Proof. intros. unfold scan. rewrite H. reflexivity. Qed.

(* ---------- the index of a function ---------- *)

Lemma bus_of_idx: forall b d f, 0 <= b -> 0 <= d < 32 -> 0 <= f < 8 -> bus_of (b * 256 + d * 8 + f) = b.
Proof.
  intros. unfold bus_of. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  replace (b * 256 + d * 8 + f) with ((d * 8 + f) + b * 256) by ring.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma dev_of_idx: forall b d f, 0 <= b -> 0 <= d < 32 -> 0 <= f < 8 -> dev_of (b * 256 + d * 8 + f) = d.
Proof.
  intros. unfold dev_of. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  replace (b * 256 + d * 8 + f) with (f + (b * 32 + d) * 8) by ring.
  rewrite Z.div_add by lia. rewrite (Z.div_small f 8) by lia. rewrite Z.add_0_l.
  change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2 ^ 5) with 32.
  replace (b * 32 + d) with (d + b * 32) by ring. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma fn_of_idx: forall b d f, 0 <= b -> 0 <= d < 32 -> 0 <= f < 8 -> fn_of (b * 256 + d * 8 + f) = f.
Proof.
  intros. unfold fn_of. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  replace (b * 256 + d * 8 + f) with (f + (b * 32 + d) * 8) by ring.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma bdf_zero: bus_of 0 = 0 /\ dev_of 0 = 0 /\ fn_of 0 = 0.
Proof. repeat split; reflexivity. Qed.

(* ---------- casts ---------- *)

Lemma zext8_small: forall x, 0 <= x <= 255 -> Int.zero_ext 8 (Int.repr x) = Int.repr x.
Proof.
  intros. rewrite Int.zero_ext_and by lia. change (two_p 8 - 1) with (Z.ones 8).
  rewrite and_repr, Z.land_ones by lia. rewrite Z.mod_small by (change (2 ^ 8) with 256; lia). reflexivity.
Qed.

Lemma zext16_land: forall x, Int.zero_ext 16 (Int.repr x) = Int.repr (Z.land x 65535).
Proof. intros. rewrite Int.zero_ext_and by lia. change (two_p 16 - 1) with 65535. apply and_repr. Qed.

Lemma land65535_range: forall a, 0 <= Z.land a 65535 < 65536.
Proof.
  intros. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. reflexivity.
Qed.

Lemma offset_cast: forall w, 0 <= w < 16 ->
  Int.zero_ext 8 (Int.zero_ext 8 (Int.mul (Int.repr w) (Int.repr 4))) = Int.repr (4 * w).
Proof. intros. rewrite mul_repr, Z.mul_comm. rewrite !zext8_small by lia. reflexivity. Qed.
