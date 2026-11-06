(* Law capabilities_adversarial: arithmetic on the harness's words, and reading the device's log. *)
Require Import VST.floyd.proofauto.
Require Import LeanosCaps.proof.Defs.
Require LeanosCaps.proof.CapsSpecs.
Require Import LeanosCaps.proof.AdvProg LeanosCaps.proof.AdvWalk LeanosCaps.proof.AdvFacts LeanosCaps.proof.AdvSpecs.
Local Open Scope Z_scope.

Lemma land_range: forall a b, 0 <= a <= Int.max_unsigned -> 0 <= Z.land a b <= Int.max_unsigned.
Proof.
  intros a b Ha. split; [ apply Z.land_nonneg; lia | ].
  assert (E: Z.land a (Z.ones 32) = a) by (rewrite Z.land_ones by lia; apply Z.mod_small; rep_lia).
  rewrite <- E. rewrite <- Z.land_assoc, (Z.land_comm (Z.ones 32) b), Z.land_assoc, Z.land_ones by lia.
  pose proof (Z.mod_pos_bound (Z.land a b) (2 ^ 32) ltac:(lia)).
  change (2 ^ 32) with (Int.max_unsigned + 1) in *. lia.
Qed.

Lemma shiftr_range: forall v n, 0 <= v <= Int.max_unsigned -> 0 <= n -> 0 <= Z.shiftr v n <= Int.max_unsigned.
Proof.
  intros v n Hv Hn. rewrite Z.shiftr_div_pow2 by lia. split.
  - apply Z.div_pos; [ lia | ]. pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) Hn). lia.
  - apply Z.le_trans with v; [ | lia ]. apply Z.div_le_upper_bound.
    + pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) Hn). lia.
    + assert (1 <= 2 ^ n) by (apply Z.pow_le_mono_r with (a := 2) (b := 0) (c := n) in Hn; simpl in Hn; lia). nia.
Qed.

(* (v >> 8) & 255 on a 32-bit word. *)
Lemma nptr_repr: forall v, 0 <= v <= Int.max_unsigned ->
  Int.and (Int.shru (Int.repr v) (Int.repr 8)) (Int.repr 255) = Int.repr (Z.land (Z.shiftr v 8) 255).
Proof.
  intros v Hv. unfold Int.shru. rewrite !Int.unsigned_repr by rep_lia. apply and_repr.
Qed.

Lemma repr_eq_unsigned: forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.repr a = Int.repr b -> a = b.
Proof.
  intros a b Ha Hb E. apply (f_equal Int.unsigned) in E. rewrite !Int.unsigned_repr in E by auto. exact E.
Qed.

Lemma repr_neq_unsigned: forall a b, Int.repr a <> Int.repr b -> a <> b.
Proof. intros a b N E. subst. apply N. reflexivity. Qed.

Lemma Int_eq_repr: forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.eq (Int.repr a) (Int.repr b) = (a =? b).
Proof.
  intros a b Ha Hb. rewrite eq_repr_zeq by auto. destruct (zeq a b); destruct (Z.eqb_spec a b); auto; lia.
Qed.

Lemma Int_ltu_repr: forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.ltu (Int.repr a) (Int.repr b) = (a <? b).
Proof.
  intros a b Ha Hb. rewrite ltu_repr_zlt by auto. destruct (zlt a b); destruct (Z.ltb_spec a b); auto; lia.
Qed.

Lemma answers_ok_Znth: forall h i, answers_ok h -> 0 <= i < Zlength h ->
  0 <= aoff (Znth i h) <= 252 /\ 0 <= aval (Znth i h) <= Int.max_unsigned.
Proof.
  intros h i A Hi. unfold answers_ok in A. pose proof (proj1 (Forall_Znth _ _) A i Hi) as X. simpl in X.
  unfold CapsSpecs.u32_ok in X. exact X.
Qed.

Lemma words_Znth: forall words i, Forall CapsSpecs.u32_ok words -> 0 <= i < Zlength words ->
  0 <= Znth i words <= Int.max_unsigned.
Proof.
  intros words i A Hi. pose proof (proj1 (Forall_Znth _ _) A i Hi) as X. exact X.
Qed.

Lemma Znth_words: forall words i, 0 <= i < Zlength words ->
  Znth i (map (fun w => Vint (Int.repr w)) words) = Vint (Int.repr (Znth i words)).
Proof. intros. rewrite Znth_map by auto. reflexivity. Qed.

Lemma list_head_repr: forall words, Zlength words = 16 -> Forall CapsSpecs.u32_ok words ->
  0 <= list_head words <= Int.max_unsigned.
Proof. intros. pose proof (list_head_range words). rep_lia. Qed.

(* Loads from arrays of a struct give Znth at the reptype of the element type, or with Vundef as the default:
   as Znth on val with its Inhabitant. *)
Ltac znth_val :=
  repeat match goal with
  | |- context [@Znth ?A ?d ?i ?l] =>
      lazymatch d with Inhabitant_val => fail | _ => change (@Znth A d i l) with (@Znth val Inhabitant_val i l) end
  end.

Lemma zext8: forall x, 0 <= x <= Byte.max_unsigned -> Int.zero_ext 8 (Int.repr x) = Int.repr x.
Proof.
  intros. apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. rep_lia.
Qed.

Ltac zext :=
  repeat match goal with |- context [Int.zero_ext 8 (Int.repr ?x)] => rewrite (zext8 x) by rep_lia end.

(* Freezing (as the reference proofs' Law3Tac): the indices of the SEP items of R that mention neither p nor q. *)
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

Ltac freeze_except p q F :=
  match goal with
  | |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
      let L := sep_idx_free R p q 0 in let L := eval cbn in L in freeze_tac L F
  end.

Ltac sep_idx_of R p i :=
  lazymatch R with
  | ?x :: ?R' => match x with context [p] => eval cbn in i | _ => sep_idx_of R' p (Z.succ i) end
  end.

Ltac sep_front1 p1 :=
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
    let i := sep_idx_of R p1 0%Z in grab_indexes_SEP (i :: nil) end.

(* forward, with the typecheck side goals entailer! proves. *)
Ltac fw := forward; try solve [ entailer!; try rep_lia ].

(* ---------------------------------------------------------------------- *)
(* The arguments that may be NULL                                          *)
(* ---------------------------------------------------------------------- *)

Lemma sel_isnull: forall (b: bool) p, isptr p -> CapsSpecs.isnull (if b then nullval else p) = b.
Proof.
  intros b p P. unfold CapsSpecs.isnull. destruct b.
  - rewrite if_true by reflexivity. reflexivity.
  - rewrite if_false; [ reflexivity | destruct p; try contradiction; discriminate ].
Qed.

Lemma sel_eq_null: forall (b: bool) p, isptr p -> (if b then nullval else p) = nullval -> b = true.
Proof. intros [|] p P E; [ reflexivity | subst; contradiction ]. Qed.

Lemma sel_ne_null: forall (b: bool) p, (if b then nullval else p) <> nullval -> b = false.
Proof. intros [|] p N; [ exfalso; apply N; reflexivity | reflexivity ]. Qed.

Lemma sel_cmp_eq: forall (b: bool) p, isptr p ->
  force_val (sem_cmp_pp Ceq (if b then nullval else p) (Vlong (Int64.repr 0))) = Vint (Int.repr (CapsSpecs.b2z b)).
Proof. intros [|] p P; [ reflexivity | destruct p; try contradiction; reflexivity ]. Qed.

Lemma sel_cmp_ne: forall (b: bool) p, isptr p ->
  force_val (sem_cmp_pp Cne (if b then nullval else p) (Vlong (Int64.repr 0))) = Vint (Int.repr (CapsSpecs.b2z (negb b))).
Proof. intros [|] p P; [ reflexivity | destruct p; try contradiction; reflexivity ]. Qed.

Lemma sel_tc_test: forall (b: bool) p (P: mpred), (P |-- valid_pointer p) -> isptr p ->
  P |-- denote_tc_test_eq (if b then nullval else p) (Vlong (Int64.repr 0)).
Proof.
  intros b p P V I. apply denote_tc_test_eq_split; [ | apply valid_pointer_zero64; reflexivity ].
  destruct b; [ apply valid_pointer_null | exact V ].
Qed.

Lemma b2z_true: forall c, Int.repr (CapsSpecs.b2z c) <> Int.zero -> c = true.
Proof. intros [|] H; [ reflexivity | exfalso; apply H; reflexivity ]. Qed.

Lemma b2z_false: forall c, Int.repr (CapsSpecs.b2z c) = Int.zero -> c = false.
Proof. intros [|] H; [ exfalso; apply Int.one_not_zero; exact H | reflexivity ]. Qed.

Ltac b2z_hyps :=
  repeat match goal with
  | E: Int.repr (CapsSpecs.b2z _) <> Int.zero |- _ => apply b2z_true in E
  | E: Int.repr (CapsSpecs.b2z _) = Int.zero |- _ => apply b2z_false in E
  end.

(* ---------------------------------------------------------------------- *)
(* The walker's arguments, under the unit's compspecs                      *)
(* ---------------------------------------------------------------------- *)

Lemma data_at_cs: forall sh t (v: @reptype CapsSpecs.CS t) (v': @reptype LCS t) p,
  JMeq v v' -> cs_preserve_type CapsSpecs.CS LCS (@coeq _ _ LCR) t = true ->
  @data_at CapsSpecs.CS sh t v p = @data_at LCS sh t v' p.
Proof.
  intros. apply (f_equal (fun f => f p)). apply (@data_at_change_composite CapsSpecs.CS LCS LCR); auto.
Qed.

(* An object of the harness at p, as the walker's maybe_at of the argument p or NULL, and what stays with the
   harness. *)
Lemma maybe_split: forall (b: bool) sh t (v: @reptype CapsSpecs.CS t) (v': @reptype LCS t) p,
  isptr p -> JMeq v v' -> cs_preserve_type CapsSpecs.CS LCS (@coeq _ _ LCR) t = true ->
  @data_at LCS sh t v' p =
  (CapsSpecs.maybe_at sh t v (if b then nullval else p) * (if b then @data_at LCS sh t v' p else emp))%logic.
Proof.
  intros b sh t v v' p P J C. unfold CapsSpecs.maybe_at. destruct b.
  - rewrite if_true by reflexivity. rewrite emp_sepcon. reflexivity.
  - rewrite if_false by (destruct p; try contradiction; discriminate). rewrite sepcon_emp.
    symmetry. apply data_at_cs; auto.
Qed.

Lemma maybe_join: forall (b: bool) sh t (vn: @reptype CapsSpecs.CS t) (vn': @reptype LCS t) (vo: @reptype LCS t) p,
  isptr p -> JMeq vn vn' -> cs_preserve_type CapsSpecs.CS LCS (@coeq _ _ LCR) t = true ->
  (CapsSpecs.maybe_at sh t vn (if b then nullval else p) * (if b then @data_at LCS sh t vo p else emp))%logic =
  @data_at LCS sh t (if b then vo else vn') p.
Proof.
  intros b sh t vn vn' vo p P J C. unfold CapsSpecs.maybe_at. destruct b.
  - rewrite if_true by reflexivity. rewrite emp_sepcon. reflexivity.
  - rewrite if_false by (destruct p; try contradiction; discriminate). rewrite sepcon_emp.
    apply data_at_cs; auto.
Qed.

Lemma maybe_read_split: forall (b: bool) p,
  func_ptr' (CapsSpecs.read_spec Dev_adv) p |--
  (CapsSpecs.maybe_read Dev_adv (if b then nullval else p) * func_ptr' (CapsSpecs.read_spec Dev_adv) p)%logic.
Proof.
  intros b p. unfold CapsSpecs.maybe_read. rewrite split_func_ptr' at 1. destruct b.
  - rewrite if_true by reflexivity. apply sepcon_derives; [ unfold func_ptr'; apply andp_left2 | ]; apply derives_refl.
  - destruct (Val.eq p nullval); [ | apply derives_refl ].
    apply sepcon_derives; [ unfold func_ptr'; apply andp_left2 | ]; apply derives_refl.
Qed.

Lemma dev_init: forall bus dev fn p,
  data_at Tsh t_device
    (Vint (Int.repr bus), (Vint (Int.repr dev), (Vint (Int.repr fn), (Vint (Int.repr 0),
     snd (snd (snd (snd (default_val t_device)))))))) p
  |-- Dev_adv p (bus, dev, fn) nil.
Proof.
  intros. unfold Dev_adv. Exists (Zrepeat Vundef 52) (Zrepeat Vundef 52) (Zrepeat Vundef 52).
  unfold dev_val, CapsSpecs.bus_of, CapsSpecs.dev_of, CapsSpecs.fn_of. simpl fst; simpl snd.
  rewrite Zlength_nil. entailer!.
  split; [ constructor | ]. unfold log_at. split; [ reflexivity | ]. split; [ reflexivity | ].
  split; [ reflexivity | ]. intros i Hi. rewrite Zlength_nil in Hi. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* The argument test of the harness                                        *)
(* ---------------------------------------------------------------------- *)

Lemma Int_lt_repr: forall a b, Int.min_signed <= a <= Int.max_signed -> Int.min_signed <= b <= Int.max_signed ->
  Int.lt (Int.repr a) (Int.repr b) = (a <? b).
Proof.
  intros a b Ha Hb. unfold Int.lt. rewrite !Int.signed_repr by auto.
  destruct (zlt a b); destruct (Z.ltb_spec a b); auto; lia.
Qed.

Lemma shru_and_repr: forall v k m, 0 <= v <= Int.max_unsigned -> 0 <= k < 32 -> 0 <= m <= Int.max_unsigned ->
  Int.and (Int.shru (Int.repr v) (Int.repr k)) (Int.repr m) = Int.repr (Z.land (Z.shiftr v k) m).
Proof.
  intros v k m Hv Hk Hm. unfold Int.shru. rewrite !Int.unsigned_repr by rep_lia. apply and_repr.
Qed.

Lemma inv_eq: forall (rb ib sb: bool) dev fn ws,
  (rb || ib || sb || (31 <? dev) || (7 <? fn) || (1 <? Z.land (Z.shiftr (Znth 3 ws) 16) 127) ||
   (Z.land (Znth 0 ws) 65535 =? 65535))%bool =
  (rb || ib || sb || negb (args_ok dev fn ws))%bool.
Proof.
  intros. unfold args_ok. rewrite !Z.leb_antisym.
  destruct rb, ib, sb, (31 <? dev), (7 <? fn), (1 <? _), (_ =? 65535); reflexivity.
Qed.

Lemma bool_cast_b2z: forall c, force_val (sem_cast_i2bool (Vint (Int.repr (CapsSpecs.b2z c)))) = Vint (Int.repr (CapsSpecs.b2z c)).
Proof. intros [|]; reflexivity. Qed.

(* The same, giving the walker an object of any contents (it overwrites them). *)
Lemma maybe_split_: forall (b: bool) sh t (v': @reptype LCS t) p,
  isptr p -> cs_preserve_type CapsSpecs.CS LCS (@coeq _ _ LCR) t = true ->
  @data_at LCS sh t v' p |--
  (CapsSpecs.maybe_at sh t (@default_val CapsSpecs.CS t) (if b then nullval else p) *
   (if b then @data_at LCS sh t v' p else emp))%logic.
Proof.
  intros b sh t v' p P C. unfold CapsSpecs.maybe_at. destruct b.
  - rewrite if_true by reflexivity. rewrite emp_sepcon. apply derives_refl.
  - rewrite if_false by (destruct p; try contradiction; discriminate). rewrite sepcon_emp.
    change (@data_at CapsSpecs.CS sh t (@default_val CapsSpecs.CS t) p) with (@data_at_ CapsSpecs.CS sh t p).
    eapply derives_trans; [ apply data_at_data_at_ | ].
    rewrite (@data_at__change_composite CapsSpecs.CS LCS LCR sh t C). apply derives_refl.
Qed.

Lemma sel_ptr_or_null: forall (b: bool) p, isptr p -> is_pointer_or_null (if b then nullval else p).
Proof. intros [|] p P; [ unfold nullval; simpl; reflexivity | destruct p; try contradiction; exact I ]. Qed.

Lemma maybe_join': forall (b: bool) sh t (vn: @reptype CapsSpecs.CS t) (vn': @reptype LCS t) (vo: @reptype LCS t) p,
  isptr p -> JMeq vn vn' -> cs_preserve_type CapsSpecs.CS LCS (@coeq _ _ LCR) t = true ->
  (CapsSpecs.maybe_at sh t vn (if b then nullval else p) * (if b then @data_at LCS sh t vo p else emp))%logic |--
  @data_at LCS sh t (if b then vo else vn') p.
Proof. intros. rewrite (maybe_join b sh t vn vn' vo p) by auto. apply derives_refl. Qed.

Lemma maybe_split_snap: forall (b: bool) sh (v': @reptype LCS CapsSpecs.t_snapshot) p, isptr p ->
  @data_at LCS sh CapsSpecs.t_snapshot v' p |--
  (CapsSpecs.maybe_at sh CapsSpecs.t_snapshot (@default_val LCS CapsSpecs.t_snapshot) (if b then nullval else p) *
   (if b then @data_at LCS sh CapsSpecs.t_snapshot v' p else emp))%logic.
Proof. intros. apply (maybe_split_ b sh CapsSpecs.t_snapshot v' p H). reflexivity. Qed.

Lemma maybe_split_res: forall (b: bool) sh (v': @reptype LCS CapsSpecs.t_result) p, isptr p ->
  @data_at LCS sh CapsSpecs.t_result v' p |--
  (CapsSpecs.maybe_at sh CapsSpecs.t_result (@default_val LCS CapsSpecs.t_result) (if b then nullval else p) *
   (if b then @data_at LCS sh CapsSpecs.t_result v' p else emp))%logic.
Proof. intros. apply (maybe_split_ b sh CapsSpecs.t_result v' p H). reflexivity. Qed.

Lemma if_pair {A B: Type}: forall (b: bool) (x1 y1: A) (x2 y2: B),
  (if b then (x1, x2) else (y1, y2)) = (if b then x1 else y1, if b then x2 else y2).
Proof. intros [|]; reflexivity. Qed.

Lemma if_vint: forall (b: bool) x y, (if b then Vint (Int.repr x) else Vint (Int.repr y)) = Vint (Int.repr (if b then x else y)).
Proof. intros [|]; reflexivity. Qed.

Lemma if_same {A: Type}: forall (b: bool) (x: A), (if b then x else x) = x.
Proof. intros [|]; reflexivity. Qed.
