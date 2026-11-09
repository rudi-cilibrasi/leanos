(* Law enumeration_exact: what main's proof needs besides the device: the arguments that may be NULL, the scan's
   objects under the unit's compspecs and the law's, words and comparisons. *)
Require Import VST.floyd.proofauto.
Require Import LeanosEnum.proof.Defs.
Require LeanosEnum.proof.EnumSpecs.
Require Import LeanosEnum.proof.LawProg LeanosEnum.proof.LawRun LeanosEnum.proof.LawSpecs.
Local Open Scope Z_scope.
#[export] Existing Instance LawProg.LCS.

Definition b2z (b: bool) : Z := if b then 1 else 0.

Lemma zext8: forall x, 0 <= x <= Byte.max_unsigned -> Int.zero_ext 8 (Int.repr x) = Int.repr x.
Proof.
  intros. apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. rep_lia.
Qed.

Ltac zext :=
  repeat match goal with |- context [Int.zero_ext 8 (Int.repr ?x)] => rewrite (zext8 x) by rep_lia end.

(* forward, with the typecheck side goals entailer! proves. *)
Ltac fw := forward; try solve [ entailer!; try rep_lia ].

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

Lemma Int_lt_repr: forall a b, Int.min_signed <= a <= Int.max_signed -> Int.min_signed <= b <= Int.max_signed ->
  Int.lt (Int.repr a) (Int.repr b) = (a <? b).
Proof.
  intros a b Ha Hb. unfold Int.lt. rewrite !Int.signed_repr by auto.
  destruct (zlt a b); destruct (Z.ltb_spec a b); auto; lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* The arguments that may be NULL                                          *)
(* ---------------------------------------------------------------------- *)

Lemma sel_isnull: forall (b: bool) p, isptr p -> EnumSpecs.isnull (if b then nullval else p) = b.
Proof.
  intros b p P. unfold EnumSpecs.isnull. destruct b.
  - rewrite if_true by reflexivity. reflexivity.
  - rewrite if_false; [ reflexivity | destruct p; try contradiction; discriminate ].
Qed.

Lemma sel_eq_null: forall (b: bool) p, isptr p -> (if b then nullval else p) = nullval -> b = true.
Proof. intros [|] p P E; [ reflexivity | subst; contradiction ]. Qed.

Lemma sel_ne_null: forall (b: bool) p, (if b then nullval else p) <> nullval -> b = false.
Proof. intros [|] p N; [ exfalso; apply N; reflexivity | reflexivity ]. Qed.

Lemma sel_tc_test: forall (b: bool) p (P: mpred), (P |-- valid_pointer p) -> isptr p ->
  P |-- denote_tc_test_eq (if b then nullval else p) (Vlong (Int64.repr 0)).
Proof.
  intros b p P V I. apply denote_tc_test_eq_split; [ | apply valid_pointer_zero64; reflexivity ].
  destruct b; [ apply valid_pointer_null | exact V ].
Qed.

Lemma sel_ptr_or_null: forall (b: bool) p, isptr p -> is_pointer_or_null (if b then nullval else p).
Proof. intros [|] p P; [ unfold nullval; simpl; reflexivity | destruct p; try contradiction; exact I ]. Qed.

Lemma b2z_true: forall c, Int.repr (b2z c) <> Int.zero -> c = true.
Proof. intros [|] H; [ reflexivity | exfalso; apply H; reflexivity ]. Qed.

Lemma b2z_false: forall c, Int.repr (b2z c) = Int.zero -> c = false.
Proof. intros [|] H; [ exfalso; apply Int.one_not_zero; exact H | reflexivity ]. Qed.

Ltac b2z_hyps :=
  repeat match goal with
  | E: Int.repr (b2z _) <> Int.zero |- _ => apply b2z_true in E
  | E: Int.repr (b2z _) = Int.zero |- _ => apply b2z_false in E
  end.

(* ---------------------------------------------------------------------- *)
(* The scan's arguments, under the unit's compspecs                        *)
(* ---------------------------------------------------------------------- *)

Lemma data_at_cs: forall sh t (v: @reptype EnumSpecs.CS t) (v': @reptype LCS t) p,
  JMeq v v' -> cs_preserve_type EnumSpecs.CS LCS (@coeq _ _ LCR) t = true ->
  @data_at EnumSpecs.CS sh t v p = @data_at LCS sh t v' p.
Proof.
  intros. apply (f_equal (fun f => f p)). apply (@data_at_change_composite EnumSpecs.CS LCS LCR); auto.
Qed.

(* An object of the harness at p, given to the scan as its argument p or NULL (any contents: the scan
   overwrites them), and what stays with the harness. *)
Lemma maybe_split_: forall (b: bool) sh t (v': @reptype LCS t) p,
  isptr p -> cs_preserve_type EnumSpecs.CS LCS (@coeq _ _ LCR) t = true ->
  @data_at LCS sh t v' p |--
  (EnumSpecs.maybe_at sh t (@default_val EnumSpecs.CS t) (if b then nullval else p) *
   (if b then @data_at LCS sh t v' p else emp))%logic.
Proof.
  intros b sh t v' p P C. unfold EnumSpecs.maybe_at. destruct b.
  - rewrite if_true by reflexivity. rewrite emp_sepcon. apply derives_refl.
  - rewrite if_false by (destruct p; try contradiction; discriminate). rewrite sepcon_emp.
    change (@data_at EnumSpecs.CS sh t (@default_val EnumSpecs.CS t) p) with (@data_at_ EnumSpecs.CS sh t p).
    eapply derives_trans; [ apply data_at_data_at_ | ].
    rewrite (@data_at__change_composite EnumSpecs.CS LCS LCR sh t C). apply derives_refl.
Qed.

Lemma maybe_join': forall (b: bool) sh t (vn: @reptype EnumSpecs.CS t) (vn': @reptype LCS t) (vo: @reptype LCS t) p,
  isptr p -> JMeq vn vn' -> cs_preserve_type EnumSpecs.CS LCS (@coeq _ _ LCR) t = true ->
  (EnumSpecs.maybe_at sh t vn (if b then nullval else p) * (if b then @data_at LCS sh t vo p else emp))%logic |--
  @data_at LCS sh t (if b then vo else vn') p.
Proof.
  intros b sh t vn vn' vo p P J C. unfold EnumSpecs.maybe_at. destruct b.
  - rewrite if_true by reflexivity. rewrite emp_sepcon. apply derives_refl.
  - rewrite if_false by (destruct p; try contradiction; discriminate). rewrite sepcon_emp.
    rewrite (data_at_cs sh t vn vn' p J C). apply derives_refl.
Qed.

Lemma maybe_read_split: forall (b: bool) p,
  func_ptr' (EnumSpecs.read_spec Dev_exact) p |--
  (EnumSpecs.maybe_read Dev_exact (if b then nullval else p) * func_ptr' (EnumSpecs.read_spec Dev_exact) p)%logic.
Proof.
  intros b p. unfold EnumSpecs.maybe_read. rewrite split_func_ptr' at 1. destruct b.
  - rewrite if_true by reflexivity. apply sepcon_derives; [ unfold func_ptr'; apply andp_left2 | ]; apply derives_refl.
  - destruct (Val.eq p nullval); [ | apply derives_refl ].
    apply sepcon_derives; [ unfold func_ptr'; apply andp_left2 | ]; apply derives_refl.
Qed.

Lemma if_pair {A B: Type}: forall (b: bool) (x1 y1: A) (x2 y2: B),
  (if b then (x1, x2) else (y1, y2)) = (if b then x1 else y1, if b then x2 else y2).
Proof. intros [|]; reflexivity. Qed.

Lemma if_vint: forall (b: bool) x y, (if b then Vint (Int.repr x) else Vint (Int.repr y)) = Vint (Int.repr (if b then x else y)).
Proof. intros [|]; reflexivity. Qed.

Lemma if_same {A: Type}: forall (b: bool) (x: A), (if b then x else x) = x.
Proof. intros [|]; reflexivity. Qed.

Lemma sel_cmp_eq: forall (b: bool) p, isptr p ->
  force_val (sem_cmp_pp Ceq (if b then nullval else p) (Vlong (Int64.repr 0))) = Vint (Int.repr (b2z b)).
Proof. intros [|] p P; [ reflexivity | destruct p; try contradiction; reflexivity ]. Qed.

Lemma sel_cmp_ne: forall (b: bool) p, isptr p ->
  force_val (sem_cmp_pp Cne (if b then nullval else p) (Vlong (Int64.repr 0))) = Vint (Int.repr (b2z (negb b))).
Proof. intros [|] p P; [ reflexivity | destruct p; try contradiction; reflexivity ]. Qed.

Lemma read_TT: forall r f,
  (EnumSpecs.maybe_read Dev_exact r * func_ptr' (EnumSpecs.read_spec Dev_exact) f)%logic |--
  (TT * func_ptr' (EnumSpecs.read_spec Dev_exact) f)%logic.
Proof. intros. apply sepcon_derives; [ apply TT_right | apply derives_refl ]. Qed.
