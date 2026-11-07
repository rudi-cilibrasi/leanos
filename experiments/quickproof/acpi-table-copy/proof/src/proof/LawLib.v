(* Law table_copy_exact: arithmetic of the harness's 32- and 64-bit words, and the tactics the proofs of its
   functions share. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosAcpi.harness.table_copy_exact.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.LawProg LeanosAcpi.proof.LawDefs LeanosAcpi.proof.LawFacts.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[export] Existing Instance LawProg.LCS.

Lemma Int64_eq_repr: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.eq (Int64.repr a) (Int64.repr b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold Int64.eq. rewrite !Int64.unsigned_repr by auto.
  destruct (zeq a b); destruct (Z.eqb_spec a b); auto; lia.
Qed.

Lemma Int64_ltu_repr: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr a) (Int64.repr b) = (a <? b).
Proof.
  intros a b Ha Hb. unfold Int64.ltu. rewrite !Int64.unsigned_repr by auto.
  destruct (zlt a b); destruct (Z.ltb_spec a b); auto; lia.
Qed.

Lemma Int_eq_repr: forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.eq (Int.repr a) (Int.repr b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold Int.eq. rewrite !Int.unsigned_repr by auto.
  destruct (zeq a b); destruct (Z.eqb_spec a b); auto; lia.
Qed.

Lemma Int_ltu_repr: forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.ltu (Int.repr a) (Int.repr b) = (a <? b).
Proof.
  intros a b Ha Hb. unfold Int.ltu. rewrite !Int.unsigned_repr by auto.
  destruct (zlt a b); destruct (Z.ltb_spec a b); auto; lia.
Qed.

Lemma add64_repr': forall a b, Int64.add (Int64.repr a) (Int64.repr b) = Int64.repr (a + b).
Proof.
  intros. unfold Int64.add. apply Int64.eqm_samerepr. apply Int64.eqm_add; apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Lemma sub64_repr': forall a b, Int64.sub (Int64.repr a) (Int64.repr b) = Int64.repr (a - b).
Proof.
  intros. unfold Int64.sub. apply Int64.eqm_samerepr. apply Int64.eqm_sub; apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Lemma add32_repr': forall a b, Int.add (Int.repr a) (Int.repr b) = Int.repr (a + b).
Proof. intros. apply add_repr. Qed.

Lemma repr64_inj: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.repr a = Int64.repr b -> a = b.
Proof.
  intros a b Ha Hb E. apply (f_equal Int64.unsigned) in E. rewrite !Int64.unsigned_repr in E by auto. exact E.
Qed.

Lemma repr64_neq: forall a b, Int64.repr a <> Int64.repr b -> a <> b.
Proof. intros a b N E. subst. apply N. reflexivity. Qed.

Lemma repr32_neq: forall a b, Int.repr a <> Int.repr b -> a <> b.
Proof. intros a b N E. subst. apply N. reflexivity. Qed.

(* A 32-bit word widened to 64 bits. *)
Lemma cast_u32_u64: forall a, 0 <= a <= Int.max_unsigned ->
  Int64.repr (Int.unsigned (Int.repr a)) = Int64.repr a.
Proof. intros. rewrite Int.unsigned_repr by auto. reflexivity. Qed.

(* A 64-bit word truncated to 32 bits. *)
Lemma loword_repr: forall a, Int.repr (Int64.unsigned (Int64.repr a)) = Int.repr a.
Proof.
  intros. apply Int.eqm_samerepr. unfold Int.eqm. apply Zbits.eqmod_trans with (Int64.unsigned (Int64.repr a)).
  - apply Zbits.eqmod_refl.
  - apply Zbits.eqmod_sym. apply Zbits.eqmod_divides with Int64.modulus.
    + apply Int64.eqm_unsigned_repr.
    + exists (2 ^ 32). reflexivity.
Qed.

Lemma b2z_true: forall b, Int.repr (Z.b2z b) <> Int.zero -> b = true.
Proof. intros [ ] E; [ reflexivity | exfalso; apply E; reflexivity ]. Qed.

Lemma b2z_false: forall b, Int.repr (Z.b2z b) = Int.zero -> b = false.
Proof. intros [ ] E; [ exfalso; exact (Int.one_not_zero E) | reflexivity ]. Qed.

(* The branch hypothesis of `if (t)` with t the truth value of b, as b. *)
Ltac b2z_hyp :=
  match goal with
  | E: Int.repr (Z.b2z _) <> Int.zero |- _ => apply b2z_true in E
  | E: Int.repr (Z.b2z _) = Int.zero |- _ => apply b2z_false in E
  end.

(* The branch conditions of 32- and 64-bit arithmetic as facts on Z. *)
Ltac uns_hyps :=
  repeat match goal with
  | E: context [Int64.unsigned (Int64.repr ?k)] |- _ => rewrite (Int64.unsigned_repr k) in E by rep_lia
  | E: context [Int.unsigned (Int.repr ?k)] |- _ => rewrite (Int.unsigned_repr k) in E by rep_lia
  end.

Ltac wordc :=
  change Int64.zero with (Int64.repr 0) in *; change Int64.one with (Int64.repr 1) in *;
  change Int.zero with (Int.repr 0) in *; change Int.one with (Int.repr 1) in *;
  rewrite ?sub64_repr', ?add64_repr' in *; uns_hyps;
  repeat match goal with
  | E: Int.repr _ = Int.repr _ |- _ => apply repr_inj_unsigned in E; [ | rep_lia | rep_lia ]
  | E: Int.repr _ <> Int.repr _ |- _ => apply repr32_neq in E
  | E: Int64.repr _ = Int64.repr _ |- _ => apply repr64_inj in E; [ | rep_lia | rep_lia ]
  | E: Int64.repr _ <> Int64.repr _ |- _ => apply repr64_neq in E
  | E: context [Int64.ltu (Int64.repr ?a) (Int64.repr ?b)] |- _ => rewrite (Int64_ltu_repr a b) in E by rep_lia
  | E: context [Int64.eq (Int64.repr ?a) (Int64.repr ?b)] |- _ => rewrite (Int64_eq_repr a b) in E by rep_lia
  | E: context [Int.ltu (Int.repr ?a) (Int.repr ?b)] |- _ => rewrite (Int_ltu_repr a b) in E by rep_lia
  | E: context [Int.eq (Int.repr ?a) (Int.repr ?b)] |- _ => rewrite (Int_eq_repr a b) in E by rep_lia
  end.

(* Decide the goal by the comparisons in it. *)
Ltac uns_repr :=
  repeat match goal with
  | |- context [Int.unsigned (Int.repr ?k)] => rewrite (Int.unsigned_repr k) by rep_lia
  | |- context [Int64.unsigned (Int64.repr ?k)] => rewrite (Int64.unsigned_repr k) by rep_lia
  end.
Ltac cmp_atoms :=
  repeat (uns_repr; cbn [andb negb orb Z.b2z proj_sumbool];
          match goal with
          | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
          | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
          | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b)
          | |- context [zeq ?a ?b] => destruct (zeq a b)
          | |- context [zlt ?a ?b] => destruct (zlt a b)
          end);
  uns_repr; cbn [andb negb orb Z.b2z proj_sumbool].

(* A truth value the C computed: the comparisons of the goal, decided. *)
Ltac bool_fin :=
  wordc;
  unfold bool2val, Int64.cmpu, Int.cmpu; cbv beta iota;
  repeat match goal with
  | |- context [Int64.eq (Int64.repr ?a) (Int64.repr ?b)] => rewrite (Int64_eq_repr a b) by rep_lia
  | |- context [Int64.ltu (Int64.repr ?a) (Int64.repr ?b)] => rewrite (Int64_ltu_repr a b) by rep_lia
  | |- context [Int.eq (Int.repr ?a) (Int.repr ?b)] => rewrite (Int_eq_repr a b) by rep_lia
  | |- context [Int.ltu (Int.repr ?a) (Int.repr ?b)] => rewrite (Int_ltu_repr a b) by rep_lia
  end;
  cmp_atoms; try discriminate; try (exfalso; lia); try reflexivity.

(* The branch of a condition that does not hold. *)
Ltac else_false :=
  exfalso; wordc;
  match goal with
  | E: ?a <> ?a |- _ => apply E; reflexivity
  | E: Int.one = Int.zero |- _ => exact (Int.one_not_zero E)
  | E: (?a =? ?b) = true |- _ => apply Z.eqb_eq in E; lia
  | E: (?a =? ?b) = false |- _ => apply Z.eqb_neq in E; lia
  | E: (?a <? ?b) = true |- _ => apply Z.ltb_lt in E; lia
  | E: (?a <? ?b) = false |- _ => apply Z.ltb_ge in E; lia
  | _ => lia
  end.

Ltac first_stmt c := lazymatch c with Ssequence ?c1 _ => first_stmt c1 | _ => c end.

(* Statements before the next if or call. *)
Ltac to_branch :=
  repeat match goal with |- semax _ _ ?c _ =>
    let s := first_stmt c in
    lazymatch s with Sifthenelse _ _ _ => fail | Scall _ _ _ => fail | _ => forward end
  end.

(* qp_assert(1). *)
Ltac gp := to_branch; forward_call Int.one.

(* Freeze every SEP item but the law's fields named in L and the data_at's whose addresses are in A. *)
Ltac keep_item x L A :=
  lazymatch x with
  | field_at _ _ (StructField ?f :: nil) _ _ => lazymatch L with context [f] => constr:(true) | _ => constr:(false) end
  | data_at _ _ _ ?p => lazymatch A with context [p] => constr:(true) | _ => constr:(false) end
  | _ => constr:(false)
  end.
Ltac idx_frozen R L A i :=
  lazymatch R with
  | nil => constr:(@nil Z)
  | ?x :: ?R' =>
      let rest := idx_frozen R' L A (Z.succ i) in
      let k := keep_item x L A in
      lazymatch k with true => rest | false => let i' := eval cbn in i in constr:(i' :: rest) end
  end.
Ltac freeze_but L A F :=
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
    let I := idx_frozen R L A 0 in freeze_tac I F
  end.

Lemma signed_small: forall x, 0 <= x <= 255 -> Int.signed (Int.repr x) = x.
Proof. intros. apply Int.signed_repr. rep_lia. Qed.

(* An array of bytes in three pieces: [0, k), [k, k + n) at offset k, the rest. *)
Lemma bytes_split3: forall sh N k n bs b, 0 <= k -> 0 <= n -> k + n <= N -> Zlength bs = N ->
  field_compatible (tarray tuchar N) nil b ->
  data_at sh (tarray tuchar N) (bytes_val bs) b =
  (data_at sh (tarray tuchar k) (bytes_val (sublist 0 k bs)) b *
   data_at sh (tarray tuchar n) (bytes_val (sublist k (k + n) bs)) (offset_val k b) *
   data_at sh (tarray tuchar (N - (k + n))) (bytes_val (sublist (k + n) N bs)) (offset_val (k + n) b))%logic.
Proof.
  intros sh N k n bs b K L1 L2 Lb FC.
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh N k (k + n)) by (rewrite ?Zlength_bytes_val; lia).
  rewrite !sublist_bytes_val. replace (k + n - k) with n by lia.
  rewrite !field_address0_offset.
  - simpl nested_field_offset. rewrite !Z.mul_1_l. reflexivity.
  - eapply field_compatible0_cons_Tarray; [ reflexivity | exact FC | lia ].
  - eapply field_compatible0_cons_Tarray; [ reflexivity | exact FC | lia ].
Qed.

Lemma bytes_join3: forall sh N k n bs mid b, 0 <= k -> 0 <= n -> k + n <= N -> Zlength bs = N -> Zlength mid = n ->
  field_compatible (tarray tuchar N) nil b ->
  (data_at sh (tarray tuchar k) (bytes_val (sublist 0 k bs)) b *
   data_at sh (tarray tuchar n) (bytes_val mid) (offset_val k b) *
   data_at sh (tarray tuchar (N - (k + n))) (bytes_val (sublist (k + n) N bs)) (offset_val (k + n) b))%logic =
  data_at sh (tarray tuchar N) (bytes_val (overlay k mid bs)) b.
Proof.
  intros sh N k n bs mid b K L1 L2 Lb Lm FC.
  rewrite (bytes_split3 sh N k n (overlay k mid bs) b) by (try rewrite Zlength_overlay; auto; lia).
  unfold overlay. rewrite Lm.
  f_equal; [ f_equal | ]; f_equal; f_equal; list_solve.
Qed.

Lemma tc_byte: forall b, 0 <= b <= 255 -> tc_val tuchar (Vint (Int.repr b)).
Proof. intros. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. Qed.

Lemma Znth_default_irrel: forall {A} (d d': Inhabitant A) (l: list A) i, 0 <= i < Zlength l ->
  @Znth A d i l = @Znth A d' i l.
Proof.
  intros. unfold Znth. destruct (Z_lt_dec i 0); [ lia | ]. apply nth_indep. rewrite Zlength_correct in H. lia.
Qed.

Lemma Znth_bytes_sub: forall (d: Inhabitant val) bs k n i, 0 <= k -> 0 <= i < n -> k + n <= Zlength bs ->
  @Znth val d i (bytes_val (sublist k (k + n) bs)) = Vint (Int.repr (Znth (k + i) bs)).
Proof.
  intros. rewrite (Znth_default_irrel d Inhabitant_val) by (rewrite Zlength_bytes_val, Zlength_sublist; lia).
  rewrite Znth_bytes_val by (rewrite Zlength_sublist; lia). rewrite Znth_sublist by lia.
  f_equal; f_equal; f_equal; lia.
Qed.

(* Rewrite with the boolean facts of the context. *)
Ltac rw_bools :=
  repeat match goal with
  | E: ?b = true |- context [?b] => match type of b with bool => rewrite E end
  | E: ?b = false |- context [?b] => match type of b with bool => rewrite E end
  end.

Lemma sig_at4: forall bs k c0 c1 c2 c3, sig_at bs k [c0; c1; c2; c3] =
  ((Znth k bs =? c0) && (Znth (k + 1) bs =? c1) && (Znth (k + 2) bs =? c2) && (Znth (k + 3) bs =? c3))%bool.
Proof. reflexivity. Qed.

(* Int64.Z_mod_modulus / Int.Z_mod_modulus (VST's unsigned (repr _), simplified) as mod, then dropped in range. *)
Ltac zmod_norm :=
  repeat match goal with
  | E: context [Int64.Z_mod_modulus ?a] |- _ => rewrite (Int64.Z_mod_modulus_eq a) in E
  | E: context [Int.Z_mod_modulus ?a] |- _ => rewrite (Int.Z_mod_modulus_eq a) in E
  end;
  repeat match goal with
  | E: context [?a mod Int64.modulus] |- _ => rewrite (Z.mod_small a Int64.modulus) in E by rep_lia
  end.
