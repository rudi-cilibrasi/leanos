(* Law window_roots_isolated: specifications and bodies of the harness's static helpers member, phys_ok,
   apart, table, tables_at, inventory_ok and geometry_ok, under the roots unit's compspecs (the harness's
   composites are among the unit's).  Each returns its check as a Defs.v / Law2Model.v boolean. *)
Require Import VST.floyd.proofauto.
Require Import LeanosRoots.proof.Defs.
Require Import LeanosRoots.proof.RootsSpecs.
Require Import LeanosRoots.proof.Law2Model.
Require Import LeanosRoots.harness.window_roots_isolated.code.
#[local] Existing Instance RootsSpecs.CS.

Definition h_member_spec :=
  DECLARE _member
  WITH f: Z, p: val, sh: share, fs: list Z, n: Z
  PRE [ tulong, tptr tulong, tulong ]
    PROP (readable_share sh; word_ok f; words_ok fs; 0 <= n <= Zlength fs; Zlength fs <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr f); p; Vlong (Int64.repr n))
    SEP (data_at sh (tarray tulong (Zlength fs)) (longs fs) p)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (b2z (member f (sublist 0 n fs)))))
    SEP (data_at sh (tarray tulong (Zlength fs)) (longs fs) p).

Definition h_phys_ok_spec :=
  DECLARE _phys_ok
  WITH a: Z
  PRE [ tulong ] PROP (word_ok a) PARAMS (Vlong (Int64.repr a)) SEP ()
  POST [ tint ] PROP () RETURN (Vint (Int.repr (b2z (phys_ok a)))) SEP ().

Definition h_apart_spec :=
  DECLARE _apart
  WITH a: Z, b: Z
  PRE [ tulong, tulong ]
    PROP (word_ok a; word_ok b) PARAMS (Vlong (Int64.repr a); Vlong (Int64.repr b)) SEP ()
  POST [ tint ] PROP () RETURN (Vint (Int.repr (b2z (apart a b)))) SEP ().

Definition h_table_spec :=
  DECLARE _table
  WITH phys: Z, k: Z
  PRE [ tulong, tulong ]
    PROP (word_ok phys; 0 <= k <= 10) PARAMS (Vlong (Int64.repr phys); Vlong (Int64.repr k)) SEP ()
  POST [ tulong ] PROP () RETURN (Vlong (Int64.repr (table_entry phys k))) SEP ().

Definition h_tables_at_spec :=
  DECLARE _tables_at
  WITH r: val, sh: share, rv: root, phys: Z, ig: Z
  PRE [ tptr t_root, tulong, tulong ]
    PROP (readable_share sh; root_ok rv; word_ok phys; word_ok ig)
    PARAMS (r; Vlong (Int64.repr phys); Vlong (Int64.repr ig))
    SEP (data_at sh t_root (root_val rv) r)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (b2z (tables_ok rv phys ig))))
    SEP (data_at sh t_root (root_val rv) r).

Definition h_inventory_ok_spec :=
  DECLARE _inventory_ok
  WITH p: val, sh: share, fs: list Z, n: Z
  PRE [ tptr tulong, tulong ]
    PROP (readable_share sh; words_ok fs; word_ok n; 16 < n \/ n <= Zlength fs; Zlength fs <= Int64.max_unsigned)
    PARAMS (p; Vlong (Int64.repr n))
    SEP (data_at sh (tarray tulong (Zlength fs)) (longs fs) p)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (b2z (inventory_ok fs n))))
    SEP (data_at sh (tarray tulong (Zlength fs)) (longs fs) p).

Definition h_geometry_ok_spec :=
  DECLARE _geometry_ok
  WITH w: window
  PRE [ tulong, tulong, tulong ]
    PROP (window_wf w)
    PARAMS (Vlong (Int64.repr (w_base w)); Vlong (Int64.repr (w_limit w)); Vlong (Int64.repr (w_slot w)))
    SEP ()
  POST [ tint ] PROP () RETURN (Vint (Int.repr (b2z (geometry_ok w)))) SEP ().

Definition Hvprog : varspecs := nil.
Definition Hgprog : funspecs := [h_table_spec].

Lemma bool2val_b2z: forall b, bool2val b = Vint (Int.repr (b2z b)).
Proof. destruct b; reflexivity. Qed.

Lemma vint_b2z: forall b c, b = c -> Vint (Int.repr (b2z b)) = Vint (Int.repr (b2z c)).
Proof. intros; subst; reflexivity. Qed.

(* Constants of the Clight code and the 64-bit operations, to Z. *)
Ltac i64 :=
  repeat match goal with
  | |- context [Int.unsigned (Int.repr ?n)] => rewrite (Int.unsigned_repr n) by rep_lia
  | |- context [Int.signed (Int.repr ?n)] => rewrite (Int.signed_repr n) by rep_lia
  end;
  unfold Int64.cmpu;
  repeat first [ rewrite add64_repr | rewrite sub64_repr | rewrite mul64_repr | rewrite and64_repr
               | rewrite or64_repr | rewrite not64_repr | rewrite shl64_repr by rep_lia ];
  rewrite ?eq64_mod, ?ltu64_mod.

Lemma cast_b2z: forall b, (if Int.eq (Int.repr (b2z b)) Int.zero then Int.zero else Int.one) = Int.repr (b2z b).
Proof. destruct b; reflexivity. Qed.

Ltac bdone := entailer!; rewrite ?bool2val_b2z, ?cast_b2z;
  try change (Vint (if Int.eq (Int.repr 1) Int.zero then Int.zero else Int.one)) with (Vint (Int.repr (b2z true)));
  try change (Vint (Int.repr 0)) with (Vint (Int.repr (b2z false)));
  try change (Vint (Int.repr 1)) with (Vint (Int.repr (b2z true)));
  apply vint_b2z.

Lemma body_phys_ok: semax_body Hvprog Hgprog f_phys_ok h_phys_ok_spec.
Proof.
  start_function.
  forward_if (temp _t'1 (Vint (Int.repr (b2z (negb (a =? 0) && (a mod 4096 =? 0)))))).
  { forward. bdone. assert (a <> 0) by (intro; subst; contradiction).
    i64. rewrite modu64_repr by (auto; rep_lia). rewrite eq64_mod.
    rewrite (proj2 (Z.eqb_neq a 0)) by auto. rewrite (Z.mod_small (a mod 4096)), Zmod_0_l by
      (pose proof (Z.mod_pos_bound a 4096); unfold W; rep_lia). reflexivity. }
  { forward. bdone. assert (a = 0) by (apply (f_equal Int64.unsigned) in H0; rewrite Int64.unsigned_repr in H0 by
      (unfold word_ok in H; rep_lia); auto). subst. reflexivity. }
  forward_if (temp _t'2 (Vint (Int.repr (b2z (phys_ok a))))).
  { forward. bdone. unfold phys_ok. rewrite H0. i64. unfold ROOT_BYTES.
    rewrite (Z.mod_small a), Z.mod_small by (unfold word_ok, W in *; rep_lia).
    change (1 * 2 ^ 52 - 45056) with 4503599627325440.
    destruct (Z.ltb_spec 4503599627325440 a); destruct (Z.leb_spec a 4503599627325440); simpl; auto; lia. }
  { forward. bdone. unfold phys_ok. rewrite H0. reflexivity. }
  forward.
Qed.

Lemma body_apart: semax_body Hvprog Hgprog f_apart h_apart_spec.
Proof.
  start_function.
  forward_if (temp _t'1 (Vint (Int.repr (b2z (apart a b))))).
  { forward. bdone. unfold apart, ROOT_BYTES. revert H1. i64. intros H1.
    rewrite (Z.mod_small b) in H1 by (unfold word_ok, W in *; rep_lia).
    destruct (Z.ltb_spec b ((a + 45056) mod W)); [ discriminate | ].
    rewrite (proj2 (Z.leb_le _ b)) by lia. reflexivity. }
  { forward. bdone. unfold apart, ROOT_BYTES. revert H1. i64. intros H1.
    rewrite (Z.mod_small b) in H1 by (unfold word_ok, W in *; rep_lia).
    rewrite (Z.mod_small a) by (unfold word_ok, W in *; rep_lia).
    destruct (Z.ltb_spec b ((a + 45056) mod W)); [ | discriminate ].
    rewrite (proj2 (Z.leb_gt _ b)) by lia. simpl.
    destruct (Z.ltb_spec a ((b + 45056) mod W)); destruct (Z.leb_spec ((b + 45056) mod W) a); simpl; auto; lia. }
  forward.
Qed.

Lemma body_table: semax_body Hvprog Hgprog f_table h_table_spec.
Proof.
  start_function.
  forward. entailer!. unfold table_entry. rewrite <- !or64_repr, w_repr_mod. replace (4096 * k) with (k * 4096) by lia. reflexivity.
Qed.

Lemma Zlength_longs: forall l, Zlength (longs l) = Zlength l.
Proof. intros. unfold longs. apply Zlength_map. Qed.

Lemma Znth_longs: forall i l, 0 <= i < Zlength l -> Znth i (longs l) = Vlong (Int64.repr (Znth i l)).
Proof. intros. unfold longs. rewrite Znth_map by lia. reflexivity. Qed.

Lemma In_sublist_Znth: forall (l: list Z) i n, 0 <= i < n -> n <= Zlength l -> In (Znth i l) (sublist 0 n l).
Proof.
  intros. replace (Znth i l) with (Znth i (sublist 0 n l)) by (rewrite Znth_sublist by lia; f_equal; lia).
  apply Znth_In. rewrite Zlength_sublist by lia. lia.
Qed.

Lemma body_member: semax_body Hvprog Hgprog f_member h_member_spec.
Proof.
  start_function.
  forward_for_simple_bound n
    (EX i: Z,
     PROP (member f (sublist 0 i fs) = false)
     LOCAL (temp _frame (Vlong (Int64.repr f)); temp _frames p; temp _n (Vlong (Int64.repr n)))
     SEP (data_at sh (tarray tulong (Zlength fs)) (longs fs) p)).
  { entailer!. }
  { assert (Wi := words_Znth fs i H0 ltac:(lia)).
    cbv beta. forward.
    { entailer!. rewrite Znth_longs by lia. exact I. }
    rewrite Znth_longs by lia.
    forward_if.
    { forward. entailer!.
      assert (E: Znth i fs = f) by (rewrite eq64_w in H5 by auto; apply Z.eqb_eq; auto).
      rewrite (proj2 (member_true_iff f (sublist 0 n fs))); [ reflexivity | ].
      rewrite <- E. apply In_sublist_Znth; lia. }
    { forward. entailer!.
      rewrite sublist_snoc, member_app, member_one, H4 by lia. simpl.
      apply Z.eqb_neq. intro E. subst. contradiction. } }
  forward. entailer!. rewrite H3. reflexivity.
Qed.

Lemma repr64_inj: forall x y, word_ok x -> word_ok y -> Int64.repr x = Int64.repr y -> x = y.
Proof.
  intros x y Hx Hy E. unfold word_ok in *.
  rewrite <- (Int64.unsigned_repr x), <- (Int64.unsigned_repr y) by lia. rewrite E. reflexivity.
Qed.

Lemma repr64_neq: forall x y, Int64.repr x <> Int64.repr y -> x <> y.
Proof. intros x y H E. subst. auto. Qed.

Lemma cmpu_eq64: forall x y, Int64.cmpu Ceq x y = Int64.eq x y.
Proof. reflexivity. Qed.
Lemma cmpu_ne64: forall x y, Int64.cmpu Cne x y = negb (Int64.eq x y).
Proof. reflexivity. Qed.
Lemma cmpu_lt64: forall x y, Int64.cmpu Clt x y = Int64.ltu x y.
Proof. reflexivity. Qed.
Lemma cmpu_le64: forall x y, Int64.cmpu Cle x y = negb (Int64.ltu y x).
Proof. reflexivity. Qed.
Lemma cmpu_gt64: forall x y, Int64.cmpu Cgt x y = Int64.ltu y x.
Proof. reflexivity. Qed.
Lemma cmpu_ge64: forall x y, Int64.cmpu Cge x y = negb (Int64.ltu x y).
Proof. reflexivity. Qed.

(* Int64 constants and operations in hypotheses and goal, to repr of Z. *)
Ltac n64 :=
  unfold Int64.zero, Int64.one in *;
  repeat match goal with
  | H: context [Int.unsigned (Int.repr ?n)] |- _ => rewrite (Int.unsigned_repr n) in H by rep_lia
  | H: context [Int.signed (Int.repr ?n)] |- _ => rewrite (Int.signed_repr n) in H by rep_lia
  | |- context [Int.unsigned (Int.repr ?n)] => rewrite (Int.unsigned_repr n) by rep_lia
  | |- context [Int.signed (Int.repr ?n)] => rewrite (Int.signed_repr n) by rep_lia
  end;
  rewrite ?cmpu_eq64, ?cmpu_ne64, ?cmpu_lt64, ?cmpu_le64, ?cmpu_gt64, ?cmpu_ge64 in *;
  repeat first [ rewrite add64_repr in * | rewrite sub64_repr in * | rewrite mul64_repr in *
               | rewrite and64_repr in * | rewrite or64_repr in * | rewrite not64_repr in * ].

Ltac cmp64 :=
  repeat match goal with
  | |- context [Int64.ltu (Int64.repr ?a) (Int64.repr ?b)] => rewrite (ltu64_w a b) by (unfold word_ok in *; rep_lia)
  | |- context [Int64.eq (Int64.repr ?a) (Int64.repr ?b)] => rewrite (eq64_w a b) by (unfold word_ok in *; rep_lia)
  | H: context [Int64.ltu (Int64.repr ?a) (Int64.repr ?b)] |- _ =>
      rewrite (ltu64_w a b) in H by (unfold word_ok in *; rep_lia)
  | H: context [Int64.eq (Int64.repr ?a) (Int64.repr ?b)] |- _ =>
      rewrite (eq64_w a b) in H by (unfold word_ok in *; rep_lia)
  end.

Ltac andb_split :=
  repeat match goal with H: (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H end.

Ltac zfacts :=
  repeat match goal with
  | H: (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
  | H: (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H: (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H: (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H: negb (_ =? _) = true |- _ => apply negb_true_iff in H; apply Z.eqb_neq in H
  | H: (_ || _)%bool = true |- _ => apply orb_true_iff in H; destruct H
  end.

Ltac wmod :=
  repeat match goal with
  | |- context [?x mod W] => rewrite (Z.mod_small x W) by (unfold W; rep_lia)
  | H: context [?x mod W] |- _ => rewrite (Z.mod_small x W) in H by (unfold W; rep_lia)
  end.

Ltac zcases :=
  repeat match goal with
  | H: context [?a =? ?b] |- _ => destruct (Z.eqb_spec a b)
  | H: context [?a <? ?b] |- _ => destruct (Z.ltb_spec a b)
  | H: context [?a <=? ?b] |- _ => destruct (Z.leb_spec a b)
  | |- context [?a =? ?b] => destruct (Z.eqb_spec a b)
  | |- context [?a <? ?b] => destruct (Z.ltb_spec a b)
  | |- context [?a <=? ?b] => destruct (Z.leb_spec a b)
  | H: context [zlt ?a ?b] |- _ => destruct (zlt a b)
  | H: context [zeq ?a ?b] |- _ => destruct (zeq a b)
  | |- context [zlt ?a ?b] => destruct (zlt a b)
  | |- context [zeq ?a ?b] => destruct (zeq a b)
  end; simpl in *; try discriminate; try reflexivity; try lia.

Lemma body_geometry_ok: semax_body Hvprog Hgprog f_geometry_ok h_geometry_ok_spec.
Proof.
  start_function.
  destruct w as [fp sp b l s]. unfold window_wf, word_ok in H. cbn [w_base w_limit w_slot w_fetch_phys w_send_phys] in *.
  destruct H as (Hfp & Hsp & Hb & Hl & Hs).
  assert (Bm := Z.mod_pos_bound b 4096 ltac:(lia)).
  assert (Lb: Z.land b 4095 = b mod 4096) by (apply land4095; lia).
  forward_if (temp _t'1 (Vint (Int.repr (b2z ((Z.land b 4095 =? 0) && (b <? l)))))).
  { forward. bdone. n64. rewrite modu64_repr in H by (unfold word_ok; rep_lia).
    apply repr64_inj in H; [ | unfold word_ok; rep_lia | unfold word_ok; rep_lia ].
    rewrite Lb, H. zcases. }
  { forward. bdone. n64. rewrite modu64_repr in H by (unfold word_ok; rep_lia).
    apply repr64_neq in H. rewrite Lb. zcases. }
  forward_if (temp _t'2 (Vint (Int.repr (b2z ((Z.land b 4095 =? 0) && (b <? l) && (l <=? 16777216)))))).
  { forward. bdone. rewrite H. n64. cmp64. zcases. }
  { forward. bdone. rewrite H. reflexivity. }
  forward_if (temp _t'3 (Vint (Int.repr (b2z ((Z.land b 4095 =? 0) && (b <? l) && (l <=? 16777216) &&
    (((l - b) mod W =? 4096) || ((l - b) mod W =? 8192))))))).
  { forward_if (temp _t'3 (Vint (Int.repr (b2z ((Z.land b 4095 =? 0) && (b <? l) && (l <=? 16777216) &&
      (((l - b) mod W =? 4096) || ((l - b) mod W =? 8192))))))).
    { forward. bdone. rewrite H. n64. rewrite eq64_mod in *. wmod. zcases. }
    { forward. forward. bdone. rewrite H. n64. rewrite eq64_mod in *. wmod. apply repr64_neq in H0. zcases. } }
  { forward. bdone. rewrite H. reflexivity. }
  forward_if (temp _t'4 (Vint (Int.repr (b2z ((Z.land b 4095 =? 0) && (b <? l) && (l <=? 16777216) &&
    (((l - b) mod W =? 4096) || ((l - b) mod W =? 8192)) && negb (s =? 0)))))).
  { forward. bdone. rewrite H. n64. cmp64. zcases. }
  { forward. bdone. rewrite H. reflexivity. }
  forward_if (temp _t'5 (Vint (Int.repr (b2z ((Z.land b 4095 =? 0) && (b <? l) && (l <=? 16777216) &&
    (((l - b) mod W =? 4096) || ((l - b) mod W =? 8192)) && negb (s =? 0) && (s <=? LEAVES)))))).
  { forward. bdone. rewrite H. n64. cmp64. unfold LEAVES. zcases. }
  { forward. bdone. rewrite H. reflexivity. }
  forward_if (temp _t'6 (Vint (Int.repr (b2z (geometry_ok (mkwindow fp sp b l s)))))).
  { forward. bdone. unfold geometry_ok, pages_of; cbn [w_base w_limit w_slot w_fetch_phys w_send_phys].
    rewrite H. n64. unfold LEAVES in *. zfacts;
    rewrite (Z.mod_small (l - b)) in * by (unfold W; rep_lia);
    match goal with E: l - b = _ |- _ => rewrite E end;
    change (4096 / 4096) with 1; change (8192 / 4096) with 2;
      rewrite ltu64_w by (unfold word_ok; rep_lia); rewrite Z.mod_small by (unfold W; rep_lia); zcases. }
  { forward. bdone. unfold geometry_ok, pages_of; cbn [w_base w_limit w_slot w_fetch_phys w_send_phys].
    rewrite H. reflexivity. }
  forward.
Qed.
