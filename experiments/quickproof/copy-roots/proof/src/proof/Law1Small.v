(* Law copy_roots_exact: the bodies of the harness's helpers table, phys_ok, apart and member, and the
   tactics the other bodies use. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env.
Require Import LeanosRoots.proof.Defs.
Require Import LeanosRoots.proof.RootsSpecs.
Require Import LeanosRoots.proof.Law1Specs.
Require Import LeanosRoots.proof.Law1Pure.
Require Import LeanosRoots.harness.copy_roots_exact.code.
Local Open Scope Z_scope.
Lemma repr_lor_mod: forall x y, Int64.repr (Z.lor (x mod W) y) = Int64.repr (Z.lor x y).
Proof.
  intros. apply Int64.same_bits_eq. intros i Hi. rewrite !Int64.testbit_repr by lia.
  rewrite !Z.lor_spec. unfold W. change Int64.modulus with (2 ^ 64). rewrite Z.mod_pow2_bits_low; auto.
  change Int64.zwordsize with 64 in Hi. lia.
Qed.
Lemma bool2val_b2z: forall b, bool2val b = Vint (Int.repr (b2z b)).
Proof. destruct b; reflexivity. Qed.
Lemma repr_inj64: forall a b, word_ok a -> word_ok b -> Int64.repr a = Int64.repr b -> a = b.
Proof.
  intros a b Ha Hb E. unfold word_ok in *. rewrite <- (Int64.unsigned_repr a), <- (Int64.unsigned_repr b) by lia.
  congruence.
Qed.
Lemma pd_entry_word: forall phys i, word_ok (pd_entry phys i).
Proof. intros. unfold pd_entry. destruct (i <? 8); [ apply table_entry_word | unfold word_ok; rep_lia ]. Qed.
Ltac wok :=
  first [ apply table_entry_word | apply pd_entry_word | apply alias_leaf_word | apply mod_word
        | apply land_word; wok | apply lor_word; wok
        | unfold word_ok in *;
          first [ rep_lia
                | match goal with |- context [?a mod ?b] => pose proof (Z.mod_pos_bound a b ltac:(lia)); rep_lia end ] ].
Ltac bcase :=
  repeat match goal with
  | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
  | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
  | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b)
  | |- context [zeq ?a ?b] => destruct (zeq a b)
  | |- context [zlt ?a ?b] => destruct (zlt a b)
  end; simpl; first [ reflexivity | exfalso; lia | congruence ].
Ltac w64 :=
  unfold Int64.cmpu, Int64.modu in *;
  rewrite ?and_not_repr, ?and_repr, ?or_repr in *;
  rewrite ?bool2val_b2z;
  rewrite ?add64_repr in *;
  rewrite ?(Int64.unsigned_repr 4096) in * by rep_lia;
  repeat match goal with
  | H: context [Int.unsigned (Int.repr ?a)] |- _ => rewrite (Int.unsigned_repr a) in H by rep_lia
  | |- context [Int.unsigned (Int.repr ?a)] => rewrite (Int.unsigned_repr a) by rep_lia
  | H: context [Int.signed (Int.repr ?a)] |- _ => rewrite (Int.signed_repr a) in H by rep_lia
  | |- context [Int.signed (Int.repr ?a)] => rewrite (Int.signed_repr a) by rep_lia
  | H: Int64.repr ?a = Int64.zero |- _ => change Int64.zero with (Int64.repr 0) in H
  | H: Int64.repr ?a = Int64.repr ?b |- _ => apply repr_inj64 in H; [ | wok | wok ]
  | H: Int64.repr ?a <> Int64.repr ?b |- _ => assert (a <> b) by congruence; clear H
  | H: context [Int64.ltu (Int64.repr ?a) (Int64.repr ?b)] |- _ => rewrite (ltu_repr a b) in H by wok
  | H: context [Int64.eq (Int64.repr ?a) (Int64.repr ?b)] |- _ => rewrite (eq_repr a b) in H by wok
  | H: (?a =? ?b) = true |- _ => apply Z.eqb_eq in H
  | H: (?a =? ?b) = false |- _ => apply Z.eqb_neq in H
  | H: (?a <? ?b) = true |- _ => apply Z.ltb_lt in H
  | H: (?a <? ?b) = false |- _ => apply Z.ltb_ge in H
  | H: context [Int64.unsigned (Int64.repr ?a)] |- _ => rewrite (Int64.unsigned_repr a) in H by wok
  | |- context [Int64.unsigned (Int64.repr ?a)] => rewrite (Int64.unsigned_repr a) by wok
  | |- context [Int64.eq (Int64.repr ?a) (Int64.repr ?b)] => rewrite (eq_repr a b) by wok
  | |- context [Int64.ltu (Int64.repr ?a) (Int64.repr ?b)] => rewrite (ltu_repr a b) by wok
  end.
Lemma body_table: semax_body Vharness Gharness f_table table_spec.
Proof.
  start_function. forward. entailer!. unfold table_entry. rewrite repr_lor_mod. do 3 f_equal. lia.
Qed.
Lemma body_phys_ok: semax_body Vharness Gharness f_phys_ok h_phys_ok_spec.
Proof.
  start_function. 
  forward_if (temp _t'1 (Vint (Int.repr (b2z (negb (a =? 0) && (a mod 4096 =? 0)))))).
  - forward. entailer!. rewrite bool2val_b2z. do 2 f_equal.
    change (Int.unsigned (Int.repr 4096)) with 4096. change (Int.signed (Int.repr 0)) with 0.
    w64. bcase.
  - forward. entailer!. w64. subst. reflexivity.
  - forward_if (temp _t'2 (Vint (Int.repr (b2z (phys_ok a))))).
    + forward. entailer!. rewrite bool2val_b2z. do 2 f_equal.
      change (Int64.sub (Int64.shl (Int64.repr 1) (Int64.repr 52)) (Int64.repr 45056)) with (Int64.repr 4503599627325440).
      unfold Int64.cmpu. w64. unfold phys_ok. rewrite H0. unfold ROOT_BYTES. bcase.
    + forward. entailer!. unfold phys_ok. rewrite H0. reflexivity.
    + forward.
Qed.
Lemma body_apart: semax_body Vharness Gharness f_apart apart_spec.
Proof.
  start_function. unfold ROOT_BYTES in *.
  forward_if (temp _t'1 (Vint (Int.repr (b2z (disjoint a b))))).
  - forward. entailer!. w64. unfold disjoint, ROOT_BYTES. bcase.
  - forward. entailer!. rewrite bool2val_b2z. do 2 f_equal. w64. unfold disjoint, ROOT_BYTES. bcase.
  - forward.
Qed.


Lemma Znth_longs: forall {d: Inhabitant val} i l, 0 <= i < Zlength l -> @Znth val d i (longs l) = Vlong (Int64.repr (Znth i l)).
Proof. intros. unfold longs. rewrite Znth_map by lia. reflexivity. Qed.
Lemma word_Znth: forall l i, words_ok l -> 0 <= i < Zlength l -> word_ok (Znth i l).
Proof. intros l i H Hi. apply (Forall_Znth l word_ok); auto. Qed.
Lemma body_member: semax_body Vharness Gharness f_member member_spec.
Proof.
  start_function.
  forward_for_simple_bound n
    (EX i: Z, PROP (forall j, 0 <= j < i -> Znth j fs <> f)
     LOCAL (temp _frame (Vlong (Int64.repr f)); temp _frames p; temp _n (Vlong (Int64.repr n)))
     SEP (data_at sh (tarray tulong (Zlength fs)) (longs fs) p)).
  - entailer!.
  - cbv beta. Intros. assert (Wi: word_ok (Znth i fs)) by (apply word_Znth; auto; lia).
    forward. { entailer!; rewrite ?Znth_longs by lia; simpl; auto. }
    rewrite Znth_longs by lia.
    forward_if.
    + forward. entailer!. w64.
      assert (M: member f (sublist 0 n fs) = true).
      { apply member_Znth. exists i. rewrite Zlength_sublist, Znth_sublist by lia. rewrite Z.add_0_r. split; [ lia | auto ]. }
      rewrite M. reflexivity.
    + forward.
      assert (Hn: forall j, 0 <= j < i + 1 -> Znth j fs <> f).
      { intros j Hj. destruct (zeq j i).
        - subst j. match goal with Hc: Int64.repr _ <> Int64.repr _ |- _ => intro E; apply Hc; rewrite E; reflexivity end.
        - match goal with Hinv: forall j, 0 <= j < i -> _ |- _ => apply Hinv; lia end. }
      entailer!.
  - forward. entailer!. assert (M: member f (sublist 0 n fs) = false); [ | rewrite M; reflexivity ].
    apply member_false. intros j Hj. rewrite Zlength_sublist in Hj by lia. rewrite Znth_sublist by lia.
    replace (j + 0) with j by lia.
    match goal with Hinv: forall j, 0 <= j < n -> _ |- _ => apply Hinv; lia end.
Qed.

(* ---------------------------------------------------------------------- *)
(* The kit of the other bodies                                             *)
(* ---------------------------------------------------------------------- *)

Definition rootv (a b c d: list val) : reptype t_root := (a, (b, (c, d))).
Lemma root_val_v: forall rv, root_val rv = rootv (longs (pml4 rv)) (longs (pdpt rv)) (longs (pd rv)) (longs (pt rv)).
Proof. reflexivity. Qed.
Ltac ld := forward; [ try lia .. ]; [ try solve [ entailer!; rewrite ?Znth_longs by lia; simpl; auto ] .. ].
Lemma forallb_Znth_false: forall {A} {d: Inhabitant A} (f: A -> bool) l i, 0 <= i < Zlength l -> f (Znth i l) = false -> forallb f l = false.
Proof.
  intros. destruct (forallb f l) eqn:F; auto. rewrite forallb_forall in F.
  rewrite F in H0; [ discriminate | apply Znth_In; auto ].
Qed.
Lemma forallb_Znth: forall {A} {d: Inhabitant A} (f: A -> bool) l, (forall i, 0 <= i < Zlength l -> f (Znth i l) = true) -> forallb f l = true.
Proof.
  intros. apply forallb_forall. intros x Hx. apply In_Znth in Hx. destruct Hx as (i & Hi & <-). auto.
Qed.
#[export] Instance Inhabitant_alias : Inhabitant alias := mkalias 0 0 0.
Lemma Znth_alias_val: forall {d: Inhabitant (reptype t_alias)} i al, 0 <= i < Zlength al ->
  @Znth (reptype t_alias) d i (map alias_val al) = alias_val (Znth i al).
Proof. intros. rewrite Znth_map by lia. reflexivity. Qed.
Lemma alias_val_eq: forall p f w, alias_val (mkalias p f w) = (Vlong (Int64.repr p), (Vlong (Int64.repr f), Vlong (Int64.repr w))).
Proof. reflexivity. Qed.
Ltac ldA := forward; [ rewrite ?Znth_alias_val by lia;
                         repeat (match goal with E: Znth ?i ?l = mkalias _ _ _ |- context [Znth ?i ?l] => rewrite E end);
                         rewrite ?alias_val_eq; cbv beta iota zeta .. ];
             [ try lia .. ]; [ try solve [ entailer! ] .. ].
Lemma b2z_false: forall c, Int.repr (b2z c) = Int.zero -> c = false.
Proof. intros [] H; auto; exfalso; apply Int.one_not_zero; exact H. Qed.
Lemma b2z_true: forall c, Int.repr (b2z c) <> Int.zero -> c = true.
Proof. intros [] H; auto; exfalso; apply H; reflexivity. Qed.
Ltac bhyp := repeat match goal with
 | H: Int.repr (b2z ?c) = Int.zero |- _ => apply b2z_false in H
 | H: Int.repr (b2z ?c) <> Int.zero |- _ => apply b2z_true in H
 | H: negb ?c = true |- _ => apply negb_true_iff in H
 | H: negb ?c = false |- _ => apply negb_false_iff in H
 | H: (?a || ?b)%bool = false |- _ => apply orb_false_iff in H; destruct H
 | H: (?a && ?b)%bool = true |- _ => apply andb_true_iff in H; destruct H
 | H: (?a =? ?b) = true |- _ => apply Z.eqb_eq in H
 | H: (?a =? ?b) = false |- _ => apply Z.eqb_neq in H
 | H: (?a <=? ?b) = true |- _ => apply Z.leb_le in H
 | H: (?a <=? ?b) = false |- _ => apply Z.leb_gt in H
 | H: (?a <? ?b) = true |- _ => apply Z.ltb_lt in H
 | H: (?a <? ?b) = false |- _ => apply Z.ltb_ge in H
 end.

Lemma forallb_idx1_false: forall f j, 1 <= j < 512 -> f j = false -> forallb f (map (Z.add 1) (idx 511)) = false.
Proof.
  intros f j Hj E. destruct (forallb f (map (Z.add 1) (idx 511))) eqn:F; auto.
  rewrite forallb_idx1 in F. rewrite F in E by lia. discriminate.
Qed.
Lemma forallb_idx_false: forall f n j, 0 <= j < n -> f j = false -> forallb f (idx n) = false.
Proof.
  intros f n j Hj E. destruct (forallb f (idx n)) eqn:F; auto.
  rewrite forallb_idx in F by lia. rewrite F in E by lia. discriminate.
Qed.
