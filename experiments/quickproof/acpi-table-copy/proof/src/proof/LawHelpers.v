(* Law table_copy_exact: the bodies of the harness's small helpers any_u64, little, byte_sum, padded, signature,
   stop, begin_sdt and transition. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosAcpi.harness.table_copy_exact.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.LawProg LeanosAcpi.proof.LawDefs LeanosAcpi.proof.LawFacts LeanosAcpi.proof.LawLib.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Lemma body_any_u64 : semax_body nil [nondet_u32_spec] f_any_u64 any_u64_spec.
Proof.
  start_function.
  rewrite <- seq_assoc. forward_call. Intros hi. forward.
  rewrite <- seq_assoc. forward_call. Intros lo. forward.
  forward.
  Exists (Int64.unsigned (Int64.or (Int64.shl (Int64.repr hi) (Int64.repr 32)) (Int64.repr lo))).
  entailer!. split; [ apply Int64.unsigned_range_2 | unfold vl; rewrite Int64.repr_unsigned; reflexivity ].
Qed.

Lemma body_stop : semax_body nil nil f_stop stop_spec.
Proof. start_function. forward. forward. entailer!. Qed.

Lemma body_begin_sdt : semax_body nil nil f_begin_sdt begin_sdt_spec.
Proof. start_function. repeat forward. entailer!. Qed.

Lemma body_padded : semax_body nil nil f_padded padded_spec.
Proof.
  start_function. unfold MAX_SDT_BYTES in *. unfold vi in *. forward.
  all: try (entailer!; unfold padded; simpl; f_equal;
    rewrite add_repr; unfold Int.divu; rewrite !Int.unsigned_repr by rep_lia; rewrite mul_repr; reflexivity).
Qed.

Lemma body_little : semax_body nil nil f_little little_spec.
Proof.
  start_function. try subst p. unfold vi, vl in *.
  assert_PROP (field_compatible (tarray tuchar N) nil b) as FC by entailer!.
  rewrite (bytes_split3 sh N k n bs b) by (auto; lia). Intros.
  forward.
  forward_for_simple_bound n
    (EX i: Z, PROP ()
     LOCAL (temp _v (vl (little (sublist k (k + i) bs))); temp _p (offset_val k b); temp _n (vi n))
     SEP (data_at sh (tarray tuchar k) (bytes_val (sublist 0 k bs)) b;
          data_at sh (tarray tuchar n) (bytes_val (sublist k (k + n) bs)) (offset_val k b);
          data_at sh (tarray tuchar (N - (k + n))) (bytes_val (sublist (k + n) N bs)) (offset_val (k + n) b)))%assert.
  - entailer!; try (rewrite ?Z.add_0_r, sublist_nil; reflexivity).
  - assert (Rb: 0 <= Znth (k + i) bs <= 255) by (apply byte_at; auto; lia).
    forward.
    { entailer!. rewrite Znth_bytes_sub by lia. apply tc_byte; auto. }
    rewrite Znth_bytes_sub by lia.
    forward.
    { entailer!. change (Int.unsigned Int64.iwordsize') with 64. rewrite ?mul_repr, ?Int.unsigned_repr by rep_lia. lia. }
    entailer!.
    assert (Ls: Zlength (sublist k (k + i) bs) = i) by (rewrite Zlength_sublist; lia).
    rewrite (sublist_split k (k + i) (k + (i + 1))) by lia.
    replace (k + (i + 1)) with (k + i + 1) by lia. rewrite (sublist_len_1 (k + i)) by lia.
    unfold vl. rewrite <- little_step64 by (try apply Forall_sublist; auto; lia).
    rewrite Ls. f_equal. f_equal. unfold Int64.shl. rewrite ?mul_repr.
    rewrite ?Int.unsigned_repr by rep_lia. rewrite !Int64.unsigned_repr by rep_lia. reflexivity.
  - forward. entailer!.
    rewrite (bytes_split3 sh (Zlength bs) k n bs b) by (auto; lia). cancel.
Qed.

Lemma body_byte_sum : semax_body nil nil f_byte_sum byte_sum_spec.
Proof.
  start_function. try subst p. unfold vi, vl in *.
  assert_PROP (field_compatible (tarray tuchar N) nil b) as FC by entailer!.
  rewrite (bytes_split3 sh N k n bs b) by (auto; lia). Intros.
  forward.
  forward_for_simple_bound n
    (EX i: Z, PROP ()
     LOCAL (temp _sum (vi (fold_left Z.add (sublist k (k + i) bs) 0)); temp _p (offset_val k b); temp _n (vi n))
     SEP (data_at sh (tarray tuchar k) (bytes_val (sublist 0 k bs)) b;
          data_at sh (tarray tuchar n) (bytes_val (sublist k (k + n) bs)) (offset_val k b);
          data_at sh (tarray tuchar (N - (k + n))) (bytes_val (sublist (k + n) N bs)) (offset_val (k + n) b)))%assert.
  - entailer!; try (rewrite ?Z.add_0_r, sublist_nil; reflexivity).
  - assert (Rb: 0 <= Znth (k + i) bs <= 255) by (apply byte_at; auto; lia).
    forward.
    { entailer!. rewrite Znth_bytes_sub by lia. apply tc_byte; auto. }
    rewrite Znth_bytes_sub by lia.
    forward.
    entailer!.
    rewrite (sublist_split k (k + i) (k + (i + 1))) by lia.
    replace (k + (i + 1)) with (k + i + 1) by lia. rewrite (sublist_len_1 (k + i)) by lia.
    rewrite sum_snoc. reflexivity.
  - forward. entailer!.
    rewrite (bytes_split3 sh (Zlength bs) k n bs b) by (auto; lia). cancel.
Qed.

Lemma body_signature : semax_body nil nil f_signature signature_spec.
Proof.
  start_function. try subst p. unfold vi in *. unfold byte_ok in *.
  assert_PROP (field_compatible (tarray tuchar N) nil b) as FC by entailer!.
  rewrite (bytes_split3 sh N k 4 bs b) by (auto; lia). Intros.
  assert (R0: 0 <= Znth k bs <= 255) by (apply byte_at; auto; lia).
  assert (R1: 0 <= Znth (k + 1) bs <= 255) by (apply byte_at; auto; lia).
  assert (R2: 0 <= Znth (k + 2) bs <= 255) by (apply byte_at; auto; lia).
  assert (R3: 0 <= Znth (k + 3) bs <= 255) by (apply byte_at; auto; lia).
  forward.
  { entailer!. rewrite (Znth_bytes_sub _ bs k 4 0) by lia. rewrite Z.add_0_r. apply tc_byte; auto. }
  rewrite (Znth_bytes_sub _ bs k 4 0) by lia. rewrite Z.add_0_r.
  forward_if (temp _t'1 (Vint (Int.repr (Z.b2z ((Znth k bs =? c0) && (Znth (k + 1) bs =? c1))%bool)))).
  { forward. { entailer!. rewrite (Znth_bytes_sub _ bs k 4 1) by lia. apply tc_byte; auto. }
    rewrite (Znth_bytes_sub _ bs k 4 1) by lia. forward. entailer!. bool_fin. }
  { forward. entailer!. bool_fin. }
  forward_if (temp _t'2 (Vint (Int.repr (Z.b2z ((Znth k bs =? c0) && (Znth (k + 1) bs =? c1) &&
                                                  (Znth (k + 2) bs =? c2))%bool)))).
  { try b2z_hyp. forward. { entailer!. rewrite (Znth_bytes_sub _ bs k 4 2) by lia. apply tc_byte; auto. }
    rewrite (Znth_bytes_sub _ bs k 4 2) by lia. forward. entailer!. rw_bools. bool_fin. }
  { try b2z_hyp. forward. entailer!. rw_bools. reflexivity. }
  forward_if (temp _t'3 (Vint (Int.repr (Z.b2z (sig_at bs k [c0; c1; c2; c3]))))).
  { try b2z_hyp. forward. { entailer!. rewrite (Znth_bytes_sub _ bs k 4 3) by lia. apply tc_byte; auto. }
    rewrite (Znth_bytes_sub _ bs k 4 3) by lia. forward. entailer!. rewrite sig_at4.
    rw_bools. bool_fin. }
  { try b2z_hyp. forward. entailer!. rewrite sig_at4. rw_bools. reflexivity. }
  forward. entailer!.
  all: try (destruct (sig_at bs k [c0; c1; c2; c3]); reflexivity).
  all: rewrite (bytes_split3 sh (Zlength bs) k 4 bs b) by (auto; lia); cancel.
Qed.

Lemma body_transition : semax_body nil nil f_transition transition_spec.
Proof.
  start_function.
  assert (A0: 0 <= Znth 0 a <= Int64.max_unsigned) by (apply (Forall_Znth' _ _ 0 H0); lia).
  assert (A1: 0 <= Znth 1 a <= Int64.max_unsigned) by (apply (Forall_Znth' _ _ 1 H0); lia).
  assert (A2: 0 <= Znth 2 a <= Int64.max_unsigned) by (apply (Forall_Znth' _ _ 2 H0); lia).
  assert (A3: 0 <= Znth 3 a <= Int64.max_unsigned) by (apply (Forall_Znth' _ _ 3 H0); lia).
  assert (A4: 0 <= Znth 4 a <= Int64.max_unsigned) by (apply (Forall_Znth' _ _ 4 H0); lia).
  unfold u64_ok in *.
  forward. forward. forward. forward. forward.
  unfold vl, vi in *.
  forward_if; [ forward; entailer!; unfold law_transition; bool_fin | ].
  forward_if; [ forward; entailer!; unfold law_transition; bool_fin | ].
  forward_if; [ forward; entailer!; unfold law_transition; bool_fin | ].
  forward_if; [ forward; entailer!; unfold law_transition; bool_fin | ].
  forward_if; [ forward; entailer!; unfold law_transition; bool_fin | ].
  forward_if; [ forward; entailer!; unfold law_transition; bool_fin | ].
  forward_if; [ forward; entailer!; unfold law_transition; bool_fin | ].
  forward_if; [ forward; entailer!; unfold law_transition; bool_fin | ].
  forward_if; [ forward; entailer!; unfold law_transition; bool_fin | ].
  forward_if (temp _t'1 (Vint (Int.repr (Z.b2z ((last =? 0) && negb (Znth 3 a =? cursor))%bool)))).
  { repeat forward. entailer!. bool_fin. }
  { repeat forward. entailer!. bool_fin. }
  forward_if. { try b2z_hyp. forward. entailer!. unfold law_transition. rw_bools. bool_fin. }
  try b2z_hyp.
  forward_if (temp _t'2 (Vint (Int.repr (Z.b2z (negb (last =? 0) && (Znth 3 a <=? cursor))%bool)))).
  { repeat forward. entailer!. bool_fin. }
  { repeat forward. entailer!. bool_fin. }
  forward_if. { try b2z_hyp. forward. entailer!. unfold law_transition. rw_bools. bool_fin. }
  try b2z_hyp. forward. entailer!. unfold law_transition. rw_bools. bool_fin.
Qed.
