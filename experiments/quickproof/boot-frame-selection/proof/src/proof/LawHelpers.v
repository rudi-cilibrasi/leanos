(* Law frame_selection_exact: the bodies of the harness's helpers any_u64, stop, same_manifest, select_done and
   next_candidate, and of main's begin_terminal, begin_select, begin_scrub and begin_publication_result: each moves
   the law's record to the model's start of its step. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosFrameSelection.harness.frame_selection_exact.code.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
Require Import LeanosFrameSelection.proof.LawProg LeanosFrameSelection.proof.LawDefs LeanosFrameSelection.proof.LawFacts
  LeanosFrameSelection.proof.LawLib.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Lemma body_any_u64: semax_body nil [nondet_u32_spec] f_any_u64 any_u64_spec.
Proof.
  start_function.
  rewrite <- seq_assoc. forward_call. Intros hi. forward.
  rewrite <- seq_assoc. forward_call. Intros lo. forward.
  forward.
  Exists (Int64.unsigned (Int64.or (Int64.shl (Int64.repr hi) (Int64.repr 32)) (Int64.repr lo))).
  entailer!. split; [ apply Int64.unsigned_range_2 | unfold vl; rewrite Int64.repr_unsigned; reflexivity ].
Qed.

Lemma body_stop: semax_body nil nil f_stop stop_spec.
Proof. start_function. forward. forward. entailer!. Qed.

Lemma body_same_manifest: semax_body Vlaw nil f_same_manifest same_manifest_spec.
Proof.
  start_function.
  forward_for_simple_bound 18
    (EX i: Z, PROP () LOCAL (temp _words wp; gvars gv)
     SEP (data_at sh t_manifest (map vl ms) wp; field_at Ews t_law (DOT _manifest) (map vl ms) (gv _law)))%assert.
  - entailer!.
  - unfold t_manifest. forward.
    forward.
    forward_if.
    { exfalso. apply H1; reflexivity. }
    forward. entailer!.
  - forward.
Qed.

Lemma body_select_done: semax_body nil [stop_spec] f_select_done select_done_spec.
Proof.
  start_function.
  forward. forward. forward. forward. forward. forward.
  forward_call (q, e0, v0, S_OK).
  entailer!.
Qed.

Lemma body_next_candidate: semax_body nil [stop_spec; select_done_spec] f_next_candidate next_candidate_spec.
Proof.
  start_function.
  forward.
  forward_if.
  - rewrite add64_repr' in H0. rewrite !Int64.unsigned_repr in H0 by rep_lia.
    assert (E: (c + 1 <? FRAMES) = true) by (apply Z.ltb_lt; lia).
    forward. forward. forward. rewrite ?E. entailer!.
  - rewrite add64_repr' in H0. rewrite !Int64.unsigned_repr in H0 by rep_lia.
    assert (E: (c + 1 <? FRAMES) = false) by (apply Z.ltb_ge; lia).
    forward_call (q, f, fm, n, se, me, ne, e0, v0).
    rewrite ?E. entailer!.
Qed.

(* ---------------------------------------------------------------------- *)
(* The steps' starts that only set the record                              *)
(* ---------------------------------------------------------------------- *)

Lemma seq_ok_keep: forall x p p' s s', seq_ok x p s -> w_call s' = w_call s -> w_scrubbed s' = w_scrubbed s ->
  (i_step x = FScrub -> forall m, p' <> Return S_OK m) -> seq_ok x p' s'.
Proof.
  intros x p p' s s' (A & B) C D E. split.
  - intros F. rewrite C, D. auto.
  - intros F m G. exfalso. exact (E F m G).
Qed.

Lemma lst_ok_set: forall s c r st e v b w ca sc ms me cm f fm se sb,
  lst_ok s -> u32_ok c -> u32_ok r -> u32_ok st -> u32_ok e -> u32_ok v -> u64_ok b -> u64_ok w -> u64_ok ca ->
  u32_ok sc -> u64_ok ms -> u64_ok me -> u64_ok cm -> u64_ok f -> u64_ok fm -> u64_ok se -> u32_ok sb ->
  lst_ok (mk_lst c r st e v b w ca sc ms me (w_free s) cm f fm se (w_answer s) sb).
Proof.
  intros. unfold lst_ok in *; lst_cbn. tauto.
Qed.

Ltac lst_ok_tac :=
  match goal with H: lst_ok ?s |- lst_ok _ =>
    let L := fresh in pose proof H as L; unfold lst_ok in L;
    apply lst_ok_set; auto; try tauto; unfold u32_ok, u64_ok, E_MANIFEST, E_DECODE, E_SCRUB, E_AUTHORITY, E_NOTHING,
      ST_TERMINAL, ST_SELECT, ST_SCRUB, ST_PUBLICATION_RESULT in *; rep_lia
  end.

Definition s_terminal (s: lst) : lst :=
  mk_lst (w_call s) (w_running s) ST_TERMINAL E_MANIFEST (w_verdict s) 0 1 (w_candidate s) (w_scan s) 1 0
         (w_free s) (w_cm s) (w_first s) (w_fm s) (w_second s) (w_answer s) (w_scrubbed s).

Lemma J_begin_terminal: forall x s, i_step x = FTerminal -> lst_ok s -> seq_ok x (start x) s ->
  J x (start x) (s_terminal s).
Proof.
  intros x s F L Q. unfold J, start. rewrite F. split_and.
  - unfold s_terminal. lst_ok_tac.
  - apply (seq_ok_keep x (start x) _ s); auto. intros G. congruence.
  - unfold go_inv, s_terminal; lst_cbn. rewrite Zlength_nil, !sublist_nil. split_and; auto; lia.
Qed.

Lemma body_begin_terminal: semax_body nil nil f_begin_terminal begin_terminal_spec.
Proof.
  start_function.
  rename H into F, H0 into Ix, H1 into Hs, H2 into Q.
  unfold lfields. Intros.
  forward. forward. forward. forward. forward. forward.
  Exists (s_terminal s). unfold lfields, s_terminal; lst_cbn.
  entailer!. apply J_begin_terminal; auto.
Qed.

Definition s_select (s: lst) : lst :=
  mk_lst (w_call s) (w_running s) ST_SELECT E_DECODE (w_verdict s) (w_block s) (w_word s) 0 0 (w_ms s) (w_me s)
         (w_free s) (w_cm s) FRAMES 0 FRAMES (w_answer s) (w_scrubbed s).

Lemma J_begin_select: forall x s, i_step x = FSelect -> lst_ok s -> seq_ok x (start x) s ->
  J x (start x) (s_select s).
Proof.
  intros x s F L Q. unfold J, start. rewrite F. split_and.
  - unfold s_select. lst_ok_tac.
  - apply (seq_ok_keep x (start x) _ s); auto. intros G. congruence.
  - unfold go_inv, s_select; lst_cbn. split_and; auto; lia.
Qed.

Lemma body_begin_select: semax_body nil nil f_begin_select begin_select_spec.
Proof.
  start_function.
  rename H into F, H0 into Ix, H1 into Hs, H2 into Q.
  unfold lfields. Intros.
  forward. forward. forward. forward. forward. forward. forward.
  Exists (s_select s). unfold lfields, s_select; lst_cbn.
  entailer!. apply J_begin_select; auto.
Qed.

Definition s_scrub (s: lst) : lst :=
  mk_lst (w_call s) (w_running s) ST_SCRUB E_SCRUB (w_verdict s) (w_block s) (w_word s) (w_candidate s) (w_scan s)
         (w_ms s) (w_me s) (w_free s) (w_cm s) (w_first s) (w_fm s) (w_second s) (w_answer s) (w_scrubbed s).

Lemma J_begin_scrub: forall x s, i_step x = FScrub -> lst_ok s -> seq_ok x (start x) s ->
  J x (start x) (s_scrub s).
Proof.
  intros x s F L Q. unfold J, start. rewrite F. split_and.
  - unfold s_scrub. lst_ok_tac.
  - apply (seq_ok_keep x (start x) _ s); auto. intros G m E. discriminate.
  - unfold go_inv, s_scrub; lst_cbn. reflexivity.
Qed.

Lemma body_begin_scrub: semax_body nil nil f_begin_scrub begin_scrub_spec.
Proof.
  start_function.
  rename H into F, H0 into Ix, H1 into Hs, H2 into Q.
  unfold lfields. Intros.
  forward. forward.
  Exists (s_scrub s). unfold lfields, s_scrub; lst_cbn.
  entailer!. apply J_begin_scrub; auto.
Qed.

Definition s_publication_result (s: lst) : lst :=
  mk_lst (w_call s) (w_running s) ST_PUBLICATION_RESULT E_AUTHORITY (w_verdict s) (w_block s) 0 (w_candidate s)
         (w_scan s) (w_ms s) (w_me s) (w_free s) (w_cm s) (w_first s) (w_fm s) (w_second s) (w_answer s)
         (w_scrubbed s).

Lemma J_begin_publication_result: forall x s, i_step x = FPublicationResult -> lst_ok s -> seq_ok x (start x) s ->
  J x (start x) (s_publication_result s).
Proof.
  intros x s F L Q. unfold J, start. rewrite F. split_and.
  - unfold s_publication_result. lst_ok_tac.
  - apply (seq_ok_keep x (start x) _ s); auto. intros G. congruence.
  - unfold go_inv, s_publication_result; lst_cbn. split_and; auto; lia.
Qed.

Lemma body_begin_publication_result:
  semax_body nil nil f_begin_publication_result begin_publication_result_spec.
Proof.
  start_function.
  rename H into F, H0 into Ix, H1 into Hs, H2 into Q.
  unfold lfields. Intros.
  forward. forward. forward.
  Exists (s_publication_result s). unfold lfields, s_publication_result; lst_cbn.
  entailer!. apply J_begin_publication_result; auto.
Qed.
