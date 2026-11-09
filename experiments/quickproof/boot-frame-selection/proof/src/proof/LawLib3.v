(* Law frame_selection_exact: the state k (0 or 1) of the law's model of the two states as one row and the other,
   and the tactics that close a callee: the invariant J of the new record, the oracle at the new progress. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosFrameSelection.harness.frame_selection_exact.code.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
Require Import LeanosFrameSelection.proof.LawProg LeanosFrameSelection.proof.LawDefs LeanosFrameSelection.proof.LawFacts
  LeanosFrameSelection.proof.LawLib LeanosFrameSelection.proof.LawLib2 LeanosFrameSelection.proof.LawRows.
Local Open Scope Z_scope.
#[export] Existing Instance LawProg.LCS.

Lemma states_rows_k: forall q ss k, field_compatible t_law (DOT _states_expect) q -> Zlength ss = 2 ->
  Zlength (Znth 0 ss) = WORDS -> Zlength (Znth 1 ss) = WORDS -> (k = 0 \/ k = 1) ->
  field_at Ews t_law (DOT _states_expect) (states_val ss) q =
  (data_at Ews (tarray tulong 41) (map vl (Znth k ss)) (srow q k) *
   data_at Ews (tarray tulong 41) (map vl (Znth (1 - k) ss)) (srow q (1 - k)))%logic.
Proof.
  intros q ss k FC L L0 L1 K. rewrite states_rows by auto. unfold t_state.
  destruct K as [-> | ->]; [ reflexivity | apply sepcon_comm ].
Qed.

Lemma states_rows_k_fold: forall q ss k, field_compatible t_law (DOT _states_expect) q -> Zlength ss = 2 ->
  Zlength (Znth 0 ss) = WORDS -> Zlength (Znth 1 ss) = WORDS -> (k = 0 \/ k = 1) ->
  (data_at Ews (tarray tulong 41) (map vl (Znth k ss)) (srow q k) *
   data_at Ews (tarray tulong 41) (map vl (Znth (1 - k) ss)) (srow q (1 - k)))%logic
  |-- field_at Ews t_law (DOT _states_expect) (states_val ss) q.
Proof. intros. rewrite (states_rows_k q ss k) by auto. apply derives_refl. Qed.

Ltac unfold_S := unfold S_OK, S_TERMINAL_VERSION, S_TERMINAL_STATUS, S_TERMINAL_ERROR, S_TERMINAL_FRAME,
  S_TERMINAL_OWNER, S_TERMINAL_ENTRY_COUNT, S_DECODER, S_AUTHORITY_NONE, S_AUTHORITY_NOMINATION, S_AUTHORITY_TARGET,
  S_AUTHORITY_ENTRY_COUNT, S_AUTHORITY_HIGHEST, S_AUTHORITY_USABLE, S_AUTHORITY_BLOCKED, S_AUTHORITY_MANIFEST,
  S_SCRUB, S_PUBLICATION_VERSION, S_PUBLICATION_STATUS, S_PUBLICATION_ERROR, S_PUBLICATION_FRAME,
  S_PUBLICATION_OBJECT, S_UNPUBLISHED_LIMIT, S_UNPUBLISHED_ORDER, S_RESCAN_ENTRY_COUNT, S_RESCAN_HIGHEST,
  S_RESCAN_TARGET, S_RESCAN_STATUS, S_RESCAN_USABLE, S_RESCAN_BLOCKED, S_RESCAN_MANIFEST in *.

(* J of a record built from s by set_* (its ranges, the stage's counters, main's sequence record kept). *)
Ltac Jtac :=
  unfold J, seq_ok, ret_inv; cbn [go_inv]; set_unfold; lst_cbn;
  split_and;
  [ apply lst_ok_mk; auto; unfold u32_ok, u64_ok, E_MANIFEST, E_FREE, E_FINISH, E_DECODE, E_CANDIDATE, E_CONSUME,
      E_SCRUB, E_AUTHORITY, E_NOTHING, ST_TERMINAL, ST_SELECT, ST_CROSS_CHECK, ST_SCRUB, ST_PUBLICATION_RESULT,
      ST_PUBLICATION_CHECK, ST_RESCAN in *; unfold_S; rep_lia | .. ];
  try (intros; congruence); try reflexivity; try assumption; try lia; auto.

(* The oracle at progress p' and record s', the law's fields at hand (thawed). *)
Ltac ora_close_tac p' s' :=
  unfold Ora_law; Exists p' s'; unfold lfields; set_unfold; lst_cbn;
  cbn [mem_of m_reserved m_terminal m_states m_publication m_rescan m_selected m_selected_manifest m_next m_decoder
       with_reserved with_terminal with_states with_state with_publication with_rescan with_records with_decoder];
  upd_vl; rewrite ?add64_repr'; entailer!; try (apply answers_ok_snoc; auto).

(* The 64-bit temps as Vlong, so that VST computes with them (array indices). *)
Ltac vl_temps := repeat match goal with |- context [temp ?i (vl ?e)] =>
  change (temp i (vl e)) with (temp i (Vlong (Int64.repr e))) end.

(* The ranges of the words at the indices ks of l. *)
Ltac rng_at l ks :=
  lazymatch ks with
  | nil => idtac
  | ?k :: ?ks' =>
      assert (0 <= Znth k l <= Int64.max_unsigned) by (apply Forall_u64_Znth; [ assumption | rep_lia ]);
      rng_at l ks'
  end.
