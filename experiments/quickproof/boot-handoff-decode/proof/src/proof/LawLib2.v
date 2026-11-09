(* Law handoff_decode_exact: tactics the bodies of the harness's callees share: the oracle opened at the entry and
   re-established at the return, the law's pointer valid, the 64-bit temps as VST evaluates them. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosHandoff.harness.handoff_decode_exact.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.LawProg LeanosHandoff.proof.LawDefs LeanosHandoff.proof.LawFacts
  LeanosHandoff.proof.LawLib.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[export] Existing Instance LawProg.LCS.

Lemma law_valid: forall v q, field_at Ews t_law (DOT _call) v q |-- valid_pointer q.
Proof.
  intros. apply field_at_valid_ptr0; [ apply readable_nonidentity, writable_readable, writable_Ews | | ];
    reflexivity.
Qed.
#[export] Hint Resolve law_valid : valid_pointer.

Ltac mem_cbn := cbn [mem_of m_total m_extent_ok m_copy m_usable m_blocked m_reserved m_states m_at
  with_extent with_copy with_bitmaps with_states Z.b2z] in *.

(* The oracle at the record s' and the model's p'. *)
Ltac ora_fin p' s' ce ie :=
  unfold Ora_law; Exists p' s' ce ie; unfold lfields, arrays, s_stop, s_stream, s_store, s_more; mem_cbn; lst_cbn;
  entailer!.

(* The oracle at the entry, opened: its hypotheses named. *)
Ltac ora_open x h p s ce ie :=
  unfold Ora_law; Intros p s ce ie;
  repeat match goal with H: ?c = ?g _law |- _ => is_var c; subst c end;
  match goal with H: inputs_ok x |- _ => rename H into Ix end;
  match goal with H: x_fit x |- _ => rename H into Xf end;
  match goal with H: run x (start x) h = Some p |- _ => rename H into Hrun end;
  match goal with H: J x p s |- _ => rename H into HJ end;
  match goal with H: ptr_ok x ce ie |- _ => rename H into Pie end.

(* The 64-bit temps as Vlong, so that VST computes with them (array indices). *)
Ltac vl_temps := repeat match goal with |- context [temp ?i (vl ?e)] =>
  change (temp i (vl e)) with (temp i (Vlong (Int64.repr e))) end.

(* The step of the model at a word that is not the last. *)
Lemma step_more: forall n (a: list Z) v, Zlength a + 1 < n -> (Zlength (a ++ [v]) <? n) = true.
Proof. intros. apply Z.ltb_lt. rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. Qed.

Lemma step_last: forall n (a: list Z) v, Zlength a + 1 = n -> (Zlength (a ++ [v]) <? n) = false.
Proof. intros. apply Z.ltb_ge. rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. Qed.

(* The answers after the last word: the first n words of the answer array. *)
Lemma answers_last: forall s a v n, prefix s a -> Zlength a + 1 = n -> n <= WORDS -> Zlength (w_answer s) = WORDS ->
  a ++ [v] = sublist 0 n (upd_Znth (w_word s) (w_answer s) v).
Proof.
  intros s a v n P L N W. pose proof (prefix_store s a v P ltac:(lia)) as E. rewrite <- L, E. reflexivity.
Qed.

(* The branch of a condition that does not hold. *)
Ltac else_false2 :=
  first [ solve [ exfalso; lia ] | solve [ exfalso; u64c; first [ lia | contradiction ] ] | solve [ else_false ] ].

(* `if (c) t = (bool) c'; else t = 0;` with c and c' true. *)
Ltac if2 :=
  to_branch;
  match goal with |- semax _ _ ?c _ =>
    let s := first_stmt c in
    lazymatch s with
    | Sifthenelse _ _ (Sset ?t (Econst_int (Int.repr 0) tint)) => forward_if (temp t (Vint Int.one))
    end
  end;
  [ solve [ repeat forward; entailer!; try cmp_close ] | solve [ else_false2 ] | ].

Lemma upd_Znth_map_vl': forall l i v, upd_Znth i (map vl l) (Vlong (Int64.repr v)) = map vl (upd_Znth i l v).
Proof. intros. apply upd_Znth_map_vl. Qed.

Ltac upd_vl := rewrite ?upd_Znth_map_vl, ?upd_Znth_map_vl'.

(* The statuses, as numbers. *)
Ltac unfold_status := unfold S_OK, S_MAGIC, S_POINTER_ALIGNMENT, S_POINTER_LOW, S_POINTER_HIGH, S_BOUNDS_SMALL, S_BOUNDS_LARGE, S_BOUNDS_ALIGNMENT, S_BOUNDS_LIMIT, S_STREAM_INIT_VERSION, S_STREAM_INIT_STATUS, S_STREAM_INIT_ERROR, S_STREAM_INIT_IDENTITY, S_STREAM_INIT_EXTENT, S_STREAM_INIT_OFFSET, S_STREAM_STEP_VERSION, S_STREAM_STEP_ERROR, S_STREAM_STEP_IDENTITY, S_STREAM_STEP_EXTENT, S_STREAM_STEP_OFFSET, S_STREAM_STEP_COUNT, S_STREAM_STEP_EXPOSED, S_STREAM_STEP_STATUS, S_STREAM_INCOMPLETE_STATUS, S_STREAM_INCOMPLETE_OFFSET, S_COPY_LENGTH, S_DECODE_INIT_VERSION, S_DECODE_INIT_STATUS, S_DECODE_INIT_ERROR, S_DECODE_INIT_IDENTITY, S_DECODE_INIT_EXTENT, S_DECODE_INIT_OFFSET, S_DECODE_INIT_TARGET, S_DECODE_INIT_TAG_COUNT, S_DECODE_INIT_ROOT_STATUS, S_PROJECTION_COUNT_ZERO, S_PROJECTION_COUNT_LARGE, S_PROJECTION_ENTRY_STATUS, S_PROJECTION_ENTRY_ERROR, S_DECODE_INCOMPLETE_STATUS, S_DECODE_INCOMPLETE_OFFSET, S_DECODE_INCOMPLETE_PHASE, S_DECODE_REJECTED_STATUS, S_DECODE_REJECTED_ERROR, S_AUTHORITY_INIT_VERSION, S_AUTHORITY_INIT_STATUS, S_AUTHORITY_INIT_ERROR, S_AUTHORITY_INIT_IDENTITY, S_AUTHORITY_INIT_EXTENT, S_AUTHORITY_INIT_OFFSET, S_AUTHORITY_INIT_TARGET, S_AUTHORITY_INIT_TAG_COUNT, S_AUTHORITY_INIT_ROOT_STATUS, S_AUTHORITY_REJECTED_STATUS, S_AUTHORITY_REJECTED_ERROR, S_AUTHORITY_REJECTED_OFFSET, S_AUTHORITY_REJECTED_PHASE, S_AUTHORITY_REJECTED_TARGET in *.

(* A check of the model against the C's branch conditions. *)
Ltac chk_dec := unfold_status; u64c; bool_dec.

Lemma Forall_u64_app1: forall l v, Forall u64_ok l -> u64_ok v -> Forall u64_ok (l ++ [v]).
Proof. intros. apply Forall_app; split; auto. Qed.

(* The copy, as the phases that do not write it leave it. *)
Lemma copy_begin_chunk: forall x k st m, m_copy (mem_of (begin_chunk x k st m)) = m_copy m.
Proof.
  intros. unfold begin_chunk, copy_end, begin_decode. destruct (_ <? _); [ reflexivity | ].
  destruct (negb _); [ reflexivity | ]. destruct (i_call x); try reflexivity; destruct (projection x); reflexivity.
Qed.

Lemma arrays_begin_chunk: forall x ce ie k st m,
  arrays x ce ie (mem_of (begin_chunk x k st m)) = arrays x ce ie m.
Proof. intros. unfold arrays. rewrite copy_begin_chunk. reflexivity. Qed.

Ltac norm_vl := repeat (rewrite Znth_map_vl in * by lia).

(* The terminal marker as the harness computes it, `(uint64_t)(end == total)`. *)
Lemma b2z_terminal: forall T k,
  Vlong (Int64.repr (Int.signed (Int.repr (Z.b2z (8 * k + 8 =? T))))) = vl (terminal T k).
Proof. intros. unfold terminal. destruct (8 * k + 8 =? T); reflexivity. Qed.

(* The comparisons of 64-bit words, the products by 8 and the sums computed. *)
Ltac cmp_close2 :=
  try change (Int.signed (Int.repr 8)) with 8 in *;
  try change (Int.signed (Int.repr 1)) with 1 in *;
  rewrite ?mul64_repr', ?add64_repr' in *;
  cmp_close.

Ltac if3 :=
  to_branch;
  match goal with |- semax _ _ ?c _ =>
    let s := first_stmt c in
    lazymatch s with
    | Sifthenelse _ _ (Sset ?t (Econst_int (Int.repr 0) tint)) => forward_if (temp t (Vint Int.one))
    end
  end;
  [ solve [ repeat forward; entailer!; try cmp_close2 ] | solve [ else_false2 ] | ].
