(* Law handoff_decode_exact: what the decoder's callees share: the words decoded within the law's arrays, the
   states as the harness writes them, the statuses that depend on the decoder (by_call). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosHandoff.harness.handoff_decode_exact.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.LawProg LeanosHandoff.proof.LawDefs LeanosHandoff.proof.LawFacts
  LeanosHandoff.proof.LawLib LeanosHandoff.proof.LawLib2.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[export] Existing Instance LawProg.LCS.

(* The copy, when a decoder alone does not decode it. *)
Definition other_obj (x: inputs) (ce: val) (m: mem) : mpred :=
  if is_alloc x then emp else if has_copy x then data_at Ews (tarray tulong COPY_WORDS) (map vl (m_copy m)) ce else emp.

Lemma arrays_decoded: forall x ce ie m, ptr_ok x ce ie -> (has_copy x = true -> Zlength (m_copy m) = COPY_WORDS) ->
  i_call x <> FCopy ->
  arrays x ce ie m =
  (data_at Ews (tarray tulong (Zlength (decoded x m))) (map vl (decoded x m)) ie * other_obj x ce m)%logic.
Proof.
  intros x ce ie m (Pie & _) L Nc. unfold arrays, info_obj, other_obj, decoded, is_alloc, has_copy in *.
  destruct (i_call x) eqn:C.
  - rewrite (Pie eq_refl). rewrite L by reflexivity. rewrite sepcon_emp. reflexivity.
  - contradiction.
  - rewrite emp_sepcon, sepcon_emp. reflexivity.
  - rewrite emp_sepcon, sepcon_emp. reflexivity.
Qed.

Lemma other_obj_states: forall x ce m ss i, other_obj x ce (with_states m ss i) = other_obj x ce m.
Proof. reflexivity. Qed.

Lemma other_obj_bitmaps: forall x ce m u b r, other_obj x ce (with_bitmaps m u b r) = other_obj x ce m.
Proof. reflexivity. Qed.

(* A store into a state, as VST leaves it. *)
Lemma states_store: forall ss j i v, 0 <= j < Zlength ss ->
  upd_Znth j (states_val ss) (upd_Znth i (Znth j (states_val ss)) (vl v)) =
  states_val (upd_Znth j ss (upd_Znth i (Znth j ss) v)).
Proof.
  intros. unfold states_val. rewrite Znth_map by auto. rewrite upd_Znth_map_vl.
  rewrite upd_Znth_map. reflexivity.
Qed.

Lemma states_store': forall ss j i v, 0 <= j < Zlength ss ->
  upd_Znth j (states_val ss) (upd_Znth i (Znth j (states_val ss)) (Vlong (Int64.repr v))) =
  states_val (upd_Znth j ss (upd_Znth i (Znth j ss) v)).
Proof. intros. apply states_store; auto. Qed.

(* The row j of the states, written word by word from the answers. *)
Lemma row_step: forall (ss: list (list Z)) j (ans: list Z) i, 0 <= j < Zlength ss -> 0 <= i < WORDS ->
  Zlength ans = WORDS -> Zlength (Znth j ss) = WORDS ->
  upd_Znth j (upd_Znth j ss (sublist 0 i ans ++ sublist i WORDS (Znth j ss)))
    (upd_Znth i (Znth j (upd_Znth j ss (sublist 0 i ans ++ sublist i WORDS (Znth j ss)))) (Znth i ans)) =
  upd_Znth j ss (sublist 0 (i + 1) ans ++ sublist (i + 1) WORDS (Znth j ss)).
Proof.
  intros ss j ans i J I La Lr.
  rewrite upd_Znth_same by auto. rewrite upd_Znth_twice by auto. f_equal. list_solve.
Qed.

Lemma row_start: forall (ss: list (list Z)) j, 0 <= j < Zlength ss -> Zlength (Znth j ss) = WORDS ->
  upd_Znth j ss (sublist 0 0 (Znth j ss) ++ sublist 0 WORDS (Znth j ss)) = ss.
Proof.
  intros ss j J L. rewrite sublist_nil, app_nil_l, sublist_same by auto. apply upd_Znth_triv; auto.
Qed.

(* The statuses prefixed DECODE_ with a projection, AUTHORITY_ for a candidate. *)
Lemma by_call_t: forall x d a, proj_code x <> 0 -> by_call x d a = d.
Proof. intros. unfold by_call, proj_code in *. destruct (projection x); [ reflexivity | lia ]. Qed.

Lemma by_call_f: forall x d a, proj_code x = 0 -> by_call x d a = a.
Proof. intros. unfold by_call, proj_code in *. destruct (projection x); [ lia | reflexivity ]. Qed.

Lemma by_call_u32: forall x d a, u32_ok d -> u32_ok a -> u32_ok (by_call x d a).
Proof. intros. unfold by_call. destruct (projection x); auto. Qed.

(* `p ? d : a` with p the law's projection. *)
Ltac by_call_if x :=
  match goal with |- semax _ _ ?c _ =>
    let st := first_stmt c in
    lazymatch st with
    | Sifthenelse (Etempvar _ tuint) (Sset ?t (Ecast (Econst_int (Int.repr ?d) tint) tint))
                  (Sset _ (Ecast (Econst_int (Int.repr ?au) tint) tint)) =>
        forward_if (temp t (vi (by_call x d au)));
        [ forward; entailer!; u64c; rewrite by_call_t by lia; reflexivity
        | forward; entailer!; u64c; rewrite by_call_f by lia; reflexivity
        | ]
    end
  end.

(* The states after a reset or a transition wrote row n, as two rows. *)
Lemma states_upd0: forall (L: list (list Z)) r, Zlength L = 2 ->
  states_val (upd_Znth 0 L r) = [map vl r; map vl (Znth 1 L)].
Proof.
  intros L r H. destruct L as [ | r0 [ | r1 [ | r2 L]]]; try (rewrite ?Zlength_cons, ?Zlength_nil in H; rep_lia).
  reflexivity.
Qed.

Lemma states_upd1: forall (L: list (list Z)) r, Zlength L = 2 ->
  states_val (upd_Znth 1 L r) = [map vl (Znth 0 L); map vl r].
Proof.
  intros L r H. destruct L as [ | r0 [ | r1 [ | r2 L]]]; try (rewrite ?Zlength_cons, ?Zlength_nil in H; rep_lia).
  reflexivity.
Qed.

Lemma rows_upd0: forall q L r, field_compatible t_law (DOT _states_expect) q -> Zlength L = 2 ->
  Zlength r = WORDS -> Zlength (Znth 1 L) = WORDS ->
  field_at Ews t_law (DOT _states_expect) (states_val (upd_Znth 0 L r)) q =
  (data_at Ews t_state (map vl r) (row q 0) * data_at Ews t_state (map vl (Znth 1 L)) (row q 1))%logic.
Proof. intros. rewrite states_upd0 by auto. apply states_rows; auto. Qed.

Lemma rows_upd1: forall q L r, field_compatible t_law (DOT _states_expect) q -> Zlength L = 2 ->
  Zlength r = WORDS -> Zlength (Znth 0 L) = WORDS ->
  field_at Ews t_law (DOT _states_expect) (states_val (upd_Znth 1 L r)) q =
  (data_at Ews t_state (map vl (Znth 0 L)) (row q 0) * data_at Ews t_state (map vl r) (row q 1))%logic.
Proof. intros. rewrite states_upd1 by auto. apply states_rows; auto. Qed.

Lemma rows_upd0_fold: forall q L r, field_compatible t_law (DOT _states_expect) q -> Zlength L = 2 ->
  Zlength r = WORDS -> Zlength (Znth 1 L) = WORDS ->
  (data_at Ews t_state (map vl r) (row q 0) * data_at Ews t_state (map vl (Znth 1 L)) (row q 1))%logic
  |-- field_at Ews t_law (DOT _states_expect) (states_val (upd_Znth 0 L r)) q.
Proof. intros. rewrite rows_upd0 by auto. apply derives_refl. Qed.

Lemma rows_upd1_fold: forall q L r, field_compatible t_law (DOT _states_expect) q -> Zlength L = 2 ->
  Zlength r = WORDS -> Zlength (Znth 0 L) = WORDS ->
  (data_at Ews t_state (map vl (Znth 0 L)) (row q 0) * data_at Ews t_state (map vl r) (row q 1))%logic
  |-- field_at Ews t_law (DOT _states_expect) (states_val (upd_Znth 1 L r)) q.
Proof. intros. rewrite rows_upd1 by auto. apply derives_refl. Qed.

(* The oracle after an answer, the model then at p (of memory m') and the record s. *)
Lemma ora_close': forall gv x h c v p m' s ce ie,
  inputs_ok x -> x_fit x -> run x (start x) (h ++ [(c, v)]) = Some p -> mem_of p = m' -> J x p s ->
  ptr_ok x ce ie ->
  (lfields (gv _law) x ce ie m' s * arrays x ce ie m')%logic |-- Ora_law gv (gv _law) (gv _law) x (h ++ [(c, v)]).
Proof.
  intros gv x h c v p m' s ce ie Ix Xf R M HJ Pie. subst m'. unfold Ora_law. Exists p s ce ie. entailer!.
Qed.

(* The same, with the arrays of a memory m0 with the same copy. *)
Lemma ora_close2: forall gv x h c v p m' m0 s ce ie,
  inputs_ok x -> x_fit x -> run x (start x) (h ++ [(c, v)]) = Some p -> mem_of p = m' -> J x p s ->
  ptr_ok x ce ie -> m_copy m0 = m_copy m' ->
  (lfields (gv _law) x ce ie m' s * arrays x ce ie m0)%logic |-- Ora_law gv (gv _law) (gv _law) x (h ++ [(c, v)]).
Proof.
  intros gv x h c v p m' m0 s ce ie Ix Xf R M HJ Pie C.
  replace (arrays x ce ie m0) with (arrays x ce ie m') by (unfold arrays; rewrite C; reflexivity).
  apply (ora_close' gv x h c v p m' s ce ie); auto.
Qed.

(* The oracle at the record s' and the model's p' of memory m', through the law's fields folded (cheaper than
   ora_fin): Rn the run, HJ' the invariant; the arrays of memory m0, m' having its copy. *)
Ltac ora_fin3 gv x h p' m' m0 s' ce ie Ix Xf Rn HJ' Pie :=
  sep_apply (lfields_fold (gv _law) x ce ie m' s');
  let OC := fresh "OC" in
  pose proof (ora_close2 gv x h _ _ p' m' m0 s' ce ie Ix Xf Rn eq_refl HJ' Pie eq_refl) as OC;
  sep_apply OC; clear OC;
  entailer!.

(* The generic store into a state and the row's address with a constant index. *)
Lemma Znth_dflt: forall {A} (d1 d2: Inhabitant A) (l: list A) i, 0 <= i < Zlength l ->
  @Znth A d1 i l = @Znth A d2 i l.
Proof.
  intros A d1 d2 l i I. unfold Znth. rewrite !if_false by lia. apply nth_indep.
  rewrite <- ZtoNat_Zlength. apply Z2Nat.inj_lt; lia.
Qed.

Lemma states_store_g: forall (d: Inhabitant (list val)) ss j i v, 0 <= j < Zlength ss ->
  upd_Znth j (states_val ss) (upd_Znth i (@Znth _ d j (states_val ss)) (vl v)) =
  states_val (upd_Znth j ss (upd_Znth i (Znth j ss) v)).
Proof.
  intros d ss j i v J. rewrite (Znth_dflt d Inhabitant_list) by (unfold states_val; rewrite !Zlength_map; lia).
  apply states_store; auto.
Qed.

Lemma arrays_fold: forall x ce ie m, ptr_ok x ce ie -> (has_copy x = true -> Zlength (m_copy m) = COPY_WORDS) ->
  i_call x <> FCopy ->
  (data_at Ews (tarray tulong (Zlength (decoded x m))) (map vl (decoded x m)) ie * other_obj x ce m)%logic
  |-- arrays x ce ie m.
Proof. intros. rewrite arrays_decoded by auto. apply derives_refl. Qed.
