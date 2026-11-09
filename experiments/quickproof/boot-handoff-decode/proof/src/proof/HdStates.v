(* The decoder's two states as two rows, and how the model's decoder moves (Defs: begin_transition,
   decode_init_done, decode_step_done, decode_done), for the bodies of boot_handoff_decode_projection and
   boot_handoff_decode_candidate. *)
Require Import VST.floyd.proofauto.
Require Import LeanosHandoff.handoff.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.InternalSpecs.
Require Import LeanosHandoff.proof.HdLemmas.
#[local] Existing Instance HandoffSpecs.CS.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* ---------- the rows ---------- *)

(* Row i of states, as states[i] evaluates. *)
Definition row (i: Z) (sp: val) : val := offset_val (328 * i) sp.

Lemma row_eval: forall sp i ti, isptr sp -> 0 <= i <= 1 -> (ti = tint \/ ti = tuint) ->
  eval_binop Oadd (tptr (tarray tulong 41)) ti sp (Vint (Int.repr i)) = row i sp.
Proof.
  intros. destruct H1; subst; unfold eval_binop; simpl.
  all: rewrite sem_add_pi_ptr_special; [ reflexivity | reflexivity | auto | rep_lia ].
Qed.

Lemma states_rows: forall sh (r0 r1: list Z) sp,
  field_compatible t_states [] sp ->
  data_at sh t_states (states_val [r0; r1]) sp =
  sepcon (data_at sh t_state (map vl r0) (row 0 sp)) (data_at sh t_state (map vl r1) (row 1 sp)).
Proof.
  intros. unfold t_states, states_val. cbn [map].
  change [map vl r0; map vl r1] with ([map vl r0] ++ [map vl r1]).
  rewrite split2_data_at_Tarray_app with (mid := 1) by reflexivity.
  change (2 - 1) with 1.
  rewrite (data_at_singleton_array_eq sh t_state (map vl r0)) by reflexivity.
  rewrite (data_at_singleton_array_eq sh t_state (map vl r1)) by reflexivity.
  rewrite field_address0_offset by auto with field_compatible.
  unfold row. replace (328 * 0) with 0 by reflexivity. rewrite isptr_offset_val_zero by auto.
  reflexivity.
Qed.

Lemma states_two: forall (ss: list (list Z)), Zlength ss = 2 -> ss = [Znth 0 ss; Znth 1 ss].
Proof.
  intros [ | r0 [ | r1 [ | r2 l ] ] ] L; try (rewrite ?Zlength_nil, ?Zlength_cons, ?Zlength_nil in L; rep_lia).
  reflexivity.
Qed.

(* Split states into the row at, the current one, and the other. *)
Lemma states_split: forall sh (ss: list (list Z)) i sp,
  Zlength ss = 2 -> (i = 0 \/ i = 1) -> field_compatible t_states [] sp ->
  data_at sh t_states (states_val ss) sp =
  sepcon (data_at sh t_state (map vl (Znth i ss)) (row i sp))
         (data_at sh t_state (map vl (Znth (1 - i) ss)) (row (1 - i) sp)).
Proof.
  intros. rewrite (states_two ss H) at 1. rewrite states_rows by auto.
  destruct H0; subst i; cbn; [ reflexivity | apply sepcon_comm ].
Qed.

Lemma Znth_upd_other: forall {A} {d: Inhabitant A} (ss: list A) i v,
  Zlength ss = 2 -> (i = 0 \/ i = 1) -> Znth i (upd_Znth (1 - i) ss v) = Znth i ss.
Proof. intros. rewrite upd_Znth_diff by lia. reflexivity. Qed.

Lemma Znth_upd_this: forall {A} {d: Inhabitant A} (ss: list A) i v,
  Zlength ss = 2 -> (i = 0 \/ i = 1) -> Znth (1 - i) (upd_Znth (1 - i) ss v) = v.
Proof. intros. rewrite upd_Znth_same by lia. reflexivity. Qed.

(* After the transition into row 1 - i: the rows as the new states hold them, the current one 1 - i. *)
Lemma states_join: forall sh (ss: list (list Z)) i a sp,
  Zlength ss = 2 -> (i = 0 \/ i = 1) -> field_compatible t_states [] sp ->
  sepcon (data_at sh t_state (map vl (Znth i ss)) (row i sp)) (data_at sh t_state (map vl a) (row (1 - i) sp)) =
  data_at sh t_states (states_val (upd_Znth (1 - i) ss a)) sp.
Proof.
  intros. rewrite (states_split sh (upd_Znth (1 - i) ss a) (1 - i) sp)
    by first [ rewrite upd_Znth_Zlength by lia; lia | lia | auto ].
  replace (1 - (1 - i)) with i by lia.
  rewrite Znth_upd_this, Znth_upd_other by auto. apply sepcon_comm.
Qed.

Lemma states_put0: forall sh (ss: list (list Z)) a sp,
  Zlength ss = 2 -> field_compatible t_states [] sp ->
  sepcon (data_at sh t_state (map vl a) (row 0 sp)) (data_at sh t_state (map vl (Znth 1 ss)) (row 1 sp)) |--
  data_at sh t_states (states_val (upd_Znth 0 ss a)) sp.
Proof.
  intros. pose proof (states_join sh ss 1 a sp H ltac:(lia) H0) as J. change (1 - 1) with 0 in J.
  rewrite <- J, sepcon_comm. apply derives_refl.
Qed.

Lemma states_put: forall sh (ss: list (list Z)) i a sp,
  Zlength ss = 2 -> (i = 0 \/ i = 1) -> field_compatible t_states [] sp ->
  sepcon (data_at sh t_state (map vl (Znth i ss)) (row i sp)) (data_at sh t_state (map vl a) (row (1 - i) sp)) |--
  data_at sh t_states (states_val (upd_Znth (1 - i) ss a)) sp.
Proof. intros. rewrite (states_join sh ss i a sp) by auto. apply derives_refl. Qed.

(* The states as they stay well formed. *)
Definition states_ok (ss: list (list Z)) : Prop := Zlength ss = 2 /\ Forall (fun s => Zlength s = WORDS) ss.

Lemma states_ok_upd: forall ss i a, states_ok ss -> 0 <= i < 2 -> Zlength a = WORDS -> states_ok (upd_Znth i ss a).
Proof.
  intros ss i a [L F] I La. split; [ rewrite upd_Znth_Zlength; lia | ].
  apply Forall_upd_Znth; auto.
Qed.

Lemma states_ok_row: forall ss i, states_ok ss -> 0 <= i < 2 -> Zlength (Znth i ss) = WORDS.
Proof. intros ss i [L F] I. apply (proj1 (Forall_Znth ss _) F i). lia. Qed.

(* A word of the current row, as states[i][j] loads it. *)
Lemma Znth_states_val: forall (d1: Inhabitant (list val)) (d2: Inhabitant val) ss i j,
  states_ok ss -> 0 <= i < 2 -> 0 <= j < WORDS ->
  @Znth val d2 j (@Znth (list val) d1 i (states_val ss)) = vl (Znth j (Znth i ss)).
Proof.
  intros. unfold states_val. destruct H as [L F].
  rewrite Znth_map by lia. rewrite Znth_map; auto.
  rewrite (proj1 (Forall_Znth ss _) F i) by lia. lia.
Qed.

(* ---------- the decoder in the model ---------- *)

Lemma begin_transition_go (x: inputs) (k: Z) (m: mem) :
  8 * k < m_total m -> begin_transition x k m = Go (ExpectDecodeStep k nil) m.
Proof. intros. unfold begin_transition. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.

Lemma begin_transition_end (x: inputs) (k: Z) (m: mem) :
  m_total m <= 8 * k -> begin_transition x k m = decode_done x m.
Proof. intros. unfold begin_transition. rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity. Qed.

Lemma decode_init_fail (x: inputs) (a: list Z) (m: mem) (st: Z) :
  decode_init_check x (m_total m) a = st -> st <> S_OK ->
  decode_init_done x a m = Return st (with_states m (upd_Znth 0 (m_states m) a) 0).
Proof.
  intros C N. unfold decode_init_done. cbn [m_total with_states]. rewrite C.
  destruct (Z.eqb_spec st S_OK); [ contradiction | reflexivity ].
Qed.

Lemma decode_init_ok (x: inputs) (a: list Z) (m: mem) :
  decode_init_check x (m_total m) a = S_OK ->
  decode_init_done x a m = begin_transition x 0 (with_states m (upd_Znth 0 (m_states m) a) 0).
Proof. intros C. unfold decode_init_done. cbn [m_total with_states]. rewrite C. reflexivity. Qed.

Lemma step_stop (x: inputs) (k: Z) (a: list Z) (m: mem) :
  Znth 2 a <> 0 ->
  decode_step_done x k a m = decode_done x (with_states m (upd_Znth (1 - m_at m) (m_states m) a) (1 - m_at m)).
Proof. intros. unfold decode_step_done. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.

Lemma step_next (x: inputs) (k: Z) (a: list Z) (m: mem) :
  Znth 2 a = 0 -> projection x && (Znth 19 a =? 1) = false ->
  decode_step_done x k a m = begin_transition x (k + 1) (with_states m (upd_Znth (1 - m_at m) (m_states m) a) (1 - m_at m)).
Proof. intros. unfold decode_step_done. rewrite (proj2 (Z.eqb_eq _ _) H), H0. reflexivity. Qed.

Lemma step_event (x: inputs) (k: Z) (a: list Z) (m: mem) :
  Znth 2 a = 0 -> projection x = true -> Znth 19 a = 1 ->
  decode_step_done x k a m =
  (let m' := with_states m (upd_Znth (1 - m_at m) (m_states m) a) (1 - m_at m) in
   if event_check a =? S_OK then Go (ExpectRecord k) m' else Return (event_check a) m').
Proof.
  intros. unfold decode_step_done. rewrite (proj2 (Z.eqb_eq _ _) H), H0, (proj2 (Z.eqb_eq _ _) H1).
  reflexivity.
Qed.

(* ---------- offsets ---------- *)

Lemma chunk_index: forall k T, 0 <= k -> 8 * k < T -> T mod 8 = 0 -> k < T / 8.
Proof.
  intros. pose proof (next8 k T H0 H1). pose proof (Z.div_mod T 8 ltac:(lia)) as D. rewrite H1 in D.
  set (q := T / 8) in *. lia.
Qed.

Lemma div8: forall k, 8 * k / 8 = k.
Proof. intros. rewrite Z.mul_comm, Z_div_mult by lia. reflexivity. Qed.

(* Load a word states[i][j] of the current states, and give it as a word of the model. *)
Ltac sload :=
  forward;
  [ first [ entailer!; rewrite Znth_states_val by (auto; lia); unfold vl; simpl; auto | idtac ] .. ];
  rewrite ?Znth_states_val by (auto; lia).

Lemma out_current_fail: forall x st m, st <> S_OK -> out_current_record x st m = i_current_record x.
Proof.
  intros. unfold out_current_record. destruct (Z.eqb_spec st S_OK); [ contradiction | ].
  rewrite andb_false_r. reflexivity.
Qed.

Lemma out_current_ok: forall x m, i_call x <> FCopy -> out_current_record x S_OK m = m_at m.
Proof. intros. unfold out_current_record, is_copy. destruct (i_call x); try reflexivity. contradiction. Qed.

Lemma decode_done_alone: forall x m, projection x = false ->
  decode_done x m = Return (authority_check x (m_total m) (current m)) m.
Proof. intros. unfold decode_done. rewrite H. reflexivity. Qed.

Lemma vi_sub1: forall i, (i = 0 \/ i = 1) -> Vint (Int.sub (Int.repr 1) (Int.repr i)) = vi (1 - i).
Proof. intros. unfold vi. rewrite sub32 by rep_lia. reflexivity. Qed.

Lemma row_eval_sub: forall sp i, isptr sp -> (i = 0 \/ i = 1) ->
  eval_binop Oadd (tptr (tarray tulong 41)) tuint sp (Vint (Int.sub (Int.repr 1) (Int.repr i))) = row (1 - i) sp.
Proof. intros. rewrite sub32 by rep_lia. apply row_eval; auto; lia. Qed.

(* ---------- the decoder with a projection ---------- *)

Lemma target_projection: forall x, projection x = true -> target x = 0.
Proof. intros x P. unfold projection, target in *. destruct (i_call x); try discriminate; reflexivity. Qed.

Lemma mem_ok_with: forall m u b r ss i,
  Zlength u = BLOCKS -> Zlength b = BLOCKS -> Zlength r = BLOCKS -> states_ok ss -> (i = 0 \/ i = 1) ->
  mem_ok (with_states (with_bitmaps m u b r) ss i).
Proof. intros m u b r ss i U B R [L F] I. unfold mem_ok; cbn. repeat split; auto. Qed.

Lemma mem_ok_states: forall m, mem_ok m -> states_ok (m_states m).
Proof. intros m (_ & _ & _ & L & F & _). split; auto. Qed.

(* An array of words as the C overwrites it from the front, word w at a time. *)
Lemma prefix_step: forall (pre u: list Z) w v n,
  Zlength pre = w -> Zlength u = n -> 0 <= w < n ->
  upd_Znth w (map vl (pre ++ sublist w n u)) (vl v) = map vl ((pre ++ [v]) ++ sublist (w + 1) n u).
Proof.
  intros. rewrite upd_Znth_map. f_equal.
  rewrite upd_Znth_app2 by (rewrite Zlength_sublist by lia; lia).
  rewrite H, Z.sub_diag.
  rewrite (sublist_split w (w + 1) n u) by lia. rewrite sublist_len_1 by lia. cbn [app].
  rewrite upd_Znth0. rewrite <- app_assoc. reflexivity.
Qed.

Lemma zeros_snoc: forall b, 0 <= b -> Zrepeat 0 b ++ [0] = Zrepeat 0 (b + 1).
Proof. intros. rewrite <- Zrepeat_app by lia. reflexivity. Qed.

Lemma prefix_start: forall (u: list Z) n, Zlength u = n -> map vl (Zrepeat 0 0 ++ sublist 0 n u) = map vl u.
Proof. intros. cbn [Zrepeat repeat Z.to_nat app]. rewrite sublist_same by lia. reflexivity. Qed.

Lemma prefix_end: map vl (Zrepeat 0 BLOCKS ++ sublist BLOCKS BLOCKS (@nil Z)) = map vl zeros.
Proof. reflexivity. Qed.

Lemma prefix_end': forall (u: list Z), map vl (Zrepeat 0 BLOCKS ++ sublist BLOCKS BLOCKS u) = map vl zeros.
Proof. intros. rewrite sublist_nil, app_nil_r. reflexivity. Qed.

Lemma decode_done_proj: forall x m, projection x = true ->
  decode_done x m =
  projection_end x (if Znth 2 (current m) =? 0 then incomplete_check (m_total m) (current m) else S_OK) m.
Proof. intros. unfold decode_done. rewrite H. reflexivity. Qed.

Lemma row_add: forall sp i si, isptr sp -> 0 <= i <= 1 ->
  force_val (sem_add_ptr_int (tarray tulong 41) si sp (Vint (Int.repr i))) = row i sp.
Proof.
  intros. rewrite sem_add_pi_ptr_special; [ reflexivity | reflexivity | auto | destruct si; rep_lia ].
Qed.

Lemma Zlength_zeros: Zlength zeros = BLOCKS.
Proof. reflexivity. Qed.

Lemma prefix_step0: forall (pre u: list Z) w n,
  Zlength pre = w -> Zlength u = n -> 0 <= w < n ->
  upd_Znth w (map vl (pre ++ sublist w n u)) (Vlong (Int64.repr 0)) = map vl ((pre ++ [0]) ++ sublist (w + 1) n u).
Proof. intros. apply (prefix_step pre u w 0 n); auto. Qed.

Lemma row_add_vi: forall sp i si, isptr sp -> 0 <= i <= 1 ->
  force_val (sem_add_ptr_int (tarray tulong 41) si sp (vi i)) = row i sp.
Proof. intros. apply row_add; auto. Qed.

Lemma if_fail: forall {A} st (a b: A), st <> S_OK -> (if st =? S_OK then a else b) = b.
Proof. intros. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.

(* A block projection's four answers. *)
Lemma entry_next: forall x p H k bk a M v,
  run x p H = Some (Go (ExpectEntry k bk a) M) -> Zlength a < 3 ->
  run x p (H ++ [(expected x (ExpectEntry k bk a) M, v)]) = Some (Go (ExpectEntry k bk (a ++ [v])) M).
Proof.
  intros. rewrite (run_snoc _ _ _ _ _ v H0). cbn [step].
  rewrite Zlength_app, Zlength_cons, Zlength_nil, (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma entry_last: forall x p H k bk a M v,
  run x p H = Some (Go (ExpectEntry k bk a) M) -> Zlength a = 3 ->
  run x p (H ++ [(expected x (ExpectEntry k bk a) M, v)]) = Some (entry_done x k bk (a ++ [v]) M).
Proof.
  intros. rewrite (run_snoc _ _ _ _ _ v H0). cbn [step].
  rewrite Zlength_app, Zlength_cons, Zlength_nil, (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
Qed.

Lemma entry_expected: forall x k bk a M s,
  current M = s ->
  expected x (ExpectEntry k bk a) M =
  Entry (Znth 20 s) (Znth 21 s) (Znth 22 s) bk (Znth bk (m_usable M)) (Znth bk (m_blocked M)) (Zlength a + 1).
Proof. intros. subst. reflexivity. Qed.

Lemma entry_done_fail: forall x k bk v1 v2 v3 v4 M st,
  entry_check [v1; v2; v3; v4] = st -> st <> S_OK -> entry_done x k bk [v1; v2; v3; v4] M = Return st M.
Proof. intros. unfold entry_done. rewrite H. destruct (Z.eqb_spec st S_OK); [ contradiction | reflexivity ]. Qed.

Lemma entry_done_ok: forall x k bk v1 v2 v3 v4 M,
  entry_check [v1; v2; v3; v4] = S_OK ->
  entry_done x k bk [v1; v2; v3; v4] M =
  (if bk + 1 <? BLOCKS
   then Go (ExpectEntry k (bk + 1) [])
          (with_bitmaps M (upd_Znth bk (m_usable M) v3) (upd_Znth bk (m_blocked M) v4) (m_reserved M))
   else begin_transition x (k + 1)
          (with_bitmaps M (upd_Znth bk (m_usable M) v3) (upd_Znth bk (m_blocked M) v4) (m_reserved M))).
Proof. intros. unfold entry_done. rewrite H. reflexivity. Qed.

Lemma entry_check4: forall v1 v2 v3 v4,
  entry_check [v1; v2; v3; v4] =
  (if negb (v1 =? 1) then S_PROJECTION_ENTRY_STATUS else if negb (v2 =? 0) then S_PROJECTION_ENTRY_ERROR else S_OK).
Proof. reflexivity. Qed.

Lemma entry_call: forall x H k bk a M s,
  run x (start x) H = Some (Go (ExpectEntry k bk a) M) -> current M = s ->
  next_call x H =
  Some (Entry (Znth 20 s) (Znth 21 s) (Znth 22 s) bk (Znth bk (m_usable M)) (Znth bk (m_blocked M)) (Zlength a + 1)).
Proof. intros. rewrite (next_call_go _ _ _ _ H0). subst s. reflexivity. Qed.

Lemma entry_step: forall x H k bk a M s v,
  run x (start x) H = Some (Go (ExpectEntry k bk a) M) -> current M = s -> Zlength a < 3 ->
  run x (start x)
    (H ++ [(Entry (Znth 20 s) (Znth 21 s) (Znth 22 s) bk (Znth bk (m_usable M)) (Znth bk (m_blocked M))
              (Zlength a + 1), v)]) = Some (Go (ExpectEntry k bk (a ++ [v])) M).
Proof. intros. subst s. apply entry_next; auto. Qed.

Lemma entry_fin: forall x H k bk a M s v,
  run x (start x) H = Some (Go (ExpectEntry k bk a) M) -> current M = s -> Zlength a = 3 ->
  run x (start x)
    (H ++ [(Entry (Znth 20 s) (Znth 21 s) (Znth 22 s) bk (Znth bk (m_usable M)) (Znth bk (m_blocked M))
              (Zlength a + 1), v)]) = Some (entry_done x k bk (a ++ [v]) M).
Proof. intros. subst s. apply entry_last; auto. Qed.

Lemma row_binop: forall sp i, isptr sp -> (i = 0 \/ i = 1) ->
  force_val (sem_binary_operation' Oadd (tptr (tarray tulong 41)) tuint sp (vi i)) = row i sp.
Proof. intros. apply (row_eval sp i tuint); auto; lia. Qed.

Lemma upd_vl: forall i (l: list Z) v, upd_Znth i (map vl l) (Vlong (Int64.repr v)) = map vl (upd_Znth i l v).
Proof. intros. apply (upd_Znth_map vl). Qed.
