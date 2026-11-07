(* Law admission_exact: the oracle's invariant J against the model's run, one answer at a time: what a call of each
   export implies of the law's record (its checks), and the record after each export's update. *)
Require Import VST.floyd.proofauto.
Require Import LeanosMadtAdmission.proof.Defs.
Require Import LeanosMadtAdmission.proof.MgaSpecs.
Require Import LeanosMadtAdmission.proof.LawProg LeanosMadtAdmission.proof.LawDefs.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* ---------------------------------------------------------------------- *)
(* The run                                                                 *)
(* ---------------------------------------------------------------------- *)

Lemma J_snoc: forall x h g v s, run x (start x) h = Some (Go g) ->
  J x (h ++ [(expected x g, v)]) s = Jp x (step x g v) s.
Proof. intros x h g v s R. unfold J. rewrite (run_snoc x (start x) h g v R). reflexivity. Qed.

Lemma J_nil: forall x s, J x nil s = Jp x (start x) s.
Proof. reflexivity. Qed.

Lemma next_go: forall x h c, next_call x h = Some c ->
  exists g, run x (start x) h = Some (Go g) /\ c = expected x g.
Proof.
  unfold next_call. intros x h c E. destruct (run x (start x) h) as [[g | o] | ]; inversion E; eauto.
Qed.

Lemma J_go: forall x h g s, run x (start x) h = Some (Go g) -> J x h s -> go_inv x g s.
Proof. unfold J. intros x h g s R K. rewrite R in K. exact K. Qed.

Lemma J_returns: forall x h o s, returns x h = Some o -> J x h s -> ret_inv o s.
Proof.
  unfold returns, J. intros x h o s R K. destruct (run x (start x) h) as [[g | o'] | ]; inversion R; subst; auto.
Qed.

(* ---------------------------------------------------------------------- *)
(* The calls                                                               *)
(* ---------------------------------------------------------------------- *)

Lemma envelope_call: forall x h s st len off byte term word,
  next_call x h = Some (EnvelopeStep st len off byte term word) -> J x h s ->
  exists cur, run x (start x) h = Some (Go (ExpectEnvelope off st cur)) /\
    go_inv x (ExpectEnvelope off st cur) s /\
    len = i_length x /\ byte = Znth off (i_bytes x) /\ term = terminal x off /\ word = Zlength cur.
Proof.
  intros x h s st len off byte term word N K. destruct (next_go _ _ _ N) as [g [R E]].
  pose proof (J_go _ _ _ _ R K) as G.
  destruct g as [i st' cur | k st' cur | args cur]; simpl in E; inversion E; subst.
  exists cur. auto 7.
Qed.

Lemma entry_call: forall x h s st len ex off byte word,
  next_call x h = Some (EntryStep st len ex off byte word) -> J x h s ->
  exists cur, run x (start x) h = Some (Go (ExpectEntries off st cur)) /\
    go_inv x (ExpectEntries off st cur) s /\
    len = i_length x /\ ex = i_executing x /\ byte = Znth off (i_bytes x) /\ word = Zlength cur.
Proof.
  intros x h s st len ex off byte word N K. destruct (next_go _ _ _ N) as [g [R E]].
  pose proof (J_go _ _ _ _ R K) as G.
  destruct g as [i st' cur | k st' cur | args cur]; simpl in E; inversion E; subst.
  exists cur. auto 7.
Qed.

Lemma result_call: forall x h s args word,
  next_call x h = Some (ResultQuery args word) -> J x h s ->
  exists cur, run x (start x) h = Some (Go (ExpectResult args cur)) /\
    go_inv x (ExpectResult args cur) s /\ word = Zlength cur.
Proof.
  intros x h s args word N K. destruct (next_go _ _ _ N) as [g [R E]].
  pose proof (J_go _ _ _ _ R K) as G.
  destruct g as [i st' cur | k st' cur | args' cur]; simpl in E; inversion E; subst.
  exists cur. auto.
Qed.

(* ---------------------------------------------------------------------- *)
(* The record's updates                                                    *)
(* ---------------------------------------------------------------------- *)

(* The answer of the current word recorded (every export's first update). *)
Definition s_store (s: lst) (v: Z) : lst :=
  mk_lst (ls_args s) (ls_expect s) (ls_verdict s) (ls_at s) (ls_word s) (ls_state s)
         (upd_Znth (ls_word s) (ls_answer s) v) (ls_id s).
(* ... and the word advanced. *)
Definition s_more (s: lst) (v: Z) : lst :=
  mk_lst (ls_args s) (ls_expect s) (ls_verdict s) (ls_at s) (ls_word s + 1) (ls_state s)
         (upd_Znth (ls_word s) (ls_answer s) v) (ls_id s).
(* stop(m, r). *)
Definition s_stop (s: lst) (r: Z) : lst :=
  mk_lst (ls_args s) E_NOTHING r (ls_at s) (ls_word s) (ls_state s) (ls_answer s) (ls_id s).
(* The envelope's transition accepted: the next byte, with words 3, 4, 5 of the answers. *)
Definition s_env_acc (s: lst) : lst :=
  mk_lst (ls_args s) (ls_expect s) (ls_verdict s) (ls_at s + 1) 0
         (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 (ls_state s) (Znth 3 (ls_answer s))) (Znth 4 (ls_answer s)))
            (Znth 5 (ls_answer s)))
         (ls_answer s) (ls_id s).
(* The entry stream's transition accepted: the next offset, with words 3..14 of the answers. *)
Definition s_ent_acc (s: lst) : lst :=
  mk_lst (ls_args s) (ls_expect s) (ls_verdict s) (ls_at s + 1) 0 (sublist 3 15 (ls_answer s)) (ls_answer s)
         (ls_id s).

Lemma Forall_upd: forall (P: Z -> Prop) l i x, Forall P l -> P x -> Forall P (upd_Znth i l x).
Proof.
  intros P l i x F Px. destruct (zlt i 0); [ rewrite upd_Znth_out_of_range by lia; auto | ].
  destruct (zlt i (Zlength l)); [ | rewrite upd_Znth_out_of_range by lia; auto ].
  apply Forall_Znth. intros j Hj. rewrite upd_Znth_Zlength in Hj by lia.
  destruct (Z.eq_dec j i) as [-> | N]; [ rewrite upd_Znth_same by lia; auto | ].
  rewrite upd_Znth_diff by lia. apply Forall_Znth; auto.
Qed.

Lemma Forall_u64_upd: forall l i v, Forall u64_ok l -> u64_ok v -> Forall u64_ok (upd_Znth i l v).
Proof. intros. apply Forall_upd; auto. Qed.

Lemma Forall_u64_sublist: forall l a b, Forall u64_ok l -> Forall u64_ok (sublist a b l).
Proof. intros. apply Forall_sublist. auto. Qed.

Ltac split_and := repeat match goal with |- _ /\ _ => split end.

Lemma lst_ok_store: forall s v, lst_ok s -> u64_ok v -> lst_ok (s_store s v).
Proof.
  intros s v (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11) V. unfold s_store, lst_ok; lst_cbn.
  split_and; auto; [ | apply Forall_u64_upd; auto ].
  destruct (zlt (ls_word s) 0); [ rewrite upd_Znth_out_of_range by lia; auto | ].
  destruct (zlt (ls_word s) 16); [ rewrite upd_Znth_Zlength by lia; auto | rewrite upd_Znth_out_of_range by lia; auto ].
Qed.

Lemma lst_ok_more: forall s v, lst_ok s -> u64_ok v -> 0 <= ls_word s < 16 -> lst_ok (s_more s v).
Proof.
  intros s v (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11) V W. unfold s_more, lst_ok; lst_cbn.
  split_and; auto; [ unfold u64_ok in *; rep_lia | rewrite upd_Znth_Zlength by lia; auto | apply Forall_u64_upd; auto ].
Qed.

Lemma lst_ok_stop: forall s r, lst_ok s -> u32_ok r -> lst_ok (s_stop s r).
Proof.
  intros s r (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11) V. unfold s_stop, lst_ok; lst_cbn.
  split_and; auto. unfold u32_ok, E_NOTHING; rep_lia.
Qed.

Lemma lst_ok_env_acc: forall s, lst_ok s -> 0 <= ls_at s < Int.max_unsigned -> lst_ok (s_env_acc s).
Proof.
  intros s (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11) I. unfold s_env_acc, lst_ok; lst_cbn.
  assert (F: forall k, 0 <= k < 16 -> u64_ok (Znth k (ls_answer s))) by (intros; apply Forall_Znth; auto; lia).
  split_and; auto; try (unfold u64_ok; rep_lia); try (rewrite !upd_Znth_Zlength by list_solve; auto);
    repeat apply Forall_u64_upd; auto; apply F; lia.
Qed.

Lemma lst_ok_ent_acc: forall s, lst_ok s -> 0 <= ls_at s < Int.max_unsigned -> lst_ok (s_ent_acc s).
Proof.
  intros s (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11) I. unfold s_ent_acc, lst_ok; lst_cbn.
  split_and; auto; try (unfold u64_ok; rep_lia); [ rewrite Zlength_sublist by lia; lia | ].
  apply Forall_u64_sublist; auto.
Qed.

(* ---------------------------------------------------------------------- *)
(* The model's steps                                                       *)
(* ---------------------------------------------------------------------- *)

(* The answers of a transition so far and the next one, as the record holds them. *)
Lemma cur_snoc: forall s v, lst_ok s -> 0 <= ls_word s < 16 ->
  sublist 0 (ls_word s) (ls_answer s) ++ [v] = sublist 0 (ls_word s + 1) (upd_Znth (ls_word s) (ls_answer s) v).
Proof. intros s v (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11) W. list_solve. Qed.

Lemma go_env_more: forall x i st cur s v, lst_ok s -> go_inv x (ExpectEnvelope i st cur) s -> ls_word s < 6 ->
  go_inv x (ExpectEnvelope i st (cur ++ [v])) (s_more s v).
Proof.
  intros x i st cur s v Ok (E & I & S & C & W & A & R) L. unfold go_inv, s_more; lst_cbn. subst.
  split_and; auto; try lia. apply cur_snoc; auto; lia.
Qed.

Lemma go_ent_more: forall x k st cur s v, lst_ok s -> go_inv x (ExpectEntries k st cur) s -> ls_word s < 15 ->
  go_inv x (ExpectEntries k st (cur ++ [v])) (s_more s v).
Proof.
  intros x k st cur s v Ok (E & I & S & C & W & A & R) L. unfold go_inv, s_more; lst_cbn. subst.
  split_and; auto; try lia. apply cur_snoc; auto; lia.
Qed.

Lemma go_res_more: forall x args cur s v, lst_ok s -> go_inv x (ExpectResult args cur) s -> ls_word s < 3 ->
  go_inv x (ExpectResult args (cur ++ [v])) (s_more s v).
Proof.
  intros x args cur s v Ok (E & A & C & W) L. unfold go_inv, s_more; lst_cbn. subst.
  split_and; auto; try lia. apply cur_snoc; auto; lia.
Qed.

(* A transition's answers with the last one recorded. *)
Lemma cur_last: forall s v n, lst_ok s -> ls_word s = n - 1 -> 0 < n <= 16 ->
  sublist 0 (ls_word s) (ls_answer s) ++ [v] = sublist 0 n (upd_Znth (n - 1) (ls_answer s) v).
Proof. intros s v n (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11) W N. subst. list_solve. Qed.

Lemma Znth_sublist0: forall (l: list Z) n k, 0 <= k < n -> n <= Zlength l -> Znth k (sublist 0 n l) = Znth k l.
Proof. intros. rewrite Znth_sublist by lia. f_equal. lia. Qed.

(* ---------------------------------------------------------------------- *)
(* The helpers' progress                                                   *)
(* ---------------------------------------------------------------------- *)

Lemma begin_entries_bounds: forall x, ((i_length x <=? 44) || (255 <? i_executing x)) = true ->
  begin_entries x = Return (S_ENTRIES_BOUNDS, None).
Proof. intros x E. unfold begin_entries. rewrite E. reflexivity. Qed.

Lemma begin_entries_go: forall x, ((i_length x <=? 44) || (255 <? i_executing x)) = false ->
  begin_entries x = Go (ExpectEntries 44 initial_entries nil).
Proof.
  intros x E. unfold begin_entries. rewrite E. unfold entries_from.
  apply orb_false_iff in E as [E _]. apply Z.leb_gt in E.
  destruct (Z.eqb_spec 44 (i_length x)); [ lia | reflexivity ].
Qed.

Lemma lst_ok_entries0: forall s, lst_ok s ->
  lst_ok (mk_lst (ls_args s) E_ENTRIES (ls_verdict s) 44 0 initial_entries (ls_answer s) (ls_id s)).
Proof.
  intros s (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11). unfold lst_ok; lst_cbn.
  split_and; auto; try (unfold u32_ok, u64_ok, E_ENTRIES; rep_lia).
  repeat constructor; unfold u64_ok; rep_lia.
Qed.

Lemma go_entries0: forall x s, ls_args s = i_args x -> 44 < i_length x ->
  go_inv x (ExpectEntries 44 initial_entries nil)
    (mk_lst (ls_args s) E_ENTRIES (ls_verdict s) 44 0 initial_entries (ls_answer s) (ls_id s)).
Proof. intros x s A L. unfold go_inv; lst_cbn. split_and; auto; try lia. Qed.

Lemma envelope_done_length: forall x st, Zlength st = 12 -> Znth 1 st <> i_length x ->
  envelope_done x (sublist 0 3 st) = Return (S_ENVELOPE_LENGTH, None).
Proof.
  intros x st L N. unfold envelope_done, envelope_final, envelope_end. rewrite !Znth_sublist0 by lia.
  destruct (Z.eqb_spec (Znth 1 st) (i_length x)); [ contradiction | reflexivity ].
Qed.

Lemma envelope_done_checksum: forall x st, Zlength st = 12 -> Znth 1 st = i_length x -> Znth 2 st <> 0 ->
  envelope_done x (sublist 0 3 st) = Return (S_ENVELOPE_CHECKSUM, None).
Proof.
  intros x st L E N. unfold envelope_done, envelope_final, envelope_end. rewrite !Znth_sublist0 by lia.
  rewrite E, Z.eqb_refl. destruct (Z.eqb_spec (Znth 2 st) 0); [ contradiction | reflexivity ].
Qed.

Lemma envelope_done_ok: forall x st, Zlength st = 12 -> Znth 1 st = i_length x -> Znth 2 st = 0 ->
  envelope_done x (sublist 0 3 st) =
  match i_call x with FEnvelope => Return (S_OK, None) | _ => begin_entries x end.
Proof.
  intros x st L E N. unfold envelope_done, envelope_final, envelope_end. rewrite !Znth_sublist0 by lia.
  rewrite E, N, !Z.eqb_refl. reflexivity.
Qed.

(* entries_done's tests, in the model's form. *)
Definition rec_clean (st: list Z) : bool :=
  (Znth 1 st =? 0) && (Znth 2 st =? 0) && (Znth 3 st =? 0) && (Znth 4 st =? 0) && (Znth 5 st =? 0).
Definition none_seen (st: list Z) : bool :=
  (Znth 8 st =? 0) && (Znth 9 st =? 0) && (Znth 10 st =? 0) && (Znth 11 st =? 0).

Lemma entries_done_record: forall x st, rec_clean st = false ->
  entries_done x st = Return (S_ENTRIES_RECORD, None).
Proof. intros x st R. unfold entries_done, entries_final, entries_end. unfold rec_clean in R. rewrite R. reflexivity. Qed.

Lemma entries_done_enabled: forall x st, rec_clean st = true -> Znth 6 st <> 1 ->
  entries_done x st = Return (S_ENTRIES_ENABLED, None).
Proof.
  intros x st R N. unfold entries_done, entries_final, entries_end. unfold rec_clean in R. rewrite R.
  destruct (Z.eqb_spec (Znth 6 st) 1); [ contradiction | reflexivity ].
Qed.

Lemma entries_done_apic: forall x st, rec_clean st = true -> Znth 6 st = 1 -> Znth 7 st <> i_executing x ->
  entries_done x st = Return (S_ENTRIES_APIC_ID, None).
Proof.
  intros x st R E N. unfold entries_done, entries_final, entries_end. unfold rec_clean in R. rewrite R, E.
  simpl. destruct (Z.eqb_spec (Znth 7 st) (i_executing x)); [ contradiction | reflexivity ].
Qed.

Lemma entries_done_seen: forall x st, rec_clean st = true -> Znth 6 st = 1 -> Znth 7 st = i_executing x ->
  none_seen st = true -> entries_done x st = Return (S_ENTRIES_SEEN, None).
Proof.
  intros x st R E E7 N. unfold entries_done, entries_final, entries_end. unfold rec_clean in R. unfold none_seen in N.
  rewrite R, E, E7, N, !Z.eqb_refl. reflexivity.
Qed.

Lemma entries_done_ok: forall x st, rec_clean st = true -> Znth 6 st = 1 -> Znth 7 st = i_executing x ->
  none_seen st = false ->
  entries_done x st =
  match i_call x with
  | FEntries => Return (S_OK, Some (Znth 7 st))
  | _ => Go (ExpectResult (admission_args x (Znth 7 st)) nil)
  end.
Proof.
  intros x st R E E7 N. unfold entries_done, entries_final, entries_end. unfold rec_clean in R. unfold none_seen in N.
  rewrite R, E, E7, N, !Z.eqb_refl. reflexivity.
Qed.

(* entries_done in an admission: the result's arguments a0..a4, 1, 1, 0, s7 and the executing ID. *)
Definition result_args (a: list Z) (id ex: Z) : list Z :=
  upd_Znth 9 (upd_Znth 8 (upd_Znth 7 (upd_Znth 6 (upd_Znth 5 a 1) 1) 0) id) ex.

Lemma admission_args_result: forall x id, Zlength (i_args x) = 10 ->
  admission_args x id = result_args (i_args x) id (i_executing x).
Proof. intros x id L. unfold admission_args, result_args. list_solve. Qed.

Lemma lst_ok_result0: forall s id ex, lst_ok s -> u64_ok id -> u32_ok ex ->
  lst_ok (mk_lst (result_args (ls_args s) id ex) E_RESULT (ls_verdict s) (ls_at s) 0 (ls_state s) (ls_answer s)
            (ls_id s)).
Proof.
  intros s id ex (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11) I E. unfold lst_ok, result_args; lst_cbn.
  split_and; auto; try (unfold u32_ok, u64_ok, E_RESULT in *; rep_lia).
  - list_solve.
  - repeat apply Forall_upd; auto; unfold u32_ok, u64_ok in *; rep_lia.
Qed.

Lemma go_result0: forall x s id, ls_args s = i_args x -> Zlength (i_args x) = 10 ->
  go_inv x (ExpectResult (admission_args x id) nil)
    (mk_lst (result_args (ls_args s) id (i_executing x)) E_RESULT (ls_verdict s) (ls_at s) 0 (ls_state s)
       (ls_answer s) (ls_id s)).
Proof.
  intros x s id A L. unfold go_inv; lst_cbn. rewrite A, admission_args_result by auto. split_and; auto; lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* The exports' steps                                                      *)
(* ---------------------------------------------------------------------- *)

Lemma env_step_more: forall x i st cur v, Zlength cur < 6 ->
  step x (ExpectEnvelope i st cur) v = Go (ExpectEnvelope i st (cur ++ [v])).
Proof.
  intros x i st cur v L. simpl. unfold envelope_collect. rewrite Zlength_app, Zlength_cons, Zlength_nil.
  destruct (Z.ltb_spec (Zlength cur + Z.succ 0) 7); [ reflexivity | lia ].
Qed.

Lemma ent_step_more: forall x k st cur v, Zlength cur < 15 ->
  step x (ExpectEntries k st cur) v = Go (ExpectEntries k st (cur ++ [v])).
Proof.
  intros x k st cur v L. simpl. unfold entries_collect. rewrite Zlength_app, Zlength_cons, Zlength_nil.
  destruct (Z.ltb_spec (Zlength cur + Z.succ 0) 16); [ reflexivity | lia ].
Qed.

Lemma res_step_more: forall x args cur v, Zlength cur < 3 ->
  step x (ExpectResult args cur) v = Go (ExpectResult args (cur ++ [v])).
Proof.
  intros x args cur v L. simpl. unfold result_collect. rewrite Zlength_app, Zlength_cons, Zlength_nil.
  destruct (Z.ltb_spec (Zlength cur + Z.succ 0) 4); [ reflexivity | lia ].
Qed.

(* The envelope's transition with its seventh answer: its verdict on the answers a as the law holds them. *)
Lemma env_last: forall x s v a, lst_ok s -> ls_word s = 6 -> a = upd_Znth 6 (ls_answer s) v ->
  step x (ExpectEnvelope (ls_at s) (sublist 0 3 (ls_state s)) (sublist 0 (ls_word s) (ls_answer s))) v =
  if envelope_check x (ls_at s) a =? S_OK then envelope_from x (ls_at s + 1) [Znth 3 a; Znth 4 a; Znth 5 a]
  else Return (envelope_check x (ls_at s) a, None).
Proof.
  intros x s v a Ok W A. pose proof Ok as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
  assert (La: Zlength a = 16) by (subst a; rewrite upd_Znth_Zlength; lia).
  simpl step. rewrite (cur_last s v 7) by (auto; lia). change (7 - 1) with 6. rewrite <- A. unfold envelope_collect.
  rewrite Zlength_sublist by lia. simpl.
  assert (K: forall k, 0 <= k < 7 -> Znth k (sublist 0 7 a) = Znth k a) by (intros; apply Znth_sublist0; lia).
  unfold envelope_check. rewrite !K by lia. reflexivity.
Qed.

(* The entry stream's transition with its sixteenth answer. *)
Lemma ent_last: forall x s v a, lst_ok s -> ls_word s = 15 -> a = upd_Znth 15 (ls_answer s) v ->
  step x (ExpectEntries (ls_at s) (ls_state s) (sublist 0 (ls_word s) (ls_answer s))) v =
  if entries_check x (ls_at s) a =? S_OK then entries_from x (ls_at s + 1) (sublist 3 15 a)
  else Return (entries_check x (ls_at s) a, None).
Proof.
  intros x s v a Ok W A. pose proof Ok as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
  assert (La: Zlength a = 16) by (subst a; rewrite upd_Znth_Zlength; lia).
  simpl step. rewrite (cur_last s v 16) by (auto; lia). change (16 - 1) with 15. rewrite <- A. unfold entries_collect.
  rewrite Zlength_sublist by lia. simpl.
  rewrite sublist_same by lia. reflexivity.
Qed.

(* The result with its fourth answer. *)
Lemma res_last: forall x s v a args, lst_ok s -> ls_word s = 3 -> a = upd_Znth 3 (ls_answer s) v ->
  step x (ExpectResult args (sublist 0 (ls_word s) (ls_answer s))) v =
  result_end (result_check args a) (Znth 3 a).
Proof.
  intros x s v a args Ok W A. pose proof Ok as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
  assert (La: Zlength a = 16) by (subst a; rewrite upd_Znth_Zlength; lia).
  simpl step. rewrite (cur_last s v 4) by (auto; lia). change (4 - 1) with 3. rewrite <- A. unfold result_collect.
  rewrite Zlength_sublist by lia. simpl.
  assert (K: forall k, 0 <= k < 4 -> Znth k (sublist 0 4 a) = Znth k a) by (intros; apply Znth_sublist0; lia).
  unfold result_check. rewrite !K by lia. reflexivity.
Qed.

Lemma J_snoc_intro: forall x h g v s, run x (start x) h = Some (Go g) -> Jp x (step x g v) s ->
  J x (h ++ [(expected x g, v)]) s.
Proof. intros x h g v s R K. rewrite (J_snoc _ _ _ _ _ R). exact K. Qed.

(* The envelope's accepted transition: the record of the next byte. *)
Definition env_next (s: lst) (a: list Z) : lst :=
  mk_lst (ls_args s) (ls_expect s) (ls_verdict s) (ls_at s + 1) 0
    (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 (ls_state s) (Znth 3 a)) (Znth 4 a)) (Znth 5 a)) a (ls_id s).

Lemma lst_ok_env_next: forall s a, lst_ok s -> Zlength a = 16 -> Forall u64_ok a -> 0 <= ls_at s < Int.max_unsigned ->
  lst_ok (env_next s a).
Proof.
  intros s a (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11) La Fa I. unfold env_next, lst_ok; lst_cbn.
  assert (F: forall k, 0 <= k < 16 -> u64_ok (Znth k a)) by (intros; apply Forall_Znth; auto; lia).
  split_and; auto; try (unfold u64_ok; rep_lia); try (rewrite !upd_Znth_Zlength by list_solve; auto);
    repeat apply Forall_u64_upd; auto; apply F; lia.
Qed.

Lemma env_next_state: forall s a, lst_ok s ->
  sublist 0 3 (ls_state (env_next s a)) = [Znth 3 a; Znth 4 a; Znth 5 a].
Proof.
  intros s a (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11). unfold env_next; lst_cbn. list_solve.
Qed.

Lemma go_env_next: forall x s a, lst_ok s -> ls_expect s = E_ENVELOPE -> ls_args s = i_args x ->
  0 <= ls_at s -> ls_at s + 1 < i_length x ->
  go_inv x (ExpectEnvelope (ls_at s + 1) [Znth 3 a; Znth 4 a; Znth 5 a] nil) (env_next s a).
Proof.
  intros x s a Ok E A I L. unfold go_inv. rewrite <- (env_next_state s a Ok). unfold env_next; lst_cbn.
  split_and; auto; lia.
Qed.

(* The entry stream's accepted transition: the record of the next offset, with the state words 3..14 of a. *)
Definition ent_next (s: lst) (a: list Z) : lst :=
  mk_lst (ls_args s) (ls_expect s) (ls_verdict s) (ls_at s + 1) 0 (sublist 3 15 a) a (ls_id s).

Lemma lst_ok_ent_next: forall s a, lst_ok s -> Zlength a = 16 -> Forall u64_ok a -> 0 <= ls_at s < Int.max_unsigned ->
  lst_ok (ent_next s a).
Proof.
  intros s a (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11) La Fa I. unfold ent_next, lst_ok; lst_cbn.
  split_and; auto; try (unfold u64_ok; rep_lia); [ rewrite Zlength_sublist by lia; lia | ].
  apply Forall_u64_sublist; auto.
Qed.

Lemma go_ent_next: forall x s a, ls_expect s = E_ENTRIES -> ls_args s = i_args x ->
  0 <= ls_at s -> ls_at s + 1 < i_length x ->
  go_inv x (ExpectEntries (ls_at s + 1) (sublist 3 15 a) nil) (ent_next s a).
Proof. intros x s a E A I L. unfold go_inv, ent_next; lst_cbn. split_and; auto; lia. Qed.
