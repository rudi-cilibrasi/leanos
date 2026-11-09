(* Law handoff_decode_exact: the model's run as the law's callees see it: which stage each call comes from (its
   arguments as the model's), the record's updates and their ranges, and the model's memory under the updates. *)
Require Import VST.floyd.proofauto.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.LawProg LeanosHandoff.proof.LawDefs.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Ltac split_and := repeat match goal with |- _ /\ _ => split end.

(* ---------------------------------------------------------------------- *)
(* The run                                                                 *)
(* ---------------------------------------------------------------------- *)

Lemma next_go: forall x h p c, run x (start x) h = Some p -> next_call x h = Some c ->
  exists g m, p = Go g m /\ c = expected x g m.
Proof.
  intros x h p c R N. destruct (next_call_run x h c N) as (g & m & R' & E).
  rewrite R in R'. inversion R'; subst. eauto.
Qed.

Lemma run_snoc': forall x h g m c v, run x (start x) h = Some (Go g m) -> c = expected x g m ->
  run x (start x) (h ++ [(c, v)]) = Some (step x g m v).
Proof. intros. subst. apply run_snoc; auto. Qed.

(* ---------------------------------------------------------------------- *)
(* The calls                                                               *)
(* ---------------------------------------------------------------------- *)

Lemma call_read: forall x g m a, expected x g m = Read a ->
  (g = ExpectSize /\ a = i_address x) \/ (exists k st, g = ExpectChunk k st /\ a = i_address x + 8 * k).
Proof. intros x g m a E. destruct g; simpl in E; inversion E; subst; eauto. Qed.

Lemma call_stream_init: forall x g m mg ad t id q, expected x g m = StreamInit mg ad t id q ->
  exists a, g = ExpectStreamInit a /\ mg = i_magic x /\ ad = i_address x /\ t = m_total m /\ id = i_address x /\
    q = Zlength a.
Proof. intros. destruct g; simpl in H; inversion H; subst; eauto 7. Qed.

Lemma call_stream_step: forall x g m st id off cnt ch term q, expected x g m = StreamStep st id off cnt ch term q ->
  exists k c a, g = ExpectStreamStep k st c a /\ id = i_address x /\ off = 8 * k /\ cnt = 8 /\ ch = c /\
    term = terminal (m_total m) k /\ q = Zlength a.
Proof. intros. destruct g; simpl in H; inversion H; subst; eauto 10. Qed.

Lemma call_decode_init: forall x g m mg ad t tg q, expected x g m = DecodeInit mg ad t tg q ->
  exists a, g = ExpectDecodeInit a /\ mg = i_magic x /\ ad = i_address x /\ t = m_total m /\ tg = target x /\
    q = Zlength a.
Proof. intros. destruct g; simpl in H; inversion H; subst; eauto 7. Qed.

Lemma call_decode_step: forall x g m s id off ch term q, expected x g m = DecodeStep s id off ch term q ->
  exists k a, g = ExpectDecodeStep k a /\ s = current m /\ id = i_address x /\ off = 8 * k /\
    ch = Znth k (decoded x m) /\ term = terminal (m_total m) k /\ q = Zlength a.
Proof. intros. destruct g; simpl in H; inversion H; subst; eauto 10. Qed.

Lemma call_record: forall x g m slot base len kind, expected x g m = Record slot base len kind ->
  exists k, g = ExpectRecord k /\ slot = Znth 11 (current m) - 1 /\ base = Znth 20 (current m) /\
    len = Znth 21 (current m) /\ kind = Znth 22 (current m).
Proof. intros. destruct g; simpl in H; inversion H; subst; eauto 7. Qed.

Lemma call_entry: forall x g m bs ln kd blk us bl q, expected x g m = Entry bs ln kd blk us bl q ->
  exists k b a, g = ExpectEntry k b a /\ bs = Znth 20 (current m) /\ ln = Znth 21 (current m) /\
    kd = Znth 22 (current m) /\ blk = b /\ us = Znth b (m_usable m) /\ bl = Znth b (m_blocked m) /\
    q = Zlength a + 1.
Proof. intros. destruct g; simpl in H; inversion H; subst; eauto 12. Qed.

(* ---------------------------------------------------------------------- *)
(* Lists                                                                   *)
(* ---------------------------------------------------------------------- *)

Lemma Forall_upd: forall (P: Z -> Prop) l i x, Forall P l -> P x -> Forall P (upd_Znth i l x).
Proof.
  intros P l i x F Px. destruct (zlt i 0); [ rewrite upd_Znth_out_of_range by lia; auto | ].
  destruct (zlt i (Zlength l)); [ | rewrite upd_Znth_out_of_range by lia; auto ].
  apply Forall_Znth. intros j Hj. rewrite upd_Znth_Zlength in Hj by lia.
  destruct (Z.eq_dec j i) as [-> | N]; [ rewrite upd_Znth_same by lia; auto | ].
  rewrite upd_Znth_diff by lia. apply Forall_Znth; auto.
Qed.

Lemma Forall_u64_Znth: forall l i, Forall u64_ok l -> 0 <= i < Zlength l -> u64_ok (Znth i l).
Proof. intros l i F I. exact (proj1 (Forall_Znth _ _) F i I). Qed.

Lemma Forall_u64_sublist: forall l a b, Forall u64_ok l -> Forall u64_ok (sublist a b l).
Proof. intros. apply Forall_sublist. auto. Qed.

Lemma Forall_u64_zeros: Forall u64_ok zeros.
Proof. unfold zeros, Zrepeat. apply Forall_repeat. unfold u64_ok; rep_lia. Qed.

Lemma Zlength_zeros: Zlength zeros = BLOCKS.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* The record's updates                                                    *)
(* ---------------------------------------------------------------------- *)

Definition s_store (s: lst) (v: Z) : lst :=
  mk_lst (w_running s) (w_records s) (w_expect s) (w_verdict s) (w_chunk s) (w_word s) (w_block s) (w_value s)
         (w_stream s) (upd_Znth (w_word s) (w_answer s) v).
Definition s_more (s: lst) (v: Z) : lst :=
  mk_lst (w_running s) (w_records s) (w_expect s) (w_verdict s) (w_chunk s) (w_word s + 1) (w_block s) (w_value s)
         (w_stream s) (upd_Znth (w_word s) (w_answer s) v).
Definition s_stop (s: lst) (r: Z) : lst :=
  mk_lst (w_running s) (w_records s) E_NOTHING r (w_chunk s) (w_word s) (w_block s) (w_value s)
         (w_stream s) (w_answer s).
Definition s_stream (s: lst) (st: list Z) : lst :=
  mk_lst (w_running s) (w_records s) (w_expect s) (w_verdict s) (w_chunk s) (w_word s) (w_block s) (w_value s)
         st (w_answer s).

Lemma lst_ok_store: forall s v, lst_ok s -> u64_ok v -> lst_ok (s_store s v).
Proof.
  intros s v (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12) V. unfold s_store, lst_ok; lst_cbn.
  split_and; auto; [ | apply Forall_upd; auto ].
  destruct (zlt (w_word s) 0); [ rewrite upd_Znth_out_of_range by lia; auto | ].
  destruct (zlt (w_word s) WORDS); [ rewrite upd_Znth_Zlength by lia; auto | rewrite upd_Znth_out_of_range by lia; auto ].
Qed.

Lemma lst_ok_more: forall s v, lst_ok s -> u64_ok v -> 0 <= w_word s < WORDS -> lst_ok (s_more s v).
Proof.
  intros s v (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12) V W. unfold s_more, lst_ok; lst_cbn.
  split_and; auto; [ unfold u64_ok in *; rep_lia | rewrite upd_Znth_Zlength by lia; auto | apply Forall_upd; auto ].
Qed.

Lemma lst_ok_stop: forall s r, lst_ok s -> u32_ok r -> lst_ok (s_stop s r).
Proof.
  intros s r (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12) V. unfold s_stop, lst_ok; lst_cbn.
  split_and; auto. unfold u32_ok, E_NOTHING; rep_lia.
Qed.

Lemma lst_ok_stream: forall s st, lst_ok s -> Zlength st = 7 -> Forall u64_ok st -> lst_ok (s_stream s st).
Proof.
  intros s st (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12) L F. unfold s_stream, lst_ok; lst_cbn.
  split_and; auto.
Qed.

(* The answers so far. *)
Lemma prefix_nil: forall s, w_word s = 0 -> prefix s nil.
Proof. intros s W. unfold prefix. rewrite W, sublist_nil. split; reflexivity. Qed.

Lemma prefix_more: forall s a v, prefix s a -> Zlength a < Zlength (w_answer s) -> prefix (s_more s v) (a ++ [v]).
Proof.
  intros s a v (W & P) L. unfold prefix, s_more; lst_cbn. rewrite Zlength_app, Zlength_cons, Zlength_nil.
  split; [ lia | ]. rewrite W. rewrite <- P. list_solve.
Qed.

Lemma prefix_store: forall s a v, prefix s a -> Zlength a < Zlength (w_answer s) ->
  sublist 0 (Zlength a + 1) (upd_Znth (w_word s) (w_answer s) v) = a ++ [v].
Proof. intros s a v (W & P) L. rewrite W. rewrite <- P. list_solve. Qed.

Lemma Znth_prefix: forall s a i, prefix s a -> 0 <= i < Zlength a -> Znth i (w_answer s) = Znth i a.
Proof. intros s a i (W & P) I. rewrite <- P. rewrite Znth_sublist by lia. f_equal; lia. Qed.

(* ---------------------------------------------------------------------- *)
(* The model's memory under the updates                                    *)
(* ---------------------------------------------------------------------- *)

Lemma mem_fit_extent: forall x m T, mem_fit x m -> u32_ok T -> mem_fit x (with_extent m T).
Proof. intros x m T F U. unfold mem_fit in *; simpl. tauto. Qed.

Lemma mem_fit_copy: forall x m c, mem_fit x m -> (has_copy x = true -> Zlength c = COPY_WORDS) ->
  (has_copy x = true -> Forall u64_ok c) -> mem_fit x (with_copy m c).
Proof. intros x m c F L C. unfold mem_fit in *; simpl. tauto. Qed.

Lemma mem_fit_zeros: forall x m, mem_fit x m -> mem_fit x (with_bitmaps m zeros zeros zeros).
Proof.
  intros x m F. pose proof Forall_u64_zeros. unfold mem_fit in *; simpl. rewrite Zlength_zeros. tauto.
Qed.

Lemma mem_fit_bitmaps: forall x m b u bl, mem_fit x m -> 0 <= b < BLOCKS -> u64_ok u -> u64_ok bl ->
  mem_fit x (with_bitmaps m (upd_Znth b (m_usable m) u) (upd_Znth b (m_blocked m) bl) (m_reserved m)).
Proof.
  intros x m b u bl F B U Bl. unfold mem_fit in *; simpl.
  destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13).
  rewrite !upd_Znth_Zlength by lia. split_and; auto; apply Forall_upd; auto.
Qed.

Lemma mem_fit_states: forall x m n a, mem_fit x m -> (n = 0 \/ n = 1) -> Zlength a = WORDS -> Forall u64_ok a ->
  mem_fit x (with_states m (upd_Znth n (m_states m) a) n).
Proof.
  intros x m n a F N L A. unfold mem_fit in *; simpl.
  destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13).
  rewrite upd_Znth_Zlength by lia. split_and; auto.
  - destruct N as [-> | ->]; [ rewrite upd_Znth_same by lia | rewrite upd_Znth_diff by lia ]; auto. split; auto.
  - destruct N as [-> | ->]; [ rewrite upd_Znth_diff by lia | rewrite upd_Znth_same by lia ]; auto. split; auto.
Qed.

Lemma copy_ctx_copy: forall x m c, copy_ctx x m -> copy_ctx x (with_copy m c).
Proof. intros. exact H. Qed.

Lemma dec_ctx_states: forall x m ss n, dec_ctx x m -> dec_ctx x (with_states m ss n).
Proof. intros. exact H. Qed.

Lemma dec_ctx_bitmaps: forall x m u b r, dec_ctx x m -> dec_ctx x (with_bitmaps m u b r).
Proof. intros. exact H. Qed.

Lemma dec_ctx_of_copy: forall x m, mem_fit x m -> copy_ctx x m -> i_call x <> FCopy -> dec_ctx x m.
Proof.
  intros x m F (C & E) N. unfold dec_ctx. split; [ exact N | split; [ exact E | ] ].
  destruct C as [C | C]; [ | contradiction ].
  unfold decoded. rewrite C. destruct F as (_ & F2 & _). rewrite F2 by (unfold has_copy; rewrite C; reflexivity).
  destruct E as [E1 E2]. apply Z.div_le_upper_bound; lia.
Qed.

(* The memory a phase leaves. *)
Lemma mem_of_decode_done: forall x m, mem_of (decode_done x m) = m.
Proof.
  intros. unfold decode_done, projection_end.
  destruct (projection x); [ | reflexivity ].
  destruct (negb _); [ reflexivity | ]. destruct (i_call x); reflexivity.
Qed.

Lemma mem_of_begin_transition: forall x k m, mem_of (begin_transition x k m) = m.
Proof. intros. unfold begin_transition. destruct (_ <? _); [ reflexivity | apply mem_of_decode_done ]. Qed.

Lemma mem_of_begin_decode: forall x m,
  mem_of (begin_decode x m) = if projection x then with_bitmaps m zeros zeros zeros else m.
Proof. reflexivity. Qed.

(* The decoder's words, as the bitmaps and states change. *)
Lemma decoded_states: forall x m ss n, decoded x (with_states m ss n) = decoded x m.
Proof. reflexivity. Qed.

Lemma decoded_bitmaps: forall x m u b r, decoded x (with_bitmaps m u b r) = decoded x m.
Proof. reflexivity. Qed.

(* The terminal marker's range. *)
Lemma terminal_range: forall T k, 0 <= terminal T k <= 1.
Proof. intros. unfold terminal. destruct (_ =? _); lia. Qed.

(* A decoder state's words. *)
Lemma state_word: forall r i, state_ok r -> 0 <= i < WORDS -> u64_ok (Znth i r).
Proof. intros r i (L & F) I. apply Forall_u64_Znth; auto. lia. Qed.

Lemma current_ok: forall x m, mem_fit x m -> state_ok (current m).
Proof.
  intros x m F. unfold current. destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R0 & R1 & A).
  destruct A as [-> | ->]; auto.
Qed.

Lemma call_code_inj: forall f g, call_code f = call_code g -> f = g.
Proof. intros [ ] [ ]; simpl; intros; congruence. Qed.

Lemma call_code_range: forall f, 0 <= call_code f <= 3.
Proof. intros [ ]; simpl; lia. Qed.

Lemma J_stop: forall x m s st, lst_ok s -> mem_fit x m -> u32_ok st -> J x (Return st m) (s_stop s st).
Proof.
  intros. unfold J. split_and; auto.
  - apply lst_ok_stop; auto.
  - unfold ret_inv, s_stop; lst_cbn. split; reflexivity.
Qed.

