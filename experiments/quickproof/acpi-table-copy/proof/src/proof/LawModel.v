(* Law table_copy_exact: the law's record follows the model (J), answer by answer: every way the firmware and the
   two exports update the record keeps J of the model's step, and so do the helpers begin_table, root_copied and
   table_copied at the model's begin_table, root_copied and table_copied.  No program here. *)
Require Import VST.floyd.proofauto.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.LawDefs LeanosAcpi.proof.LawFacts.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* stop(m, v) *)
Definition s_stop (s: lst) (v: Z) : lst := set_verdict (set_expect s E_NOTHING) v.

(* begin_table(m, t): BUDGET, or table t from the arena cursor. *)
Definition bt_state (x: inputs) (pl: place) (te: val) (s: lst) (t: Z) : lst :=
  if table_capacity x <=? w_arena s then s_stop s S_BUDGET
  else set_expect (set_word (set_byte (set_cursor (set_capacity (set_dexp (set_dest (set_sdt_address (set_table
         (set_is_root (set_offsets s (upd_Znth t (w_offsets s) (w_arena s))) 0) t) (Znth t (w_addresses s)))
         (offset_val (w_arena s) (p_tables pl))) (offset_val (w_arena s) te)) (table_capacity x - w_arena s))
         (w_arena s)) 0) 0) E_HEADER.

Ltac Jsimp := unfold J, go_inv, ret_inv, mem_rel, slot_of, sdt_inv, tgt_inv, tab_inv, cst_inv, seq_inv in *.

Ltac csplit := repeat match goal with |- _ /\ _ => split end.

Ltac u32_tac := unfold u32_ok, u64_ok, VERDICT_TABLES, E_HEADER, E_BODY, E_STREAM, E_SEQUENCE, E_NOTHING,
  MAX_SDT_BYTES, HEADER_BYTES, MAX_ENTRIES, MAX_U32 in *; rep_lia.

(* lst_ok of an updated record from lst_ok of the old one. *)
Ltac lst_ok_tac :=
  unfold lst_ok in *; lst_cbn;
  repeat match goal with H: _ /\ _ |- _ => destruct H end;
  repeat split; auto;
  repeat match goal with
  | |- Zlength (upd_Znth _ _ _) = _ => rewrite upd_Znth_Zlength by lia; auto
  | |- Forall _ (upd_Znth _ _ _) => apply Forall_upd; auto
  end;
  try u32_tac.

Lemma status_u32: forall st, 0 <= st <= 255 -> u32_ok st.
Proof. intros. unfold u32_ok. rep_lia. Qed.

(* ---------------------------------------------------------------------- *)
(* Returning                                                               *)
(* ---------------------------------------------------------------------- *)

Lemma J_stop: forall x pl re te st m s,
  lst_ok s -> mem_fit x m -> mem_rel x s m -> 0 < st < VERDICT_TABLES ->
  J x pl re te (Return st None m) (s_stop s st).
Proof.
  intros x pl re te st m s L F R S. unfold J, s_stop. cbn [mem_of].
  split; [ lst_ok_tac | ].
  split; [ auto | ].
  split; [ unfold mem_rel, slot_of in *; lst_cbn; exact R | ].
  unfold ret_inv; lst_cbn. split; [ reflexivity | ]. unfold VERDICT_TABLES, S_OK in *.
  split; [ intros; lia | ]. intros _. split; [ reflexivity | ]. split; [ lia | reflexivity ].
Qed.

(* ---------------------------------------------------------------------- *)
(* The calls                                                               *)
(* ---------------------------------------------------------------------- *)

Lemma next_call_J: forall x pl re te h p s c,
  run x (start x) h = Some p -> J x pl re te p s -> next_call x h = Some c ->
  exists st m, p = Go st m /\ c = expected x st /\ go_inv x pl re te st m s /\ lst_ok s /\ mem_fit x m /\
    mem_rel x s m.
Proof.
  intros x pl re te h p s c R HJ N. unfold next_call in N. rewrite R in N.
  destruct p as [st m | st pub m]; [ | discriminate ]. inversion N; subst.
  destruct HJ as (L & F & M & G). cbn [mem_of] in *. exists st, m. repeat (split; [ solve [ auto ] | ]); auto.
Qed.

Lemma copy_call: forall x st a d len, Copy a d len = expected x st ->
  (exists g, st = Copying g CHeader /\ a = address_of x g /\ d = DHeader /\ len = HEADER_BYTES) \/
  (exists g len', st = Copying g (CBody len') /\ a = address_of x g /\ d = dest_of g /\ len = len').
Proof.
  intros x st a d len E. destruct st as [g c | l cur]; [ destruct c | ]; simpl in E; inversion E; subst.
  - left. eauto 10.
  - right. eauto 10.
Qed.

Lemma stream_call: forall x st a1 a2 a3 a4 a5 a6 a7 a8 a9, Stream a1 a2 a3 a4 a5 a6 a7 a8 a9 = expected x st ->
  exists g len bs cursor byte cur, st = Copying g (CChunk len bs cursor byte cur) /\
    a1 = cursor /\ a2 = address_of x g /\ a3 = byte /\ a4 = address_of x g /\ a5 = len /\ a6 = byte /\
    a7 = little (sublist byte (byte + chunk_bytes len byte) bs) /\ a8 = terminal len byte /\
    a9 = stream_word (Zlength cur).
Proof.
  intros. destruct st as [g c | l cur]; [ destruct c | ]; simpl in H; inversion H; subst. do 6 eexists; csplit; reflexivity.
Qed.

Lemma sequence_call: forall x st a1 a2 a3 a4 a5 a6, Sequence a1 a2 a3 a4 a5 a6 = expected x st ->
  exists l cur, st = Sequencing l cur /\ a1 = l_ordinal l /\ a2 = Zlength (l_addresses l) /\ a3 = l_entry l /\
    a4 = 1 /\ a5 = (if l_entry l + 1 =? Zlength (l_addresses l) then 1 else 0) /\ a6 = Zlength cur + 1.
Proof.
  intros. destruct st as [g c | l cur]; [ destruct c | ]; simpl in H; inversion H; subst. do 2 eexists; csplit; reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* The firmware                                                            *)
(* ---------------------------------------------------------------------- *)

Lemma mem_fit_header: forall x m bs, mem_fit x m -> Zlength bs = HEADER_BYTES -> Forall byte_ok bs ->
  mem_fit x (write m DHeader bs).
Proof. intros x m bs (A & B & C & D & E & F) L Fb. unfold mem_fit. simpl. auto 10. Qed.

Lemma J_header_fail: forall x pl re te g m s,
  J x pl re te (Go (Copying g CHeader) m) s ->
  J x pl re te (step x (Copying g CHeader) m (Copied 0 (region m DHeader HEADER_BYTES))) (s_stop s S_PHYSICAL).
Proof.
  intros x pl re te g m s (L & F & R & G). unfold step. cbn [reply_bytes reply_value]. cbn [mem_of] in *.
  rewrite write_header_same by (destruct F; auto).
  apply J_stop; auto. unfold S_PHYSICAL, VERDICT_TABLES. lia.
Qed.

(* The length the header declares: rejected, or the body's. *)
Definition hdr_bad (x: inputs) (g: target) (len: Z) : bool :=
  (len <? HEADER_BYTES) || (MAX_SDT_BYTES <? len) || (capacity_of x g <? len).

Lemma J_header_bad: forall x pl re te g m s ret bs,
  J x pl re te (Go (Copying g CHeader) m) s -> ret <> 0 -> Zlength bs = HEADER_BYTES -> Forall byte_ok bs ->
  hdr_bad x g (little (sublist 4 8 bs)) = true ->
  J x pl re te (step x (Copying g CHeader) m (Copied ret bs)) (s_stop s S_SDT_LENGTH).
Proof.
  intros x pl re te g m s ret bs (L & F & R & G) N Lb Fb B. unfold step. cbn [reply_bytes reply_value mem_of] in *.
  rewrite (proj2 (Z.eqb_neq ret 0) N). unfold hdr_bad in B. rewrite B.
  apply J_stop; [ exact L | apply mem_fit_header; auto | exact R | unfold S_SDT_LENGTH, VERDICT_TABLES; lia ].
Qed.

Lemma J_header_ok: forall x pl re te g m s ret bs,
  J x pl re te (Go (Copying g CHeader) m) s -> ret <> 0 -> Zlength bs = HEADER_BYTES -> Forall byte_ok bs ->
  hdr_bad x g (little (sublist 4 8 bs)) = false ->
  J x pl re te (step x (Copying g CHeader) m (Copied ret bs))
    (set_expect (set_length s (little (sublist 4 8 bs))) E_BODY).
Proof.
  intros x pl re te g m s ret bs (L & F & R & G) N Lb Fb B. unfold step. cbn [reply_bytes reply_value mem_of] in *.
  rewrite (proj2 (Z.eqb_neq ret 0) N). unfold hdr_bad in B. rewrite B.
  set (len := little (sublist 4 8 bs)) in *.
  repeat rewrite orb_false_iff in B. destruct B as [[B1 B2] B3].
  apply Z.ltb_ge in B1, B2, B3.
  unfold J. cbn [mem_of]. split; [ lst_ok_tac | ].
  split; [ apply mem_fit_header; auto | ].
  split; [ unfold mem_rel, slot_of in *; simpl; lst_cbn; exact R | ].
  destruct G as (SI & TI & CI). unfold go_inv.
  split; [ unfold sdt_inv in *; lst_cbn; exact SI | ].
  split; [ destruct g; unfold tgt_inv, tab_inv in *; simpl; lst_cbn; exact TI | ].
  unfold cst_inv in *. lst_cbn. destruct CI as [_ C]. unfold len_ok.
  csplit; auto; try lia; try (unfold len_ok in *; unfold HEADER_BYTES, MAX_SDT_BYTES in *; lia).
Qed.

Lemma J_body_fail: forall x pl re te g len m s,
  J x pl re te (Go (Copying g (CBody len)) m) s ->
  J x pl re te (step x (Copying g (CBody len)) m (Copied 0 (region m (dest_of g) len))) (s_stop s S_PHYSICAL).
Proof.
  intros x pl re te g len m s (L & F & R & G). unfold step. cbn [reply_bytes reply_value mem_of] in *.
  destruct G as (SI & TI & CI). unfold cst_inv, len_ok in CI. destruct CI as (_ & _ & _ & (C1 & C2) & C3).
  rewrite write_region.
  - apply J_stop; auto. unfold S_PHYSICAL, VERDICT_TABLES. lia.
  - unfold HEADER_BYTES in *; lia.
  - destruct F as (_ & F2 & F3 & _). rewrite capacity_base in C3.
    destruct g; simpl in *; [ rewrite F2 | rewrite F3 ]; lia.
  - destruct g; simpl; [ lia | ]. unfold tgt_inv, tab_inv in TI. lia.
Qed.

Lemma J_body_ok: forall x pl re te g len m s ret bs,
  J x pl re te (Go (Copying g (CBody len)) m) s -> ret <> 0 -> Zlength bs = len -> Forall byte_ok bs ->
  J x pl re te (step x (Copying g (CBody len)) m (Copied ret bs))
    (set_expect (set_word (set_byte s 0) 0) E_STREAM).
Proof.
  intros x pl re te g len m s ret bs (L & F & R & G) N Lb Fb. unfold step. cbn [reply_bytes reply_value mem_of] in *.
  rewrite (proj2 (Z.eqb_neq ret 0) N).
  destruct G as (SI & TI & CI). unfold cst_inv, len_ok in CI. destruct CI as (C0 & C1 & C2 & (C3 & C4) & C5).
  unfold HEADER_BYTES, MAX_SDT_BYTES in C3, C4.
  assert (Off: 0 <= cursor_of g) by (destruct g; simpl; [ lia | unfold tgt_inv, tab_inv in TI; lia ]).
  assert (Fit: cursor_of g + Zlength bs <= Zlength (base_mem m g)).
  { destruct F as (_ & F2 & F3 & _). rewrite capacity_base in C5. destruct g; simpl in *; [ rewrite F2 | rewrite F3 ]; lia. }
  pose proof (write_meta m (dest_of g) bs) as (W1 & W2 & W3).
  unfold J. cbn [mem_of]. split; [ lst_ok_tac | ].
  split.
  { destruct F as (F1 & F2 & F3 & F4 & F5 & F6). unfold mem_fit.
    destruct g; simpl in *; rewrite ?Zlength_overlay by lia; csplit; auto; apply Forall_overlay; auto. }
  split; [ unfold mem_rel, slot_of in *; rewrite W1, W2, W3; lst_cbn; exact R | ].
  unfold go_inv. split; [ unfold sdt_inv in *; lst_cbn; exact SI | ].
  split; [ destruct g; unfold tgt_inv, tab_inv in *; rewrite ?W1, ?W2, ?W3; lst_cbn; exact TI | ].
  unfold cst_inv. lst_cbn. rewrite Zlength_nil.
  csplit; auto; try lia; try (unfold len_ok in *; unfold HEADER_BYTES, MAX_SDT_BYTES in *; lia).
  - rewrite region_base, base_write. rewrite <- Lb. apply sublist_overlay; auto.
Qed.

(* ---------------------------------------------------------------------- *)
(* The copy stream                                                         *)
(* ---------------------------------------------------------------------- *)

Lemma chunk_bytes_range: forall len byte, 0 <= byte < len -> 0 < chunk_bytes len byte <= 8 /\
  byte + chunk_bytes len byte <= len.
Proof. intros. unfold chunk_bytes. lia. Qed.

Lemma J_stream_more: forall x pl re te g len bs cursor byte cur m s v,
  J x pl re te (Go (Copying g (CChunk len bs cursor byte cur)) m) s -> Zlength cur < 4 -> u64_ok v ->
  J x pl re te (step x (Copying g (CChunk len bs cursor byte cur)) m (Word v))
    (set_word (set_answer s (upd_Znth (Zlength cur) (w_answer s) v)) (Zlength cur + 1)).
Proof.
  intros x pl re te g len bs cursor byte cur m s v (L & F & R & G) Lc V. unfold step. cbn [reply_value].
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  replace (Zlength cur + Z.succ 0 <? 5) with true by (symmetry; apply Z.ltb_lt; lia).
  pose proof (Zlength_nonneg cur).
  destruct G as (SI & TI & CI).
  unfold J. cbn [mem_of]. split; [ lst_ok_tac | ]. split; [ auto | ].
  split; [ unfold mem_rel, slot_of in *; lst_cbn; exact R | ].
  unfold go_inv. split; [ unfold sdt_inv in *; lst_cbn; exact SI | ].
  split; [ destruct g; unfold tgt_inv, tab_inv in *; lst_cbn; exact TI | ].
  unfold cst_inv in *. lst_cbn. destruct CI as (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  assert (La: Zlength (w_answer s) = 5) by (unfold lst_ok in L; tauto).
  csplit; auto; try lia; try (unfold len_ok in *; unfold HEADER_BYTES, MAX_SDT_BYTES in *; lia).
  apply prefix_snoc with (k := 5); auto; lia.
Qed.

(* The five answers of a transition. *)
Lemma answers_full: forall (cur: list Z) s v, lst_ok s -> Zlength cur = 4 ->
  sublist 0 (Zlength cur) (w_answer s) = cur -> upd_Znth (Zlength cur) (w_answer s) v = cur ++ [v].
Proof.
  intros. apply prefix_full with (k := 4); auto; [ unfold lst_ok in H; tauto | lia ].
Qed.

Lemma transition_u32: forall a chunk cursor byte n last, 0 <= transition a chunk cursor byte n last < VERDICT_TABLES.
Proof.
  intros. unfold transition, VERDICT_TABLES.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; cbv; split; congruence.
Qed.

Lemma J_stream_reject: forall x pl re te g len bs cursor byte cur m s v,
  J x pl re te (Go (Copying g (CChunk len bs cursor byte cur)) m) s -> Zlength cur = 4 -> u64_ok v ->
  let a := cur ++ [v] in
  let n := chunk_bytes len byte in
  let t := transition a (little (sublist byte (byte + n) bs)) cursor byte n (terminal len byte) in
  t <> S_OK ->
  J x pl re te (step x (Copying g (CChunk len bs cursor byte cur)) m (Word v)) (s_stop (set_answer s a) t).
Proof.
  intros x pl re te g len bs cursor byte cur m s v (L & F & R & G) Lc V a n t T. unfold step. cbn [reply_value].
  fold a. replace (Zlength a <? 5) with false by (symmetry; apply Z.ltb_ge; unfold a; rewrite Zlength_app; list_solve).
  fold n. fold t. rewrite (proj2 (Z.eqb_neq t S_OK) T). simpl negb. cbv iota.
  apply J_stop; [ | exact F | exact R | ].
  - lst_ok_tac. unfold a. rewrite Zlength_app, Lc. reflexivity. unfold a. apply Forall_app; split; auto.
    destruct G as (_ & _ & CI). unfold cst_inv in CI. destruct CI as (_ & _ & _ & _ & _ & C5 & _).
    rewrite <- C5. apply Forall_sublist; auto.
  - pose proof (transition_u32 a (little (sublist byte (byte + n) bs)) cursor byte n (terminal len byte)).
    fold t in H. unfold S_OK in T. lia.
Qed.

(* An accepted transition: the next chunk's offset and the cursor. *)
Lemma transition_ok: forall a chunk cursor byte n last, transition a chunk cursor byte n last = S_OK ->
  Znth 2 a = byte + n /\ (last = 0 -> Znth 3 a = cursor) /\ (last <> 0 -> cursor < Znth 3 a).
Proof.
  intros a chunk cursor byte n last T. unfold transition in T.
  repeat match type of T with context [if ?b then _ else _] =>
    let E := fresh "E" in destruct b eqn:E; [ discriminate T | ] end.
  repeat match goal with
  | E: negb _ = false |- _ => apply negb_false_iff in E
  | E: (_ && _) = false |- _ => apply andb_false_iff in E
  | E: (Znth 2 a =? _) = true |- _ => apply Z.eqb_eq in E
  end.
  split; [ assumption | ].
  split; intros Hl.
  - match goal with E: (last =? 0) = false \/ _ |- _ =>
      destruct E as [X | X]; [ rewrite Hl in X; discriminate | apply negb_false_iff, Z.eqb_eq in X; auto ] end.
  - match goal with E: negb (last =? 0) = false \/ _ |- _ =>
      destruct E as [X | X]; [ apply negb_false_iff, Z.eqb_eq in X; contradiction | apply Z.leb_gt in X; auto ] end.
Qed.

Definition s_accept (s: lst) (a: list Z) : lst :=
  set_word (set_cursor (set_byte (set_answer s a) (Znth 2 a)) (Znth 3 a)) 0.

Lemma J_stream_next: forall x pl re te g len bs cursor byte cur m s v,
  J x pl re te (Go (Copying g (CChunk len bs cursor byte cur)) m) s -> Zlength cur = 4 -> u64_ok v ->
  let a := cur ++ [v] in
  let n := chunk_bytes len byte in
  transition a (little (sublist byte (byte + n) bs)) cursor byte n (terminal len byte) = S_OK ->
  terminal len byte = 0 ->
  J x pl re te (step x (Copying g (CChunk len bs cursor byte cur)) m (Word v)) (s_accept s a).
Proof.
  intros x pl re te g len bs cursor byte cur m s v (L & F & R & G) Lc V a n T Tm. unfold step. cbn [reply_value].
  fold a. replace (Zlength a <? 5) with false by (symmetry; apply Z.ltb_ge; unfold a; rewrite Zlength_app; list_solve).
  fold n. rewrite T. simpl negb. cbv iota. rewrite Tm. simpl Z.eqb. cbv iota.
  destruct (transition_ok _ _ _ _ _ _ T) as (T2 & T3 & _). specialize (T3 Tm).
  destruct G as (SI & TI & CI). unfold cst_inv in CI.
  destruct CI as (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
  pose proof (chunk_bytes_range len byte C7) as (N1 & N2). fold n in N1, N2.
  assert (Lt: byte + n < len).
  { unfold terminal in Tm. fold n in Tm. destruct (byte + n =? len) eqn:E; [ discriminate | apply Z.eqb_neq in E; lia ]. }
  rewrite T2. replace (byte + n <? len) with true by (symmetry; apply Z.ltb_lt; lia).
  assert (Fa: Forall u64_ok a) by (unfold a; apply Forall_app; split; auto; rewrite <- C5; apply Forall_sublist; unfold lst_ok in L; tauto).
  assert (La: Zlength a = 5) by (unfold a; rewrite Zlength_app, Lc; reflexivity).
  unfold J, s_accept. cbn [mem_of]. split.
  { lst_ok_tac; apply (Forall_Znth' _ a _ Fa); lia. }
  split; [ auto | ].
  split; [ unfold mem_rel, slot_of in *; lst_cbn; exact R | ].
  unfold go_inv. split; [ unfold sdt_inv in *; lst_cbn; exact SI | ].
  split; [ destruct g; unfold tgt_inv, tab_inv in *; lst_cbn; exact TI | ].
  unfold cst_inv. lst_cbn. rewrite T2, T3, Zlength_nil.
  csplit; auto; try lia; try (unfold len_ok in *; unfold HEADER_BYTES, MAX_SDT_BYTES in *; lia).
Qed.

(* The last chunk accepted: the record as root_copied / table_copied find it. *)
Lemma stream_last: forall x pl re te g len bs cursor byte cur m s v,
  J x pl re te (Go (Copying g (CChunk len bs cursor byte cur)) m) s -> Zlength cur = 4 -> u64_ok v ->
  let a := cur ++ [v] in
  let n := chunk_bytes len byte in
  transition a (little (sublist byte (byte + n) bs)) cursor byte n (terminal len byte) = S_OK ->
  terminal len byte <> 0 ->
  step x (Copying g (CChunk len bs cursor byte cur)) m (Word v) = sdt_copied x g len (Znth 3 a) m /\
  lst_ok (s_accept s a) /\ mem_fit x m /\ mem_rel x (s_accept s a) m /\ sdt_inv x pl re te g (s_accept s a) /\
  tgt_inv x g m (s_accept s a) /\ w_length (s_accept s a) = len /\ w_cursor (s_accept s a) = Znth 3 a /\
  len_ok x g len /\ Znth 2 a = len.
Proof.
  intros x pl re te g len bs cursor byte cur m s v (L & F & R & G) Lc V a n T Tm.
  destruct (transition_ok _ _ _ _ _ _ T) as (T2 & _ & T4). specialize (T4 Tm).
  destruct G as (SI & TI & CI). unfold cst_inv in CI.
  destruct CI as (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
  pose proof (chunk_bytes_range len byte C7) as (N1 & N2). fold n in N1, N2.
  assert (Eq: byte + n = len).
  { unfold terminal in Tm. fold n in Tm. destruct (byte + n =? len) eqn:E; [ apply Z.eqb_eq in E; auto | contradiction ]. }
  assert (Fa: Forall u64_ok a) by (unfold a; apply Forall_app; split; auto; rewrite <- C5; apply Forall_sublist; unfold lst_ok in L; tauto).
  assert (La: Zlength a = 5) by (unfold a; rewrite Zlength_app, Lc; reflexivity).
  split.
  { unfold step. cbn [reply_value]. fold a.
    replace (Zlength a <? 5) with false by (symmetry; apply Z.ltb_ge; lia).
    fold n. rewrite T. simpl negb. cbv iota.
    replace (terminal len byte =? 0) with false by (symmetry; apply Z.eqb_neq; auto). cbv iota.
    rewrite T2, Eq, Z.ltb_irrefl. reflexivity. }
  unfold s_accept. split.
  { lst_ok_tac; apply (Forall_Znth' _ a _ Fa); lia. }
  split; [ auto | ].
  split; [ unfold mem_rel, slot_of in *; lst_cbn; exact R | ].
  split; [ unfold sdt_inv in *; lst_cbn; exact SI | ].
  split; [ destruct g; unfold tgt_inv, tab_inv in *; lst_cbn; exact TI | ].
  lst_cbn. split; [ auto | ]. split; [ reflexivity | ]. split; [ split; auto | ]. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* begin_table                                                             *)
(* ---------------------------------------------------------------------- *)

(* The loop l before table l_entry l: as tab_inv, the table field aside. *)
Definition loop_inv (x: inputs) (l: tloop) (m: mem) (s: lst) : Prop :=
  let n := Zlength (l_addresses l) in
  w_count s = n /\ 1 <= n <= MAX_ENTRIES /\ sublist 0 n (w_addresses s) = l_addresses l /\
  Forall (fun a => 0 < a <= MAX_U32) (l_addresses l) /\ 0 <= l_entry l < n /\
  w_arena s = l_offset l /\ 0 <= l_offset l /\ w_ordinal s = l_ordinal l /\ tiled (m_slots m) (l_offset l) /\
  Zlength (m_slots m) = l_entry l /\ l_offset l <= table_capacity x.

Lemma Znth_prefix: forall (l pre: list Z) n i, sublist 0 n l = pre -> 0 <= i < n -> n <= Zlength l ->
  Znth i l = Znth i pre.
Proof. intros. subst pre. rewrite Znth_sublist by lia. f_equal. lia. Qed.

Lemma J_begin_table: forall x pl re te l m s,
  lst_ok s -> mem_fit x m -> mem_rel x s m -> inputs_ok x -> loop_inv x l m s ->
  J x pl re te (begin_table x l m) (bt_state x pl te s (l_entry l)).
Proof.
  intros x pl re te l m s L F R I LI.
  destruct LI as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11).
  unfold begin_table, bt_state. rewrite N6.
  destruct (table_capacity x <=? l_offset l) eqn:B.
  - apply J_stop; auto. unfold S_BUDGET, VERDICT_TABLES. lia.
  - apply Z.leb_gt in B.
    assert (La: Zlength (w_addresses s) = MAX_ENTRIES) by (unfold lst_ok in L; tauto).
    assert (Lo: Zlength (w_offsets s) = MAX_ENTRIES) by (unfold lst_ok in L; tauto).
    assert (Ea: Znth (l_entry l) (w_addresses s) = Znth (l_entry l) (l_addresses l))
      by (apply (Znth_prefix _ _ (Zlength (l_addresses l))); auto; lia).
    assert (Ra: 0 < Znth (l_entry l) (l_addresses l) <= MAX_U32) by (apply (Forall_Znth' _ _ _ N4); lia).
    unfold begin_sdt. cbn [address_of]. replace (MAX_U32 <? Znth (l_entry l) (l_addresses l)) with false
      by (symmetry; apply Z.ltb_ge; lia).
    unfold J. cbn [mem_of].
    assert (Rc: u32_ok (table_capacity x)) by (destruct I as (_ & _ & _ & _ & I5 & _); unfold u32_ok; rep_lia).
    split; [ lst_ok_tac | ].
    split; [ auto | ].
    split.
    { unfold mem_rel, slot_of in *. lst_cbn. destruct R as (R1 & R2 & R3 & R4 & R5).
      csplit; auto. intros t Ht. rewrite R4 by auto. rewrite upd_Znth_diff by lia. reflexivity. }
    unfold go_inv. split.
    { unfold sdt_inv. lst_cbn. cbn [address_of dest_of dest_ptr dexp_of capacity_of]. rewrite Ea.
      csplit; reflexivity. }
    split.
    { unfold tgt_inv, tab_inv. lst_cbn. csplit; auto; try lia; try (unfold len_ok in *; unfold HEADER_BYTES, MAX_SDT_BYTES in *; lia).
      rewrite upd_Znth_same by lia. reflexivity. }
    unfold cst_inv. lst_cbn. cbn [cursor_of]. split; reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* The copy sequence                                                       *)
(* ---------------------------------------------------------------------- *)

Lemma J_seq_more: forall x pl re te l cur m s v,
  J x pl re te (Go (Sequencing l cur) m) s -> Zlength cur < 2 -> u64_ok v ->
  J x pl re te (step x (Sequencing l cur) m (Word v))
    (set_word (set_answer s (upd_Znth (Zlength cur) (w_answer s) v)) (Zlength cur + 1)).
Proof.
  intros x pl re te l cur m s v (L & F & R & G) Lc V. unfold step. cbn [reply_value].
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  replace (Zlength cur + Z.succ 0 <? 3) with true by (symmetry; apply Z.ltb_lt; lia).
  pose proof (Zlength_nonneg cur).
  unfold J. cbn [mem_of]. split; [ lst_ok_tac | ]. split; [ auto | ].
  split; [ unfold mem_rel, slot_of in *; lst_cbn; exact R | ].
  unfold go_inv, seq_inv in *. lst_cbn.
  destruct G as (C0 & C1 & C2 & C3 & C4 & C5 & C6).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  assert (La: Zlength (w_answer s) = 5) by (unfold lst_ok in L; tauto).
  split; [ unfold tab_inv in *; lst_cbn; exact C0 | ].
  csplit; auto; try lia; try (unfold len_ok in *; unfold HEADER_BYTES, MAX_SDT_BYTES in *; lia).
  apply prefix_snoc with (k := 5); auto; lia.
Qed.

Definition seq_bad (l: tloop) (a: list Z) : bool :=
  negb (Znth 0 a =? 1) || negb (Znth 1 a =? 0) || negb (Znth 2 a =? l_entry l + 1).

Lemma seq_answers: forall (cur: list Z) s v, lst_ok s -> Zlength cur = 2 ->
  sublist 0 (Zlength cur) (w_answer s) = cur -> upd_Znth (Zlength cur) (w_answer s) v = cur ++ [v] ++ sublist 3 5 (w_answer s).
Proof.
  intros. assert (Zlength (w_answer s) = 5) by (unfold lst_ok in H; tauto). rewrite <- H1. list_solve.
Qed.

Lemma J_seq_reject: forall x pl re te l cur m s v,
  J x pl re te (Go (Sequencing l cur) m) s -> Zlength cur = 2 -> u64_ok v ->
  seq_bad l (cur ++ [v]) = true ->
  J x pl re te (step x (Sequencing l cur) m (Word v))
    (s_stop (set_answer s (upd_Znth (Zlength cur) (w_answer s) v)) S_SEQUENCE).
Proof.
  intros x pl re te l cur m s v (L & F & R & G) Lc V B. unfold step. cbn [reply_value].
  replace (Zlength (cur ++ [v]) <? 3) with false by (symmetry; apply Z.ltb_ge; list_solve).
  unfold seq_bad in B. rewrite B.
  apply J_stop; [ lst_ok_tac | exact F | exact R | unfold S_SEQUENCE, VERDICT_TABLES; lia ].
Qed.

Lemma J_seq_last: forall x pl re te l cur m s v,
  J x pl re te (Go (Sequencing l cur) m) s -> Zlength cur = 2 -> u64_ok v ->
  seq_bad l (cur ++ [v]) = false -> l_entry l + 1 = Zlength (l_addresses l) ->
  J x pl re te (step x (Sequencing l cur) m (Word v))
    (s_stop (set_word_ordinal (set_answer s (upd_Znth (Zlength cur) (w_answer s) v)) (Znth 2 (cur ++ [v])))
       VERDICT_TABLES).
Proof.
  intros x pl re te l cur m s v (L & F & R & G) Lc V B Ll. unfold step. cbn [reply_value].
  replace (Zlength (cur ++ [v]) <? 3) with false by (symmetry; apply Z.ltb_ge; list_solve).
  unfold seq_bad in B. rewrite B. cbv iota. cbn [Defs.set_ordinal l_entry l_addresses].
  replace (l_entry l + 1 <? Zlength (l_addresses l)) with false by (symmetry; apply Z.ltb_ge; lia).
  unfold seq_inv, tab_inv in G. destruct G as ((T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10) & G2 & G3 & G4 & G5 & G6 & G7).
  assert (Fa: Forall u64_ok (cur ++ [v])).
  { apply Forall_app; split; [ rewrite <- G4; apply Forall_sublist; unfold lst_ok in L; tauto | auto ]. }
  set (s' := s_stop (set_word_ordinal (set_answer s (upd_Znth (Zlength cur) (w_answer s) v)) (Znth 2 (cur ++ [v])))
                VERDICT_TABLES).
  assert (Ls: lst_ok s') by (unfold s', s_stop; lst_ok_tac; apply (Forall_Znth' _ _ 2 Fa); list_solve).
  assert (Rs: mem_rel x s' m) by (unfold s', s_stop, mem_rel, slot_of in *; lst_cbn; exact R).
  assert (Ri: ret_inv x (stat (select_madt m))
                (match select_madt m with inl _ => None | inr i => Some (Zlength (l_addresses l), i) end) m s').
  { unfold ret_inv, s', s_stop. lst_cbn. split; [ reflexivity | ].
    split; [ | intros C; exfalso; apply C; reflexivity ].
    intros _. rewrite T1, T7. csplit; auto; try lia. }
  unfold tables_done. destruct (select_madt m) eqn:Sel;
    unfold J; cbn [mem_of]; (split; [ exact Ls | split; [ exact F | split; [ exact Rs | exact Ri ] ] ]).
Qed.

Lemma J_seq_next: forall x pl re te l cur m s v,
  J x pl re te (Go (Sequencing l cur) m) s -> Zlength cur = 2 -> u64_ok v -> inputs_ok x ->
  seq_bad l (cur ++ [v]) = false -> l_entry l + 1 < Zlength (l_addresses l) ->
  J x pl re te (step x (Sequencing l cur) m (Word v))
    (bt_state x pl te (set_word_ordinal (set_answer s (upd_Znth (Zlength cur) (w_answer s) v)) (Znth 2 (cur ++ [v])))
       (l_entry l + 1)).
Proof.
  intros x pl re te l cur m s v (L & F & R & G) Lc V I B Ll. unfold step. cbn [reply_value].
  replace (Zlength (cur ++ [v]) <? 3) with false by (symmetry; apply Z.ltb_ge; list_solve).
  unfold seq_bad in B. rewrite B. cbv iota. cbn [Defs.set_ordinal l_entry l_addresses].
  replace (l_entry l + 1 <? Zlength (l_addresses l)) with true by (symmetry; apply Z.ltb_lt; lia).
  unfold seq_inv, tab_inv in G. destruct G as ((T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10) & G2 & G3 & G4 & G5 & G6 & G7).
  assert (Fa: Forall u64_ok (cur ++ [v])).
  { apply Forall_app; split; [ rewrite <- G4; apply Forall_sublist; unfold lst_ok in L; tauto | auto ]. }
  match goal with |- J _ _ _ _ (begin_table x ?l' m) _ =>
    replace (l_entry l + 1) with (l_entry l') by reflexivity end.
  apply J_begin_table; [ | exact F | exact R | exact I | ].
  - lst_ok_tac; apply (Forall_Znth' _ _ 2 Fa); list_solve.
  - unfold loop_inv. cbn [next_entry Defs.set_ordinal l_addresses l_entry l_offset l_ordinal]. lst_cbn.
    csplit; auto; try lia; try (unfold len_ok in *; unfold HEADER_BYTES, MAX_SDT_BYTES in *; lia).
Qed.

(* ---------------------------------------------------------------------- *)
(* table_copied                                                            *)
(* ---------------------------------------------------------------------- *)

(* The record of the table's copy. *)
Definition tc_s1 (s: lst) : lst :=
  set_ended (set_finals (set_lengths s (upd_Znth (w_table s) (w_lengths s) (w_length s)))
    (upd_Znth (w_table s) (w_finals s) (w_cursor s))) (w_table s + 1).

Lemma tiles_snoc: forall ss off e sd, tiles_from off ss e -> s_offset sd = e -> s_next sd = e + padded (s_length sd) ->
  tiles_from off (ss ++ [sd]) (e + padded (s_length sd)).
Proof.
  induction ss as [ | s0 ss IH]; intros off e sd T O N; simpl in *.
  - subst. auto.
  - destruct T as (T1 & T2 & T3). auto.
Qed.

Lemma padded_range: forall len, 0 <= len <= MAX_SDT_BYTES -> len <= padded len <= len + 7 /\ 0 <= padded len.
Proof.
  intros. unfold padded. pose proof (Z.mod_pos_bound (len + 7) 8 ltac:(lia)).
  pose proof (Z_div_mod_eq_full (len + 7) 8). lia.
Qed.

Lemma tc_common: forall x pl re te l s m len cursor,
  tc_pre x pl re te l s m len cursor ->
  lst_ok (tc_s1 s) /\ mem_rel x (tc_s1 s) (add_slot m (mk_sdt (Znth (l_entry l) (l_addresses l)) (l_offset l) len
                                              (cursor mod 2 ^ 32))) /\
  mem_fit x (add_slot m (mk_sdt (Znth (l_entry l) (l_addresses l)) (l_offset l) len (cursor mod 2 ^ 32))).
Proof.
  intros x pl re te l s m len cursor (L & F & R & SI & TI & Ln & Cu & LO & I).
  unfold tgt_inv, tab_inv in TI. destruct TI as ((T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10) & U1 & U2 & U3).
  assert (La: Zlength (w_addresses s) = MAX_ENTRIES) by (unfold lst_ok in L; tauto).
  assert (Ll: Zlength (w_lengths s) = MAX_ENTRIES) by (unfold lst_ok in L; tauto).
  assert (Lf: Zlength (w_finals s) = MAX_ENTRIES) by (unfold lst_ok in L; tauto).
  unfold len_ok in LO.
  split; [ unfold tc_s1; lst_ok_tac | ].
  split; [ | unfold mem_fit in *; simpl; auto ].
  unfold mem_rel, slot_of, tc_s1 in *. lst_cbn. simpl.
  destruct R as (R1 & R2 & R3 & R4 & R5).
  rewrite Zlength_app, Zlength_cons, Zlength_nil. rewrite T5.
  csplit; auto; try lia; try (unfold len_ok in *; unfold HEADER_BYTES, MAX_SDT_BYTES in *; lia).
  - intros t Ht. destruct (Z.eq_dec t (Zlength (m_slots m))) as [E | E].
    + subst t. rewrite Znth_app2 by lia. replace (Zlength (m_slots m) - Zlength (m_slots m)) with 0 by lia.
      rewrite Znth_0_cons. rewrite U1. rewrite !upd_Znth_same by lia. f_equal.
      * symmetry. apply (Znth_prefix _ _ (Zlength (l_addresses l))); auto; lia.
      * symmetry. exact U2.
      * symmetry. exact Ln.
      * rewrite Cu. reflexivity.
    + rewrite Znth_app1 by lia. rewrite R4 by lia. rewrite !upd_Znth_diff by lia. reflexivity.
  - apply Forall_app; split; auto. constructor; [ simpl; lia | constructor ].
Qed.

Lemma J_tc_budget: forall x pl re te l s m len cursor,
  tc_pre x pl re te l s m len cursor -> table_capacity x < w_arena s + padded len ->
  J x pl re te (table_copied x l len cursor m) (s_stop (tc_s1 s) S_BUDGET).
Proof.
  intros x pl re te l s m len cursor P B. pose proof (tc_common _ _ _ _ _ _ _ _ _ P) as (C1 & C2 & C3).
  destruct P as (L & F & R & SI & TI & Ln & Cu & LO & I). unfold tgt_inv, tab_inv in TI.
  unfold table_copied. cbv zeta.
  replace (table_capacity x - l_offset l <? padded len) with true by (symmetry; apply Z.ltb_lt; lia).
  apply J_stop; auto. unfold S_BUDGET, VERDICT_TABLES. lia.
Qed.

Lemma J_tc_stream: forall x pl re te l s m len cursor,
  tc_pre x pl re te l s m len cursor -> w_arena s + padded len <= table_capacity x ->
  cursor mod 2 ^ 32 <> w_arena s + padded len ->
  J x pl re te (table_copied x l len cursor m) (s_stop (tc_s1 s) S_STREAM).
Proof.
  intros x pl re te l s m len cursor P B N. pose proof (tc_common _ _ _ _ _ _ _ _ _ P) as (C1 & C2 & C3).
  destruct P as (L & F & R & SI & TI & Ln & Cu & LO & I). unfold tgt_inv, tab_inv in TI.
  unfold table_copied. cbv zeta.
  replace (table_capacity x - l_offset l <? padded len) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (cursor mod 2 ^ 32 =? l_offset l + padded len) with false by (symmetry; apply Z.eqb_neq; lia).
  apply J_stop; auto. unfold S_STREAM, VERDICT_TABLES. lia.
Qed.

Lemma J_tc_ok: forall x pl re te l s m len cursor,
  tc_pre x pl re te l s m len cursor -> w_arena s + padded len <= table_capacity x ->
  cursor mod 2 ^ 32 = w_arena s + padded len ->
  J x pl re te (table_copied x l len cursor m)
    (set_expect (set_word (set_arena (tc_s1 s) (w_arena s + padded len)) 0) E_SEQUENCE).
Proof.
  intros x pl re te l s m len cursor P B N. pose proof (tc_common _ _ _ _ _ _ _ _ _ P) as (C1 & C2 & C3).
  destruct P as (L & F & R & SI & TI & Ln & Cu & LO & I).
  unfold tgt_inv, tab_inv in TI. destruct TI as ((T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10) & U1 & U2 & U3).
  unfold len_ok, HEADER_BYTES, MAX_SDT_BYTES in LO. pose proof (padded_range len ltac:(unfold MAX_SDT_BYTES; lia)) as (P1 & P2).
  unfold table_copied. cbv zeta.
  replace (table_capacity x - l_offset l <? padded len) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (cursor mod 2 ^ 32 =? l_offset l + padded len) with true by (symmetry; apply Z.eqb_eq; lia).
  cbv iota. simpl negb. cbv iota.
  assert (Rc: table_capacity x <= Int.max_unsigned) by (destruct I as (_ & _ & _ & _ & I5 & _); auto).
  unfold J. cbn [mem_of]. split.
  { clear C2 C3. unfold tc_s1 in *. lst_ok_tac. }
  split; [ auto | ].
  split; [ unfold mem_rel, slot_of, tc_s1 in *; lst_cbn; exact C2 | ].
  unfold go_inv, seq_inv, tab_inv. unfold tc_s1. lst_cbn. cbn [set_offset l_addresses l_entry l_offset l_ordinal].
  simpl m_slots. rewrite Zlength_app, Zlength_cons, Zlength_nil, Zlength_nil.
  csplit; auto; try lia; try (unfold len_ok in *; unfold HEADER_BYTES, MAX_SDT_BYTES in *; lia).
  - apply tiles_snoc; auto; simpl. rewrite T7 in N. lia.
Qed.
