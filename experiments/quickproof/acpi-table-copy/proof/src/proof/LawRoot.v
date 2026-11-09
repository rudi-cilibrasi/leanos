(* Law table_copy_exact: root_copied's checks against the model's root_copied (validate, decode_entries,
   decode_addresses, tables_start), and the record it leaves keeping J.  No program here. *)
Require Import VST.floyd.proofauto.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.LawDefs LeanosAcpi.proof.LawFacts LeanosAcpi.proof.LawModel.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Definition rc_sig (x: inputs) : list Z := if i_kind x =? 1 then RSDT else XSDT.
Definition rc_w (x: inputs) : Z := if i_kind x =? 1 then 4 else 8.

(* root_done, root_length, root_cursor; then entries_done, width, count. *)
Definition rc_s1 (s: lst) (len cursor: Z) : lst :=
  set_root_cursor (set_root_length (set_root_done s 1) len) cursor.
Definition rc_s2 (s: lst) (len cursor count w: Z) : lst :=
  set_count (set_width (set_entries_done (rc_s1 s len cursor) 1) w) count.

Definition rc_m1 (x: inputs) (m: mem) (len cursor: Z) : mem :=
  set_root_copy m (mk_sdt (i_address x) 0 len (cursor mod 2 ^ 32)).

(* The C's checks of the root's envelope and checksum are the model's validate. *)
Lemma validate_c: forall len bs sg, HEADER_BYTES <= len <= Zlength bs -> Zlength sg = 4 ->
  validate len bs (Some sg) =
  if negb (little (sublist 4 8 bs) =? len) || negb (sig_at bs 0 sg) then S_SDT_ENVELOPE
  else if negb ((fold_left Z.add (sublist 0 len bs) 0) mod 256 =? 0) then S_SDT_CHECKSUM
  else S_OK.
Proof.
  intros len bs sg L S. unfold validate, signature_matches, sig_at.
  replace (len <? HEADER_BYTES) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (HEADER_BYTES <=? len) with true by (symmetry; apply Z.leb_le; lia).
  rewrite checksum_sum. cbn [orb andb Z.add]. reflexivity.
Qed.

Lemma decode_entries_c: forall x len, (i_kind x = 1 \/ i_kind x = 2) -> HEADER_BYTES <= len ->
  decode_entries (i_kind x) len =
  if negb ((len - HEADER_BYTES) mod rc_w x =? 0) then inl S_ROOT_WIDTH
  else if MAX_ENTRIES <? (len - HEADER_BYTES) / rc_w x then inl S_ROOT_ENTRIES
  else inr ((len - HEADER_BYTES) / rc_w x, rc_w x).
Proof.
  intros x len K L. unfold decode_entries, rc_w.
  destruct K as [K | K]; rewrite K; simpl Z.eqb; cbv iota;
    replace (len <? HEADER_BYTES) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity.
Qed.

Lemma rc_w_range: forall x, rc_w x = 4 \/ rc_w x = 8.
Proof. intros. unfold rc_w. destruct (i_kind x =? 1); auto. Qed.

(* Entry e of the root's entry vector, read from the root's bytes. *)
Lemma entry_at_root: forall bs w e, 0 <= e -> 0 < w -> HEADER_BYTES + e * w + w <= Zlength bs ->
  entry_at (sublist HEADER_BYTES (Zlength bs) bs) w e =
  little (sublist (HEADER_BYTES + e * w) (HEADER_BYTES + e * w + w) bs).
Proof.
  intros. unfold entry_at. rewrite sublist_sublist by (unfold HEADER_BYTES in *; nia).
  f_equal. f_equal; lia.
Qed.

Lemma decode_from_inr: forall vec w es pre addrs, Forall byte_ok vec -> decode_from vec w es pre = inr addrs ->
  Forall (fun a => 0 < a <= MAX_U32) pre ->
  Forall (fun a => 0 < a <= MAX_U32) addrs /\ Zlength addrs = Zlength pre + Zlength es.
Proof.
  intros vec w es. induction es as [ | e es IH]; intros pre addrs Fv D F; simpl in D.
  - inversion D; subst. rewrite Zlength_nil. split; [ auto | lia ].
  - destruct ((entry_at vec w e =? 0) || (MAX_U32 <? entry_at vec w e)) eqn:B; [ discriminate | ].
    destruct (existsb (Z.eqb (entry_at vec w e)) pre); [ discriminate | ].
    apply orb_false_iff in B as [B1 B2]. apply Z.eqb_neq in B1. apply Z.ltb_ge in B2.
    destruct (IH _ _ Fv D) as [F' L'].
    + apply Forall_app; split; auto. constructor; [ | constructor ].
      assert (0 <= entry_at vec w e).
      { unfold entry_at. apply little_bound. apply Forall_sublist; auto. }
      lia.
    + split; auto. rewrite L', Zlength_app, Zlength_cons, Zlength_cons, Zlength_nil. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* The outcomes of root_copied                                             *)
(* ---------------------------------------------------------------------- *)

Lemma rc_common: forall x pl re te s m len cursor, rc_pre x pl re te s m len cursor ->
  lst_ok (rc_s1 s len cursor) /\ mem_fit x (rc_m1 x m len cursor) /\
  mem_rel x (rc_s1 s len cursor) (rc_m1 x m len cursor) /\
  m_root (rc_m1 x m len cursor) = m_root m /\ m_entries m = None /\ m_slots m = nil /\ w_arena s = 0 /\
  w_ordinal s = 0 /\ (i_kind x = 1 \/ i_kind x = 2).
Proof.
  intros x pl re te s m len cursor (L & F & R & SI & TI & Ln & Cu & LO & I & _).
  unfold tgt_inv in TI. destruct TI as (K & A & T1 & T2 & T3 & T4 & T5).
  unfold len_ok in LO. cbn [capacity_of] in LO.
  assert (Rr: root_capacity x <= Int.max_unsigned) by (destruct I as (_ & _ & _ & I4 & _); auto).
  split; [ unfold rc_s1; subst; lst_ok_tac | ].
  split; [ unfold mem_fit in *; simpl; auto | ].
  split.
  { unfold mem_rel, slot_of, rc_s1, rc_m1 in *. simpl. lst_cbn. rewrite T1, T2, T3 in *. simpl in R.
    destruct R as (R1 & R2 & R3 & R4 & R5). csplit; auto; try (subst; reflexivity). }
  auto 10.
Qed.

Lemma rc_ret1: forall x pl re te s m len cursor st, rc_pre x pl re te s m len cursor ->
  validate len (m_root m) (Some (rc_sig x)) = st -> st <> S_OK -> 0 < st < VERDICT_TABLES ->
  J x pl re te (root_copied x len cursor m) (s_stop (rc_s1 s len cursor) st).
Proof.
  intros x pl re te s m len cursor st P V N B. pose proof (rc_common _ _ _ _ _ _ _ _ P) as (C1 & C2 & C3 & C4 & _).
  unfold root_copied. cbv zeta. fold (rc_m1 x m len cursor). rewrite C4. fold (rc_sig x). rewrite V.
  rewrite (proj2 (Z.eqb_neq st S_OK) N). simpl negb. cbv iota.
  apply J_stop; auto.
Qed.

Lemma rc_ret2: forall x pl re te s m len cursor st, rc_pre x pl re te s m len cursor ->
  validate len (m_root m) (Some (rc_sig x)) = S_OK -> decode_entries (i_kind x) len = inl st ->
  0 < st < VERDICT_TABLES ->
  J x pl re te (root_copied x len cursor m) (s_stop (rc_s1 s len cursor) st).
Proof.
  intros x pl re te s m len cursor st P V D B. pose proof (rc_common _ _ _ _ _ _ _ _ P) as (C1 & C2 & C3 & C4 & _).
  unfold root_copied. cbv zeta. fold (rc_m1 x m len cursor). rewrite C4. fold (rc_sig x). rewrite V.
  simpl negb. cbv iota. rewrite D.
  apply J_stop; auto.
Qed.

Lemma rc_s2_ok: forall x pl re te s m len cursor count w A, rc_pre x pl re te s m len cursor ->
  decode_entries (i_kind x) len = inr (count, w) -> Zlength A = MAX_ENTRIES -> Forall u64_ok A ->
  lst_ok (set_addresses (rc_s2 s len cursor count w) A) /\
  mem_fit x (set_entries (rc_m1 x m len cursor) count w) /\
  mem_rel x (set_addresses (rc_s2 s len cursor count w) A) (set_entries (rc_m1 x m len cursor) count w).
Proof.
  intros x pl re te s m len cursor count w A P D LA FA.
  pose proof (rc_common _ _ _ _ _ _ _ _ P) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
  assert (Rw: (count, w) = ((len - HEADER_BYTES) / rc_w x, rc_w x) /\ count <= MAX_ENTRIES /\ 0 <= count).
  { destruct P as (_ & _ & _ & _ & TI & _ & _ & LO & _). unfold len_ok in LO.
    rewrite decode_entries_c in D by (auto || lia).
    destruct (negb _); [ discriminate | ]. destruct (MAX_ENTRIES <? _) eqn:E; [ discriminate | ].
    apply Z.ltb_ge in E. injection D as D1 D2. subst count w. split; [ reflexivity | ]. split; [ exact E | ].
    apply Z.div_pos; [ lia | ]. destruct (rc_w_range x) as [W | W]; rewrite W; lia. }
  destruct Rw as (Rw & Rc & R0). injection Rw as Rw1 Rw2.
  split.
  { unfold rc_s2. clear C3. lst_ok_tac; try (rewrite Rw2; destruct (rc_w_range x) as [W | W]; rewrite W; u32_tac). }
  split; [ unfold mem_fit in *; simpl; auto | ].
  unfold mem_rel, slot_of, rc_s2 in *. simpl. lst_cbn. destruct C3 as (R1 & R2 & R3 & R4 & R5).
  simpl in R1, R2, R3, R4, R5. csplit; auto.
  intros t Ht. rewrite C6, Zlength_nil in Ht. lia.
Qed.

Lemma rc_ret3: forall x pl re te s m len cursor count w st A, rc_pre x pl re te s m len cursor ->
  validate len (m_root m) (Some (rc_sig x)) = S_OK -> decode_entries (i_kind x) len = inr (count, w) ->
  decode_addresses (sublist HEADER_BYTES (Zlength (m_root m)) (m_root m)) w count = inl st ->
  0 < st < VERDICT_TABLES -> Zlength A = MAX_ENTRIES -> Forall u64_ok A ->
  J x pl re te (root_copied x len cursor m) (s_stop (set_addresses (rc_s2 s len cursor count w) A) st).
Proof.
  intros x pl re te s m len cursor count w st A P V D DA B LA FA.
  pose proof (rc_common _ _ _ _ _ _ _ _ P) as (C1 & C2 & C3 & C4 & _).
  pose proof (rc_s2_ok _ _ _ _ _ _ _ _ _ _ A P D LA FA) as (S1 & S2 & S3).
  unfold root_copied. cbv zeta. fold (rc_m1 x m len cursor). rewrite C4. fold (rc_sig x). rewrite V.
  simpl negb. cbv iota. rewrite D.
  replace (m_root (set_entries (rc_m1 x m len cursor) count w)) with (m_root m) by (rewrite <- C4; reflexivity).
  rewrite DA.
  apply J_stop; auto.
Qed.

Lemma rc_seq: forall x pl re te s m len cursor w A, rc_pre x pl re te s m len cursor ->
  validate len (m_root m) (Some (rc_sig x)) = S_OK -> decode_entries (i_kind x) len = inr (0, w) ->
  Zlength A = MAX_ENTRIES -> Forall u64_ok A ->
  J x pl re te (root_copied x len cursor m) (s_stop (set_addresses (rc_s2 s len cursor 0 w) A) S_SEQUENCE).
Proof.
  intros x pl re te s m len cursor w A P V D LA FA.
  pose proof (rc_common _ _ _ _ _ _ _ _ P) as (C1 & C2 & C3 & C4 & _).
  pose proof (rc_s2_ok _ _ _ _ _ _ _ _ _ _ A P D LA FA) as (S1 & S2 & S3).
  unfold root_copied. cbv zeta. fold (rc_m1 x m len cursor). rewrite C4. fold (rc_sig x). rewrite V.
  simpl negb. cbv iota. rewrite D.
  unfold decode_addresses. change (range 0) with (@nil Z). simpl decode_from. cbv iota.
  unfold tables_start. simpl.
  apply J_stop; auto. unfold S_SEQUENCE, VERDICT_TABLES. lia.
Qed.

Lemma rc_tables: forall x pl re te s m len cursor count w addrs, rc_pre x pl re te s m len cursor ->
  validate len (m_root m) (Some (rc_sig x)) = S_OK -> decode_entries (i_kind x) len = inr (count, w) ->
  decode_addresses (sublist HEADER_BYTES (Zlength (m_root m)) (m_root m)) w count = inr addrs -> 0 < count ->
  J x pl re te (root_copied x len cursor m)
    (bt_state x pl te (set_addresses (rc_s2 s len cursor count w) (addrs ++ sublist count MAX_ENTRIES (w_addresses s)))
       0).
Proof.
  intros x pl re te s m len cursor count w addrs P V D DA Cp.
  pose proof (rc_common _ _ _ _ _ _ _ _ P) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
  assert (Fv: Forall byte_ok (sublist HEADER_BYTES (Zlength (m_root m)) (m_root m))).
  { destruct P as (_ & F & _). destruct F as (_ & _ & _ & _ & F5 & _). apply Forall_sublist; auto. }
  destruct (decode_from_inr _ _ _ _ _ Fv DA (Forall_nil _)) as [Fa La].
  rewrite Zlength_nil, Zlength_range in La by lia.
  assert (Rc: count <= MAX_ENTRIES).
  { destruct P as (_ & _ & _ & _ & TI & _ & _ & LO & _). unfold len_ok in LO.
    rewrite decode_entries_c in D by (auto || lia).
    destruct (negb _); [ discriminate | ]. destruct (MAX_ENTRIES <? _) eqn:E; [ discriminate | ].
    apply Z.ltb_ge in E. injection D as D1 D2. subst count w. exact E. }
  assert (LA: Zlength (w_addresses s) = MAX_ENTRIES) by (destruct P as (L & _); unfold lst_ok in L; tauto).
  assert (FA: Forall u64_ok (w_addresses s)) by (destruct P as (L & _); unfold lst_ok in L; tauto).
  assert (LA': Zlength (addrs ++ sublist count MAX_ENTRIES (w_addresses s)) = MAX_ENTRIES)
    by (rewrite Zlength_app, Zlength_sublist by lia; lia).
  assert (FA': Forall u64_ok (addrs ++ sublist count MAX_ENTRIES (w_addresses s))).
  { apply Forall_app; split; [ | apply Forall_sublist; auto ].
    eapply Forall_impl; [ | exact Fa ]. intros a Ha. unfold u64_ok, MAX_U32 in *. rep_lia. }
  pose proof (rc_s2_ok _ _ _ _ _ _ _ _ _ _ _ P D LA' FA') as (S1 & S2 & S3).
  unfold root_copied. cbv zeta. fold (rc_m1 x m len cursor). rewrite C4. fold (rc_sig x). rewrite V.
  simpl negb. cbv iota. rewrite D.
  replace (m_root (set_entries (rc_m1 x m len cursor) count w)) with (m_root m) by (rewrite <- C4; reflexivity).
  rewrite DA. unfold tables_start.
  replace (Zlength addrs =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace 0 with (l_entry (mk_tloop addrs 0 0 0)) at 2 by reflexivity.
  apply J_begin_table; auto.
  - destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & I & _). auto.
  - unfold loop_inv, rc_s2, rc_s1. lst_cbn. cbn [l_addresses l_entry l_offset l_ordinal]. simpl m_slots.
    rewrite C6. rewrite La. csplit; auto; try lia.
    + rewrite sublist_app1 by lia. rewrite sublist_same by lia. reflexivity.
    + reflexivity.
    + destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & I & _). destruct I as (_ & _ & _ & _ & I5 & _).
      unfold table_capacity. pose proof (Zlength_nonneg (i_tables x)). lia.
Qed.
