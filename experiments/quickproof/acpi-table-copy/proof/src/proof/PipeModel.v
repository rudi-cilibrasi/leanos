(* Lemmas about the model of Defs.v for the body proofs (Pipe*.v): the run one answer at a time, the steps of
   acpi_copy_sdt (the header, the body, the stream chunk) and of the table loop, and what the copies leave in the
   mem (its regions, mem_ok, copy_frame). *)
Require Import VST.floyd.proofauto.
Require Import LeanosAcpi.acpi.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.InternalSpecs.
Require Import LeanosAcpi.proof.PipeLemmas.
#[local] Existing Instance AcpiSpecs.CS.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* ---------- the run, one answer at a time ---------- *)

Lemma run_snoc': forall x p hs s m r, run x p hs = Some (Go s m) -> fits (expected x s) r = true ->
  run x p (hs ++ [(expected x s, r)]) = Some (step x s m r).
Proof.
  intros. rewrite run_app, H. simpl. rewrite call_eqb_refl, H0. reflexivity.
Qed.

Lemma run_glue: forall x h p hs q, run x (start x) h = Some p -> run x p hs = Some q ->
  run x (start x) (h ++ hs) = Some q.
Proof. intros. rewrite run_app, H. exact H0. Qed.

Lemma next_call_go: forall x hh s m, run x (start x) hh = Some (Go s m) -> next_call x hh = Some (expected x s).
Proof. intros. unfold next_call. rewrite H. reflexivity. Qed.

(* The call of stage s after h ++ hs, when the copy started at p after h. *)
Lemma next_call_at: forall x h p hs s m, run x (start x) h = Some p -> run x p hs = Some (Go s m) ->
  next_call x (h ++ hs) = Some (expected x s).
Proof. intros. eapply next_call_go. eapply run_glue; eauto. Qed.

Lemma holds_at: forall x h p hs s m d n, run x (start x) h = Some p -> run x p hs = Some (Go s m) ->
  holds x (h ++ hs) d n = region m d n.
Proof. intros. eapply holds_run. eapply run_glue; eauto. Qed.

Lemma fits_word: forall c v, (match c with Copy _ _ _ => False | _ => True end) -> fits c (Word v) = true.
Proof. intros [ ] v H; simpl in *; tauto. Qed.

Lemma fits_copy: forall a d len ret bs, Zlength bs = len -> fits (Copy a d len) (Copied ret bs) = true.
Proof. intros. simpl. apply Z.eqb_eq. auto. Qed.

(* ---------- acpi_copy_sdt ---------- *)

Lemma begin_sdt_go: forall x g m, address_of x g <= MAX_U32 -> begin_sdt x g m = Go (Copying g CHeader) m.
Proof. intros. unfold begin_sdt. rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity. Qed.

Lemma begin_sdt_fail: forall x g m, MAX_U32 < address_of x g ->
  begin_sdt x g m = Return S_SDT_ADDRESS_WIDTH None m.
Proof. intros. unfold begin_sdt. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.

Lemma step_header: forall x g m ret hb,
  step x (Copying g CHeader) m (Copied ret hb) =
  (if ret =? 0 then Return S_PHYSICAL None (write m DHeader hb)
   else if (little (sublist 4 8 hb) <? HEADER_BYTES) || (MAX_SDT_BYTES <? little (sublist 4 8 hb)) ||
           (capacity_of x g <? little (sublist 4 8 hb))
   then Return S_SDT_LENGTH None (write m DHeader hb)
   else Go (Copying g (CBody (little (sublist 4 8 hb)))) (write m DHeader hb)).
Proof. reflexivity. Qed.

Lemma step_body: forall x g m len ret bs,
  step x (Copying g (CBody len)) m (Copied ret bs) =
  (if ret =? 0 then Return S_PHYSICAL None (write m (dest_of g) bs)
   else Go (Copying g (CChunk len bs (cursor_of g) 0 nil)) (write m (dest_of g) bs)).
Proof. reflexivity. Qed.

Lemma step_chunk_more: forall x g m len bs cursor byte cur v, Zlength cur < 4 ->
  step x (Copying g (CChunk len bs cursor byte cur)) m (Word v) =
  Go (Copying g (CChunk len bs cursor byte (cur ++ [v]))) m.
Proof.
  intros. unfold step. cbv zeta. rewrite (proj2 (Z.ltb_lt _ _)) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  reflexivity.
Qed.

Lemma step_chunk_last: forall x g m len bs cursor byte s e nb em ex,
  step x (Copying g (CChunk len bs cursor byte [s; e; nb; em])) m (Word ex) =
  (let n := chunk_bytes len byte in
   let last := terminal len byte in
   let st := transition [s; e; nb; em; ex] (little (sublist byte (byte + n) bs)) cursor byte n last in
   if negb (st =? S_OK) then Return st None m
   else
     let cursor' := if last =? 0 then cursor else em in
     if nb <? len then Go (Copying g (CChunk len bs cursor' nb nil)) m
     else sdt_copied x g len cursor' m).
Proof. reflexivity. Qed.

Lemma transition_eq: forall s e nb em ex chunk cursor byte n last,
  transition [s; e; nb; em; ex] chunk cursor byte n last =
  if e =? 43 then S_BUDGET
  else if e =? 44 then S_LENGTH
  else if e =? 45 then S_ADDRESS
  else if e =? 46 then S_OFFSET
  else if e =? 47 then S_TERMINAL
  else if negb (e =? 0) then S_ERROR
  else if negb (s =? 1) then S_STATUS
  else if negb (nb =? byte + n) then S_NEXT_BYTE
  else if negb (ex =? chunk) then S_EXPOSED
  else if (last =? 0) && negb (em =? cursor) then S_PARTIAL_CURSOR
  else if negb (last =? 0) && (em <=? cursor) then S_FINAL_CURSOR
  else S_OK.
Proof. reflexivity. Qed.

Lemma stream_word_0: stream_word 0 = 1. Proof. reflexivity. Qed.
Lemma stream_word_1: stream_word 1 = 2. Proof. reflexivity. Qed.
Lemma stream_word_2: stream_word 2 = 4. Proof. reflexivity. Qed.
Lemma stream_word_3: stream_word 3 = 5. Proof. reflexivity. Qed.
Lemma stream_word_4: stream_word 4 = 6. Proof. reflexivity. Qed.

Lemma chunk_bytes_range: forall len byte, byte < len -> 1 <= chunk_bytes len byte <= 8.
Proof. intros. unfold chunk_bytes. lia. Qed.

(* ---------- the mem of a copy ---------- *)


(* Where the arena of g lies in the mem, and its bounds. *)
Definition dest_fits (x: inputs) (g: target) : Prop :=
  match g with TRoot => True | TTable l => 0 <= l_offset l < table_capacity x end.

Ltac msimpl := cbn [capacity_of dest_of region cursor_of write m_header m_root m_tables m_root_copy m_entries m_slots
                    copy_frame dest_fits offset_of base_of dest_ptr] in *.

Lemma capacity_range: forall x g, inputs_ok x -> dest_fits x g -> 0 <= capacity_of x g <= Int.max_unsigned.
Proof.
  intros x g I D. destruct I as (_ & _ & _ & R & T & _). destruct g as [ | l]; msimpl.
  - unfold root_capacity in *. pose proof (Zlength_nonneg (i_root x)). lia.
  - lia.
Qed.

Lemma cursor_range: forall x g, inputs_ok x -> dest_fits x g -> 0 <= cursor_of g <= Int.max_unsigned.
Proof.
  intros x g I D. destruct I as (_ & _ & _ & R & T & _). destruct g as [ | l]; msimpl; rep_lia.
Qed.

Lemma region_header: forall m hb g n, region (write m DHeader hb) (dest_of g) n = region m (dest_of g) n.
Proof. intros. destruct g; reflexivity. Qed.

Lemma Zlength_region: forall x m g, mem_ok x m -> dest_fits x g ->
  Zlength (region m (dest_of g) (capacity_of x g)) = capacity_of x g.
Proof.
  intros x m g M D. destruct M as (_ & MR & MT & _). destruct g as [ | l]; msimpl.
  - rewrite sublist_same by (unfold root_capacity in *; lia). unfold root_capacity in *; lia.
  - rewrite Zlength_sublist by lia. lia.
Qed.

Lemma Forall_region: forall x m g n, mem_ok x m -> Forall byte_ok (region m (dest_of g) n).
Proof.
  intros x m g n M. destruct M as (_ & _ & _ & _ & FR & FT). destruct g; msimpl; apply Forall_sublist; auto.
Qed.

Lemma region_prefix: forall x m g len, mem_ok x m -> dest_fits x g -> 0 <= len <= capacity_of x g ->
  sublist 0 len (region m (dest_of g) (capacity_of x g)) = region m (dest_of g) len.
Proof.
  intros x m g len M D L. destruct M as (_ & MR & MT & _). destruct g as [ | l]; msimpl.
  - unfold root_capacity in *. rewrite sublist_sublist by lia. f_equal; lia.
  - rewrite sublist_sublist by lia. f_equal; lia.
Qed.

Lemma region_write: forall x m g bs, mem_ok x m -> dest_fits x g -> Zlength bs <= capacity_of x g ->
  region (write m (dest_of g) bs) (dest_of g) (capacity_of x g) =
  bs ++ sublist (Zlength bs) (capacity_of x g) (region m (dest_of g) (capacity_of x g)).
Proof.
  intros x m g bs M D L. pose proof (Zlength_nonneg bs).
  destruct M as (_ & MR & MT & _). destruct g as [ | l]; msimpl; unfold overlay, root_capacity in *.
  - list_solve.
  - list_solve.
Qed.

Lemma mem_ok_header: forall x m hb, mem_ok x m -> Zlength hb = HEADER_BYTES -> Forall byte_ok hb ->
  mem_ok x (write m DHeader hb).
Proof. intros x m hb (A & B & C & D & E & F) L H. repeat split; msimpl; auto. Qed.

Lemma Zlength_overlay: forall off bs l, 0 <= off -> off + Zlength bs <= Zlength l -> Zlength (overlay off bs l) = Zlength l.
Proof.
  intros. unfold overlay. pose proof (Zlength_nonneg bs). rewrite !Zlength_app, !Zlength_sublist by lia. lia.
Qed.

Lemma Forall_overlay: forall off bs l, Forall byte_ok bs -> Forall byte_ok l -> Forall byte_ok (overlay off bs l).
Proof. intros. unfold overlay. apply Forall_app; split; [ apply Forall_sublist; auto | apply Forall_app; split; auto ].
  apply Forall_sublist; auto. Qed.

Lemma mem_ok_dest: forall x m g bs, mem_ok x m -> dest_fits x g -> Zlength bs <= capacity_of x g ->
  Forall byte_ok bs -> mem_ok x (write m (dest_of g) bs).
Proof.
  intros x m g bs (A & B & C & D & E & F) G L H. pose proof (Zlength_nonneg bs).
  destruct g as [ | l]; msimpl; unfold root_capacity in *; repeat split; msimpl; auto.
  - rewrite Zlength_overlay by lia. auto.
  - apply Forall_overlay; auto.
  - rewrite Zlength_overlay by lia. auto.
  - apply Forall_overlay; auto.
Qed.

Lemma copy_frame_refl: forall g m, copy_frame g m m.
Proof. intros. unfold copy_frame. destruct g; repeat split; auto. Qed.

Lemma copy_frame_header: forall g m hb, Zlength hb = Zlength (m_header m) -> copy_frame g m (write m DHeader hb).
Proof. intros. unfold copy_frame. destruct g; msimpl; repeat split; auto. Qed.

Lemma copy_frame_dest: forall x m g hb bs, mem_ok x m -> dest_fits x g -> Zlength bs <= capacity_of x g ->
  Zlength hb = Zlength (m_header m) ->
  copy_frame g m (write (write m DHeader hb) (dest_of g) bs).
Proof.
  intros x m g hb bs (A & B & C & _) G L H. pose proof (Zlength_nonneg bs).
  unfold copy_frame. destruct g as [ | l]; msimpl; unfold root_capacity in *; repeat split; msimpl; auto.
  - rewrite Zlength_overlay by lia. auto.
  - rewrite Zlength_overlay by lia. auto.
  - unfold overlay. rewrite sublist_app1 by (rewrite ?Zlength_sublist by lia; lia).
    rewrite sublist_sublist by lia. f_equal; lia.
Qed.

Lemma dest_base: forall pl g, isptr (dest_ptr pl (dest_of g)) ->
  offset_val (offset_of g) (base_of pl g) = dest_ptr pl (dest_of g).
Proof. intros. destruct g; simpl in *; [ apply isptr_offset_val_zero; auto | reflexivity ]. Qed.

Lemma run_one: forall x s m r, fits (expected x s) r = true -> run x (Go s m) [(expected x s, r)] = Some (step x s m r).
Proof. intros. simpl. rewrite call_eqb_refl, H. reflexivity. Qed.

Lemma run_nil: forall x p, run x p [] = Some p.
Proof. reflexivity. Qed.

Lemma if_false_eq: forall {A} (a b: A), (if false then a else b) = b.
Proof. reflexivity. Qed.

Lemma if_true_eq: forall {A} (a b: A), (if true then a else b) = a.
Proof. reflexivity. Qed.

Lemma m_header_write_header: forall m hb, m_header (write m DHeader hb) = hb.
Proof. reflexivity. Qed.

Lemma m_header_write_dest: forall m g bs, m_header (write m (dest_of g) bs) = m_header m.
Proof. intros. destruct g; reflexivity. Qed.

Lemma holds_header: forall x h s m, mem_ok x m -> run x (start x) h = Some (Go s m) ->
  holds x h DHeader HEADER_BYTES = m_header m.
Proof.
  intros x h s m M R. rewrite (holds_run x h s m DHeader HEADER_BYTES R). simpl.
  destruct M as (L & _). rewrite sublist_same by lia. reflexivity.
Qed.

Lemma copy_frame_write: forall x m m1 g bs, mem_ok x m1 -> dest_fits x g -> Zlength bs <= capacity_of x g ->
  copy_frame g m m1 -> copy_frame g m (write m1 (dest_of g) bs).
Proof.
  intros x m m1 g bs (A & B & C & _) G L F. pose proof (Zlength_nonneg bs).
  unfold copy_frame in *. destruct g as [ | l]; msimpl; unfold root_capacity in *.
  - destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7). repeat split; auto.
    rewrite Zlength_overlay by lia. auto.
  - destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8). repeat split; auto.
    + rewrite Zlength_overlay by lia. auto.
    + rewrite <- F8. unfold overlay. rewrite sublist_app1 by (rewrite ?Zlength_sublist by lia; lia).
      rewrite sublist_sublist by lia. f_equal; lia.
Qed.

Lemma split2_region: forall sh x m g bs p, mem_ok x m -> dest_fits x g -> Zlength bs <= capacity_of x g ->
  field_compatible (tarray tuchar (capacity_of x g)) [] p ->
  data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) p *
  data_at sh (tarray tuchar (capacity_of x g - Zlength bs))
    (bytes_val (sublist (Zlength bs) (capacity_of x g) (region m (dest_of g) (capacity_of x g))))
    (offset_val (Zlength bs) p)
  |-- data_at sh (tarray tuchar (capacity_of x g))
        (bytes_val (region (write m (dest_of g) bs) (dest_of g) (capacity_of x g))) p.
Proof.
  intros. pose proof (Zlength_nonneg bs). pose proof (Zlength_region x m g H H0).
  rewrite (split2_bytes sh _ (capacity_of x g) (Zlength bs)); auto;
    try (rewrite region_write by auto; rewrite Zlength_app, Zlength_sublist by lia; lia); try lia.
  rewrite region_write by auto.
  set (X := sublist (Zlength bs) (capacity_of x g) (region m (dest_of g) (capacity_of x g))).
  assert (LX: Zlength X = capacity_of x g - Zlength bs) by (unfold X; rewrite Zlength_sublist by lia; lia).
  replace (sublist 0 (Zlength bs) (bs ++ X)) with bs by list_solve.
  replace (sublist (Zlength bs) (capacity_of x g) (bs ++ X)) with X by list_solve.
  apply derives_refl.
Qed.

Lemma region_body: forall x m g bs, mem_ok x m -> dest_fits x g -> Zlength bs <= capacity_of x g ->
  sublist 0 (Zlength bs) (region (write m (dest_of g) bs) (dest_of g) (capacity_of x g)) = bs.
Proof.
  intros. pose proof (Zlength_nonneg bs). pose proof (Zlength_region x m g H H0).
  rewrite region_write by auto. rewrite sublist_app1 by lia. apply sublist_same; lia.
Qed.

Lemma Znth_prefix: forall (L bs: list Z) n i, sublist 0 n L = bs -> 0 <= i < n -> n <= Zlength L ->
  Znth i L = Znth i bs.
Proof. intros. subst bs. rewrite Znth_sublist by lia. f_equal; lia. Qed.

Lemma stream_more: forall x p hs g len bs cursor byte cur m v c,
  run x p hs = Some (Go (Copying g (CChunk len bs cursor byte cur)) m) -> Zlength cur < 4 ->
  c = expected x (Copying g (CChunk len bs cursor byte cur)) ->
  run x p (hs ++ [(c, Word v)]) = Some (Go (Copying g (CChunk len bs cursor byte (cur ++ [v]))) m).
Proof.
  intros. subst c. rewrite (run_snoc' x p hs _ _ (Word v) H) by reflexivity. rewrite step_chunk_more by auto.
  reflexivity.
Qed.

Lemma stream_last: forall x p hs g len bs cursor byte s e nb em m ex c,
  run x p hs = Some (Go (Copying g (CChunk len bs cursor byte [s; e; nb; em])) m) ->
  c = expected x (Copying g (CChunk len bs cursor byte [s; e; nb; em])) ->
  run x p (hs ++ [(c, Word ex)]) = Some (step x (Copying g (CChunk len bs cursor byte [s; e; nb; em])) m (Word ex)).
Proof. intros. subst c. apply (run_snoc' x p hs _ _ (Word ex) H). reflexivity. Qed.

Lemma terminal_word: forall byte n len, 0 <= byte -> 0 <= n <= Int.max_unsigned -> 0 <= len <= Int.max_unsigned ->
  byte + n <= Int.max_unsigned ->
  Int64.repr (Int.signed (Int.repr (Z.b2z (Int64.cmpu Ceq (Int64.add (Int64.repr byte) (Int64.repr (Int.unsigned (Int.repr n))))
                                             (Int64.repr (Int.unsigned (Int.repr len))))))) =
  Int64.repr (if byte + n =? len then 1 else 0).
Proof.
  intros. rewrite !Int.unsigned_repr by auto. rewrite add64_repr. unfold Int64.cmpu.
  rewrite eq64_repr by (unfold u64_ok; rep_lia). destruct (byte + n =? len); reflexivity.
Qed.

Lemma terminal_word2: forall byte n len, n = chunk_bytes len byte -> 0 <= byte -> 0 <= n <= Int.max_unsigned ->
  0 <= len <= Int.max_unsigned -> byte + n <= Int.max_unsigned ->
  Int64.repr (Int.signed (Int.repr (Z.b2z (Int64.cmpu Ceq (Int64.add (Int64.repr byte) (Int64.repr (Int.unsigned (Int.repr n))))
                                             (Int64.repr (Int.unsigned (Int.repr len))))))) =
  Int64.repr (terminal len byte).
Proof. intros. rewrite terminal_word by auto. unfold terminal. subst n. reflexivity. Qed.

(* ---------- acpi_copy_root_tables ---------- *)

Lemma tables_start_go: forall x addresses m, Zlength addresses <> 0 ->
  tables_start x addresses m = begin_table x (mk_tloop addresses 0 0 0) m.
Proof. intros. unfold tables_start. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.

Lemma tables_start_nil: forall x addresses m, Zlength addresses = 0 ->
  tables_start x addresses m = Return S_SEQUENCE None m.
Proof. intros. unfold tables_start. rewrite H. reflexivity. Qed.

Lemma begin_table_go: forall x l m, l_offset l < table_capacity x -> begin_table x l m = begin_sdt x (TTable l) m.
Proof. intros. unfold begin_table. rewrite (proj2 (Z.leb_gt _ _) H). reflexivity. Qed.

Lemma begin_table_fail: forall x l m, table_capacity x <= l_offset l -> begin_table x l m = Return S_BUDGET None m.
Proof. intros. unfold begin_table. rewrite (proj2 (Z.leb_le _ _) H). reflexivity. Qed.

Lemma sdt_copied_table: forall x l len cursor m, sdt_copied x (TTable l) len cursor m = table_copied x l len cursor m.
Proof. reflexivity. Qed.

Lemma table_copied_eq: forall x l len cursor m,
  table_copied x l len cursor m =
  (if table_capacity x - l_offset l <? padded len
   then Return S_BUDGET None (add_slot m (mk_sdt (Znth (l_entry l) (l_addresses l)) (l_offset l) len (cursor mod 2 ^ 32)))
   else if negb (cursor mod 2 ^ 32 =? l_offset l + padded len)
   then Return S_STREAM None (add_slot m (mk_sdt (Znth (l_entry l) (l_addresses l)) (l_offset l) len (cursor mod 2 ^ 32)))
   else Go (Sequencing (set_offset l (l_offset l + padded len)) nil)
          (add_slot m (mk_sdt (Znth (l_entry l) (l_addresses l)) (l_offset l) len (cursor mod 2 ^ 32)))).
Proof. reflexivity. Qed.

Lemma seq_more: forall x p hs l cur m v c, run x p hs = Some (Go (Sequencing l cur) m) -> Zlength cur < 2 ->
  c = expected x (Sequencing l cur) ->
  run x p (hs ++ [(c, Word v)]) = Some (Go (Sequencing l (cur ++ [v])) m).
Proof.
  intros. subst c. rewrite (run_snoc' x p hs _ _ (Word v) H) by reflexivity. unfold step. cbv zeta.
  rewrite (proj2 (Z.ltb_lt _ _)) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; simpl reply_value; lia).
  reflexivity.
Qed.

Lemma seq_last: forall x p hs l a b m c v, run x p hs = Some (Go (Sequencing l [a; b]) m) ->
  c = expected x (Sequencing l [a; b]) ->
  run x p (hs ++ [(c, Word v)]) =
  Some (if negb (a =? 1) || negb (b =? 0) || negb (v =? l_entry l + 1) then Return S_SEQUENCE None m
        else if l_entry l + 1 <? Zlength (l_addresses l) then begin_table x (next_entry (set_ordinal l v)) m
        else tables_done (Zlength (l_addresses l)) m).
Proof. intros. subst c. rewrite (run_snoc' x p hs _ _ (Word v) H) by reflexivity. reflexivity. Qed.

Lemma slot_ok_len: forall T T' s, Zlength T = Zlength T' -> slot_ok T s -> slot_ok T' s.
Proof. unfold slot_ok. intros. rewrite <- H. auto. Qed.

Lemma Forall_slot_ok_len: forall T T' ss, Zlength T = Zlength T' -> Forall (slot_ok T) ss -> Forall (slot_ok T') ss.
Proof. intros. eapply Forall_impl; [ | eauto ]. intros. eapply slot_ok_len; eauto. Qed.

(* The table arena around the destination of table l: [0, off) and the region from off. *)
Lemma tables_split: forall sh x m off p, mem_ok x m -> 0 <= off <= table_capacity x ->
  field_compatible (tarray tuchar (table_capacity x)) [] p ->
  data_at sh (tarray tuchar (table_capacity x)) (bytes_val (m_tables m)) p =
  (data_at sh (tarray tuchar off) (bytes_val (sublist 0 off (m_tables m))) p *
   data_at sh (tarray tuchar (table_capacity x - off)) (bytes_val (region m (DTables off) (table_capacity x - off)))
     (offset_val off p))%logic.
Proof.
  intros sh x m off p (A & B & C & _) O F. rewrite (split2_bytes sh (m_tables m) (table_capacity x) off) by auto.
  simpl region. replace (off + (table_capacity x - off)) with (table_capacity x) by lia. reflexivity.
Qed.

Lemma tables_join: forall sh x m m' off p, mem_ok x m' -> 0 <= off <= table_capacity x ->
  sublist 0 off (m_tables m') = sublist 0 off (m_tables m) ->
  field_compatible (tarray tuchar (table_capacity x)) [] p ->
  data_at sh (tarray tuchar off) (bytes_val (sublist 0 off (m_tables m))) p *
  data_at sh (tarray tuchar (table_capacity x - off)) (bytes_val (region m' (DTables off) (table_capacity x - off)))
     (offset_val off p)
  |-- data_at sh (tarray tuchar (table_capacity x)) (bytes_val (m_tables m')) p.
Proof.
  intros. rewrite (tables_split sh x m' off p) by auto. rewrite H1. apply derives_refl.
Qed.

Lemma terminal_01: forall len byte, terminal len byte = 0 \/ terminal len byte = 1.
Proof. intros. unfold terminal. destruct (_ =? _); auto. Qed.

Lemma terminal_spec: forall len byte, terminal len byte = 1 <-> byte + chunk_bytes len byte = len.
Proof. intros. unfold terminal. destruct (Z.eqb_spec (byte + chunk_bytes len byte) len); split; intros; auto; lia. Qed.

Ltac tsolve :=
  rewrite transition_eq;
  repeat (first [ rewrite (proj2 (Z.eqb_eq _ _)) by lia
                | rewrite (proj2 (Z.eqb_neq _ _)) by lia
                | rewrite (proj2 (Z.leb_le _ _)) by lia
                | rewrite (proj2 (Z.leb_gt _ _)) by lia ]; cbn [negb andb]);
  reflexivity.
