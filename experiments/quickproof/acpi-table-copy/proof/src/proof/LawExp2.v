(* Law table_copy_exact: the model's step on the answers of the two exports leaves the byte objects of the mem
   (the header scratch and the two arenas) as they were. *)
Require Import VST.floyd.proofauto.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.LawDefs LeanosAcpi.proof.LawFacts LeanosAcpi.proof.LawModel.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Definition same_bytes (m m': mem) : Prop :=
  m_header m' = m_header m /\ m_root m' = m_root m /\ m_tables m' = m_tables m.

Lemma same_bytes_refl: forall m, same_bytes m m.
Proof. intros. repeat split. Qed.

Lemma begin_sdt_bytes: forall x g m, same_bytes m (mem_of (begin_sdt x g m)).
Proof. intros. unfold begin_sdt. destruct (_ <? _); apply same_bytes_refl. Qed.

Lemma begin_table_bytes: forall x l m, same_bytes m (mem_of (begin_table x l m)).
Proof. intros. unfold begin_table. destruct (_ <=? _); [ apply same_bytes_refl | apply begin_sdt_bytes ]. Qed.

Lemma tables_done_bytes: forall c m, same_bytes m (mem_of (tables_done c m)).
Proof. intros. unfold tables_done. destruct (select_madt m); apply same_bytes_refl. Qed.

Ltac sb_tac := unfold same_bytes; cbn [mem_of set_root_copy set_entries add_slot m_header m_root m_tables];
  repeat split.

Lemma root_copied_bytes: forall x len cursor m, same_bytes m (mem_of (root_copied x len cursor m)).
Proof.
  intros. unfold root_copied. cbv zeta.
  destruct (negb _); [ sb_tac | ].
  destruct (decode_entries _ _) as [st | [c w]]; [ sb_tac | ].
  destruct (decode_addresses _ _ _) as [st | a]; [ sb_tac | ].
  unfold tables_start. destruct (_ =? 0); [ sb_tac | ].
  pose proof (begin_table_bytes x (mk_tloop a 0 0 0) (set_entries (set_root_copy m (mk_sdt (i_address x) 0 len (cursor mod 2 ^ 32))) c w)) as B.
  destruct B as (B1 & B2 & B3). unfold same_bytes. rewrite B1, B2, B3. sb_tac.
Qed.

Lemma table_copied_bytes: forall x l len cursor m, same_bytes m (mem_of (table_copied x l len cursor m)).
Proof.
  intros. unfold table_copied. cbv zeta.
  destruct (_ <? _); [ sb_tac | ]. destruct (negb _); sb_tac.
Qed.

Lemma seq_step_bytes: forall x l cur m r, same_bytes m (mem_of (step x (Sequencing l cur) m r)).
Proof.
  intros. unfold step. destruct (_ <? 3); [ apply same_bytes_refl | ].
  destruct (_ || _); [ apply same_bytes_refl | ].
  destruct (_ <? _); [ apply begin_table_bytes | apply tables_done_bytes ].
Qed.

Lemma chunk_step_bytes: forall x g len bs cursor byte cur m r,
  same_bytes m (mem_of (step x (Copying g (CChunk len bs cursor byte cur)) m r)).
Proof.
  intros. unfold step. destruct (_ <? 5); [ apply same_bytes_refl | ]. cbv zeta.
  destruct (negb _); [ apply same_bytes_refl | ].
  destruct (_ <? len); [ apply same_bytes_refl | ].
  destruct g; [ apply root_copied_bytes | apply table_copied_bytes ].
Qed.

Lemma fits_word_stream: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 v, fits (Stream a1 a2 a3 a4 a5 a6 a7 a8 a9) (Word v) = true.
Proof. reflexivity. Qed.

Lemma fits_word_seq: forall a1 a2 a3 a4 a5 a6 v, fits (Sequence a1 a2 a3 a4 a5 a6) (Word v) = true.
Proof. reflexivity. Qed.

(* The chunk the stream export reads, in the expectation arena of g. *)
Lemma dexp_byte: forall re te g byte, isptr re ->
  offset_val byte (dexp_of re te g) = offset_val (cursor_of g + byte) (base_exp re te g).
Proof. intros. destruct g; simpl; [ rewrite Z.add_0_l; reflexivity | rewrite offset_offset_val; reflexivity ]. Qed.

Lemma dexp_isptr: forall re te g, isptr re -> isptr te -> isptr (dexp_of re te g).
Proof. intros. destruct g; simpl; auto. Qed.

Lemma chunk_in_base: forall m g len byte n, 0 <= byte -> 0 <= n -> byte + n <= len -> 0 <= cursor_of g ->
  cursor_of g + len <= Zlength (base_mem m g) ->
  sublist byte (byte + n) (region m (dest_of g) len) =
  sublist (cursor_of g + byte) (cursor_of g + byte + n) (base_mem m g).
Proof.
  intros. rewrite region_base. rewrite sublist_sublist by lia. f_equal; lia.
Qed.

Lemma end_value: forall len byte, 0 <= byte < len ->
  (if len - byte <? 8 then len else byte + 8) = byte + chunk_bytes len byte.
Proof. intros. unfold chunk_bytes. destruct (Z.ltb_spec (len - byte) 8); lia. Qed.

(* LawLib's rw_bools, but never rewriting a constant (which loops). *)
Ltac rwb :=
  repeat match goal with
  | E: ?b = true |- context [?b] =>
      lazymatch b with true => fail | false => fail | _ => match type of b with bool => rewrite E end end
  | E: ?b = false |- context [?b] =>
      lazymatch b with true => fail | false => fail | _ => match type of b with bool => rewrite E end end
  end.
