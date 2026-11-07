(* Law table_copy_exact: the law's oracle as the firmware and the exports re-establish it after an answer, the two
   expectation arenas around the destination of a copy, and the model's step on each kind of answer. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosAcpi.harness.table_copy_exact.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.LawProg LeanosAcpi.proof.LawDefs LeanosAcpi.proof.LawFacts LeanosAcpi.proof.LawLib
  LeanosAcpi.proof.LawModel.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

(* The oracle after the answers h', the law's record s' and the model's p'. *)
Lemma ora_intro: forall gv pl x h' p' s' re te,
  inputs_ok x -> run x (start x) h' = Some p' -> J x pl re te p' s' ->
  isptr (p_header pl) -> isptr (p_root pl) -> isptr (p_tables pl) -> isptr re -> isptr te ->
  (lfields (gv _law) x pl re te (m_header (mem_of p')) s' *
   data_at Ews (tarray tuchar (root_capacity x)) (bytes_val (m_root (mem_of p'))) re *
   data_at Ews (tarray tuchar (table_capacity x)) (bytes_val (m_tables (mem_of p'))) te)%logic
  |-- Ora_law gv (gv _law) pl x h'.
Proof. intros. unfold Ora_law. Exists p' s' re te. entailer!. Qed.

(* The model's step on each answer of the firmware. *)
Lemma step_header_fail: forall x g m, Zlength (m_header m) = HEADER_BYTES ->
  step x (Copying g CHeader) m (Copied 0 (region m DHeader HEADER_BYTES)) = Return S_PHYSICAL None m.
Proof. intros. unfold step. cbn [reply_bytes reply_value]. rewrite write_header_same by auto. reflexivity. Qed.

Lemma step_header_bad: forall x g m ret bs, ret <> 0 -> hdr_bad x g (little (sublist 4 8 bs)) = true ->
  step x (Copying g CHeader) m (Copied ret bs) = Return S_SDT_LENGTH None (write m DHeader bs).
Proof.
  intros. unfold step. cbn [reply_bytes reply_value]. rewrite (proj2 (Z.eqb_neq ret 0) H).
  unfold hdr_bad in H0. rewrite H0. reflexivity.
Qed.

Lemma step_header_ok: forall x g m ret bs, ret <> 0 -> hdr_bad x g (little (sublist 4 8 bs)) = false ->
  step x (Copying g CHeader) m (Copied ret bs) = Go (Copying g (CBody (little (sublist 4 8 bs)))) (write m DHeader bs).
Proof.
  intros. unfold step. cbn [reply_bytes reply_value]. rewrite (proj2 (Z.eqb_neq ret 0) H).
  unfold hdr_bad in H0. rewrite H0. reflexivity.
Qed.

Lemma step_body_fail: forall x g len m, 0 <= len -> cursor_of g + len <= Zlength (base_mem m g) -> 0 <= cursor_of g ->
  step x (Copying g (CBody len)) m (Copied 0 (region m (dest_of g) len)) = Return S_PHYSICAL None m.
Proof. intros. unfold step. cbn [reply_bytes reply_value]. rewrite write_region by auto. reflexivity. Qed.

Lemma step_body_ok: forall x g len m ret bs, ret <> 0 ->
  step x (Copying g (CBody len)) m (Copied ret bs) =
  Go (Copying g (CChunk len bs (cursor_of g) 0 nil)) (write m (dest_of g) bs).
Proof. intros. unfold step. cbn [reply_bytes reply_value]. rewrite (proj2 (Z.eqb_neq ret 0) H). reflexivity. Qed.

(* The expectation arena of the SDT g, and the other one. *)
Definition other_arr (x: inputs) (m: mem) (re te: val) (g: target) : mpred :=
  match g with
  | TRoot => data_at Ews (tarray tuchar (table_capacity x)) (bytes_val (m_tables m)) te
  | TTable _ => data_at Ews (tarray tuchar (root_capacity x)) (bytes_val (m_root m)) re
  end.

Lemma arrays_base: forall x m re te g,
  (data_at Ews (tarray tuchar (root_capacity x)) (bytes_val (m_root m)) re *
   data_at Ews (tarray tuchar (table_capacity x)) (bytes_val (m_tables m)) te)%logic =
  (data_at Ews (tarray tuchar (base_cap x g)) (bytes_val (base_mem m g)) (base_exp re te g) *
   other_arr x m re te g)%logic.
Proof. intros. destruct g; simpl; [ reflexivity | apply sepcon_comm ]. Qed.

Lemma other_write: forall x m re te g bs, other_arr x (write m (dest_of g) bs) re te g = other_arr x m re te g.
Proof. intros. destruct g; reflexivity. Qed.

Lemma base_cap_fit: forall x m g, mem_fit x m -> Zlength (base_mem m g) = base_cap x g.
Proof. intros x m g (A & B & C & _). destruct g; simpl; auto. Qed.

(* The destination of the copy within its expectation arena. *)
Lemma dexp_split: forall g re te N B len, isptr re -> 0 <= cursor_of g -> 0 <= len -> cursor_of g + len <= N ->
  Zlength B = N -> field_compatible (tarray tuchar N) nil (base_exp re te g) ->
  data_at Ews (tarray tuchar N) (bytes_val B) (base_exp re te g) =
  (data_at Ews (tarray tuchar (cursor_of g)) (bytes_val (sublist 0 (cursor_of g) B)) (base_exp re te g) *
   data_at Ews (tarray tuchar len) (bytes_val (sublist (cursor_of g) (cursor_of g + len) B)) (dexp_of re te g) *
   data_at Ews (tarray tuchar (N - (cursor_of g + len))) (bytes_val (sublist (cursor_of g + len) N B))
     (offset_val (cursor_of g + len) (base_exp re te g)))%logic.
Proof.
  intros g re te N B len Pr O L1 L2 LB FC.
  rewrite (bytes_split3 Ews N (cursor_of g) len B (base_exp re te g)) by auto.
  destruct g; simpl; [ rewrite isptr_offset_val_zero by auto | ]; reflexivity.
Qed.

Lemma dexp_join: forall g re te N B len bs, isptr re -> 0 <= cursor_of g -> 0 <= len -> cursor_of g + len <= N ->
  Zlength B = N -> Zlength bs = len -> field_compatible (tarray tuchar N) nil (base_exp re te g) ->
  (data_at Ews (tarray tuchar (cursor_of g)) (bytes_val (sublist 0 (cursor_of g) B)) (base_exp re te g) *
   data_at Ews (tarray tuchar len) (bytes_val bs) (dexp_of re te g) *
   data_at Ews (tarray tuchar (N - (cursor_of g + len))) (bytes_val (sublist (cursor_of g + len) N B))
     (offset_val (cursor_of g + len) (base_exp re te g)))%logic =
  data_at Ews (tarray tuchar N) (bytes_val (overlay (cursor_of g) bs B)) (base_exp re te g).
Proof.
  intros g re te N B len bs Pr O L1 L2 LB Lb FC.
  rewrite <- (bytes_join3 Ews N (cursor_of g) len B bs (base_exp re te g)) by auto.
  destruct g; simpl; [ rewrite isptr_offset_val_zero by auto | ]; reflexivity.
Qed.

(* A pointer to which a data_at of a nonempty byte array is, is valid. *)
Lemma bytes_valid: forall sh n v p, readable_share sh -> 0 < n ->
  data_at sh (tarray tuchar n) v p |-- valid_pointer p.
Proof. intros. apply data_at_valid_ptr; [ apply readable_nonidentity; auto | simpl; rewrite Z.max_r; lia ]. Qed.

Lemma law_valid: forall v q, field_at Ews t_law (DOT _kind) v q |-- valid_pointer q.
Proof.
  intros. apply field_at_valid_ptr0; [ apply readable_nonidentity, writable_readable, writable_Ews | | ];
    reflexivity.
Qed.

(* The law's firmware, behind the copy's function pointer. *)
Definition firmware_spec : ident * funspec := (_firmware_copy, copy_spec Ora_law).

Lemma region_header: forall m, Zlength (m_header m) = HEADER_BYTES -> region m DHeader HEADER_BYTES = m_header m.
Proof. intros. simpl. rewrite sublist_same; auto. Qed.

Lemma header_copy_step: forall (bs hx: list Z) i, Zlength bs = HEADER_BYTES -> Zlength hx = HEADER_BYTES -> 0 <= i < HEADER_BYTES ->
  upd_Znth i (bytes_val (sublist 0 i bs ++ sublist i HEADER_BYTES hx)) (Vint (Int.repr (Znth i bs))) =
  bytes_val (sublist 0 (i + 1) bs ++ sublist (i + 1) HEADER_BYTES hx).
Proof. intros. rewrite upd_bytes_val. f_equal. unfold HEADER_BYTES in *. list_solve. Qed.

Lemma body_copy_step: forall (bs old: list Z) n i, Zlength bs = n -> Zlength old = n -> 0 <= i < n ->
  upd_Znth i (bytes_val (sublist 0 i bs ++ sublist i n old)) (Vint (Int.repr (Znth i bs))) =
  bytes_val (sublist 0 (i + 1) bs ++ sublist (i + 1) n old).
Proof. intros. rewrite upd_bytes_val. f_equal. list_solve. Qed.

Lemma fits_copy: forall a d len ret bs, Zlength bs = len -> fits (Copy a d len) (Copied ret bs) = true.
Proof. intros. simpl. apply Z.eqb_eq. auto. Qed.

Ltac destruct_lst_ok' L :=
  let L' := fresh "L" in pose proof L as L';
  unfold lst_ok in L';
  destruct L' as (?L1 & ?L2 & ?L3 & ?L4 & ?L5 & ?L6 & ?L7 & ?L8 & ?L9 & ?L10 & ?L11 & ?L12 & ?L13 & ?L14 & ?L15 &
                  ?L16 & ?L17 & ?L18 & ?L19 & ?L20 & ?L21 & ?L22 & ?L23 & ?L24 & ?L25 & ?L26 & ?L27 & ?L28 & ?L29).

#[export] Hint Resolve law_valid : valid_pointer.

Lemma arrays_to_base: forall x m re te g,
  (data_at Ews (tarray tuchar (root_capacity x)) (bytes_val (m_root m)) re *
   data_at Ews (tarray tuchar (table_capacity x)) (bytes_val (m_tables m)) te)%logic |--
  (data_at Ews (tarray tuchar (base_cap x g)) (bytes_val (base_mem m g)) (base_exp re te g) *
   other_arr x m re te g)%logic.
Proof. intros. rewrite (arrays_base x m re te g). apply derives_refl. Qed.

Lemma arrays_unbase: forall x m re te g,
  (data_at Ews (tarray tuchar (base_cap x g)) (bytes_val (base_mem m g)) (base_exp re te g) *
   other_arr x m re te g)%logic |--
  (data_at Ews (tarray tuchar (root_capacity x)) (bytes_val (m_root m)) re *
   data_at Ews (tarray tuchar (table_capacity x)) (bytes_val (m_tables m)) te)%logic.
Proof. intros. rewrite (arrays_base x m re te g). apply derives_refl. Qed.

Lemma dest_ptr_isptr: forall pl g, isptr (p_root pl) -> isptr (p_tables pl) -> isptr (dest_ptr pl (dest_of g)).
Proof. intros. destruct g; simpl; auto. Qed.
