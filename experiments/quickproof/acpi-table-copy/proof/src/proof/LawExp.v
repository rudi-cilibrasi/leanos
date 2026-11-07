(* Law table_copy_exact: facts the bodies of root_copied and of the two exports share. *)
Require Import VST.floyd.proofauto.
Require Import LeanosAcpi.harness.table_copy_exact.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.LawProg LeanosAcpi.proof.LawDefs LeanosAcpi.proof.LawFacts LeanosAcpi.proof.LawModel
  LeanosAcpi.proof.LawRoot.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Existing Instance LawProg.LCS.

(* The first i entries of the root, decoded. *)
Definition entries_pre (vec: list Z) (w i: Z) : list Z := map (entry_at vec w) (range i).

Lemma Zlength_entries_pre: forall vec w i, 0 <= i -> Zlength (entries_pre vec w i) = i.
Proof. intros. unfold entries_pre. rewrite Zlength_map, Zlength_range; auto. Qed.

Lemma entries_pre_succ: forall vec w i, 0 <= i ->
  entries_pre vec w (i + 1) = entries_pre vec w i ++ [entry_at vec w i].
Proof. intros. unfold entries_pre. rewrite range_succ by auto. rewrite map_app. reflexivity. Qed.

Lemma entries_pre_0: forall vec w, entries_pre vec w 0 = nil.
Proof. reflexivity. Qed.

Lemma Znth_entries_pre: forall vec w i j, 0 <= j < i -> Znth j (entries_pre vec w i) = entry_at vec w j.
Proof.
  intros. unfold entries_pre, range. rewrite Znth_map by (rewrite Zlength_map, Zlength_correct, length_seq; lia).
  f_equal. rewrite Znth_map by (rewrite Zlength_correct, length_seq; lia).
  rewrite <- nth_Znth by (rewrite Zlength_correct, length_seq; lia). rewrite seq_nth by lia. simpl. lia.
Qed.

Lemma existsb_false: forall a l, (forall j, 0 <= j < Zlength l -> Znth j l <> a) -> existsb (Z.eqb a) l = false.
Proof.
  intros a l H. apply Bool.not_true_iff_false. intro E. apply existsb_exists in E as [y [Iy Ey]].
  apply Z.eqb_eq in Ey. subst y. apply In_Znth in Iy as [j [Jr Jz]]. apply (H j Jr). auto.
Qed.

Lemma existsb_true: forall a l j, 0 <= j < Zlength l -> Znth j l = a -> existsb (Z.eqb a) l = true.
Proof.
  intros a l j J E. apply existsb_exists. exists (Znth j l). split; [ apply Znth_In; auto | ]. rewrite E. apply Z.eqb_refl.
Qed.

(* The C's transition at the chunk's end byte + n is the model's. *)
Lemma law_transition_eq: forall a chunk byte n last cursor,
  law_transition a chunk (byte + n) last cursor = transition a chunk cursor byte n last.
Proof. reflexivity. Qed.

(* The fields, folded. *)
Lemma lfields_fold: forall q x pl re te hx s,
 (field_at Ews t_law (DOT _kind) (vl (i_kind x)) q *
  field_at Ews t_law (DOT _address) (vl (i_address x)) q *
  field_at Ews t_law (DOT _header) (p_header pl) q *
  field_at Ews t_law (DOT _root) (p_root pl) q *
  field_at Ews t_law (DOT _tables) (p_tables pl) q *
  field_at Ews t_law (DOT _root_capacity) (vi (root_capacity x)) q *
  field_at Ews t_law (DOT _table_capacity) (vi (table_capacity x)) q *
  field_at Ews t_law (DOT _header_expect) (bytes_val hx) q *
  field_at Ews t_law (DOT _root_expect) re q *
  field_at Ews t_law (DOT _tables_expect) te q *
  field_at Ews t_law (DOT _expect) (vi (w_expect s)) q *
  field_at Ews t_law (DOT _verdict) (vi (w_verdict s)) q *
  field_at Ews t_law (DOT _is_root) (vi (w_is_root s)) q *
  field_at Ews t_law (DOT _table) (vi (w_table s)) q *
  field_at Ews t_law (DOT _sdt_address) (vl (w_sdt_address s)) q *
  field_at Ews t_law (DOT _destination) (w_dest s) q *
  field_at Ews t_law (DOT _destination_expect) (w_dexp s) q *
  field_at Ews t_law (DOT _capacity) (vi (w_capacity s)) q *
  field_at Ews t_law (DOT _length) (vi (w_length s)) q *
  field_at Ews t_law (DOT _cursor) (vl (w_cursor s)) q *
  field_at Ews t_law (DOT _byte) (vl (w_byte s)) q *
  field_at Ews t_law (DOT _word) (vi (w_word s)) q *
  field_at Ews t_law (DOT _answer) (map vl (w_answer s)) q *
  field_at Ews t_law (DOT _root_done) (vi (w_root_done s)) q *
  field_at Ews t_law (DOT _root_length) (vi (w_root_length s)) q *
  field_at Ews t_law (DOT _entries_done) (vi (w_entries_done s)) q *
  field_at Ews t_law (DOT _width) (vi (w_width s)) q *
  field_at Ews t_law (DOT _count) (vi (w_count s)) q *
  field_at Ews t_law (DOT _root_cursor) (vl (w_root_cursor s)) q *
  field_at Ews t_law (DOT _addresses) (map vl (w_addresses s)) q *
  field_at Ews t_law (DOT _arena) (vi (w_arena s)) q *
  field_at Ews t_law (DOT _ended) (vi (w_ended s)) q *
  field_at Ews t_law (DOT _offsets) (map vi (w_offsets s)) q *
  field_at Ews t_law (DOT _lengths) (map vi (w_lengths s)) q *
  field_at Ews t_law (DOT _finals) (map vl (w_finals s)) q *
  field_at Ews t_law (DOT _ordinal) (vl (w_ordinal s)) q)%logic |-- lfields q x pl re te hx s.
Proof. intros. unfold lfields. apply derives_refl. Qed.

Lemma vi_eq: forall z, vi z = Vint (Int.repr z). Proof. reflexivity. Qed.
Lemma vl_eq: forall z, vl z = Vlong (Int64.repr z). Proof. reflexivity. Qed.

Lemma decode_step: forall vec w i count pre, 0 <= i < count ->
  decode_from vec w (range_from i count) pre =
  if (entry_at vec w i =? 0) || (MAX_U32 <? entry_at vec w i) then inl S_ROOT_ENTRY_ADDRESS
  else if existsb (Z.eqb (entry_at vec w i)) pre then inl S_ROOT_ENTRY_DUPLICATE
  else decode_from vec w (range_from (i + 1) count) (pre ++ [entry_at vec w i]).
Proof. intros. rewrite range_from_cons by auto. reflexivity. Qed.

Lemma decode_start: forall vec w count, decode_addresses vec w count = decode_from vec w (range_from 0 count) nil.
Proof. intros. unfold decode_addresses. rewrite range_from_0. reflexivity. Qed.

Lemma decode_end: forall vec w count pre, decode_from vec w (range_from count count) pre = inr pre.
Proof. intros. rewrite range_from_nil. reflexivity. Qed.

Lemma upd_prefix: forall (pre old: list Z) i a n, Zlength pre = i -> 0 <= i < n -> Zlength old = n ->
  upd_Znth i (pre ++ sublist i n old) a = (pre ++ [a]) ++ sublist (i + 1) n old.
Proof. intros. subst i. list_solve. Qed.

Lemma Forall_prefix_u64: forall (pre old: list Z) i n, Zlength pre = i -> 0 <= i <= n -> Zlength old = n ->
  Forall (fun a => 0 < a <= MAX_U32) pre -> Forall u64_ok old -> Forall u64_ok (pre ++ sublist i n old) /\
  Zlength (pre ++ sublist i n old) = n.
Proof.
  intros. split.
  - apply Forall_app; split; [ | apply Forall_sublist; auto ].
    eapply Forall_impl; [ | eassumption ]. intros a Ha. unfold u64_ok, MAX_U32 in *. rep_lia.
  - rewrite Zlength_app, Zlength_sublist by lia. lia.
Qed.
