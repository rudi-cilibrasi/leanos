(* The 256 copy slots: one slot split out of the array (for acpi_copy_sdt's `copied`, for the candidate of
   acpi_select_unique_madt, for the selected MADT), and the slots the pipeline wrote. *)
Require Import VST.floyd.proofauto.
Require Import LeanosAcpi.acpi.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.InternalSpecs.
Require Import LeanosAcpi.proof.PipeLemmas.
#[local] Existing Instance AcpiSpecs.CS.
Local Open Scope Z_scope.

#[export] Instance Inhabitant_sdt : Inhabitant sdt := mk_sdt 0 0 0 0.

Lemma split_slot: forall sh (L: list sdt_rep) i p, 0 <= i < MAX_ENTRIES -> Zlength L = MAX_ENTRIES ->
  field_compatible (tarray t_sdt MAX_ENTRIES) [] p ->
  data_at sh (tarray t_sdt MAX_ENTRIES) L p =
  (data_at sh (tarray t_sdt i) (sublist 0 i L) p *
   data_at sh t_sdt (Znth i L) (offset_val (SDT_BYTES * i) p) *
   data_at sh (tarray t_sdt (MAX_ENTRIES - (i + 1))) (sublist (i + 1) MAX_ENTRIES L)
     (offset_val (SDT_BYTES * (i + 1)) p))%logic.
Proof.
  intros. unfold MAX_ENTRIES in *.
  assert (E: @sublist (@reptype CS t_sdt) 0 256 L = L) by (apply sublist_same; auto).
  rewrite (@split3_data_at_Tarray CS sh t_sdt 256 i (i + 1) L L (sublist 0 i L) (sublist i (i + 1) L)
             (sublist (i + 1) 256 L)).
  2: (repeat split; simpl; auto; try reflexivity). 2: lia. 2: (split; [ lia | apply Z.eq_le_incl; symmetry; exact H0 ]).
  2: (symmetry; exact E).
  change (Tarray t_sdt 256 noattr) with (tarray t_sdt 256).
  rewrite !arr_field_address0 by (auto; lia). rewrite sizeof_t_sdt.
  replace (i + 1 - i) with 1 by lia. rewrite sublist_len_1 by lia.
  change (Tarray t_sdt 1 noattr) with (tarray t_sdt 1).
  rewrite (@data_at_singleton_array_eq CS sh t_sdt (Znth i L) [Znth i L]) by reflexivity.
  reflexivity.
  all: reflexivity.
Qed.

Lemma Zlength_slots_val: forall pl m (sold: list sdt_rep), Zlength (m_slots m) <= MAX_ENTRIES -> Zlength sold = MAX_ENTRIES ->
  Zlength (slots_val pl m sold) = MAX_ENTRIES.
Proof.
  intros. unfold slots_val. pose proof (Zlength_nonneg (m_slots m)).
  rewrite Zlength_app, Zlength_map, Zlength_sublist by (unfold MAX_ENTRIES in *; lia). lia.
Qed.

(* Slot |m_slots m| (the next one) split out of the slots. *)
Lemma slots_split: forall sh pl m (sold: list sdt_rep) cp, Zlength (m_slots m) < MAX_ENTRIES ->
  Zlength sold = MAX_ENTRIES -> field_compatible (tarray t_sdt MAX_ENTRIES) [] cp ->
  data_at sh (tarray t_sdt MAX_ENTRIES) (slots_val pl m sold) cp =
  (data_at sh (tarray t_sdt (Zlength (m_slots m))) (map (sdt_val (p_tables pl)) (m_slots m)) cp *
   data_at sh t_sdt (Znth (Zlength (m_slots m)) sold) (offset_val (SDT_BYTES * Zlength (m_slots m)) cp) *
   data_at sh (tarray t_sdt (MAX_ENTRIES - (Zlength (m_slots m) + 1)))
     (sublist (Zlength (m_slots m) + 1) MAX_ENTRIES sold) (offset_val (SDT_BYTES * (Zlength (m_slots m) + 1)) cp))%logic.
Proof.
  intros. pose proof (Zlength_nonneg (m_slots m)).
  rewrite (split_slot sh (slots_val pl m sold) (Zlength (m_slots m)) cp) by (auto; try lia; apply Zlength_slots_val; lia).
  unfold slots_val. unfold MAX_ENTRIES in *.
  set (e := Zlength (m_slots m)) in *.
  assert (A: sublist 0 e (map (sdt_val (p_tables pl)) (m_slots m) ++ sublist e 256 sold) = map (sdt_val (p_tables pl)) (m_slots m)).
  { rewrite sublist_app1 by (rewrite ?Zlength_map; lia). rewrite sublist_same by (rewrite ?Zlength_map; lia). reflexivity. }
  assert (B: Znth e (map (sdt_val (p_tables pl)) (m_slots m) ++ sublist e 256 sold) = Znth e sold).
  { rewrite Znth_app2 by (rewrite ?Zlength_map; lia). rewrite Zlength_map. fold e. rewrite Z.sub_diag.
    rewrite Znth_sublist by lia. f_equal; lia. }
  assert (C: sublist (e + 1) 256 (map (sdt_val (p_tables pl)) (m_slots m) ++ sublist e 256 sold) = sublist (e + 1) 256 sold).
  { rewrite sublist_app2 by (rewrite ?Zlength_map; lia). rewrite Zlength_map. fold e.
    rewrite sublist_sublist by lia. f_equal; lia. }
  rewrite A, B, C. reflexivity.
Qed.

Lemma slots_val_add: forall pl m s (sold: list sdt_rep),
  slots_val pl (add_slot m s) sold =
  map (sdt_val (p_tables pl)) (m_slots m) ++ [sdt_val (p_tables pl) s] ++ sublist (Zlength (m_slots m) + 1) MAX_ENTRIES sold.
Proof.
  intros. unfold slots_val, add_slot. simpl. rewrite map_app, <- app_assoc. rewrite Zlength_app, Zlength_cons, Zlength_nil.
  reflexivity.
Qed.

(* The slot written back, as slot |m_slots m| of add_slot m s. *)
Lemma slots_join_add: forall sh pl m s (sold: list sdt_rep) cp, Zlength (m_slots m) < MAX_ENTRIES ->
  Zlength sold = MAX_ENTRIES -> field_compatible (tarray t_sdt MAX_ENTRIES) [] cp ->
  data_at sh (tarray t_sdt (Zlength (m_slots m))) (map (sdt_val (p_tables pl)) (m_slots m)) cp *
  data_at sh t_sdt (sdt_val (p_tables pl) s) (offset_val (SDT_BYTES * Zlength (m_slots m)) cp) *
  data_at sh (tarray t_sdt (MAX_ENTRIES - (Zlength (m_slots m) + 1)))
    (sublist (Zlength (m_slots m) + 1) MAX_ENTRIES sold) (offset_val (SDT_BYTES * (Zlength (m_slots m) + 1)) cp)
  |-- data_at sh (tarray t_sdt MAX_ENTRIES) (slots_val pl (add_slot m s) sold) cp.
Proof.
  intros. pose proof (Zlength_nonneg (m_slots m)).
  assert (L: Zlength (slots_val pl (add_slot m s) sold) = MAX_ENTRIES)
    by (apply Zlength_slots_val; auto; unfold add_slot; simpl; rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  rewrite (split_slot sh (slots_val pl (add_slot m s) sold) (Zlength (m_slots m)) cp) by (auto; lia).
  rewrite slots_val_add in *. unfold MAX_ENTRIES in *.
  set (e := Zlength (m_slots m)) in *.
  assert (A: sublist 0 e (map (sdt_val (p_tables pl)) (m_slots m) ++ [sdt_val (p_tables pl) s] ++ sublist (e + 1) 256 sold)
             = map (sdt_val (p_tables pl)) (m_slots m)).
  { rewrite sublist_app1 by (rewrite ?Zlength_map; lia). rewrite sublist_same by (rewrite ?Zlength_map; lia). reflexivity. }
  assert (B: Znth e (map (sdt_val (p_tables pl)) (m_slots m) ++ [sdt_val (p_tables pl) s] ++ sublist (e + 1) 256 sold)
             = sdt_val (p_tables pl) s).
  { rewrite Znth_app2 by (rewrite ?Zlength_map; lia). rewrite Zlength_map. fold e. rewrite Z.sub_diag. reflexivity. }
  assert (C: sublist (e + 1) 256 (map (sdt_val (p_tables pl)) (m_slots m) ++ [sdt_val (p_tables pl) s] ++ sublist (e + 1) 256 sold)
             = sublist (e + 1) 256 sold).
  { rewrite sublist_app2 by (rewrite ?Zlength_map; lia). rewrite Zlength_map. fold e.
    replace (e + 1 - e) with 1 by lia. replace (256 - e) with (1 + (256 - (e + 1))) by lia.
    rewrite sublist_app2 by (rewrite Zlength_cons, Zlength_nil; lia). rewrite Zlength_cons, Zlength_nil.
    rewrite sublist_same by (try rewrite Zlength_sublist by lia; lia). reflexivity. }
  rewrite A, B, C. apply derives_refl.
Qed.

Lemma join_slot: forall sh (L: list sdt_rep) i p, 0 <= i < MAX_ENTRIES -> Zlength L = MAX_ENTRIES ->
  field_compatible (tarray t_sdt MAX_ENTRIES) [] p ->
  data_at sh (tarray t_sdt i) (sublist 0 i L) p *
  data_at sh t_sdt (Znth i L) (offset_val (SDT_BYTES * i) p) *
  data_at sh (tarray t_sdt (MAX_ENTRIES - (i + 1))) (sublist (i + 1) MAX_ENTRIES L) (offset_val (SDT_BYTES * (i + 1)) p)
  |-- data_at sh (tarray t_sdt MAX_ENTRIES) L p.
Proof. intros. rewrite (split_slot sh L i p) by auto. apply derives_refl. Qed.

Lemma slot_valid: forall sh (L: list sdt_rep) j p, readable_share sh -> 0 <= j < MAX_ENTRIES ->
  data_at sh (tarray t_sdt MAX_ENTRIES) L p |-- valid_pointer (offset_val (SDT_BYTES * j) p).
Proof.
  intros. eapply derives_trans; [ apply data_at_memory_block | ].
  apply memory_block_valid_pointer; [ | apply readable_nonidentity; auto ].
  change (sizeof (tarray t_sdt MAX_ENTRIES)) with (SDT_BYTES * MAX_ENTRIES). unfold SDT_BYTES, MAX_ENTRIES in *. lia.
Qed.

Lemma add_ptr_sdt_uint: forall p n, isptr p ->
  force_val (sem_binary_operation' Oadd (tptr t_sdt) tuint p (Vint n)) = offset_val (SDT_BYTES * Int.unsigned n) p.
Proof.
  intros. destruct p; try contradiction. simpl. unfold sem_add_ptr_int. simpl. f_equal. f_equal.
  unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite ptrofs_mul_repr. reflexivity.
Qed.

Lemma join2_bytes: forall sh (bs: list Z) n n1 p, Zlength bs = n -> 0 <= n1 <= n ->
  field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n1) (bytes_val (sublist 0 n1 bs)) p *
  data_at sh (tarray tuchar (n - n1)) (bytes_val (sublist n1 n bs)) (offset_val n1 p)
  |-- data_at sh (tarray tuchar n) (bytes_val bs) p.
Proof. intros. rewrite (split2_bytes sh bs n n1 p) by auto. apply derives_refl. Qed.

(* After Exists of a status st other than OK: decide `st =? S_OK` in the postcondition. *)
Ltac fix_status st :=
  let E := fresh in
  assert (E: (st =? S_OK) = false) by reflexivity; rewrite ?E; clear E; cbv iota;
  let SO := fresh "SO" in assert (SO: status_ok st) by reflexivity.

Lemma slots_join_old: forall sh pl m (sold: list sdt_rep) cp, Zlength (m_slots m) < MAX_ENTRIES ->
  Zlength sold = MAX_ENTRIES -> field_compatible (tarray t_sdt MAX_ENTRIES) [] cp ->
  data_at sh (tarray t_sdt (Zlength (m_slots m))) (map (sdt_val (p_tables pl)) (m_slots m)) cp *
  data_at sh t_sdt (Znth (Zlength (m_slots m)) sold) (offset_val (SDT_BYTES * Zlength (m_slots m)) cp) *
  data_at sh (tarray t_sdt (MAX_ENTRIES - (Zlength (m_slots m) + 1)))
    (sublist (Zlength (m_slots m) + 1) MAX_ENTRIES sold) (offset_val (SDT_BYTES * (Zlength (m_slots m) + 1)) cp)
  |-- data_at sh (tarray t_sdt MAX_ENTRIES) (slots_val pl m sold) cp.
Proof. intros. rewrite (slots_split sh pl m sold cp) by auto. apply derives_refl. Qed.

Lemma status_ok_repr: forall st, status_ok st -> Int.repr st = Int.repr 0 -> st = S_OK.
Proof.
  unfold status_ok. intros. apply andb_prop in H as [A B]. apply Z.leb_le in A. apply Z.leb_le in B.
  unfold S_MADT_SELECTION in B. apply repr_inj_unsigned in H0; [ exact H0 | rep_lia | rep_lia ].
Qed.

Lemma cmpu_eq64: forall a b, u64_ok a -> u64_ok b -> Int64.cmpu Ceq (Int64.repr a) (Int64.repr b) = (a =? b).
Proof. intros. unfold Int64.cmpu. apply eq64_repr; auto. Qed.
