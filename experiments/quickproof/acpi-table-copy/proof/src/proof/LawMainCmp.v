(* Law table_copy_exact: what main's checks after the call compare with: pointer equality inside an array, the
   truncations, the law's records against the copy slots, the statuses' range. *)
Require Import VST.floyd.proofauto.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.LawDefs LeanosAcpi.proof.LawFacts LeanosAcpi.proof.LawModel LeanosAcpi.proof.LawMainPure
  LeanosAcpi.proof.LawMainModel.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* Two equal pointers into (or one past) an array: the typecheck of their comparison. *)
Local Transparent denote_tc_test_eq test_eq_ptrs.
Lemma arr_test_eq {cs: compspecs}: forall sh t n (v: reptype (tarray t n)) p i R,
  sepalg.nonidentity sh -> 0 < sizeof t -> 0 <= i <= n -> 0 < n ->
  data_at sh (tarray t n) v p * R |-- denote_tc_test_eq (offset_val (sizeof t * i) p) (offset_val (sizeof t * i) p).
Proof.
  intros sh t n v p i R Sh St I N.
  assert (Pp: data_at sh (tarray t n) v p * R |-- !! isptr p).
  { rewrite data_at_isptr. normalize. }
  apply derives_trans with (andp (prop (isptr p)) (sepcon (data_at sh (tarray t n) v p) R)); [ apply andp_right; auto | ].
  apply derives_extract_prop. intros Pp'.
  assert (Wk: data_at sh (tarray t n) v p * R |-- weak_valid_pointer (offset_val (sizeof t * i) p)).
  { eapply derives_trans; [ apply sepcon_derives; [ apply data_at_memory_block | apply derives_refl ] | ].
    simpl sizeof. rewrite Z.max_r by lia.
    eapply derives_trans; [ apply sepcon_derives;
      [ apply (memory_block_weak_valid_pointer sh (sizeof t * n) p (sizeof t * i)); [ nia | nia | exact Sh ]
      | apply derives_refl ] | ].
    apply extend_weak_valid_pointer. }
  destruct p; try contradiction Pp'. simpl offset_val.
  unfold denote_tc_test_eq, test_eq_ptrs. simpl sameblock.
  destruct (peq b b); [ | congruence ]. simpl.
  apply andp_right; exact Wk.
Qed.
Local Opaque denote_tc_test_eq test_eq_ptrs.

Lemma arr_test_eq' {cs: compspecs}: forall sh t n (v: reptype (tarray t n)) p i P,
  sepalg.nonidentity sh -> 0 < sizeof t -> 0 <= i <= n -> 0 < n -> P |-- data_at sh (tarray t n) v p * TT ->
  P |-- denote_tc_test_eq (offset_val (sizeof t * i) p) (offset_val (sizeof t * i) p).
Proof. intros. eapply derives_trans; [ eassumption | ]. apply arr_test_eq; auto. Qed.

Lemma arr_test_eq0 {cs: compspecs}: forall sh t n (v: reptype (tarray t n)) p P,
  sepalg.nonidentity sh -> 0 < sizeof t -> 0 < n -> P |-- data_at sh (tarray t n) v p * TT ->
  P |-- denote_tc_test_eq p p.
Proof.
  intros sh t n v p P Sh St N D.
  assert (Pp: P |-- !! isptr p).
  { eapply derives_trans; [ exact D | ]. rewrite data_at_isptr. normalize. }
  apply derives_trans with (andp (prop (isptr p)) P); [ apply andp_right; auto | ].
  apply derives_extract_prop. intros Pp'.
  pose proof (arr_test_eq' sh t n v p 0 P Sh St ltac:(lia) N D) as T.
  rewrite Z.mul_0_r, isptr_offset_val_zero in T by exact Pp'. exact T.
Qed.

Lemma cmp_same: forall p, isptr p -> force_val (sem_cmp_pp Ceq p p) = Vint Int.one.
Proof. intros. rewrite force_sem_cmp_pp by auto. rewrite if_true by reflexivity. reflexivity. Qed.

Lemma repr_mod32: forall z, Int.repr (z mod 2 ^ 32) = Int.repr z.
Proof.
  intros. change (2 ^ 32) with Int.modulus. rewrite <- Int.unsigned_repr_eq. apply Int.repr_unsigned.
Qed.

(* The statuses of validate and of the MADT selection are small. *)
Lemma validate_small: forall len bs sig, 0 <= validate len bs sig <= 63.
Proof.
  intros. unfold validate. destruct (_ || _ || _); [ | destruct (negb _) ];
    unfold S_SDT_ENVELOPE, S_SDT_CHECKSUM, S_OK; lia.
Qed.

Lemma select_from_small: forall T ss k sel st, select_from T ss k sel = inl st -> 0 <= st <= 63.
Proof.
  induction ss as [ | sd ss IH]; simpl; intros k sel st H.
  - destruct sel; inversion H; subst; unfold S_MADT_MISSING; lia.
  - destruct (negb _) eqn:E.
    + injection H as <-. apply validate_small.
    + destruct (signature_matches _ _ _); [ destruct sel; [ injection H as <-; unfold S_MADT_DUPLICATE; lia | ] | ];
        eauto.
Qed.

(* Copy record t: its offset, length and cursor as the law kept them, tiling the arena. *)
Lemma tile_at: forall x s m, mem_rel x s m -> tiled (m_slots m) (w_arena s) -> w_arena s <= table_capacity x ->
  forall t, 0 <= t < Zlength (m_slots m) ->
  Znth t (w_finals s) mod 2 ^ 32 = Znth t (w_offsets s) + padded (Znth t (w_lengths s)) /\
  (t + 1 < Zlength (m_slots m) ->
     Znth (t + 1) (w_offsets s) = Znth t (w_offsets s) + padded (Znth t (w_lengths s))) /\
  (t + 1 = Zlength (m_slots m) -> w_arena s = Znth t (w_offsets s) + padded (Znth t (w_lengths s))) /\
  Znth t (w_offsets s) + padded (Znth t (w_lengths s)) <= table_capacity x /\
  0 <= Znth t (w_offsets s) /\ HEADER_BYTES <= Znth t (w_lengths s) <= MAX_SDT_BYTES /\
  (t = 0 -> Znth 0 (w_offsets s) = 0).
Proof.
  intros x s m R T A t Ht. pose proof R as (R1 & R2 & R3 & R4 & R5).
  pose proof (tiles_from_facts _ _ _ T t Ht) as (T1 & T2 & T3 & T4).
  pose proof (tiles_from_bound _ 0 _ T (Z.le_refl 0) R5 t Ht) as (B1 & B2).
  pose proof (Forall_Znth' _ _ t R5 Ht) as B.
  rewrite (R4 t Ht) in T1, T3, B1, B2, B. unfold slot_of in T1, T3, B1, B2, B.
  cbn [s_next s_offset s_length] in T1, T3, B1, B2, B.
  split; [ exact T1 | ]. split.
  { intros L. specialize (T2 L). rewrite (R4 t Ht), (R4 (t + 1) ltac:(lia)) in T2. unfold slot_of in T2.
    cbn [s_next s_offset s_length] in T2. exact T2. }
  split; [ exact T3 | ]. split; [ lia | ]. split; [ lia | ]. split; [ exact B | ].
  intros E. subst t. specialize (T4 eq_refl). rewrite (R4 0 Ht) in T4. unfold slot_of in T4.
  cbn [s_offset] in T4. exact T4.
Qed.

(* The copy slot t main reads. *)
Lemma slots_val_at: forall pl m t, Zlength (m_slots m) <= MAX_ENTRIES -> 0 <= t < MAX_ENTRIES ->
  Znth t (slots_val pl m (Zrepeat (vl 0, (nullval, (vi 0, vi 0))) MAX_ENTRIES)) =
  if t <? Zlength (m_slots m) then sdt_val (p_tables pl) (Znth t (m_slots m)) else (vl 0, (nullval, (vi 0, vi 0))).
Proof.
  intros pl m t L T. unfold slots_val. unfold MAX_ENTRIES in *. pose proof (Zlength_nonneg (m_slots m)).
  destruct (t <? Zlength (m_slots m)) eqn:E.
  - apply Z.ltb_lt in E. rewrite Znth_app1 by (rewrite Zlength_map; lia). rewrite Znth_map by lia. reflexivity.
  - apply Z.ltb_ge in E. rewrite Znth_app2 by (rewrite Zlength_map; lia). rewrite Zlength_map.
    rewrite Znth_sublist by lia. rewrite Znth_Zrepeat by lia. reflexivity.
Qed.

Lemma slots_val_len: forall pl m, Zlength (slots_val pl m (Zrepeat (vl 0, (nullval, (vi 0, vi 0))) MAX_ENTRIES)) = MAX_ENTRIES ->
  Zlength (m_slots m) <= MAX_ENTRIES.
Proof.
  intros pl m L. unfold slots_val in L. unfold MAX_ENTRIES in *. rewrite Zlength_app, Zlength_map in L.
  destruct (Z_le_gt_dec (Zlength (m_slots m)) 256) as [ | G ]; [ assumption | ].
  rewrite sublist_nil_gen in L by lia. rewrite Zlength_nil in L. lia.
Qed.
