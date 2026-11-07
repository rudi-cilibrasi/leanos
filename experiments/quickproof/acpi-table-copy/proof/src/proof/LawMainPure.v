(* Law table_copy_exact: the model facts main's proof needs: the law's record before the call (J at the model's
   start), and the tiling of the table arena that main checks on OK.  No program here. *)
Require Import VST.floyd.proofauto.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.LawDefs LeanosAcpi.proof.LawFacts LeanosAcpi.proof.LawModel LeanosAcpi.proof.LawZero.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* ---------------------------------------------------------------------- *)
(* The tiling                                                              *)
(* ---------------------------------------------------------------------- *)

Lemma tiles_from_facts: forall ss off e, tiles_from off ss e -> forall t, 0 <= t < Zlength ss ->
  s_next (Znth t ss) = s_offset (Znth t ss) + padded (s_length (Znth t ss)) /\
  (t + 1 < Zlength ss -> s_offset (Znth (t + 1) ss) = s_offset (Znth t ss) + padded (s_length (Znth t ss))) /\
  (t + 1 = Zlength ss -> e = s_offset (Znth t ss) + padded (s_length (Znth t ss))) /\
  (t = 0 -> s_offset (Znth 0 ss) = off).
Proof.
  induction ss as [ | sd ss IH]; intros off e T t Ht; [ rewrite Zlength_nil in Ht; lia | ].
  simpl in T. destruct T as (T1 & T2 & T3). rewrite Zlength_cons in *.
  destruct (Z.eq_dec t 0) as [E | E].
  - subst t. rewrite !Znth_0_cons. split; [ lia | ]. split.
    + intros L. rewrite Znth_pos_cons by lia. replace (0 + 1 - 1) with 0 by lia.
      destruct ss as [ | sd' ss']; [ rewrite Zlength_nil in L; lia | ]. rewrite Znth_0_cons.
      simpl in T3. destruct T3 as (T3a & _). lia.
    + split; [ | auto ].
      intros L. assert (ss = nil) by (destruct ss; [ reflexivity | rewrite Zlength_cons in L; pose proof (Zlength_nonneg ss); lia ]).
      subst ss. simpl in T3. lia.
  - rewrite Znth_pos_cons by lia.
    destruct (IH _ _ T3 (t - 1) ltac:(lia)) as (I1 & I2 & I3 & I4).
    split; [ exact I1 | ]. split.
    + intros L. rewrite Znth_pos_cons by lia. replace (t + 1 - 1) with (t - 1 + 1) by lia. apply I2. lia.
    + split; [ intros L; apply I3; lia | intros; lia ].
Qed.

(* ---------------------------------------------------------------------- *)
(* The record before the call                                              *)
(* ---------------------------------------------------------------------- *)

(* main's record after its stores of root_done .. table (s0 is all zeros). *)
Definition s_main : lst := set_is_root s0 1.

Lemma Forall_Zrepeat': forall {A} (P: A -> Prop) x n, P x -> Forall P (Zrepeat x n).
Proof. intros. unfold Zrepeat. induction (Z.to_nat n); simpl; constructor; auto. Qed.

Lemma lst_ok_s0: lst_ok s0.
Proof.
  unfold lst_ok, s0. lst_cbn.
  repeat split; try (unfold u32_ok, u64_ok; rep_lia); try reflexivity;
    try (apply Forall_Zrepeat'; unfold u32_ok, u64_ok; rep_lia).
Qed.

Lemma lst_ok_main: lst_ok s_main.
Proof.
  pose proof lst_ok_s0 as L. unfold s_main, lst_ok in *. lst_cbn. intuition (unfold u32_ok in *; rep_lia).
Qed.

Lemma mem_fit_initial: forall x, inputs_ok x -> mem_fit x (initial x).
Proof.
  intros x (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8). unfold mem_fit, initial. simpl. auto 10.
Qed.

Lemma mem_rel_initial: forall x, mem_rel x s_main (initial x).
Proof.
  intros. unfold mem_rel, slot_of, s_main, s0, initial. lst_cbn. simpl.
  repeat split; auto; intros; try (rewrite Zlength_nil in *; lia); constructor.
Qed.

(* begin_sdt(m, address, root, root_expect, root_capacity, 0) on main's record. *)
Definition s_begin (x: inputs) (pl: place) (re: val) : lst :=
  set_expect (set_word (set_byte (set_cursor (set_capacity (set_dexp (set_dest (set_sdt_address s_main
    (i_address x)) (p_root pl)) re) (root_capacity x)) 0) 0) 0) E_HEADER.

Definition s_start (x: inputs) (pl: place) (re: val) : lst :=
  if negb ((i_kind x =? 1) || (i_kind x =? 2)) || (i_address x =? 0) then s_stop s_main S_ROOT_SELECTION
  else if MAX_U32 <? i_address x then s_stop s_main S_SDT_ADDRESS_WIDTH
  else s_begin x pl re.

Lemma J_start: forall x pl re te, inputs_ok x -> J x pl re te (start x) (s_start x pl re).
Proof.
  intros x pl re te I. unfold start, s_start.
  destruct (negb _ || _) eqn:Sel.
  - apply J_stop; [ apply lst_ok_main | apply mem_fit_initial; auto | apply mem_rel_initial | ].
    unfold S_ROOT_SELECTION, VERDICT_TABLES. lia.
  - unfold begin_sdt. cbn [address_of].
    destruct (MAX_U32 <? i_address x) eqn:A.
    + apply J_stop; [ apply lst_ok_main | apply mem_fit_initial; auto | apply mem_rel_initial | ].
      unfold S_SDT_ADDRESS_WIDTH, VERDICT_TABLES. lia.
    + apply orb_false_iff in Sel as [S1 S2]. apply negb_false_iff in S1. apply Z.eqb_neq in S2.
      apply Z.ltb_ge in A.
      assert (Ru: u64_ok (i_address x)) by (destruct I; tauto).
      assert (Rc: 0 <= root_capacity x <= Int.max_unsigned).
      { destruct I as (_ & _ & _ & I4 & _). unfold root_capacity in *. pose proof (Zlength_nonneg (i_root x)). lia. }
      pose proof lst_ok_main as L.
      unfold J. cbn [mem_of]. split.
      { unfold s_begin, lst_ok in *. lst_cbn. intuition (unfold u32_ok, u64_ok, E_HEADER in *; rep_lia). }
      split; [ apply mem_fit_initial; auto | ].
      split; [ pose proof (mem_rel_initial x) as R; unfold mem_rel, slot_of, s_begin in *; lst_cbn; exact R | ].
      unfold go_inv, sdt_inv, tgt_inv, cst_inv, s_begin, s_main, s0. lst_cbn. cbn [address_of dest_of dest_ptr dexp_of
        capacity_of cursor_of initial m_root_copy m_entries m_slots].
      unfold u64_ok in Ru.
      apply orb_true_iff in S1.
      repeat split; auto; try lia.
      all: try (destruct S1 as [K | K]; apply Z.eqb_eq in K; auto).
Qed.

Lemma tiles_from_bound: forall ss off e, tiles_from off ss e -> 0 <= off ->
  Forall (fun sd => HEADER_BYTES <= s_length sd <= MAX_SDT_BYTES) ss ->
  forall t, 0 <= t < Zlength ss -> off <= s_offset (Znth t ss) /\ s_offset (Znth t ss) + padded (s_length (Znth t ss)) <= e.
Proof.
  induction ss as [ | sd ss IH]; intros off e T O F t Ht; [ rewrite Zlength_nil in Ht; lia | ].
  simpl in T. destruct T as (T1 & T2 & T3). rewrite Zlength_cons in Ht. inversion F; subst.
  assert (P: 0 <= padded (s_length sd)) by (apply padded_range; unfold HEADER_BYTES, MAX_SDT_BYTES in *; lia).
  assert (Ge: forall ss' off' e', tiles_from off' ss' e' -> Forall (fun sd => HEADER_BYTES <= s_length sd <= MAX_SDT_BYTES) ss' -> off' <= e').
  { induction ss' as [ | a ss' IH']; intros off' e' T' F'; simpl in T'; [ lia | ].
    destruct T' as (_ & _ & T'). inversion F'; subst.
    pose proof (IH' _ _ T' H4). pose proof (padded_range (s_length a) ltac:(unfold HEADER_BYTES, MAX_SDT_BYTES in *; lia)). lia. }
  destruct (Z.eq_dec t 0) as [E | E].
  - subst t. rewrite Znth_0_cons. split; [ lia | ]. pose proof (Ge _ _ _ T3 H2). lia.
  - rewrite Znth_pos_cons by lia. destruct (IH _ _ T3 ltac:(lia) H2 (t - 1) ltac:(lia)) as [B1 B2]. split; lia.
Qed.

Lemma mem_of_start: forall x, mem_of (start x) = initial x.
Proof.
  intros. unfold start, begin_sdt. destruct (negb _ || _); [ reflexivity | ]. destruct (_ <? _); reflexivity.
Qed.

(* The copy records as madt_verdict reads them. *)
Lemma verdict_slots: forall x s m, mem_rel x s m -> tiled (m_slots m) (w_arena s) -> w_arena s <= table_capacity x ->
  forall t, 0 <= t < Zlength (m_slots m) ->
  s_offset (Znth t (m_slots m)) = Znth t (w_offsets s) /\ s_length (Znth t (m_slots m)) = Znth t (w_lengths s) /\
  HEADER_BYTES <= Znth t (w_lengths s) <= MAX_SDT_BYTES /\ 0 <= Znth t (w_offsets s) /\
  Znth t (w_offsets s) + Znth t (w_lengths s) <= table_capacity x.
Proof.
  intros x s m R T A t Ht. destruct R as (R1 & R2 & R3 & R4 & R5).
  pose proof (R4 t Ht) as E. unfold slot_of in E.
  pose proof (Forall_Znth' _ _ t R5 Ht) as B. rewrite E in B. simpl in B.
  pose proof (tiles_from_bound (m_slots m) 0 (w_arena s) T (Z.le_refl 0) R5 t Ht) as (C1 & C2). rewrite E in C1, C2. simpl in C1, C2.
  assert (Bl: 0 <= Znth t (w_lengths s) <= MAX_SDT_BYTES) by (unfold HEADER_BYTES in B; lia).
  pose proof (padded_range (Znth t (w_lengths s)) Bl) as (P1 & P2).
  rewrite E. simpl. repeat split; try lia.
Qed.
