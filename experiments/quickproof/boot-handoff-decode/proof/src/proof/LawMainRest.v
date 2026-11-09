(* Law handoff_decode_exact: main after the fills: the three records drawn, the projection record, the law's
   copy_expect, info_expect, extent_ok, records and at, and the stage the function starts at (an allocation's magic
   and address checks, the copy's stream reset, the decoder's begin), which is the model's start; then the call
   (call_ok). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosHandoff.harness.handoff_decode_exact.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.LawProg LeanosHandoff.proof.LawDefs LeanosHandoff.proof.LawFacts
  LeanosHandoff.proof.LawLib LeanosHandoff.proof.LawLib2 LeanosHandoff.proof.LawZero
  LeanosHandoff.proof.LawMainDefs LeanosHandoff.proof.LawMainPre LeanosHandoff.proof.LawMainPre2.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Existing Instance LawProg.LCS.

Definition with_records (x: inputs) (tr lr cr: Z) : inputs :=
  mk_inputs (i_call x) (i_magic x) (i_address x) (i_total x) (i_candidate x) (i_info x) (i_copy x) (i_usable x)
    (i_blocked x) (i_reserved x) (i_states x) tr lr cr.

(* The record as main leaves it before the function's first call. *)
Definition s_init (e: Z) (w: Z) : lst := mk_lst 0 0 e 0 0 w 0 0 (Zrepeat 0 7) (Zrepeat 0 41).

Lemma lst_ok_init: forall e w, u32_ok e -> u64_ok w -> lst_ok (s_init e w).
Proof.
  intros. unfold lst_ok, s_init; lst_cbn. split_and; auto; try (unfold u32_ok, u64_ok; rep_lia);
    try reflexivity; repeat constructor; unfold u64_ok; rep_lia.
Qed.

Lemma copy_start: forall x, m_copy (mem_of (start x)) = i_copy x.
Proof.
  intros. unfold start, begin_decode. destruct (i_call x); try reflexivity.
  - destruct (_ =? _); reflexivity.
  - destruct (projection x); reflexivity.
  - destruct (projection x); reflexivity.
Qed.

Lemma start_alloc: forall x, i_call x = FAllocate ->
  start x = if pointer_check x =? S_OK then Go ExpectSize (initial x) else Return (pointer_check x) (initial x).
Proof. intros x C. unfold start. rewrite C. reflexivity. Qed.

Lemma and7'': forall T, 0 <= T <= Int.max_unsigned -> Int.and (Int.repr T) (Int.repr 7) = Int.repr (T mod 8).
Proof.
  intros T R. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia.
  change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma inputs_ok_of: forall x tr lr cr,
  x0_ok (call_code (i_call x)) (i_magic x) (i_address x) (i_total x) (i_candidate x) -> filled x ->
  u32_ok tr -> u32_ok lr -> u32_ok cr -> inputs_ok (with_records x tr lr cr).
Proof.
  intros x tr lr cr (O1 & O2 & O3 & O4 & O5 & O6) (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & S0 & S1) A B C.
  unfold inputs_ok, with_records; simpl. split_and; auto.
  destruct (i_states x) as [ | r0 [ | r1 [ | r2 l]]]; try (rewrite ?Zlength_cons, ?Zlength_nil in F11; rep_lia).
  destruct S0 as [S0 _]. destruct S1 as [S1 _]. repeat constructor; auto.
Qed.

Lemma inputs_ok_xm: forall x cep iep, inputs_ok x -> inputs_ok (xm x cep iep).
Proof. intros. exact H. Qed.

Lemma has_copy_xm: forall x cep iep, has_copy (xm x cep iep) = has_copy x.
Proof. reflexivity. Qed.

Lemma x_fit_xm: forall x cep iep,
  x0_ok (call_code (i_call x)) (i_magic x) (i_address x) (i_total x) (i_candidate x) -> filled x ->
  x_fit (xm x cep iep).
Proof.
  intros x cep iep (O1 & O2 & O3 & O4 & O5 & O6) (F1 & F2 & F3 & F4 & _).
  unfold x_fit. rewrite has_copy_xm. intros N. unfold xm; cbn [i_info i_total]. rewrite N.
  assert (Nc: call_code (i_call x) <> 0) by (unfold has_copy in N; destruct (i_call x); simpl; congruence || lia).
  split; [ auto | split; [ apply O6; auto | ] ]. rewrite F3. unfold info_len, is_alloc.
  unfold has_copy in N. destruct (i_call x); congruence || reflexivity.
Qed.

Lemma mem_fit_xm: forall x cep iep, inputs_ok x -> filled x -> mem_fit (xm x cep iep) (initial (xm x cep iep)).
Proof.
  intros x cep iep Ix Fx. pose proof Ix as (I1 & I2 & I3 & _).
  pose proof Fx as (F1 & F2 & _ & _ & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13).
  unfold mem_fit. change (has_copy (xm x cep iep)) with (has_copy x).
  unfold initial, xm; cbn [m_total m_copy m_usable m_blocked m_reserved m_states m_at i_total i_copy
    i_usable i_blocked i_reserved i_states].
  assert (Lc: has_copy x = true -> Zlength (i_copy x) = COPY_WORDS)
    by (intros Hc; rewrite F1; unfold copy_len, has_copy in *; destruct (i_call x); congruence).
  split_and; auto; try (intros Hc; rewrite Hc; auto).
Qed.

Lemma ptr_ok_xm: forall x cep iep, isptr cep -> isptr iep -> ptr_ok (xm x cep iep) cep (ie_of x cep iep).
Proof.
  intros x cep iep Pc Pi. unfold ptr_ok. change (has_copy (xm x cep iep)) with (has_copy x). split.
  - intros C. change (i_call x = FAllocate) in C. unfold ie_of, is_alloc. rewrite C. reflexivity.
  - unfold xm; cbn [i_info i_copy]. unfold ie_of, is_alloc, has_copy.
    destruct (i_call x); cbv beta iota; symmetry; apply dec_enc; auto.
Qed.

Lemma dec_ctx_xm: forall x cep iep, i_call x = FProjection \/ i_call x = FCandidate -> extent_fits (i_total x) ->
  Zlength (i_info x) = i_total x / 8 -> dec_ctx (xm x cep iep) (initial (xm x cep iep)).
Proof.
  intros x cep iep C E L. unfold dec_ctx, decoded.
  cbn [initial m_total m_copy xm i_call i_total i_info]. unfold has_copy.
  destruct C as [C | C]; rewrite C; cbv beta iota; (split; [ discriminate | split; [ exact E | rewrite L; lia ] ]).
Qed.

Lemma arrays_intro: forall x cep iep, filled x ->
  (data_at Ews (tarray tulong (copy_len x)) (map vl (i_copy x)) cep *
   data_at Ews (tarray tulong (info_len x)) (map vl (i_info x)) iep)%logic
  |-- (arrays (xm x cep iep) cep (ie_of x cep iep) (mem_of (start (xm x cep iep))) * own_obj x cep iep)%logic.
Proof.
  intros x cep iep Fx. pose proof Fx as (_ & _ & F3 & _).
  unfold arrays, info_obj, ie_of, own_obj. rewrite copy_start, has_copy_xm.
  unfold xm; cbn [i_copy i_info]. unfold copy_len, info_len, is_alloc, has_copy in *.
  destruct (i_call x); rewrite ?emp_sepcon, ?sepcon_emp; try (rewrite F3); cancel.
Qed.

Lemma tail_rest {Espec: OracleKind} (TC: @call_ok Espec): @rest_ok Espec.
Proof.
  intros gv x cp cep ip iep up bp rp sp vtr vlr vcr vpj Ox Fx Pcp Pcep Pip Piep Pup Pbp Prp Psp.
  unfold rest_pre, s_rest. start_tail_main.
  pose proof Ox as (Rcc & Rmg & Rad & Rtt & Rcd & Ext). unfold u32_ok, u64_ok in Rmg, Rad, Rtt, Rcd.
  (* the records *)
  forward_call tt. Intros tr. forward. forward.
  forward_call tt. Intros lr. forward. forward.
  forward_call tt. Intros cr. forward. forward.
  (* the projection record *)
  forward. forward. forward. forward. forward.
  (* the law's fields for the call *)
  unfold fields1, lraw. Intros.
  forward.
  forward.
  forward_if (temp _t'35 (ie_of x cep iep)).
  { assert (C: i_call x = FAllocate) by (u64c; apply call_code_inj; assumption).
    forward. entailer!. unfold ie_of, is_alloc. rewrite C. reflexivity. }
  { assert (C: i_call x <> FAllocate) by (intro C; rewrite C in *; u64c; contradiction).
    forward. entailer!. unfold ie_of, is_alloc. destruct (i_call x); first [ contradiction | reflexivity ]. }
  forward. forward. forward. forward.
  set (xr := with_records x tr lr cr).
  set (x' := xm xr cep iep).
  assert (Ixr: inputs_ok xr) by (apply inputs_ok_of; auto; unfold u32_ok; lia).
  assert (Ix': inputs_ok x') by (apply inputs_ok_xm; auto).
  assert (Fxr: filled xr) by exact Fx.
  assert (Xf': x_fit x') by (apply x_fit_xm; auto).
  assert (Mf: mem_fit x' (initial x')) by (apply mem_fit_xm; auto).
  assert (Po: ptr_ok x' cep (ie_of xr cep iep)) by (apply ptr_ok_xm; auto).
  pose proof Ix' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof (call_code_range (i_call x)) as Rc.
  change (call_code (i_call x)) with (call_code (i_call x')).
  change (ie_of x cep iep) with (ie_of x' cep iep).
  change (ie_of xr cep iep) with (ie_of x' cep iep) in Po.
  freeze_but [_call; _magic; _address; _total; _candidate; _projection; _running; _copy_expect; _info_expect;
              _usable_expect; _blocked_expect; _reserved_expect; _states_expect; _at; _extent_ok; _records;
              _expect; _verdict; _chunk; _word; _block; _value; _stream; _answer] (@nil val) FO.
  forward.
  forward_if (EX s0: lst, PROP (J x' (start x') s0)
    LOCAL (temp _m (gv _law); temp _copy_words (vi (copy_len x)); temp _copy cp; temp _copy_expect cep;
           temp _info_words (vi (info_len x)); temp _info ip; temp _info_expect iep; temp _usable up;
           temp _blocked bp; temp _reserved rp; temp _states sp;
           temp _total_prior (vi tr); temp _length_prior (vi lr); temp _current_prior (vi cr);
           lvar _total_record tuint vtr; lvar _length_record tuint vlr; lvar _current_record tuint vcr;
           lvar _projection t_projection vpj; gvars gv)
    SEP (FRZL FO; lfields (gv _law) x' cep (ie_of x' cep iep) (mem_of (start x')) s0)).
  - (* an allocation: the magic and the address *)
    assert (C: i_call x' = FAllocate) by (u64c; apply call_code_inj; assumption).
    assert (Rad': 0 <= i_address x' <= Int.max_unsigned) by (unfold x'; simpl; lia).
    assert (Rmg': 0 <= i_magic x' <= Int.max_unsigned) by (unfold x'; simpl; lia).
    assert (R8: 0 <= i_address x mod 8 < 8) by (apply Z.mod_pos_bound; lia).
    change (i_magic x) with (i_magic x'). change (i_address x) with (i_address x').
    forward.
    forward_if.
    { (* MAGIC *)
      u64c. assert (P: pointer_check x' = S_MAGIC) by (unfold pointer_check; change (i_magic x') with (i_magic x); change (i_address x') with (i_address x);
        chk_dec).
      forward_call (gv _law, z32, z32, S_MAGIC).
      assert (HJ0: J x' (Return S_MAGIC (initial x')) (s_stop (s_init 0 0) S_MAGIC))
        by (apply J_stop; auto; [ apply lst_ok_init; unfold u32_ok, u64_ok; rep_lia | unfold u32_ok; unfold_status; rep_lia ]).
      Exists (s_stop (s_init 0 0) S_MAGIC). rewrite (start_alloc x' C), P. cbn [mem_of].
      unfold lfields, s_stop, s_init in *; lst_cbn. entailer!. }
    forward. forward_if.
    { (* POINTER_ALIGNMENT *)
      rewrite and7'' in * by rep_lia. u64c.
      assert (P: pointer_check x' = S_POINTER_ALIGNMENT) by (unfold pointer_check; change (i_magic x') with (i_magic x); change (i_address x') with (i_address x);
        chk_dec).
      forward_call (gv _law, z32, z32, S_POINTER_ALIGNMENT).
      assert (HJ0: J x' (Return S_POINTER_ALIGNMENT (initial x')) (s_stop (s_init 0 0) S_POINTER_ALIGNMENT))
        by (apply J_stop; auto; [ apply lst_ok_init; unfold u32_ok, u64_ok; rep_lia | unfold u32_ok; unfold_status; rep_lia ]).
      Exists (s_stop (s_init 0 0) S_POINTER_ALIGNMENT). rewrite (start_alloc x' C), P. cbn [mem_of].
      unfold lfields, s_stop, s_init in *; lst_cbn. entailer!. }
    rewrite and7'' in * by rep_lia. u64c.
    forward. forward_if.
    { (* POINTER_LOW *)
      u64c. assert (P: pointer_check x' = S_POINTER_LOW) by (unfold pointer_check; change (i_magic x') with (i_magic x); change (i_address x') with (i_address x);
        chk_dec).
      forward_call (gv _law, z32, z32, S_POINTER_LOW).
      assert (HJ0: J x' (Return S_POINTER_LOW (initial x')) (s_stop (s_init 0 0) S_POINTER_LOW))
        by (apply J_stop; auto; [ apply lst_ok_init; unfold u32_ok, u64_ok; rep_lia | unfold u32_ok; unfold_status; rep_lia ]).
      Exists (s_stop (s_init 0 0) S_POINTER_LOW). rewrite (start_alloc x' C), P. cbn [mem_of].
      unfold lfields, s_stop, s_init in *; lst_cbn. entailer!. }
    forward. forward_if.
    { (* POINTER_HIGH *)
      change (Int.mul (Int.mul (Int.repr 16) (Int.repr 1024)) (Int.repr 1024)) with (Int.repr 16777216) in *.
      u64c. assert (P: pointer_check x' = S_POINTER_HIGH) by (unfold pointer_check; change (i_magic x') with (i_magic x); change (i_address x') with (i_address x);
        chk_dec).
      forward_call (gv _law, z32, z32, S_POINTER_HIGH).
      assert (HJ0: J x' (Return S_POINTER_HIGH (initial x')) (s_stop (s_init 0 0) S_POINTER_HIGH))
        by (apply J_stop; auto; [ apply lst_ok_init; unfold u32_ok, u64_ok; rep_lia | unfold u32_ok; unfold_status; rep_lia ]).
      Exists (s_stop (s_init 0 0) S_POINTER_HIGH). rewrite (start_alloc x' C), P. cbn [mem_of].
      unfold lfields, s_stop, s_init in *; lst_cbn. entailer!. }
    { (* the size read *)
      change (Int.mul (Int.mul (Int.repr 16) (Int.repr 1024)) (Int.repr 1024)) with (Int.repr 16777216) in *.
      u64c. assert (P: pointer_check x' = S_OK) by (unfold pointer_check; change (i_magic x') with (i_magic x); change (i_address x') with (i_address x);
        chk_dec).
      forward.
      assert (HJ0: J x' (Go ExpectSize (initial x')) (s_init 0 0)).
      { unfold J; split_and; auto.
        - apply lst_ok_init; unfold u32_ok, u64_ok; rep_lia.
        - unfold go_inv, s_init; lst_cbn; split_and; auto; unfold x'; simpl; lia. }
      Exists (s_init 0 0). rewrite (start_alloc x' C), P. cbn [mem_of].
      unfold lfields, s_init in *; lst_cbn. entailer!. }
  - (* a copy or a decoder *)
    assert (Nc0: call_code (i_call x) <> 0)
      by (u64c; change (call_code (i_call x')) with (call_code (i_call x)) in *; lia).
    forward.
    forward_if.
    + (* a copy: the stream reset *)
      assert (C: i_call x' = FCopy)
        by (u64c; change (call_code (i_call x')) with (call_code (i_call x)) in *; apply call_code_inj; assumption).
      assert (Ext': extent_fits (i_total x')) by (apply Ext; lia).
      forward_call (gv _law, z64, z32).
      assert (HJ0: J x' (Go (ExpectStreamInit nil) (initial x')) (s_init 1 0)).
      { unfold J; split_and; auto.
        - apply lst_ok_init; unfold u32_ok, u64_ok; rep_lia.
        - unfold go_inv, s_init; lst_cbn; split_and; auto; try lia.
          + apply prefix_nil. reflexivity.
          + rewrite Zlength_nil; lia.
          + unfold copy_ctx; split; [ right; exact C | exact Ext' ]. }
      Exists (s_init 1 0).
      assert (Es: start x' = Go (ExpectStreamInit nil) (initial x')) by (unfold start; rewrite C; reflexivity).
      rewrite Es. cbn [mem_of].
      unfold lfields, s_init in *; lst_cbn. entailer!.
    + (* a decoder: its begin *)
      assert (C: i_call x' = FProjection \/ i_call x' = FCandidate).
      { u64c. change (call_code (i_call x')) with (call_code (i_call x)) in *. change (i_call x') with (i_call x).
        destruct (i_call x); simpl in *; first [ lia | auto ]. }
      assert (Ext': extent_fits (i_total x')) by (apply Ext; lia).
      assert (Dc: dec_ctx x' (initial x')).
      { apply dec_ctx_xm; [ exact C | exact Ext' | ].
        pose proof Fx as (_ & _ & F3 & _). change (Zlength (i_info x) = i_total x / 8). rewrite F3.
        unfold info_len, is_alloc. change (i_call x') with (i_call x) in C.
        destruct C as [C | C]; rewrite C; reflexivity. }
      sep_apply (lfields_fold (gv _law) x' cep (ie_of x' cep iep) (initial x') (s_init 0 0)).
      forward_call (gv _law, x', cep, ie_of x' cep iep, initial x', s_init 0 0).
      { split_and; auto. apply lst_ok_init; unfold u32_ok, u64_ok; rep_lia. }
      Intros s1. Exists s1.
      assert (Es: start x' = begin_decode x' (initial x')) by (unfold start; destruct C as [C | C]; rewrite C; reflexivity).
      rewrite Es. entailer!.
  - (* the call *)
    Intros s0. thaw FO.
    sep_apply (arrays_intro xr cep iep Fxr).
    assert (Ext2: i_call xr <> FAllocate -> extent_fits (i_total xr))
      by (intros N; apply Ext; unfold xr, with_records in *; cbn [i_call i_total] in *;
          destruct (i_call x) eqn:Ec; simpl; first [ congruence | lia ]).
    subst x'. change (ie_of (xm xr cep iep) cep iep) with (ie_of xr cep iep).
    eapply semax_pre; [ | apply (TC gv xr s0 cp cep ip iep up bp rp sp vtr vlr vcr vpj); auto ].
    unfold call_pre. entailer!.
Qed.