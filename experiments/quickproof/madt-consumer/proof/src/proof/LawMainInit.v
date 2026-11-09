(* Law consumer_obligations: main from the oracle's setup to its return: the oracle's fields, the record walk, the
   call of madt_bind (the law's oracle handed over on a valid call), then the checks (LawTailInvalid,
   LawTailValid). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosMadt.harness.consumer_obligations.code.
Require Import LeanosMadt.proof.Defs.
Require Import LeanosMadt.proof.MadtSpecs.
Require Import LeanosMadt.proof.LawProg LeanosMadt.proof.LawDefs LeanosMadt.proof.LawFacts LeanosMadt.proof.LawLib
  LeanosMadt.proof.LawSplit LeanosMadt.proof.LawMainLib LeanosMadt.proof.LawMainDefs LeanosMadt.proof.LawMainCall.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

(* The typecheck of `p != NULL` with p a pointer or NULL. *)
Ltac ptr_tc := entailer!; apply sel_tc_test; [ entailer! | auto ].
(* The value of such a test. *)
Ltac ptr_val := rewrite ?sel_cmp_ne, ?sel_cmp_eq by auto;
  repeat match goal with b: bool |- _ => destruct b end; cbn [negb andb orb Z.b2z] in *;
  try discriminate; try reflexivity.

Lemma init_state_Znth: forall i, 1 <= i < 12 -> Znth i initial_state = if i =? 7 then 256 else 0.
Proof.
  intros i Hi.
  assert (i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11) by lia.
  repeat match goal with H: _ \/ _ |- _ => destruct H as [-> | H] end; try (subst; reflexivity); reflexivity.
Qed.

Lemma init_state_step: forall i, 1 <= i < 12 ->
  upd_Znth i (sublist 0 i initial_state ++ Zrepeat 0 (12 - i)) (Znth i initial_state) =
  sublist 0 (i + 1) initial_state ++ Zrepeat 0 (12 - (i + 1)).
Proof. intros i Hi. unfold initial_state. list_solve. Qed.

Lemma tail_init {Espec: OracleKind} gv q v_out v_observation n bs e1 e2 e3 e4 e5 e6 (eb obb qb: bool):
  0 <= n <= Int64.max_unsigned -> q <> nullval ->
  Zlength bs = (if length_ok n then n else 1) -> Forall byte_ok bs ->
  u64_ok e1 -> u64_ok e2 -> u64_ok e3 -> u64_ok e4 -> u64_ok e5 -> u64_ok e6 ->
  forall Delta R c, Delta = Delta0 -> R = Post0 -> c = s_init ->
  semax Delta
    (PROP ()
     LOCAL (temp _out_arg (sel qb v_out); temp _observation_arg (sel obb v_observation);
            temp _entries_arg (sel eb q); temp _entries q; temp _valid_length (Vint (Int.repr (Z.b2z (length_ok n))));
            temp _length (Vlong (Int64.repr n)); temp _o (gv _oracle);
            lvar _out t_result v_out; lvar _observation t_obs v_observation; gvars gv)
     SEP (data_at Ews (tarray tuchar (Zlength bs)) (bytes_val bs) q; mem_mgr gv;
          malloc_token Ews (tarray tuchar (Zlength bs)) q; ofields (gv _oracle) nullval 0 ob0 s0;
          data_at Tsh t_result (vl 7, (vl 7, (vl 7, (vl 7, (vl 7, vl 7))))) v_out;
          data_at Tsh t_obs (vl e1, (vl e2, (vl e3, (vl e4, (vl e5, vl e6))))) v_observation;
          has_ext tt))
    c R.
Proof.
  intros Hn Nq Lbs Hby R1 R2 R3 R4 R5 R6 Delta R c -> -> ->.
  unfold s_init. start_tail.
  unfold ofields. Intros.
  assert_PROP (isptr q /\ isptr v_out /\ isptr v_observation) as PTR by entailer!.
  destruct PTR as (Pq & Po & Pob).
  assert_PROP (headptr (gv _oracle)) as HO by entailer!.
  unfold u64_ok in R1, R2, R3, R4, R5, R6.
  assert (Lb0: 0 < Zlength bs).
  { rewrite Lbs. destruct (length_ok n) eqn:L; [ | lia ].
    unfold length_ok in L. apply andb_true_iff in L as [L1 _]. apply Z.ltb_lt in L1. lia. }
  (* the oracle's inputs *)
  freeze_other [t_obs] F1.
  Time (forward; forward; forward; forward; forward; forward; forward; forward; forward; forward; forward; forward;
        forward; forward).
  thaw F1. deadvars!.
  (* its phase *)
  freeze_oracle F2. freeze FR := (mem_mgr gv) (malloc_token _ _ _) (has_ext tt).
  Time forward_if (temp _t'18 (Vint (Int.repr (Z.b2z (negb qb && negb eb)%bool)))).
  { apply sel_tc_test; [ entailer! | auto ]. }
  { apply sel_ne_null in H. subst qb. forward; [ ptr_tc | ]. entailer!. ptr_val. }
  { apply sel_eq_null in H; [ subst qb | auto ]. forward. entailer!. }
  Time forward_if (temp _t'19 (Vint (Int.repr (Z.b2z (negb qb && negb eb && negb obb)%bool)))).
  { try b2z_hyp. forward; [ ptr_tc | ]. entailer!. ptr_val. }
  { try b2z_hyp. forward. entailer!. ptr_val. }
  set (valid := (negb qb && negb eb && negb obb && length_ok n)%bool).
  forward_if (temp _t'20 (Vint (Int.repr (Z.b2z valid)))).
  { try b2z_hyp. forward. entailer!. try unfold valid in *. destruct (length_ok n); ptr_val. }
  { try b2z_hyp. forward. entailer!. try unfold valid in *. destruct (length_ok n); ptr_val. }
  forward_if (temp _t'21 (Vint (Int.repr (if valid then 0 else 3)))).
  { try b2z_hyp. forward. entailer!. try unfold valid in *.
    match goal with E: _ = true |- _ => rewrite E end; reflexivity. }
  { try b2z_hyp. forward. entailer!. try unfold valid in *.
    match goal with E: _ = false |- _ => rewrite E end; reflexivity. }
  thaw FR. thaw F2.
  forward.
  rewrite signed_if by rep_lia.
  forward. forward. forward.
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with (vl 0).
  change (Vlong (Int64.repr (Int.signed (Int.repr 44)))) with (vl 44).
  deadvars!.
  (* the initial state *)
  replace (upd_Znth 0 (map vl (os_state s0)) (vl 44)) with (map vl (sublist 0 1 initial_state ++ Zrepeat 0 (12 - 1)))
    by reflexivity.
  freeze_but [_state] false F3.
  forward_for_simple_bound 12
    (EX k: Z, PROP ()
     LOCAL (temp _out_arg (sel qb v_out); temp _observation_arg (sel obb v_observation);
            temp _entries_arg (sel eb q); temp _entries q; temp _valid_length (Vint (Int.repr (Z.b2z (length_ok n))));
            temp _length (Vlong (Int64.repr n)); temp _o (gv _oracle);
            lvar _out t_result v_out; lvar _observation t_obs v_observation; gvars gv)
     SEP (FRZL F3;
          field_at Ews t_oracle (DOT _state) (map vl (sublist 0 k initial_state ++ Zrepeat 0 (12 - k))) (gv _oracle)))%assert.
  { entailer!. }
  { forward_if (temp _t'22 (Vint (Int.repr (Znth i initial_state)))).
    { forward. entailer!. u64c. rewrite init_state_Znth by lia. bool_dec. }
    { forward. entailer!. u64c. rewrite init_state_Znth by lia. bool_dec. }
    forward.
    entailer!.
    assert (Ri: 0 <= Znth i initial_state <= 256) by (rewrite init_state_Znth by lia; destruct (i =? 7); lia).
    rewrite Int.signed_repr by rep_lia.
    change (Vlong (Int64.repr (Znth i initial_state))) with (vl (Znth i initial_state)).
    rewrite upd_Znth_map_vl, init_state_step by lia. apply derives_refl. }
  thaw F3.
  replace (sublist 0 12 initial_state ++ Zrepeat 0 (12 - 12)) with initial_state by reflexivity.
  forward.
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with (vl 0).
  deadvars!.
  (* the record walk *)
  freeze_but [_nmi_count; _nmi] true F4.
  forward_if (EX c: Z, EX m: list Z,
    PROP (u64_ok c; Zlength m = 4; Forall u64_ok m;
          length_ok n = true -> match records bs with Some (c', m') => c = c' /\ m = m' | None => True end)
    LOCAL (temp _t'23 (Vint (Int.repr (if length_ok n then (if walk_b bs then 1 else 0) else 0)));
           temp _out_arg (sel qb v_out); temp _observation_arg (sel obb v_observation);
           temp _entries_arg (sel eb q); temp _entries q; temp _valid_length (Vint (Int.repr (Z.b2z (length_ok n))));
           temp _length (Vlong (Int64.repr n)); temp _o (gv _oracle);
           lvar _out t_result v_out; lvar _observation t_obs v_observation; gvars gv)
    SEP (FRZL F4; data_at Ews (tarray tuchar (Zlength bs)) (bytes_val bs) q;
         field_at Ews t_oracle (DOT _nmi_count) (vl c) (gv _oracle);
         field_at Ews t_oracle (DOT _nmi) (map vl m) (gv _oracle)))%assert.
  - try b2z_hyp.
    assert (Zbn: Zlength bs = n) by (rewrite Lbs; match goal with E: length_ok n = true |- _ => rewrite E end; reflexivity).
    assert (Ln: Zlength bs <= MAX_LENGTH) by (rewrite Zbn; match goal with E: length_ok n = true |- _ =>
      unfold length_ok in E; apply andb_true_iff in E as [_ E]; apply Z.leb_le in E; exact E end).
    rewrite fa_count, fa_nmi.
    sep_apply (data_at_data_at_ Ews tulong). sep_apply (data_at_data_at_ Ews (tarray tulong 4)).
    forward_call (q, Ews, bs, field_address t_oracle (DOT _nmi_count) (gv _oracle),
                  field_address t_oracle (DOT _nmi) (gv _oracle)).
    { entailer!. simpl. rewrite !fa_offset by first [ assumption | apply lnf_count | apply lnf_nmi ]. reflexivity. }
    Intros vret. destruct vret as [c m]. simpl fst in *; simpl snd in *.
    forward. Exists c m. rewrite <- fa_count, <- fa_nmi.
    match goal with E: length_ok n = true |- _ => rewrite E end.
    entailer!.
  - try b2z_hyp. forward. Exists 0 [0; 0; 0; 0].
    match goal with E: length_ok n = false |- _ => rewrite E end.
    entailer!. split; [ unfold u64_ok; rep_lia | repeat constructor; unfold u64_ok; rep_lia ].
  - Intros c m. forward. thaw F4. deadvars!.
    assert (Hob: obs_ok (mk_observation e1 e2 e3 e4 e5 e6)) by (unfold obs_ok, u64_ok; simpl; repeat split; lia).
    eapply semax_pre;
      [ | apply (tail_call gv q v_out v_observation n bs (mk_observation e1 e2 e3 e4 e5 e6) c m eb obb qb);
          first [ reflexivity | assumption | auto ] ].
    unfold ofields, s_main. entailer!.
Qed.
