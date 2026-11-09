(* Law handoff_decode_exact: the body of the harness's decode_done: the decoder's final checks on its current
   state, as the model's decode_done. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosHandoff.harness.handoff_decode_exact.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.LawProg LeanosHandoff.proof.LawDefs LeanosHandoff.proof.LawFacts
  LeanosHandoff.proof.LawLib.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Existing Instance LawProg.LCS.

(* The status decode_done returns. *)
Definition dd_rej (x: inputs) (s: list Z) : Z :=
  match i_call x with FAllocate => rejected_check s | _ => S_OK end.

Definition dd_status (x: inputs) (m: mem) : Z :=
  let s := current m in
  if projection x then
    if Znth 2 s =? 0 then
      if negb (Znth 1 s =? 1) then S_DECODE_INCOMPLETE_STATUS
      else if negb (Znth 5 s =? m_total m) then S_DECODE_INCOMPLETE_OFFSET
      else if negb (Znth 7 s =? 7) then S_DECODE_INCOMPLETE_PHASE
      else dd_rej x s
    else dd_rej x s
  else authority_check x (m_total m) s.

Lemma decode_done_ret: forall x m, decode_done x m = Return (dd_status x m) m.
Proof.
  intros. unfold decode_done, dd_status, projection_end, dd_rej.
  destruct (projection x); [ | reflexivity ].
  destruct (Znth 2 (current m) =? 0); [ unfold incomplete_check | simpl; destruct (i_call x); reflexivity ].
  destruct (negb (Znth 1 (current m) =? 1)); [ reflexivity | ].
  destruct (negb (Znth 5 (current m) =? m_total m)); [ reflexivity | ].
  destruct (negb (Znth 7 (current m) =? 7)); [ reflexivity | simpl; destruct (i_call x); reflexivity ].
Qed.

Lemma status_u32: forall st, 0 <= st <= S_AUTHORITY_REJECTED_TARGET -> u32_ok st.
Proof. intros. unfold u32_ok, S_AUTHORITY_REJECTED_TARGET in *. rep_lia. Qed.

Lemma authority_range: forall x T s, 0 <= authority_check x T s <= S_AUTHORITY_REJECTED_TARGET.
Proof.
  intros. unfold authority_check.
  unfold S_OK, S_AUTHORITY_REJECTED_STATUS, S_AUTHORITY_REJECTED_ERROR, S_AUTHORITY_REJECTED_OFFSET,
    S_AUTHORITY_REJECTED_PHASE, S_AUTHORITY_REJECTED_TARGET.
  repeat (destruct (negb _); [ lia | ]). lia.
Qed.

(* The current state's words, at the C's types. *)
Ltac cs_words cs Cok :=
  assert (0 <= Znth 1 cs <= Int64.max_unsigned) by (apply state_word; auto; lia);
  assert (0 <= Znth 2 cs <= Int64.max_unsigned) by (apply state_word; auto; lia);
  assert (0 <= Znth 5 cs <= Int64.max_unsigned) by (apply state_word; auto; lia);
  assert (0 <= Znth 7 cs <= Int64.max_unsigned) by (apply state_word; auto; lia);
  assert (0 <= Znth 16 cs <= Int64.max_unsigned) by (apply state_word; auto; lia).

(* A load of word k of the current state. *)
Ltac ld k := forward; try rewrite (Znth_map_vl _ k) by lia.

Ltac unfold_status :=
  unfold S_OK, S_DECODE_INCOMPLETE_STATUS, S_DECODE_INCOMPLETE_OFFSET, S_DECODE_INCOMPLETE_PHASE,
    S_DECODE_REJECTED_STATUS, S_DECODE_REJECTED_ERROR, S_AUTHORITY_REJECTED_STATUS, S_AUTHORITY_REJECTED_ERROR,
    S_AUTHORITY_REJECTED_OFFSET, S_AUTHORITY_REJECTED_PHASE, S_AUTHORITY_REJECTED_TARGET in *.

(* stop(m, r) with r the status decode_done returns (D: dd_status x m = r). *)
Ltac dd_stop x m P q s r :=
  let D := fresh "D" in
  assert (D: dd_status x m = r) by (unfold dd_status, dd_rej; rewrite P; unfold rejected_check,
    authority_check; unfold_status; u64c; bool_dec);
  forward_call (q, vi (w_expect s), vi (w_verdict s), r); try rewrite D.

(* The return after stop(m, r): the record s_stop s r, the states folded back. *)
Ltac dd_close q x m s F FCs Fsl Fs0 Fs1 Fat :=
  thaw F; unfold current;
  sep_apply (rows_fold q (m_states m) (m_at m) FCs Fsl Fs0 Fs1 Fat);
  match goal with D: dd_status x m = ?r |- _ =>
    Exists (s_stop s r); rewrite decode_done_ret, D; unfold lfields, s_stop; lst_cbn; entailer!;
    apply J_stop; auto; apply status_u32; unfold r, S_AUTHORITY_REJECTED_TARGET; lia
  end.

Lemma body_decode_done: semax_body nil [stop_spec] f_decode_done decode_done_spec.
Proof.
  start_function.
  rename H into Ix, H0 into Hs, H1 into Hm, H2 into Hd.
  lst_facts Hs. mem_facts Hm.
  pose proof (current_ok x m Hm) as Cok.
  cs_words (current m) Cok.
  pose proof (target_range x Ix) as Rt. pose proof (proj_code_range x) as Rp.
  pose proof (call_code_range (i_call x)) as Rc.
  assert (Lcs: Zlength (current m) = WORDS) by apply Cok.
  unfold lfields. Intros.
  assert_PROP (field_compatible t_law (DOT _states_expect) q) as FCs by entailer!.
  rewrite (states_split q (m_states m) FCs Fsl Fs0 Fs1).
  rewrite (rows_at q (m_states m) (m_at m) Fat). Intros.
  change (Znth (m_at m) (m_states m)) with (current m).
  freeze_but [_expect; _verdict; _total; _candidate; _projection; _call; _at] [row q (m_at m)] F.
  forward.
  forward.
  rewrite row_addr by (auto; destruct FCs; auto; lia).
  forward.
  forward_if.
  - (* a candidate *)
    assert (P: projection x = false).
    { unfold proj_code in *. destruct (projection x); [ | reflexivity ].
      exfalso. apply Int.one_not_zero. assumption. }
    assert (Cc: i_call x = FCandidate)
      by (destruct Hd as [Nc _]; unfold projection in P; destruct (i_call x); first [ reflexivity | discriminate | contradiction ]).
    assert (Tg: target x = i_candidate x) by (unfold target; rewrite Cc; reflexivity).
    rewrite Tg in *.
    ld 1.
    forward_if (PROP ()
      LOCAL (temp _s (row q (m_at m)); temp _m q)
      SEP (FRZL F; data_at Ews t_state (map vl (current m)) (row q (m_at m));
           field_at Ews t_law (DOT _call) (vi (call_code (i_call x))) q;
           field_at Ews t_law (DOT _total) (vi (m_total m)) q;
           field_at Ews t_law (DOT _candidate) (vl (i_candidate x)) q;
           field_at Ews t_law (DOT _projection) (vi (proj_code x)) q;
           field_at Ews t_law (DOT _at) (vi (m_at m)) q;
           field_at Ews t_law (DOT _expect) (vi E_NOTHING) q;
           field_at Ews t_law (DOT _verdict) (vi (dd_status x m)) q)).
    { dd_stop x m P q s S_AUTHORITY_REJECTED_STATUS. entailer!. }
    ld 2. forward_if.
    { dd_stop x m P q s S_AUTHORITY_REJECTED_ERROR. entailer!. }
    ld 5. forward. forward_if.
    { dd_stop x m P q s S_AUTHORITY_REJECTED_OFFSET. entailer!. }
    ld 7. forward_if.
    { dd_stop x m P q s S_AUTHORITY_REJECTED_PHASE. entailer!. }
    ld 16. forward. forward_if.
    { dd_stop x m P q s S_AUTHORITY_REJECTED_TARGET. entailer!. }
    { dd_stop x m P q s S_OK. entailer!. }
    forward.
    thaw F. unfold current.
    sep_apply (rows_fold q (m_states m) (m_at m) FCs Fsl Fs0 Fs1 Fat).
    Exists (s_stop s (dd_status x m)). rewrite decode_done_ret. unfold lfields, s_stop; lst_cbn.
    rewrite Tg. entailer!.
    apply J_stop; auto. apply status_u32. unfold dd_status. rewrite P. apply authority_range.
  - (* a projection *)
    assert (P: projection x = true).
    { unfold proj_code in *. destruct (projection x); [ reflexivity | ].
      exfalso. match goal with H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end. }
    assert (Nc: i_call x <> FCandidate) by (intro C; unfold projection in P; rewrite C in P; discriminate).
    assert (Tg: target x = 0) by (unfold target; destruct (i_call x); first [ reflexivity | contradiction ]).
    ld 2.
    forward_if (PROP (dd_status x m = dd_rej x (current m))
      LOCAL (temp _s (row q (m_at m)); temp _m q)
      SEP (FRZL F; data_at Ews t_state (map vl (current m)) (row q (m_at m));
           field_at Ews t_law (DOT _call) (vi (call_code (i_call x))) q;
           field_at Ews t_law (DOT _total) (vi (m_total m)) q;
           field_at Ews t_law (DOT _candidate) (vl (target x)) q;
           field_at Ews t_law (DOT _projection) (vi (proj_code x)) q;
           field_at Ews t_law (DOT _at) (vi (m_at m)) q;
           field_at Ews t_law (DOT _expect) (vi (w_expect s)) q;
           field_at Ews t_law (DOT _verdict) (vi (w_verdict s)) q)).
    + (* no error: the incomplete checks *)
      ld 1. forward_if.
      { dd_stop x m P q s S_DECODE_INCOMPLETE_STATUS. forward. dd_close q x m s F FCs Fsl Fs0 Fs1 Fat. }
      ld 5. forward. forward_if.
      { dd_stop x m P q s S_DECODE_INCOMPLETE_OFFSET. forward. dd_close q x m s F FCs Fsl Fs0 Fs1 Fat. }
      ld 7. forward_if.
      { dd_stop x m P q s S_DECODE_INCOMPLETE_PHASE. forward. dd_close q x m s F FCs Fsl Fs0 Fs1 Fat. }
      forward. entailer!. unfold dd_status. rewrite P. u64c. bool_dec.
    + forward. entailer!. unfold dd_status. rewrite P. u64c. bool_dec.
    + Intros.
      match goal with H: dd_status x m = _ |- _ => rename H into Ed end.
      forward.
      forward_if (temp _t'2 (Vint (Int.repr (Z.b2z (is_alloc x && negb (Znth 1 (current m) =? 1)))))).
      { assert (Ca: i_call x = FAllocate)
          by (u64c; apply call_code_inj; assumption).
        ld 1. forward. entailer!. unfold is_alloc. rewrite Ca. bool_fin. }
      { assert (Ca: i_call x <> FAllocate) by (intro C; rewrite C in *; u64c; contradiction).
        forward. entailer!. unfold is_alloc. destruct (i_call x); first [ contradiction | reflexivity ]. }
      forward_if.
      { (* the decoder accepted a state the allocation rejects: its status *)
        try b2z_hyp. match goal with E: _ && _ = true |- _ => apply andb_prop in E; destruct E as [Ea E1] end.
        assert (Ca: i_call x = FAllocate) by (unfold is_alloc in Ea; destruct (i_call x); congruence).
        assert (D: dd_status x m = S_DECODE_REJECTED_STATUS)
          by (rewrite Ed; unfold dd_rej, rejected_check; unfold is_alloc in *; rewrite Ca in *; cbn [andb negb] in *;
              unfold_status; bool_dec).
        forward_call (q, vi (w_expect s), vi (w_verdict s), S_DECODE_REJECTED_STATUS).
        dd_close q x m s F FCs Fsl Fs0 Fs1 Fat. }
      try b2z_hyp. forward.
      forward_if (temp _t'1 (Vint (Int.repr (Z.b2z (is_alloc x && negb (Znth 2 (current m) =? 0)))))).
      { assert (Ca: i_call x = FAllocate)
          by (u64c; apply call_code_inj; assumption).
        ld 2. forward. entailer!. unfold is_alloc. rewrite Ca. bool_fin. }
      { assert (Ca: i_call x <> FAllocate) by (intro C; rewrite C in *; u64c; contradiction).
        forward. entailer!. unfold is_alloc. destruct (i_call x); first [ contradiction | reflexivity ]. }
      forward_if.
      { (* its error *)
        try b2z_hyp. match goal with E: _ && _ = true |- _ => apply andb_prop in E; destruct E as [Ea E2] end.
        assert (Ca: i_call x = FAllocate) by (unfold is_alloc in Ea; destruct (i_call x); congruence).
        assert (D: dd_status x m = S_DECODE_REJECTED_ERROR)
          by (rewrite Ed; unfold dd_rej, rejected_check; unfold is_alloc in *; rewrite Ca in *; cbn [andb negb] in *;
              unfold_status; bool_dec).
        forward_call (q, vi (w_expect s), vi (w_verdict s), S_DECODE_REJECTED_ERROR).
        dd_close q x m s F FCs Fsl Fs0 Fs1 Fat. }
      { (* OK *)
        try b2z_hyp.
        assert (D: dd_status x m = S_OK).
        { rewrite Ed. unfold dd_rej, rejected_check. unfold is_alloc in *.
          destruct (i_call x); try reflexivity. cbn [andb] in *. unfold_status. bool_dec. }
        forward_call (q, vi (w_expect s), vi (w_verdict s), S_OK).
        dd_close q x m s F FCs Fsl Fs0 Fs1 Fat. }
Qed.
