(* Law handoff_decode_exact: the body of the harness's bootloader_read against read_spec Ora_law: its checks follow
   from the read the model expects (the size read or chunk k's), and the answer it records moves the law's record
   as the model's step: the bounds on the size read, then the stream's reset; or chunk k's transition. *)
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

Definition read_fspec : ident * funspec := (_bootloader_read, read_spec Ora_law).

Definition Gread : funspecs := [gp_assert_spec; any_u64_spec; stop_spec; begin_stream_spec].

Lemma law_valid: forall v q, field_at Ews t_law (DOT _call) v q |-- valid_pointer q.
Proof.
  intros. apply field_at_valid_ptr0; [ apply readable_nonidentity, writable_readable, writable_Ews | | ];
    reflexivity.
Qed.
#[local] Hint Resolve law_valid : valid_pointer.

(* The size the read declares: its low 32 bits. *)
Lemma low32: forall v, Int.repr v = Int.repr (v mod 2 ^ 32).
Proof.
  intros. rewrite <- (Int.repr_unsigned (Int.repr v)). rewrite Int.unsigned_repr_eq. reflexivity.
Qed.

Lemma low32_range: forall v, 0 <= v mod 2 ^ 32 <= Int.max_unsigned.
Proof. intros. pose proof (Z.mod_pos_bound v (2 ^ 32) ltac:(lia)). unfold Int.max_unsigned, Int.modulus; simpl. lia. Qed.

Lemma and7: forall T, 0 <= T <= Int.max_unsigned -> Int.and (Int.repr T) (Int.repr 7) = Int.repr (T mod 8).
Proof.
  intros T R. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia.
  change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
Qed.

Ltac mem_cbn := cbn [mem_of m_total m_extent_ok m_copy m_usable m_blocked m_reserved m_states m_at
  with_extent with_copy with_bitmaps with_states Z.b2z] in *.

(* The oracle at the record s' and the model's p' (R: the run, HJ': the invariant). *)
Ltac ora_fin p' s' ce ie :=
  unfold Ora_law; Exists p' s' ce ie; unfold lfields, arrays; mem_cbn; lst_cbn; entailer!.

Ltac lim_fix :=
  change (Int.mul (Int.mul (Int.repr 16) (Int.repr 1024)) (Int.repr 1024)) with (Int.repr 16777216) in *;
  rewrite ?sub_repr' in *.

Lemma body_bootloader_read: semax_body Vlaw Gread f_bootloader_read read_fspec.
Proof.
  start_function.
  rename H into Nc.
  unfold Ora_law. Intros p s ce ie.
  repeat match goal with H: ?c = gv _law |- _ => is_var c; subst c end.
  match goal with H: inputs_ok x |- _ => rename H into Ix end.
  match goal with H: x_fit x |- _ => rename H into Xf end.
  match goal with H: run x (start x) h = Some p |- _ => rename H into Hrun end.
  match goal with H: J x p s |- _ => rename H into HJ end.
  match goal with H: ptr_ok x ce ie |- _ => rename H into Pie end.
  destruct (next_go x h p _ Hrun Nc) as (g & m & -> & Ec).
  pose proof HJ as (Hs & Hm & G). cbn [mem_of] in Hm.
  lst_facts Hs. mem_facts Hm. pose proof Ix as Ix'. inputs_facts Ix'.
  destruct (call_read x g m a (eq_sym Ec)) as [(-> & ->) | (k & st & -> & ->)].
  - (* the size read *)
    pose proof G as (Ge & Gc & Ga). unfold E_SIZE in Ge.
    unfold lfields. Intros.
    forward.
    forward_call Int.one.
    forward.
    forward_if (temp _t'1 (Vint Int.one)).
    { forward. entailer!. }
    { else_false. }
    forward_call Int.one.
    forward_call tt. Intros v.
    forward.
    forward_if.
    2: { else_false. }
    forward. forward_call Int.one.
    { entailer!. rewrite Int64.eq_true. reflexivity. }
    forward.
    rewrite Int64.unsigned_repr by rep_lia. rewrite low32.
    pose proof (low32_range v) as RT.
    set (T := v mod 2 ^ 32) in *.
    assert (R8: 0 <= T mod 8 < 8) by (apply Z.mod_pos_bound; lia).
    assert (Rn: run x (start x) (h ++ [(Read (i_address x), v)]) = Some (size_done x T m))
      by (apply (run_snoc' x h ExpectSize m); auto).
    forward_if (PROP () LOCAL (temp _v (vl v))
      SEP (Ora_law gv (gv _law) (gv _law) x (h ++ [(Read (i_address x), v)]))).
    { (* SMALL *)
      u64c. assert (B: bounds_check x T = S_BOUNDS_SMALL) by (unfold bounds_check; bool_dec).
      forward_call (gv _law, vi (w_expect s), vi (w_verdict s), S_BOUNDS_SMALL).
      assert (R': size_done x T m = Return S_BOUNDS_SMALL m) by (unfold size_done; rewrite B; reflexivity).
      rewrite R' in Rn. pose proof (J_stop x m s S_BOUNDS_SMALL Hs Hm ltac:(unfold u32_ok, S_BOUNDS_SMALL; rep_lia)).
      ora_fin (Return S_BOUNDS_SMALL m) (s_stop s S_BOUNDS_SMALL) ce ie. }
    forward_if.
    { (* LARGE *)
      u64c. assert (B: bounds_check x T = S_BOUNDS_LARGE) by (unfold bounds_check; bool_dec).
      forward_call (gv _law, vi (w_expect s), vi (w_verdict s), S_BOUNDS_LARGE).
      assert (R': size_done x T m = Return S_BOUNDS_LARGE m) by (unfold size_done; rewrite B; reflexivity).
      rewrite R' in Rn. pose proof (J_stop x m s S_BOUNDS_LARGE Hs Hm ltac:(unfold u32_ok, S_BOUNDS_LARGE; rep_lia)).
      ora_fin (Return S_BOUNDS_LARGE m) (s_stop s S_BOUNDS_LARGE) ce ie. }
    forward_if.
    { (* ALIGNMENT *)
      rewrite and7 in * by rep_lia. u64c.
      assert (B: bounds_check x T = S_BOUNDS_ALIGNMENT)
        by (pose proof (Z.mod_pos_bound T 8 ltac:(lia)); unfold bounds_check; bool_dec).
      forward_call (gv _law, vi (w_expect s), vi (w_verdict s), S_BOUNDS_ALIGNMENT).
      assert (R': size_done x T m = Return S_BOUNDS_ALIGNMENT m) by (unfold size_done; rewrite B; reflexivity).
      rewrite R' in Rn.
      pose proof (J_stop x m s S_BOUNDS_ALIGNMENT Hs Hm ltac:(unfold u32_ok, S_BOUNDS_ALIGNMENT; rep_lia)).
      ora_fin (Return S_BOUNDS_ALIGNMENT m) (s_stop s S_BOUNDS_ALIGNMENT) ce ie. }
    rewrite and7 in * by rep_lia.
    forward.
    forward_if.
    { (* LIMIT *)
      lim_fix. u64c.
      assert (B: bounds_check x T = S_BOUNDS_LIMIT)
        by (pose proof (Z.mod_pos_bound T 8 ltac:(lia)); unfold bounds_check; bool_dec).
      forward_call (gv _law, vi (w_expect s), vi (w_verdict s), S_BOUNDS_LIMIT).
      assert (R': size_done x T m = Return S_BOUNDS_LIMIT m) by (unfold size_done; rewrite B; reflexivity).
      rewrite R' in Rn.
      pose proof (J_stop x m s S_BOUNDS_LIMIT Hs Hm ltac:(unfold u32_ok, S_BOUNDS_LIMIT; rep_lia)).
      ora_fin (Return S_BOUNDS_LIMIT m) (s_stop s S_BOUNDS_LIMIT) ce ie. }
    { (* the extent T: the stream's reset *)
      lim_fix. u64c.
      assert (B: bounds_check x T = S_OK)
        by (pose proof (Z.mod_pos_bound T 8 ltac:(lia)); unfold bounds_check; bool_dec).
      forward. forward.
      forward_call (gv _law, vl (w_word s), vi (w_expect s)).
      assert (R': size_done x T m = Go (ExpectStreamInit nil) (with_extent m T))
        by (unfold size_done; rewrite B; reflexivity).
      rewrite R' in Rn.
      set (s' := mk_lst (w_running s) (w_records s) E_STREAM_INIT (w_verdict s) (w_chunk s) 0 (w_block s)
                        (w_value s) (w_stream s) (w_answer s)).
      assert (HJ': J x (Go (ExpectStreamInit nil) (with_extent m T)) s').
      { unfold J; split_and.
        - unfold lst_ok, s'; lst_cbn; split_and; auto; unfold u32_ok, u64_ok, E_STREAM_INIT; rep_lia.
        - apply mem_fit_extent; auto.
        - unfold go_inv, s'; lst_cbn. split_and; auto.
          + apply prefix_nil. reflexivity.
          + rewrite Zlength_nil; lia.
          + unfold copy_ctx, extent_fits. cbn [m_total with_extent]. split; [ left; auto | split; lia ]. }
      ora_fin (Go (ExpectStreamInit nil) (with_extent m T)) s' ce ie. }
    forward. Exists v. entailer!.
  - (* chunk k *)
    pose proof G as (Ge & Gk & Gst & Gk0 & Gkt & Gc). unfold E_CHUNK in Ge. subst k st.
    pose proof Gc as (Cc & Te & Tm).
    unfold lfields. Intros.
    forward.
    forward_call Int.one.
    forward.
    forward_if (temp _t'1 (Vint Int.one)).
    { else_false. }
    { forward. forward. entailer!. }
    forward_call Int.one.
    forward_call tt. Intros v.
    forward.
    forward_if.
    { else_false. }
    forward. forward.
    forward_call Int.one.
    { entailer!. rewrite Int64.eq_true. reflexivity. }
    forward. forward. forward.
    assert (Rn: run x (start x) (h ++ [(Read (i_address x + 8 * w_chunk s), v)]) =
                Some (Go (ExpectStreamStep (w_chunk s) (w_stream s) v nil) m))
      by (apply (run_snoc' x h (ExpectChunk (w_chunk s) (w_stream s)) m); auto).
    set (s' := mk_lst (w_running s) (w_records s) E_STREAM_STEP (w_verdict s) (w_chunk s) 0 (w_block s) v
                      (w_stream s) (w_answer s)).
    assert (HJ': J x (Go (ExpectStreamStep (w_chunk s) (w_stream s) v nil) m) s').
    { unfold J; split_and; auto.
      - unfold lst_ok, s'; lst_cbn; split_and; auto; unfold u32_ok, u64_ok, E_STREAM_STEP; rep_lia.
      - unfold go_inv, s'; lst_cbn. split_and; auto.
        + apply prefix_nil. reflexivity.
        + rewrite Zlength_nil; lia. }
    forward.
    Exists v.
    change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with (vl 0).
    change (Vint (Int.repr 3)) with (vi E_STREAM_STEP).
    ora_fin (Go (ExpectStreamStep (w_chunk s) (w_stream s) v nil) m) s' ce ie.
Qed.
