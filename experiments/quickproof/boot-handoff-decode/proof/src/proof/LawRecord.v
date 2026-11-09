(* Law handoff_decode_exact: the body of the harness's projection_record against record_spec Ora_law: its checks
   follow from the record the model expects (the entry event of the current state, its slot below 256), and the
   call moves the law's record as the model's step: the event's block projections, from block 0. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosHandoff.harness.handoff_decode_exact.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.LawProg LeanosHandoff.proof.LawDefs LeanosHandoff.proof.LawFacts
  LeanosHandoff.proof.LawLib LeanosHandoff.proof.LawLib2 LeanosHandoff.proof.LawLib3.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Existing Instance LawProg.LCS.

Definition record_fspec : ident * funspec := (_projection_record, record_spec Ora_law).

Definition Grec : funspecs := [gp_assert_spec].

Ltac cmp_close3 :=
  try change (Int.signed (Int.repr 1)) with 1 in *;
  rewrite ?sub64_repr' in *;
  cmp_close2.

Ltac if4 :=
  to_branch;
  match goal with |- semax _ _ ?c _ =>
    let s := first_stmt c in
    lazymatch s with
    | Sifthenelse _ _ (Sset ?t (Econst_int (Int.repr 0) tint)) => forward_if (temp t (Vint Int.one))
    end
  end;
  [ solve [ repeat forward; entailer!; try cmp_close3 ]
  | solve [ try change (Int.signed (Int.repr 1)) with 1 in *; rewrite ?sub64_repr' in *; else_false2 ] | ].

Lemma body_projection_record: semax_body Vlaw Grec f_projection_record record_fspec.
Proof.
  start_function.
  rename H into Nc.
  ora_open x h p s ce ie.
  destruct (next_go x h p _ Hrun Nc) as (g & m & -> & Ec).
  destruct (call_record x g m _ _ _ _ (eq_sym Ec)) as (k & -> & -> & -> & -> & ->).
  pose proof HJ as (Hs & Hm & G). cbn [mem_of] in *.
  pose proof G as (Ge & Gk & Gk0 & Gkt & Dc & E11).
  lst_facts Hs. mem_facts Hm.
  unfold E_RECORD in Ge.
  pose proof (current_ok x m Hm) as Cok.
  assert (Lcs: Zlength (current m) = WORDS) by apply Cok.
  assert (R11: 0 <= Znth 11 (current m) <= Int64.max_unsigned) by (apply state_word; auto; lia).
  assert (R20: 0 <= Znth 20 (current m) <= Int64.max_unsigned) by (apply state_word; auto; lia).
  assert (R21: 0 <= Znth 21 (current m) <= Int64.max_unsigned) by (apply state_word; auto; lia).
  assert (R22: 0 <= Znth 22 (current m) <= Int64.max_unsigned) by (apply state_word; auto; lia).
  unfold lfields. Intros.
  assert_PROP (field_compatible t_law (DOT _states_expect) (gv _law)) as FCs by entailer!.
  rewrite (states_split (gv _law) (m_states m) FCs Fsl Fs0 Fs1).
  rewrite (rows_at (gv _law) (m_states m) (m_at m) Fat). Intros.
  change (Znth (m_at m) (m_states m)) with (current m).
  forward.
  if4. gp.
  forward. forward.
  rewrite row_addr by (auto; destruct FCs; auto; lia).
  if4. if4. if4. if4. gp.
  forward. forward. forward. forward. forward.
  sep_apply (rows_fold (gv _law) (m_states m) (m_at m) FCs Fsl Fs0 Fs1 Fat).
  set (s' := mk_lst (w_running s) (Int.unsigned (Int.repr (w_records s + 1))) E_ENTRY (w_verdict s) (w_chunk s) 0 0
                    (w_value s) (w_stream s) (w_answer s)).
  assert (Rn: run x (start x) (h ++ [(Record (Znth 11 (current m) - 1) (Znth 20 (current m)) (Znth 21 (current m))
                                        (Znth 22 (current m)), 0)])
              = Some (Go (ExpectEntry k 0 nil) m)).
  { erewrite (run_snoc' x h _ m); [ | exact Hrun | reflexivity ]. reflexivity. }
  assert (HJ': J x (Go (ExpectEntry k 0 nil) m) s').
  { unfold J; split_and; auto.
    - unfold lst_ok, s'; lst_cbn. split_and; auto; try (unfold u32_ok, u64_ok, E_ENTRY; rep_lia).
      all: apply Int.unsigned_range_2.
    - unfold go_inv, s'; lst_cbn. split_and; auto; try lia.
      + apply prefix_nil. reflexivity.
      + rewrite Zlength_nil; lia. }
  change (Vint (Int.repr 7)) with (vi E_ENTRY).
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with (vl 0).
  replace (Vint (Int.add (Int.repr (w_records s)) (Int.repr 1)))
    with (vi (Int.unsigned (Int.repr (w_records s + 1))))
    by (unfold vi; rewrite Int.repr_unsigned, add_repr'; reflexivity).
  ora_fin (Go (ExpectEntry k 0 nil) m) s' ce ie.
Qed.
