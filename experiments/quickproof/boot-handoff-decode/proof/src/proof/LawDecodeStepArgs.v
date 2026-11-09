(* Law handoff_decode_exact: the body of the harness's decoder transition export against decode_step_spec Ora_law:
   its 35 equality checks of the state's words (read through `o = m->states_expect[m->at]`), the chunk, its offset
   and terminal marker follow from the call the model expects; the answer it records moves the law's record as the
   model's step: the next word, or after word 40 the transition's state and its end (LawDecodeStepDone). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosHandoff.harness.handoff_decode_exact.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.LawProg LeanosHandoff.proof.LawDefs LeanosHandoff.proof.LawFacts
  LeanosHandoff.proof.LawLib LeanosHandoff.proof.LawLib2 LeanosHandoff.proof.LawLib3
  LeanosHandoff.proof.LawDecodeStepDone LeanosHandoff.proof.LawDecodeStepW.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Existing Instance LawProg.LCS.

Lemma body_decode_step: semax_body Vlaw Gdstep f_leanos_boot_decode_step_v5 (decode_step_spec Ora_law).
Proof.
  start_function.
  rename H into Nc.
  ora_open x h p w ce ie.
  destruct (next_go x h p _ Hrun Nc) as (g & m & -> & Ec).
  destruct (call_decode_step x g m _ _ _ _ _ _ (eq_sym Ec)) as (k & a & -> & -> & -> & -> & -> & -> & ->).
  pose proof HJ as (Hs & Hm & G). cbn [mem_of] in *.
  pose proof G as (Ge & Gk & Gv & (Pw & Pa) & La & Gk0 & Gkt & Dc).
  subst k.
  lst_facts Hs. mem_facts Hm. pose proof Ix as Ix'. inputs_facts Ix'.
  pose proof Dc as (Nc' & (Te & Tm) & Td).
  unfold E_DECODE_STEP in Ge.
  assert (La0: 0 <= Zlength a) by apply Zlength_nonneg.
  pose proof (current_ok x m Hm) as Cok.
  assert (Lcs: Zlength (current m) = WORDS) by apply Cok.
  assert (Lmcs: Zlength (map vl (current m)) = WORDS) by (rewrite Zlength_map; lia).
  assert (Kd: 0 <= w_chunk w < Zlength (decoded x m)).
  { split; [ lia | ]. pose proof (Z.div_mod (m_total m) 8 ltac:(lia)) as Dm. rewrite Tm in Dm. lia. }
  assert (Rv: 0 <= w_value w <= Int64.max_unsigned) by lia.
  pose proof (terminal_range (m_total m) (w_chunk w)) as Rt.
  unfold lfields. Intros.
  assert_PROP (field_compatible t_law (DOT _states_expect) (gv _law)) as FCs by entailer!.
  rewrite (states_split (gv _law) (m_states m) FCs Fsl Fs0 Fs1).
  rewrite (rows_at (gv _law) (m_states m) (m_at m) Fat). Intros.
  change (Znth (m_at m) (m_states m)) with (current m).
  forward.
  if2. gp.
  forward. forward.
  rewrite row_addr by (auto; destruct FCs; auto; lia).
  freeze_but (@nil ident) [row (gv _law) (m_at m)] FZ.
  (* words 0..18 *)
  if2. if2. if2. if2. if2. if2. if2. if2. if2. if2.
  if2. if2. if2. if2. if2. if2. if2. if2. gp.
  thaw FZ.
  sep_apply (lfields_ns_fold (gv _law) x ce ie m w).
  eapply semax_pre;
    [ | apply (ds_words gv x h w m a ce ie); first [ reflexivity | assumption | auto ] ].
  entailer!.
Qed.
