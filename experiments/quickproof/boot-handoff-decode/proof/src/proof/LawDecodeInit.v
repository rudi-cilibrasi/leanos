(* Law handoff_decode_exact: the body of the harness's decoder reset export against decode_init_spec Ora_law: its
   checks follow from the call the model expects, and the answer it records moves the law's record as the model's
   step: the next word, or after word 40 the reset's state and checks (LawDecodeInit2). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosHandoff.harness.handoff_decode_exact.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.LawProg LeanosHandoff.proof.LawDefs LeanosHandoff.proof.LawFacts
  LeanosHandoff.proof.LawLib LeanosHandoff.proof.LawLib2 LeanosHandoff.proof.LawLib3
  LeanosHandoff.proof.LawDecodeInit2.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Existing Instance LawProg.LCS.

Lemma body_decode_init: semax_body Vlaw Gdinit f_leanos_boot_decode_init_v5 (decode_init_spec Ora_law).
Proof.
  start_function.
  rename H into Nc.
  ora_open x h p s ce ie.
  destruct (next_go x h p _ Hrun Nc) as (g & m & -> & Ec).
  destruct (call_decode_init x g m _ _ _ _ _ (eq_sym Ec)) as (a & -> & -> & -> & -> & -> & ->).
  pose proof HJ as (Hs & Hm & G). cbn [mem_of] in *.
  pose proof G as (Ge & (Pw & Pa) & La & Dc).
  lst_facts Hs. mem_facts Hm. pose proof Ix as Ix'. inputs_facts Ix'.
  pose proof (target_range x Ix) as Rt.
  unfold E_DECODE_INIT in Ge.
  assert (La0: 0 <= Zlength a) by apply Zlength_nonneg.
  unfold lfields. Intros.
  forward.
  if2. gp.
  if2. if2. if2. gp.
  forward_call tt. Intros v.
  forward. vl_temps. forward.
  upd_vl.
  forward.
  forward_if.
  - (* another word *)
    change (Int.sub (Int.repr 41) (Int.repr 1)) with (Int.repr 40) in *.
    forward. forward. forward.
    Exists v. u64c.
    assert (Rn: run x (start x) (h ++ [(DecodeInit (i_magic x) (i_address x) (m_total m) (target x) (Zlength a), v)])
                = Some (Go (ExpectDecodeInit (a ++ [v])) m)).
    { rewrite (run_snoc' x h (ExpectDecodeInit a) m _ v Hrun Ec). cbn [step].
      rewrite step_more by lia. reflexivity. }
    assert (HJ': J x (Go (ExpectDecodeInit (a ++ [v])) m) (s_more s v)).
    { unfold J; split_and; auto.
      - apply lst_ok_more; auto; lia.
      - unfold go_inv, s_more; lst_cbn; split_and; auto.
        + apply prefix_more; [ split; auto | lia ].
        + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
    change (Vlong (Int64.repr (w_word s + 1))) with (vl (w_word s + 1)).
    ora_fin (Go (ExpectDecodeInit (a ++ [v])) m) (s_more s v) ce ie.
  - (* word 40: the reset's state and checks *)
    change (Int.sub (Int.repr 41) (Int.repr 1)) with (Int.repr 40) in *.
    u64c.
    assert (W40: w_word s = 40) by lia.
    sep_apply (lfields_fold (gv _law) x ce ie m (s_store s v)).
    eapply semax_pre; [ | apply (di_tail gv x h s m a v ce ie); first [ reflexivity | assumption | auto ] ].
    entailer!.
Qed.
