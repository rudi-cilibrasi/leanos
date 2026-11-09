(* Law frame_selection_exact: the body of the harness's export leanos_boot_projection_finish against finish_spec
   Ora_law, up to its 64 stores (LawFinStores) and then LawFinTail: its checks follow from the terminal result's word q the model expects (the decoded state's words 1, 2,
   11 and 17, the overlay's status and error, owner 1 and the 64 free words), and the answer moves the law's
   record as the model's finish_done: the next word, or after word 8 the terminal checks. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosFrameSelection.harness.frame_selection_exact.code.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
Require Import LeanosFrameSelection.proof.LawProg LeanosFrameSelection.proof.LawDefs LeanosFrameSelection.proof.LawFacts
  LeanosFrameSelection.proof.LawLib LeanosFrameSelection.proof.LawLib2 LeanosFrameSelection.proof.LawRows
  LeanosFrameSelection.proof.LawLib3 LeanosFrameSelection.proof.LawFinStores
  LeanosFrameSelection.proof.LawFinTail.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Existing Instance LawProg.LCS.

Definition finish_fspec : ident * funspec := finish_spec Ora_law.


Lemma body_finish: semax_body Vlaw Gfinish f_leanos_boot_projection_finish finish_fspec.
Proof.
  start_function.
  match goal with H: next_call _ _ = _ |- _ => rename H into Nc end.
  ora_open p s.
  destruct (next_go x h p _ Hrun Nc) as (g & m & -> & Ec). cbn [mem_of].
  pose proof (progress_of_run x h _ Ix Ah Hrun) as (Fs & _ & Mm & Km).
  destruct (call_finish x g m ds de ms me cnt hi own q fw (eq_sym Ec)) as (-> & Eds & Ede & Ecnt & Ehi & Eown).
  cbn [stage_step] in Fs.
  pose proof HJ as (Hs & Hq & Ge). cbn [go_inv] in Ge.
  destruct Ge as (Ge & Gw & Gq & Gms & Gme & Gf).
  lst_facts Hs. inputs_facts Ix. mem_facts Mm.
  subst ds de cnt hi own q ms me fw.
  assert (Lfw: Zlength (w_free s) = Z.of_nat 64) by (rewrite Lfl; reflexivity).
  unfold lfields. Intros.
  freeze_but [_call; _expect; _verdict; _word; _decoded; _manifest_status; _manifest_error; _free_words;
              _terminal_expect] [v_words] F.
  forward.
  if1.
  forward_call Int.one.
  rng_at (i_decoded x) [1; 2; 11; 17].
  do 6 if1.
  forward_call Int.one.
  deadvars!.
  assert (Lfw': Zlength (w_free s) = 64) by (rewrite Lfw; reflexivity).
  freeze_but (@nil ident) [v_words] F2.
  subst MORE_COMMANDS. unfold abbreviate.
  eapply semax_pre; [ | apply (semax_finish_stores gv (gv _law) (w_free s) v_words (FRZL F2)); [ reflexivity | exact Lfw' | ] ].
  { unfold finish_locals. entailer!. }
  unfold finish_locals. thaw F2. thaw F.
  sep_apply (lfields_fold (gv _law) x sp m s).
  eapply semax_pre; [ | apply (fin_tail gv sp x h s m v_words Ix Ah Mm (eq_sym Fs) Hrun HJ); reflexivity ].
  entailer!.
Qed.
