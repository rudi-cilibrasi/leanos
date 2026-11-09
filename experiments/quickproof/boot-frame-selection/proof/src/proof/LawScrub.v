(* Law frame_selection_exact: the body of the harness's scrub law_scrub against scrub_spec Ora_law: its checks
   follow from the scrub the model expects (of the selected frame), and its answer stops the step as the model's:
   OK and scrubbed 1 when the answer is 1, SCRUB otherwise. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosFrameSelection.harness.frame_selection_exact.code.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
Require Import LeanosFrameSelection.proof.LawProg LeanosFrameSelection.proof.LawDefs LeanosFrameSelection.proof.LawFacts
  LeanosFrameSelection.proof.LawLib.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Existing Instance LawProg.LCS.

Definition scrub_fspec : ident * funspec := (_law_scrub, scrub_spec Ora_law).

Definition Gscrub : funspecs := [gp_assert_spec; any_u64_spec; stop_spec].

Definition s_scrubbed (s: lst) (v: Z) : lst :=
  set_stop (set_scrubbed s (Z.b2z (v =? 1))) (if v =? 1 then S_OK else S_SCRUB).

Lemma J_scrubbed: forall x m s v, i_step x = FScrub -> lst_ok s ->
  J x (Return (if v =? 1 then S_OK else S_SCRUB) m) (s_scrubbed s v).
Proof.
  intros x m s v F L. lst_facts L. unfold J, seq_ok. split_and.
  - unfold lst_ok, s_scrubbed; set_unfold; lst_cbn. split_and; auto; unfold u32_ok, u64_ok, E_NOTHING;
      destruct (v =? 1); cbn [Z.b2z]; unfold S_OK, S_SCRUB; rep_lia.
  - intros G. congruence.
  - intros _ m' E. inversion E. unfold s_scrubbed; set_unfold; lst_cbn.
    destruct (v =? 1); [ reflexivity | unfold S_OK, S_SCRUB in *; discriminate ].
  - unfold ret_inv, s_scrubbed; set_unfold; lst_cbn. split; reflexivity.
Qed.

Lemma body_law_scrub: semax_body Vlaw Gscrub f_law_scrub scrub_fspec.
Proof.
  start_function.
  rename H into Nc.
  ora_open p s.
  destruct (next_go x h p _ Hrun Nc) as (g & m & -> & Ec).
  destruct (call_scrub x g m f (eq_sym Ec)) as [-> Ef].
  pose proof (progress_of_run x h _ Ix Ah Hrun) as (Fs & _ & Mm & Km). cbn [stage_step] in Fs.
  pose proof HJ as (Hs & Hq & Ge). cbn [go_inv] in Ge.
  lst_facts Hs. inputs_facts Ix.
  unfold lfields. Intros.
  forward.
  forward_if (temp _t'1 (Vint Int.one)).
  { forward. forward. entailer!; rewrite ?Ge; try reflexivity. }
  { else_false. }
  forward_if (temp _t'2 (Vint Int.one)).
  { forward. forward. entailer!; rewrite ?Ef, ?Int64.eq_true; try reflexivity. }
  { else_false. }
  forward_call Int.one.
  rewrite <- seq_assoc. forward_call tt. Intros v.
  forward.
  rewrite (Int64.unsigned_repr v) by rep_lia. rewrite (low32 v).
  assert (Rv: u32_ok (v mod 2 ^ 32)) by (apply low32_range).
  remember (v mod 2 ^ 32) as w eqn:Ew. clear Ew. pose proof Rv as Rv'. unfold u32_ok in Rv'.
  forward.
  rewrite (Int_eq_repr w 1) by rep_lia.
  forward_if (temp _t'4 (vi (if w =? 1 then S_OK else S_SCRUB))).
  { u64c. forward. entailer!. all: try (destruct (Z.eqb_spec w 1); [ reflexivity | lia ]). }
  { u64c. forward. entailer!. all: try (destruct (Z.eqb_spec w 1); [ lia | reflexivity ]). }
  forward_call (gv _law, vi (w_expect s), vi (w_verdict s), if w =? 1 then S_OK else S_SCRUB).
  forward.
  Exists w.
  assert (Rn: run x (start x) (h ++ [(Scrub (i_selected x), Word w)]) =
              Some (Return (if w =? 1 then S_OK else S_SCRUB) m)).
  { apply (run_word' x h ExpectScrub m w Hrun). intros c k E. discriminate. }
  pose proof (J_scrubbed x m s w (eq_sym Fs) Hs) as HJ'.
  try subst f.
  unfold Ora_law. Exists (Return (if w =? 1 then S_OK else S_SCRUB) m) (s_scrubbed s w).
  unfold lfields, s_scrubbed; set_unfold; lst_cbn; cbn [mem_of].
  entailer!.
  apply answers_ok_snoc; auto.
Qed.
