(* The body of boot_frame_rescan: the order checks of the model's start (Defs.rescan_order), the decoder into
   state 1 (decode_done into ExpectRescanCandidate), the manifest's answer for the next frame, and the checks on
   state 1 with the record written on OK (rescan_done, rescan_check). *)
Require Import VST.floyd.proofauto.
Require Import LeanosFrameSelection.frame.code.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
Require Import LeanosFrameSelection.proof.InternalSpecs.
Require Import LeanosFrameSelection.proof.FsLemmas.
Require Import LeanosFrameSelection.proof.FsFast.
#[local] Ltac simplify_remove_localdef_temp ::= fast_remove_localdef_temp.
#[local] Existing Instance FrameSpecs.CS.
Local Open Scope Z_scope.

Lemma rescan_fail (x: inputs) (v: Z) (m: mem) (st: Z) :
  rescan_check x (Znth 1 (m_states m)) v = st -> st <> S_OK -> rescan_done x v m = Return st m.
Proof. intros C N. unfold rescan_done. rewrite C. rewrite (proj2 (Z.eqb_neq _ _) N). reflexivity. Qed.

(* A failed check of state 1 (a status other than OK): the history and memory of R. *)
Ltac rfail R st :=
  forward;
  lazymatch type of R with run _ _ ?L = Some (rescan_done _ _ ?M) =>
    Exists L st M; rewrite ?Znth_with_state by (auto; lia); entailer!;
    apply returns_return; rewrite R; f_equal; apply rescan_fail;
    [ unfold rescan_check; rewrite ?Znth_with_state by (auto; lia); zb; reflexivity | sne ]
  end.

Lemma body_boot_frame_rescan (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_boot_frame_rescan (boot_rescan_spec Ora).
Proof.
  start_function.
  rename H into HC, H0 into IX. match goal with H: isptr sp |- _ => rename H into PS end.
  destruct (inputs_facts x IX) as (_ & _ & _ & UP & UN & LM & UM & LD & UD & _ & _ & _ & _ & MO).
  pose proof MO as (_ & _ & _ & _ & LS & _ & _ & _ & LR & _).
  forward_if.
  { w64. forward. Exists (@nil answer) S_UNPUBLISHED_LIMIT (i_mem x). entailer!.
    apply returns_nil. unfold start; rewrite HC. unfold rescan_order. zb. reflexivity. }
  w64.
  forward_if.
  { w64. forward. Exists (@nil answer) S_UNPUBLISHED_ORDER (i_mem x). entailer!.
    apply returns_nil. unfold start; rewrite HC. unfold rescan_order. zb. reflexivity. }
  w64.
  assert (R0: run x (start x) nil = Some (Go ExpectRescanDecode (i_mem x)))
    by (cbn [run]; unfold start; rewrite HC; unfold rescan_order; zb; reflexivity).
  forward_call (gv, dctx, sctx, sp, x, @nil answer, i_next x, 1, wsh).
  { apply (next_call_go _ _ _ _ R0). }
  Intros vret. destruct vret as [st ws]. cbn [fst snd] in *.
  rename H into Ust, H0 into Lws, H1 into Uws.
  pose proof (run_decoded x (start x) nil ExpectRescanDecode (i_mem x) (i_next x) 1 st ws R0 eq_refl) as R1.
  cbn [step reply_value reply_state] in R1. unfold decode_done in R1.
  assert (E1: Znth 1 (upd_Znth 1 (m_states (i_mem x)) ws) = ws) by (apply upd_Znth_same; lia).
  forward_if.
  { w64. forward. forward.
    rewrite (proj2 (Z.eqb_neq _ _) H) in R1.
    Exists (nil ++ (Decode (i_next x) 1, Decoded st ws) :: nil) S_DECODER (with_decoder (with_state (i_mem x) 1 ws) st).
    cbn [m_states m_rescan m_decoder with_decoder with_state with_states]. rewrite E1.
    entailer!. apply returns_return; exact R1. }
  w64. subst st. rewrite Z.eqb_refl in R1.
  do 18 forward.
  forward_call (gv, dctx, sctx, sp, x, nil ++ (Decode (i_next x) 1, Decoded 0 ws) :: nil, i_next x, i_manifest x).
  { apply (next_call_go _ _ _ _ R1). }
  Intros v. rename H into Uv.
  pose proof (run_word x (start x) _ _ _ v R1 ltac:(intros; discriminate)) as R2.
  cbn [step reply_value expected] in R2.
  forward. forward. forward. forward_if. { w64. rfail R2 S_RESCAN_ENTRY_COUNT. } w64.
  forward. forward. forward_if. { w64. rfail R2 S_RESCAN_HIGHEST. } w64.
  forward. forward_if. { w64. rfail R2 S_RESCAN_TARGET. } w64.
  forward. forward_if. { w64. rfail R2 S_RESCAN_STATUS. } w64.
  forward. forward_if. { w64. rfail R2 S_RESCAN_USABLE. } w64.
  forward. forward_if. { w64. rfail R2 S_RESCAN_BLOCKED. } w64.
  forward_if. { w64. rfail R2 S_RESCAN_MANIFEST. } w64. try subst v.
  do 9 forward.
  rewrite upd_five by (rewrite Zlength_map; auto).
  forward.
  match type of R2 with run _ _ ?L = _ =>
    Exists L S_OK (with_rescan (with_state (i_mem x) 1 ws) [Znth 16 ws; Znth 1 ws; Znth 14 ws; Znth 15 ws; 1]) end.
  cbn [m_states m_rescan m_decoder with_decoder with_rescan with_state with_states]. rewrite E1.
  entailer!.
  apply returns_return; rewrite R2. unfold rescan_done.
  rewrite Znth_with_state by (auto; lia). unfold rescan_check. zb. reflexivity.
Qed.
