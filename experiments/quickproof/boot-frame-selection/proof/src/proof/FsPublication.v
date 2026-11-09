(* The body of boot_frame_publication_result: words 0 to 4 of the authority result into the publication result,
   word q at the model's Go (ExpectAuthority q) M after the words before it (Defs.authority_done), M the memory
   before the step with the publication result p so far; after word 4, Return S_OK. *)
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

Lemma body_boot_frame_publication_result (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_boot_frame_publication_result (boot_publication_result_spec Ora).
Proof.
  start_function.
  rename H into HC, H0 into IX.
  destruct (inputs_facts x IX) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MO).
  pose proof MO as (_ & _ & _ & _ & _ & _ & LP & _).
  destruct (mem_state (i_mem x) 0 MO ltac:(lia)) as [L0 U0].
  set (s0 := Znth 0 (m_states (i_mem x))) in *.
  forward_for_simple_bound 5 (EX q: Z, EX hs: list answer, EX p: list Z,
    PROP (Zlength p = PUBLICATION_WORDS;
          run x (start x) hs = Some (if q <? PUBLICATION_WORDS then Go (ExpectAuthority q) (with_publication (i_mem x) p)
                                     else Return S_OK (with_publication (i_mem x) p)))
    LOCAL (temp _selected (vl (i_selected x)); temp _state p0; temp _selected_manifest (vl (i_selected_manifest x));
           temp _publication pp; gvars gv)
    SEP (Ora gv dctx sctx sp x hs; data_at rsh t_state (map vl s0) p0;
         data_at wsh t_publication (map vl p) pp))%assert.
  { Exists (@nil answer) (m_publication (i_mem x)). entailer!.
    rewrite with_publication_same. cbn [run]. unfold start. rewrite HC. reflexivity. }
  { Intros. rename H into Q.
    match goal with H: run _ _ hs = _ |- _ => rename H into R end.
    rewrite (proj2 (Z.ltb_lt _ _)) in R by (cbn; lia).
    do 4 forward.
    forward_call (gv, dctx, sctx, sp, x, hs, i_selected x, Znth 16 s0, Znth 1 s0, Znth 14 s0, Znth 15 s0,
                  i_selected_manifest x, 1, i).
    { apply (next_call_go _ _ _ _ R). }
    Intros v.
    pose proof (run_word x (start x) hs _ _ v R ltac:(intros; discriminate)) as R1.
    cbn [step reply_value expected] in R1.
    forward.
    Exists (hs ++ [(Authority (i_selected x) (Znth 16 s0) (Znth 1 s0) (Znth 14 s0) (Znth 15 s0)
                      (i_selected_manifest x) 1 i, Word v)]) (upd_Znth i p v).
    entailer!.
    all: first [ rewrite Zlength_upd_Znth'; auto | exact R1 | rewrite upd_Znth_map; apply derives_refl ]. }
  Intros hs p. rename H into LP', H0 into R.
  rewrite Z.ltb_irrefl in R.
  Exists hs (with_publication (i_mem x) p). entailer!.
  apply returns_return; exact R.
Qed.
