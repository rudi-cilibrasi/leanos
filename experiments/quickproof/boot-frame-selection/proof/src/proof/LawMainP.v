(* Law frame_selection_exact: main from the publication's turn: when main calls it (in the sequence after an OK, or
   CALL_PUBLICATION), begin_publication_result (main's sequence record: not CALL_ALLOCATE, or the scrub answered
   1), frame_publication_result with state 0, check_step, begin_publication_check, frame_publication_check,
   check_step; then the rescan's turn. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosFrameSelection.harness.frame_selection_exact.code.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
Require Import LeanosFrameSelection.proof.LawProg LeanosFrameSelection.proof.LawDefs LeanosFrameSelection.proof.LawFacts
  LeanosFrameSelection.proof.LawLib LeanosFrameSelection.proof.LawMainDefs LeanosFrameSelection.proof.LawMainLib
  LeanosFrameSelection.proof.LawMainLib2 LeanosFrameSelection.proof.LawFast.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.
#[local] Ltac simplify_remove_localdef_temp ::= fast_remove_localdef_temp.

(* `status = t'` after a frame call whose arguments main loads first (forward_call leaves it). *)
Ltac status_set := lazymatch goal with |- semax _ _ ?c _ =>
  let s := first_stmt c in lazymatch s with Sset _status _ => forward | _ => idtac end end.

Lemma tail_pub {Espec: OracleKind} (TN: tail_ok s_rescan (at_step FRescan)):
  tail_ok s_pub pub_fact.
Proof.
  intros gv P y s sq st (Iy & Ls & Pp & Sq & St) (Fy & Fsc) Delta R c -> -> ->.
  unfold s_pub, main_pre. start_main_tail.
  pose proof Pp as (Pmp & Pdp & Pup & Pbp & Prp & Ptp & Psp & Ppp & Prsp & Precp & Pdsp).
  lst_facts Ls. inputs_facts Iy.
  forward_if (EX b: Z, PROP (0 <= b <= 1; b <> 0 -> sq = 1 /\ st = 0)
    LOCAL (temp _t'53 (vi b); temp _status (vi st); temp _sequence (vi sq); temp _m (gv _law);
           temp _manifest (p_manifest P); temp _decoded (p_decoded P); temp _usable (p_usable P);
           temp _blocked (p_blocked P); temp _reserved (p_reserved P); temp _terminal (p_terminal P);
           temp _states (p_states P); temp _publication (p_publication P); temp _rescan (p_rescan P);
           temp _records (p_records P); temp _decoder_record (p_decoder P); gvars gv)
    SEP (lfields (gv _law) y (p_states P) (i_mem y) s; objs y (i_mem y) P; TT)).
  { u64c. forward. Exists (Z.b2z (st =? 0)). entailer!.
    all: try (destruct (zeq st 0); destruct (Z.eqb_spec st 0); try lia; cbn; repeat split; try reflexivity; try lia). }
  { u64c. forward. Exists 0. entailer!. all: try (repeat split; try lia). }
  Intros b1.
  forward_if (EX b: Z, PROP (0 <= b <= 1; b <> 0 -> b1 <> 0 \/ w_call s = 5)
    LOCAL (temp _t'54 (vi b); temp _status (vi st); temp _sequence (vi sq); temp _m (gv _law);
           temp _manifest (p_manifest P); temp _decoded (p_decoded P); temp _usable (p_usable P);
           temp _blocked (p_blocked P); temp _reserved (p_reserved P); temp _terminal (p_terminal P);
           temp _states (p_states P); temp _publication (p_publication P); temp _rescan (p_rescan P);
           temp _records (p_records P); temp _decoder_record (p_decoder P); gvars gv)
    SEP (lfields (gv _law) y (p_states P) (i_mem y) s; objs y (i_mem y) P; TT)).
  { u64c. forward. Exists 1. entailer!. all: try (repeat split; try lia). }
  { u64c. unfold lfields. Intros. forward. forward. Exists (Z.b2z (w_call s =? 5)).
    unfold lfields. entailer!.
    all: try (destruct (zeq (w_call s) 5); destruct (Z.eqb_spec (w_call s) 5); try lia; cbn; repeat split;
              try reflexivity; try lia). }
  Intros b2.
  apply semax_if_seq. forward_if.
  - (* the publication *)
    assert (Seq: w_call s <> 0 \/ w_scrubbed s = 1).
    { u64c.
      match goal with H: b2 <> 0 -> b1 <> 0 \/ w_call s = 5 |- _ => destruct (H ltac:(lia)) as [B1 | C5] end.
      - match goal with H: b1 <> 0 -> sq = 1 /\ st = 0 |- _ => destruct (H B1) as [E1 E2] end. right; auto.
      - left; lia. }
    forward_call (gv _law, y, p_states P, s).
    { split_and; auto. unfold seq_ok. split; intros G; [ auto | congruence ]. }
    Intros s1.
    match goal with H: J y (start y) s1 |- _ => rename H into HJ1 end.
    rewrite lfields_sel4. Intros. forward. forward.
    sep_apply (lfields_sel4_fold (gv _law) y (p_states P) (i_mem y) s1).
    sep_apply (ora_start gv (p_states P) y s1 Iy HJ1).
    rewrite objs_to_cs. unfold objs_cs. Intros.
    assert_PROP (@field_compatible FrameSpecs.CS t_states nil (p_states P)) as FCs by entailer!.
    pose proof (mem_ok_states (i_mem y) Im) as (Ls0 & _ & _ & _ & _).
    rewrite (states_split Ews (m_states (i_mem y)) (p_states P)) by auto. Intros.
    forward_call (gv, gv _law, gv _law, p_states P, y, p_states P, p_publication P, Ews, Ews).
    all: try (solve [ split_and; auto ]).
    all: try (solve [ entailer! ]).
    Intros vret. destruct vret as [h m']. cbn [fst snd] in *.
    match goal with H: returns y h = Some (_, m') |- _ => rename H into Hret end.
    unfold Ora_law. Intros p2 s2.
    match goal with H: run y (start y) h = Some p2 |- _ => rename H into Hrun2 end.
    match goal with H: J y p2 s2 |- _ => rename H into HJ2 end.
    match goal with H: answers_ok h |- _ => rename H into Ah2 end.
    pose proof (returns_eq y h p2 S_OK m' Hrun2 Hret) as Ep. subst p2.
    destruct (returns_ok y h S_OK m' Iy Ah2 Hret) as (Sst & Mm' & Km).
    pose proof (keeps_publication y m' Fy Km) as Km'.
    pose proof HJ2 as (Ls2 & Q2 & Ge2).
    replace (m_reserved (i_mem y)) with (m_reserved m') by (rewrite Km'; reflexivity).
    replace (m_terminal (i_mem y)) with (m_terminal m') by (rewrite Km'; reflexivity).
    replace (m_states (i_mem y)) with (m_states m') by (rewrite Km'; reflexivity).
    replace (m_rescan (i_mem y)) with (m_rescan m') by (rewrite Km'; reflexivity).
    replace (m_selected (i_mem y)) with (m_selected m') by (rewrite Km'; reflexivity).
    replace (m_selected_manifest (i_mem y)) with (m_selected_manifest m') by (rewrite Km'; reflexivity).
    replace (m_next (i_mem y)) with (m_next m') by (rewrite Km'; reflexivity).
    replace (m_decoder (i_mem y)) with (m_decoder m') by (rewrite Km'; reflexivity).
    pose proof (mem_ok_states m' Mm') as (Ls1 & _ & _ & _ & _).
    sep_apply (states_fold Ews (m_states m') (p_states P) ltac:(auto) FCs).
    sep_apply (objs_cs_fold y m' P).
    cbn [mem_of].
    status_set.
    forward_call (gv _law, y, m', s2, P, S_OK).
    all: try (solve [ reflexivity ]).
    (* the publication check, from the memory m' *)
    change (lfields (gv _law) y (p_states P) m' s2)
      with (lfields (gv _law) (with_step y FPublicationCheck m') (p_states P) (i_mem (with_step y FPublicationCheck m')) s2).
    assert (Iy2: inputs_ok (with_step y FPublicationCheck m')) by (apply inputs_ok_with; auto).
    forward_call (gv _law, with_step y FPublicationCheck m', p_states P, s2).
    { split_and; auto. unfold seq_ok. split; intros G; cbn in G; discriminate. }
    Intros s3.
    match goal with H: J (with_step y FPublicationCheck m') (start _) s3 |- _ => rename H into HJ3 end.
    rewrite lfields_sel4. Intros. forward.
    sep_apply (lfields_sel4_fold (gv _law) (with_step y FPublicationCheck m') (p_states P)
      (i_mem (with_step y FPublicationCheck m')) s3).
    sep_apply (ora_start gv (p_states P) (with_step y FPublicationCheck m') s3 Iy2 HJ3).
    rewrite objs_to_cs. unfold objs_cs. Intros.
    change (m_publication m') with (m_publication (i_mem (with_step y FPublicationCheck m'))).
    forward_call (gv, gv _law, gv _law, p_states P, with_step y FPublicationCheck m', p_publication P, Ews).
    all: try (solve [ split_and; auto ]).
    all: try (solve [ entailer! ]).
    Intros vret. destruct vret as [[h3 st3] m3]. cbn [fst snd] in *.
    match goal with H: returns _ h3 = Some (st3, m3) |- _ => rename H into Hret3 end.
    unfold Ora_law. Intros p3 s4.
    match goal with H: run _ (start _) h3 = Some p3 |- _ => rename H into Hrun3 end.
    match goal with H: J _ p3 s4 |- _ => rename H into HJ4 end.
    match goal with H: answers_ok h3 |- _ => rename H into Ah3 end.
    pose proof (returns_eq _ h3 p3 st3 m3 Hrun3 Hret3) as Ep3. subst p3.
    destruct (returns_ok _ h3 st3 m3 Iy2 Ah3 Hret3) as (Sst3 & Mm3 & Km3).
    pose proof (keeps_none (with_step y FPublicationCheck m') m3 (or_intror (or_intror eq_refl)) Km3) as Km3'.
    cbn [i_mem with_step] in Km3'. subst m3.
    pose proof HJ4 as (Ls4 & Q4 & Ge4).
    change (m_publication (i_mem (with_step y FPublicationCheck m'))) with (m_publication m').
    sep_apply (objs_cs_fold (with_step y FPublicationCheck m') m' P).
    cbn [mem_of].
    status_set.
    forward_call (gv _law, with_step y FPublicationCheck m', m', s4, P, st3).
    eapply semax_pre; [ | apply (TN gv P (with_step y FRescan m') s4 sq st3) ].
    + unfold main_pre. rewrite ?lfields_with, ?objs_with. cbn [i_mem with_step]. entailer!.
        all: try apply derives_refl.
    + unfold main_ok. split_and; auto; try apply inputs_ok_with; auto; try apply statuses_u32; auto.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - (* not called *)
    try (apply -> semax_skip_seq).
    eapply semax_pre; [ | apply (TN gv P (with_step y FRescan (i_mem y)) s sq st) ].
    + unfold main_pre. rewrite ?lfields_with, ?objs_with. cbn [i_mem with_step]. entailer!.
        all: try apply derives_refl.
    + unfold main_ok. split_and; auto; try apply inputs_ok_here; auto.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
Qed.
