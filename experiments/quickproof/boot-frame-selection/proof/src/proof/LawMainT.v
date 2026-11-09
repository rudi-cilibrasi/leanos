(* Law frame_selection_exact: main from the terminal's turn: when main calls it (CALL_ALLOCATE or CALL_TERMINAL),
   begin_terminal, the law's oracle handed over at no answers, frame_terminal, the oracle at its complete run,
   check_step, then the selection's turn from the memory the terminal returned. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosFrameSelection.harness.frame_selection_exact.code.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
Require Import LeanosFrameSelection.proof.LawProg LeanosFrameSelection.proof.LawDefs LeanosFrameSelection.proof.LawFacts
  LeanosFrameSelection.proof.LawLib LeanosFrameSelection.proof.LawMainDefs LeanosFrameSelection.proof.LawFast.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.
#[local] Ltac simplify_remove_localdef_temp ::= fast_remove_localdef_temp.

Lemma tail_terminal {Espec: OracleKind} (TN: tail_ok s_select (at_step FSelect)):
  tail_ok s_terminal (at_step FTerminal).
Proof.
  intros gv P y s sq st (Iy & Ls & Pp & Sq & St) Fy Delta R c -> -> ->.
  unfold s_terminal, main_pre. start_main_tail.
  pose proof Pp as (Pmp & Pdp & Pup & Pbp & Prp & Ptp & Psp & Ppp & Prsp & Precp & Pdsp).
  lst_facts Ls.
  forward_if (EX b: Z, PROP ()
    LOCAL (temp _t'42 (vi b); temp _status (vi st); temp _sequence (vi sq); temp _m (gv _law);
           temp _manifest (p_manifest P); temp _decoded (p_decoded P); temp _usable (p_usable P); temp _blocked (p_blocked P); temp _reserved (p_reserved P);
           temp _terminal (p_terminal P); temp _states (p_states P); temp _publication (p_publication P); temp _rescan (p_rescan P); temp _records (p_records P);
           temp _decoder_record (p_decoder P); gvars gv)
    SEP (lfields (gv _law) y (p_states P) (i_mem y) s; objs y (i_mem y) P; TT)).
  { forward. Exists 1. entailer!. }
  { unfold lfields. Intros. forward. forward. Exists (Z.b2z (w_call s =? 1)).
    unfold lfields. entailer!. destruct (zeq (w_call s) 1); destruct (Z.eqb_spec (w_call s) 1); try lia; reflexivity. }
  Intros b.
  apply semax_if_seq. forward_if.
  - (* the terminal *)
    forward_call (gv _law, y, (p_states P), s).
    { split_and; auto. unfold seq_ok. split; intros G; congruence. }
    Intros s1.
    match goal with H: J y (start y) s1 |- _ => rename H into HJ1 end.
    sep_apply (ora_start gv (p_states P) y s1 Iy HJ1).
    rewrite objs_to_cs. unfold objs_cs. Intros.
    forward_call (gv, gv _law, gv _law, (p_states P), y, (p_manifest P), (p_decoded P), (p_usable P), (p_blocked P), (p_reserved P), (p_terminal P), Ews, Ews).
    Intros vret. destruct vret as [[h st'] m']. cbn [fst snd] in *.
    match goal with H: returns y h = Some (st', m') |- _ => rename H into Hret end.
    unfold Ora_law. Intros p2 s2.
    match goal with H: run y (start y) h = Some p2 |- _ => rename H into Hrun2 end.
    match goal with H: J y p2 s2 |- _ => rename H into HJ2 end.
    match goal with H: answers_ok h |- _ => rename H into Ah2 end.
    pose proof (returns_eq y h p2 st' m' Hrun2 Hret) as Ep. subst p2.
    destruct (returns_ok y h st' m' Iy Ah2 Hret) as (Sst & Mm' & Km).
    pose proof (keeps_terminal y m' Fy Km) as Km'.
    destruct HJ2 as (Ls2 & Q2 & Ge2 & Gv2).
    replace (m_states (i_mem y)) with (m_states m') by (rewrite Km'; reflexivity).
    replace (m_publication (i_mem y)) with (m_publication m') by (rewrite Km'; reflexivity).
    replace (m_rescan (i_mem y)) with (m_rescan m') by (rewrite Km'; reflexivity).
    replace (m_selected (i_mem y)) with (m_selected m') by (rewrite Km'; reflexivity).
    replace (m_selected_manifest (i_mem y)) with (m_selected_manifest m') by (rewrite Km'; reflexivity).
    replace (m_next (i_mem y)) with (m_next m') by (rewrite Km'; reflexivity).
    replace (m_decoder (i_mem y)) with (m_decoder m') by (rewrite Km'; reflexivity).
    sep_apply (objs_cs_fold y m' P).
    cbn [mem_of].
    forward_call (gv _law, y, m', s2, P, st').
    eapply semax_pre; [ | apply (TN gv P (with_step y FSelect m')
                             s2 sq st') ].
    + unfold main_pre. entailer!. apply derives_refl.
    + unfold main_ok. split_and; auto; try apply inputs_ok_with; auto; try apply statuses_u32; auto.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - (* not called *)
    try (apply -> semax_skip_seq).
    eapply semax_pre; [ | apply (TN gv P (with_step y FSelect (i_mem y))
                             s sq st) ].
    + unfold main_pre. entailer!. apply derives_refl.
    + unfold main_ok. split_and; auto; try apply inputs_ok_here; auto.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
Qed.
