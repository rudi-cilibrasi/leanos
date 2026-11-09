(* Law frame_selection_exact: main from the selection's turn: when main calls it (in the sequence after an OK, or
   CALL_SELECT), begin_select, the oracle handed over, frame_select with the decoder law_decode and the three
   records as cells, check_step, and in the sequence the records passed on to the later steps (after_select); then
   the cross-check's turn. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosFrameSelection.harness.frame_selection_exact.code.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
Require Import LeanosFrameSelection.proof.LawProg LeanosFrameSelection.proof.LawDefs LeanosFrameSelection.proof.LawFacts
  LeanosFrameSelection.proof.LawLib LeanosFrameSelection.proof.LawMainDefs LeanosFrameSelection.proof.LawMainLib
  LeanosFrameSelection.proof.LawFast.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.
#[local] Ltac simplify_remove_localdef_temp ::= fast_remove_localdef_temp.

Lemma records_cells_fold: forall (cs: compspecs) p a b c, @field_compatible cs (tarray tulong 3) nil p ->
  (@data_at cs Ews tulong (vl a) p * @data_at cs Ews tulong (vl b) (offset_val 8 p) *
   @data_at cs Ews tulong (vl c) (offset_val 16 p))%logic |-- @data_at cs Ews (tarray tulong 3) [vl a; vl b; vl c] p.
Proof. intros. rewrite (records_cells cs p a b c) by auto. apply derives_refl. Qed.

Lemma tail_select {Espec: OracleKind} (TN: tail_ok s_cross (at_step FCrossCheck)):
  tail_ok s_select (at_step FSelect).
Proof.
  intros gv P y s sq st (Iy & Ls & Pp & Sq & St) Fy Delta R c -> -> ->.
  unfold s_select, main_pre. start_main_tail.
  pose proof Pp as (Pmp & Pdp & Pup & Pbp & Prp & Ptp & Psp & Ppp & Prsp & Precp & Pdsp).
  lst_facts Ls. inputs_facts Iy.
  (* sequence && status == OK *)
  forward_if (EX b: Z, PROP ()
    LOCAL (temp _t'44 (vi b); temp _status (vi st); temp _sequence (vi sq); temp _m (gv _law);
           temp _manifest (p_manifest P); temp _decoded (p_decoded P); temp _usable (p_usable P); temp _blocked (p_blocked P); temp _reserved (p_reserved P);
           temp _terminal (p_terminal P); temp _states (p_states P); temp _publication (p_publication P); temp _rescan (p_rescan P); temp _records (p_records P);
           temp _decoder_record (p_decoder P); gvars gv)
    SEP (lfields (gv _law) y (p_states P) (i_mem y) s; objs y (i_mem y) P; TT)).
  { forward. Exists (Z.b2z (st =? 0)). entailer!. destruct (zeq st 0); destruct (Z.eqb_spec st 0); try lia; reflexivity. }
  { forward. Exists 0. entailer!. }
  Intros b1.
  (* ... || m->call == CALL_SELECT *)
  forward_if (EX b: Z, PROP ()
    LOCAL (temp _t'45 (vi b); temp _status (vi st); temp _sequence (vi sq); temp _m (gv _law);
           temp _manifest (p_manifest P); temp _decoded (p_decoded P); temp _usable (p_usable P); temp _blocked (p_blocked P); temp _reserved (p_reserved P);
           temp _terminal (p_terminal P); temp _states (p_states P); temp _publication (p_publication P); temp _rescan (p_rescan P); temp _records (p_records P);
           temp _decoder_record (p_decoder P); gvars gv)
    SEP (lfields (gv _law) y (p_states P) (i_mem y) s; objs y (i_mem y) P; TT)).
  { forward. Exists 1. entailer!. }
  { unfold lfields. Intros. forward. forward. Exists (Z.b2z (w_call s =? 2)).
    unfold lfields. entailer!. destruct (zeq (w_call s) 2); destruct (Z.eqb_spec (w_call s) 2); try lia; reflexivity. }
  Intros b2.
  apply semax_if_seq. forward_if.
  - (* the selection *)
    forward_call (gv _law, y, (p_states P), s).
    { split_and; auto. unfold seq_ok. split; intros G; congruence. }
    Intros s1.
    match goal with H: J y (start y) s1 |- _ => rename H into HJ1 end.
    unfold lfields. Intros. forward.
    sep_apply (lfields_fold (gv _law) y (p_states P) (i_mem y) s1).
    sep_apply (ora_start gv (p_states P) y s1 Iy HJ1).
    make_func_ptr _law_decode.
    rewrite objs_to_cs. unfold objs_cs. Intros.
    unfold t_records.
    assert_PROP (@field_compatible FrameSpecs.CS (tarray tulong 3) nil (p_records P)) as FCr by entailer!.
    change (map vl [m_selected (i_mem y); m_selected_manifest (i_mem y); m_next (i_mem y)])
      with [vl (m_selected (i_mem y)); vl (m_selected_manifest (i_mem y)); vl (m_next (i_mem y))].
    rewrite (records_cells FrameSpecs.CS (p_records P)) by auto. Intros.
    forward_call (gv, gv _law_decode, gv _law, gv _law, p_states P, y, p_manifest P, p_records P,
                  offset_val 8 (p_records P), offset_val 16 (p_records P), p_decoder P, Ews, Ews).
    all: try (solve [ split_and; auto ]).
    all: try (solve [ entailer! ]).
    Intros vret. destruct vret as [[h st'] m']. cbn [fst snd] in *.
    match goal with H: returns y h = Some (st', m') |- _ => rename H into Hret end.
    unfold Ora_law. Intros p2 s2.
    match goal with H: run y (start y) h = Some p2 |- _ => rename H into Hrun2 end.
    match goal with H: J y p2 s2 |- _ => rename H into HJ2 end.
    match goal with H: answers_ok h |- _ => rename H into Ah2 end.
    pose proof (returns_eq y h p2 st' m' Hrun2 Hret) as Ep. subst p2.
    destruct (returns_ok y h st' m' Iy Ah2 Hret) as (Sst & Mm' & Km).
    pose proof (keeps_select y m' Fy Km) as Km'.
    pose proof HJ2 as (Ls2 & Q2 & Ge2).
    replace (m_reserved (i_mem y)) with (m_reserved m') by (rewrite Km'; reflexivity).
    replace (m_terminal (i_mem y)) with (m_terminal m') by (rewrite Km'; reflexivity).
    replace (m_publication (i_mem y)) with (m_publication m') by (rewrite Km'; reflexivity).
    replace (m_rescan (i_mem y)) with (m_rescan m') by (rewrite Km'; reflexivity).
    sep_apply (records_cells_fold FrameSpecs.CS (p_records P) (m_selected m') (m_selected_manifest m') (m_next m') FCr).
    change [vl (m_selected m'); vl (m_selected_manifest m'); vl (m_next m')]
      with (map vl [m_selected m'; m_selected_manifest m'; m_next m']).
    sep_apply (objs_cs_fold y m' P).
    cbn [mem_of].
    forward.
    forward_call (gv _law, y, m', s2, P, st').
    apply semax_if_seq. forward_if.
    + (* the sequence: the records passed on *)
      rewrite lfields_sel4. unfold objs, t_records. Intros.
      forward. forward. forward. forward. forward. forward. forward. forward.
      eapply semax_pre; [ | apply (TN gv P (after_select (with_step y FCrossCheck m') m') s2 sq st') ].
      * unfold main_pre. rewrite lfields_sel4, lrest4_after, lrest4_with, objs_after, objs_with.
        unfold objs, t_records. cbn [after_select with_step i_selected i_selected_manifest i_published i_next i_mem].
        entailer!. all: try apply derives_refl.
      * unfold main_ok. split_and; auto; try apply inputs_ok_after; auto; try apply statuses_u32; auto.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
    + (* not in the sequence *)
      try (apply -> semax_skip_seq).
      eapply semax_pre; [ | apply (TN gv P (with_step y FCrossCheck m') s2 sq st') ].
      * unfold main_pre. rewrite ?lfields_with, ?objs_with. cbn [i_mem with_step]. entailer!.
        all: try apply derives_refl.
      * unfold main_ok. split_and; auto; try apply inputs_ok_with; auto; try apply statuses_u32; auto.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
  - (* not called *)
    try (apply -> semax_skip_seq).
    eapply semax_pre; [ | apply (TN gv P
                                   (with_step y FCrossCheck (i_mem y)) s sq st) ].
    + unfold main_pre. rewrite ?lfields_with, ?objs_with. cbn [i_mem with_step]. entailer!.
        all: try apply derives_refl.
    + unfold main_ok. split_and; auto; try apply inputs_ok_here; auto.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
Qed.
