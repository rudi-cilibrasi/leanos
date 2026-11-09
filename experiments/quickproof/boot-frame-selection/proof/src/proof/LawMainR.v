(* Law frame_selection_exact: main from the rescan's turn: when main calls it (in the sequence after an OK with
   take_next, or CALL_RESCAN), begin_rescan, frame_rescan with the decoder law_decode and state 1, check_step;
   then main returns 0. *)
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

Lemma tail_rescan {Espec: OracleKind}: tail_ok s_rescan (at_step FRescan).
Proof.
  intros gv P y s sq st (Iy & Ls & Pp & Sq & St) Fy Delta R c -> -> ->.
  unfold s_rescan, main_pre. start_main_tail.
  pose proof Pp as (Pmp & Pdp & Pup & Pbp & Prp & Ptp & Psp & Ppp & Prsp & Precp & Pdsp).
  lst_facts Ls. inputs_facts Iy.
  forward_if (EX b: Z, PROP (0 <= b <= 1)
    LOCAL (temp _t'56 (vi b); temp _status (vi st); temp _sequence (vi sq); temp _m (gv _law);
           temp _manifest (p_manifest P); temp _decoded (p_decoded P); temp _usable (p_usable P);
           temp _blocked (p_blocked P); temp _reserved (p_reserved P); temp _terminal (p_terminal P);
           temp _states (p_states P); temp _publication (p_publication P); temp _rescan (p_rescan P);
           temp _records (p_records P); temp _decoder_record (p_decoder P); gvars gv)
    SEP (lfields (gv _law) y (p_states P) (i_mem y) s; objs y (i_mem y) P; TT)).
  { u64c. forward. Exists (Z.b2z (st =? 0)). entailer!.
    all: try (destruct (zeq st 0); destruct (Z.eqb_spec st 0); try lia; cbn; repeat split; try reflexivity; try lia). }
  { u64c. forward. Exists 0. entailer!. all: try (repeat split; try lia; try reflexivity). }
  Intros b1.
  forward_if (EX b: Z, PROP (0 <= b <= 1)
    LOCAL (temp _t'57 (vi b); temp _status (vi st); temp _sequence (vi sq); temp _m (gv _law);
           temp _manifest (p_manifest P); temp _decoded (p_decoded P); temp _usable (p_usable P);
           temp _blocked (p_blocked P); temp _reserved (p_reserved P); temp _terminal (p_terminal P);
           temp _states (p_states P); temp _publication (p_publication P); temp _rescan (p_rescan P);
           temp _records (p_records P); temp _decoder_record (p_decoder P); gvars gv)
    SEP (lfields (gv _law) y (p_states P) (i_mem y) s; objs y (i_mem y) P; TT)).
  { u64c. unfold lfields. Intros. forward. forward. Exists (Z.b2z (negb (i_take_next y =? 0))).
    unfold lfields. entailer!.
    all: try (destruct (zeq (i_take_next y) 0); destruct (Z.eqb_spec (i_take_next y) 0); try lia; cbn;
              try reflexivity; try lia;
              try (rewrite e; reflexivity);
              try (rewrite Int.eq_false; [ reflexivity | intros E; apply repr_inj_unsigned in E; rep_lia ]);
              try (rewrite Int.eq_true; reflexivity)).
    all: try (split; [ lia | reflexivity ]). }
  { u64c. forward. Exists 0. entailer!. all: try (repeat split; try lia; try reflexivity). }
  Intros b2.
  forward_if (EX b: Z, PROP (0 <= b <= 1)
    LOCAL (temp _t'58 (vi b); temp _status (vi st); temp _sequence (vi sq); temp _m (gv _law);
           temp _manifest (p_manifest P); temp _decoded (p_decoded P); temp _usable (p_usable P);
           temp _blocked (p_blocked P); temp _reserved (p_reserved P); temp _terminal (p_terminal P);
           temp _states (p_states P); temp _publication (p_publication P); temp _rescan (p_rescan P);
           temp _records (p_records P); temp _decoder_record (p_decoder P); gvars gv)
    SEP (lfields (gv _law) y (p_states P) (i_mem y) s; objs y (i_mem y) P; TT)).
  { u64c. forward. Exists 1. entailer!. all: try (repeat split; try lia; try reflexivity). }
  { u64c. unfold lfields. Intros. forward. forward. Exists (Z.b2z (w_call s =? 6)).
    unfold lfields. entailer!.
    all: try (destruct (zeq (w_call s) 6); destruct (Z.eqb_spec (w_call s) 6); try lia; cbn; repeat split;
              try reflexivity; try lia). }
  Intros b3.
  forward_if (PROP () LOCAL (gvars gv) SEP (TT)).
  - (* the rescan *)
    forward_call (gv _law, y, p_states P, s).
    { split_and; auto. unfold seq_ok. split; intros G; congruence. }
    Intros s1.
    match goal with H: J y (start y) s1 |- _ => rename H into HJ1 end.
    rewrite lfields_sel4. Intros. forward. forward.
    sep_apply (lfields_sel4_fold (gv _law) y (p_states P) (i_mem y) s1).
    sep_apply (ora_start gv (p_states P) y s1 Iy HJ1).
    make_func_ptr _law_decode.
    rewrite objs_to_cs. unfold objs_cs. Intros.
    assert_PROP (@field_compatible FrameSpecs.CS t_states nil (p_states P)) as FCs by entailer!.
    pose proof (mem_ok_states (i_mem y) Im) as (Ls0 & _ & _ & _ & _).
    rewrite (states_split Ews (m_states (i_mem y)) (p_states P)) by auto. Intros.
    forward_call (gv, gv _law_decode, gv _law, gv _law, p_states P, y, p_manifest P, p_decoded P, p_rescan P,
                  p_decoder P, Ews, Ews).
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
    pose proof (keeps_rescan y m' Fy Km) as Km'.
    pose proof HJ2 as (Ls2 & Q2 & Ge2).
    pose proof (mem_ok_states m' Mm') as (Ls1 & _ & _ & _ & _).
    replace (Znth 0 (m_states (i_mem y))) with (Znth 0 (m_states m'))
      by (rewrite Km'; cbn [m_states with_decoder with_rescan with_state with_states]; list_solve).
    replace (m_reserved (i_mem y)) with (m_reserved m') by (rewrite Km'; reflexivity).
    replace (m_terminal (i_mem y)) with (m_terminal m') by (rewrite Km'; reflexivity).
    replace (m_publication (i_mem y)) with (m_publication m') by (rewrite Km'; reflexivity).
    replace (m_selected (i_mem y)) with (m_selected m') by (rewrite Km'; reflexivity).
    replace (m_selected_manifest (i_mem y)) with (m_selected_manifest m') by (rewrite Km'; reflexivity).
    replace (m_next (i_mem y)) with (m_next m') by (rewrite Km'; reflexivity).
    sep_apply (states_fold Ews (m_states m') (p_states P) ltac:(auto) FCs).
    sep_apply (objs_cs_fold y m' P).
    cbn [mem_of].
    status_set.
    forward_call (gv _law, y, m', s2, P, st').
    entailer!.
  - forward. entailer!.
  - forward. Exists (Int.repr 0). entailer!.
Qed.
