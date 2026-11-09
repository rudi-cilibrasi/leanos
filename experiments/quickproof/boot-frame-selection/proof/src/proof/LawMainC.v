(* Law frame_selection_exact: main from the cross-check's turn: when main calls it (in the sequence after an OK,
   or CALL_CROSS_CHECK), begin_cross_check (its verdict), frame_cross_check with state 0, check_step; then the
   scrub's turn. *)
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

Lemma tail_cross {Espec: OracleKind} (TN: tail_ok s_scrub (at_step FScrub)):
  tail_ok s_cross (at_step FCrossCheck).
Proof.
  intros gv P y s sq st (Iy & Ls & Pp & Sq & St) Fy Delta R c -> -> ->.
  unfold s_cross, main_pre. start_main_tail.
  pose proof Pp as (Pmp & Pdp & Pup & Pbp & Prp & Ptp & Psp & Ppp & Prsp & Precp & Pdsp).
  lst_facts Ls. inputs_facts Iy.
  forward_if (EX b: Z, PROP (0 <= b <= 1; True)
    LOCAL (temp _t'47 (vi b); temp _status (vi st); temp _sequence (vi sq); temp _m (gv _law);
           temp _manifest (p_manifest P); temp _decoded (p_decoded P); temp _usable (p_usable P);
           temp _blocked (p_blocked P); temp _reserved (p_reserved P); temp _terminal (p_terminal P);
           temp _states (p_states P); temp _publication (p_publication P); temp _rescan (p_rescan P);
           temp _records (p_records P); temp _decoder_record (p_decoder P); gvars gv)
    SEP (lfields (gv _law) y (p_states P) (i_mem y) s; objs y (i_mem y) P; TT)).
  { forward. Exists (Z.b2z (st =? 0)). entailer!.
    all: try (destruct (zeq st 0); destruct (Z.eqb_spec st 0); try lia; cbn; repeat split; try reflexivity; try lia). }
  { u64c. forward. Exists 0. entailer!. all: try (repeat split; try lia). }
  Intros b1.
  forward_if (EX b: Z, PROP (0 <= b <= 1; True)
    LOCAL (temp _t'48 (vi b); temp _status (vi st); temp _sequence (vi sq); temp _m (gv _law);
           temp _manifest (p_manifest P); temp _decoded (p_decoded P); temp _usable (p_usable P);
           temp _blocked (p_blocked P); temp _reserved (p_reserved P); temp _terminal (p_terminal P);
           temp _states (p_states P); temp _publication (p_publication P); temp _rescan (p_rescan P);
           temp _records (p_records P); temp _decoder_record (p_decoder P); gvars gv)
    SEP (lfields (gv _law) y (p_states P) (i_mem y) s; objs y (i_mem y) P; TT)).
  { forward. Exists 1. entailer!. all: try (repeat split; try lia). }
  { unfold lfields. Intros. forward. forward. Exists (Z.b2z (w_call s =? 3)).
    unfold lfields. entailer!.
    all: try (destruct (zeq (w_call s) 3); destruct (Z.eqb_spec (w_call s) 3); try lia; cbn; repeat split;
              try reflexivity; try lia). }
  Intros b2.
  apply semax_if_seq. forward_if.
  - (* the cross-check *)
    forward_call (gv _law, y, p_states P, s).
    { split_and; auto. unfold seq_ok. split; intros G; congruence. }
    Intros s1.
    match goal with H: J y (start y) s1 |- _ => rename H into HJ1 end.
    unfold lfields. Intros. forward. forward.
    sep_apply (lfields_fold (gv _law) y (p_states P) (i_mem y) s1).
    sep_apply (ora_start gv (p_states P) y s1 Iy HJ1).
    rewrite objs_to_cs. unfold objs_cs. Intros.
    assert_PROP (@field_compatible FrameSpecs.CS t_states nil (p_states P)) as FCs by entailer!.
    pose proof (mem_ok_states (i_mem y) Im) as (Ls0 & _ & _ & _ & _).
    rewrite (states_split Ews (m_states (i_mem y)) (p_states P)) by auto. Intros.
    forward_call (gv, gv _law, gv _law, p_states P, y, p_terminal P, p_decoded P, p_states P, Ews).
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
    pose proof (keeps_none y m' (or_introl Fy) Km) as Km'. subst m'.
    pose proof HJ2 as (Ls2 & Q2 & Ge2).
    sep_apply (states_fold Ews (m_states (i_mem y)) (p_states P) ltac:(auto) FCs).
    sep_apply (objs_cs_fold y (i_mem y) P).
    cbn [mem_of].
    status_set.
    forward_call (gv _law, y, i_mem y, s2, P, st').
    eapply semax_pre; [ | apply (TN gv P (with_step y FScrub (i_mem y)) s2 sq st') ].
    + unfold main_pre. rewrite ?lfields_with, ?objs_with. cbn [i_mem with_step]. entailer!.
        all: try apply derives_refl.
    + unfold main_ok. split_and; auto; try apply inputs_ok_here; auto; try apply statuses_u32; auto.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - (* not called *)
    try (apply -> semax_skip_seq).
    eapply semax_pre; [ | apply (TN gv P (with_step y FScrub (i_mem y)) s sq st) ].
    + unfold main_pre. rewrite ?lfields_with, ?objs_with. cbn [i_mem with_step]. entailer!.
        all: try apply derives_refl.
    + unfold main_ok. split_and; auto; try apply inputs_ok_here; auto.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
Qed.
