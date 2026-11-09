(* Law frame_selection_exact: the body of main's check_step: after a step, the law's record says EXPECT_NOTHING
   with the step's status as its verdict, and every object main holds is the law's model of it (the inputs and
   the memory mm), so each of its checks holds. *)
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

Definition Gcheck : funspecs := [gp_assert_spec].

Ltac cmp_eq := entailer!; rewrite ?Int64.eq_true, ?Int.eq_true; reflexivity.

(* The parameters of check_step in a LOCAL clause, without the loops' temps. *)
Ltac keep_params Q :=
  lazymatch Q with
  | nil => constr:(@nil localdef)
  | temp ?i ?v :: ?Q' =>
      let r := keep_params Q' in
      lazymatch i with
      | _m => constr:(temp i v :: r) | _status => constr:(temp i v :: r) | _manifest => constr:(temp i v :: r)
      | _decoded => constr:(temp i v :: r) | _usable => constr:(temp i v :: r) | _blocked => constr:(temp i v :: r)
      | _reserved => constr:(temp i v :: r) | _terminal => constr:(temp i v :: r) | _states => constr:(temp i v :: r)
      | _publication => constr:(temp i v :: r) | _rescan => constr:(temp i v :: r)
      | _records => constr:(temp i v :: r) | _decoder_record => constr:(temp i v :: r)
      | _ => r
      end
  | ?d :: ?Q' => let r := keep_params Q' in constr:(d :: r)
  end.

(* A loop of n checks that keeps PROP and SEP. *)
Ltac ck_loop n :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    let Q' := keep_params Q in
    forward_for_simple_bound n (EX i: Z, PROPx P (LOCALx Q' (SEPx R)))%assert
  end.

Lemma body_check_step: semax_body nil Gcheck f_check_step check_step_spec.
Proof.
  start_function.
  rename H into Ee, H0 into Ev, H1 into Ix, H2 into Mm.
  inputs_facts Ix. mem_facts Mm.
  pose proof (mem_ok_states mm Mm) as (Ls & L0 & F0 & L1 & F1).
  destruct P as [mp dp up bp rp tp sp pp rsp recp dsp]. cbn [p_manifest p_decoded p_usable p_blocked p_reserved
    p_terminal p_states p_publication p_rescan p_records p_decoder] in *.
  unfold lfields, objs. cbn [p_manifest p_decoded p_usable p_blocked p_reserved p_terminal p_states p_publication
    p_rescan p_records p_decoder]. Intros.
  unfold t_manifest, t_state, t_bitmap, t_terminal, t_publication, t_rescan, t_records, t_states, states_val.
  forward. forward_call Int.one. { rewrite Ee. cmp_eq. }
  forward. forward_call Int.one. { rewrite Ev. cmp_eq. }
  (* the manifest *)
  ck_loop 18.
  { entailer!. }
  { forward. forward. forward_call Int.one. { cmp_eq. } entailer!. }
  (* the decoded state *)
  ck_loop 41.
  { entailer!. }
  { forward. forward. forward_call Int.one. { cmp_eq. } entailer!. }
  (* the bitmaps *)
  ck_loop 64.
  { entailer!. }
  { forward. forward. forward_if (temp _t'1 (Vint Int.one)).
    { forward. forward. forward. entailer!. rewrite ?Int64.eq_true. reflexivity. }
    { else_false. }
    forward_if (temp _t'2 (Vint Int.one)).
    { forward. forward. forward. entailer!. rewrite ?Int64.eq_true. reflexivity. }
    { else_false. }
    forward_call Int.one. entailer!. }
  (* the terminal result *)
  ck_loop 9.
  { entailer!. }
  { forward. forward. forward_call Int.one. { cmp_eq. } entailer!. }
  (* the two states *)
  ck_loop 2.
  { entailer!. }
  { match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_for_simple_bound 41 (EX j: Z, PROPx P (LOCALx Q (SEPx R)))%assert end.
    { entailer!. }
    { assert (Hk: Zlength (Znth i (m_states mm)) = 41) by (destruct (zeq i 0); [ subst; auto | assert (i = 1) by lia; subst; auto ]).
      forward.
      all: try (entailer!; rewrite Znth_map by lia; rewrite Znth_map by lia; exact I).
      forward.
      all: try (entailer!; rewrite Znth_map by lia; rewrite Znth_map by lia; exact I).
      repeat rewrite Znth_map by (try rewrite Zlength_map; lia).
      forward_call Int.one. { cmp_eq. } entailer!. }
    entailer!. }
  (* the publication result and the rescan's record *)
  ck_loop 5.
  { entailer!. }
  { forward. forward. forward_call Int.one. { cmp_eq. } entailer!. }
  ck_loop 5.
  { entailer!. }
  { forward. forward. forward_call Int.one. { cmp_eq. } entailer!. }
  (* the records *)
  forward. forward.
  forward_if (temp _t'3 (Vint Int.one)).
  { forward. forward. forward. entailer!. rewrite ?Int64.eq_true. reflexivity. }
  { else_false. }
  forward_if (temp _t'4 (Vint Int.one)).
  { forward. forward. forward. entailer!. rewrite ?Int64.eq_true. reflexivity. }
  { else_false. }
  forward_call Int.one.
  forward. forward. forward_call Int.one. { cmp_eq. }
  unfold lfields, objs, t_manifest, t_state, t_bitmap, t_terminal, t_publication, t_rescan, t_records, t_states,
    states_val.
  cbn [p_manifest p_decoded p_usable p_blocked p_reserved p_terminal p_states p_publication p_rescan p_records
    p_decoder map].
  entailer!.
Qed.
