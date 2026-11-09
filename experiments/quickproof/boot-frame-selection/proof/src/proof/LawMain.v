(* Law frame_selection_exact: the body of the harness's main up to its objects: the function and the frame
   arguments it draws into the law, the eleven objects (main returns 0 when any is NULL); the rest is
   LawMainInit (the objects' values) and the steps' tails. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosFrameSelection.harness.frame_selection_exact.code.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
Require Import LeanosFrameSelection.proof.LawProg LeanosFrameSelection.proof.LawDefs LeanosFrameSelection.proof.LawFacts
  LeanosFrameSelection.proof.LawLib LeanosFrameSelection.proof.LawSplit LeanosFrameSelection.proof.LawMainDefs
  LeanosFrameSelection.proof.LawMainLib LeanosFrameSelection.proof.LawFast LeanosFrameSelection.proof.LawMainInit.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.
#[local] Ltac simplify_remove_localdef_temp ::= fast_remove_localdef_temp.

(* Freeze every SEP item but mem_mgr, the results of malloc and the law's fields in L. *)
Ltac keep_main x L :=
  lazymatch x with
  | field_at _ _ (StructField ?f :: nil) _ _ => lazymatch L with context [f] => constr:(true) | _ => constr:(false) end
  | mem_mgr _ => constr:(true)
  | mres _ _ => constr:(true)
  | _ => constr:(false)
  end.
Ltac idx_main R L i :=
  lazymatch R with
  | nil => constr:(@nil Z)
  | ?x :: ?R' =>
      let rest := idx_main R' L (Z.succ i) in
      let k := keep_main x L in
      lazymatch k with true => rest | false => let i' := eval cbn in i in constr:(i' :: rest) end
  end.
Ltac freeze_main L F :=
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
    let I := idx_main R L 0 in freeze_tac I F
  end.

Lemma call_mod: forall v, Int.modu (Int.repr v) (Int.repr 7) = Int.repr ((v mod 2 ^ 32) mod 7).
Proof.
  intros. unfold Int.modu. rewrite Int.unsigned_repr_eq. rewrite (Int.unsigned_repr 7) by rep_lia.
  reflexivity.
Qed.

Lemma call_range: forall v, 0 <= (v mod 2 ^ 32) mod 7 <= Int.max_unsigned.
Proof. intros. pose proof (Z.mod_pos_bound (v mod 2 ^ 32) 7 ltac:(lia)). rep_lia. Qed.

Lemma body_main (TTl: forall Espec: OracleKind, @tail_ok Espec s_terminal (at_step FTerminal)):
  forall p, QPprog_vars p = [(_law, v_law)] -> semax_body Vlaw Gmain f_main (_main, main_spec_std p).
Proof.
  intros prg Hp. start_function. rewrite Hp.
  assert_PROP (headptr (gv _law)) as HO by entailer!.
  sep_apply (law_zero gv HO).
  sep_apply (create_mem_mgr gv).
  unfold lzero. Intros.
  freeze_main [_call; _take_next; _selected; _selected_manifest; _published; _next] FR.
  forward.
  forward_call tt. Intros c0. forward.
  forward_call tt. Intros t0. forward.
  forward_call tt. Intros sel. forward.
  forward_call tt. Intros sm. forward.
  forward_call tt. Intros pub. forward.
  forward_call tt. Intros nx. forward.
  freeze_main (@nil ident) FR2.
  forward_call (tarray tulong 18, gv).
  all: try (solve [ simpl; split_and; try reflexivity; rep_lia ]).
  Intros mp. change (if eq_dec mp nullval then emp else _) with (mres (tarray tulong 18) mp).
  forward_call (tarray tulong 41, gv).
  all: try (solve [ simpl; split_and; try reflexivity; rep_lia ]).
  Intros dp. change (if eq_dec dp nullval then emp else _) with (mres (tarray tulong 41) dp).
  forward_call (tarray tulong 64, gv).
  all: try (solve [ simpl; split_and; try reflexivity; rep_lia ]).
  Intros up. change (if eq_dec up nullval then emp else _) with (mres (tarray tulong 64) up).
  forward_call (tarray tulong 64, gv).
  all: try (solve [ simpl; split_and; try reflexivity; rep_lia ]).
  Intros bp. change (if eq_dec bp nullval then emp else _) with (mres (tarray tulong 64) bp).
  forward_call (tarray tulong 64, gv).
  all: try (solve [ simpl; split_and; try reflexivity; rep_lia ]).
  Intros rp. change (if eq_dec rp nullval then emp else _) with (mres (tarray tulong 64) rp).
  forward_call (tarray tulong 9, gv).
  all: try (solve [ simpl; split_and; try reflexivity; rep_lia ]).
  Intros tp. change (if eq_dec tp nullval then emp else _) with (mres (tarray tulong 9) tp).
  forward_call (t_states, gv).
  all: try (solve [ simpl; split_and; try reflexivity; rep_lia ]).
  Intros sp. change (if eq_dec sp nullval then emp else _) with (mres (t_states) sp).
  forward_call (tarray tulong 5, gv).
  all: try (solve [ simpl; split_and; try reflexivity; rep_lia ]).
  Intros pp. change (if eq_dec pp nullval then emp else _) with (mres (tarray tulong 5) pp).
  forward_call (tarray tulong 5, gv).
  all: try (solve [ simpl; split_and; try reflexivity; rep_lia ]).
  Intros qp. change (if eq_dec qp nullval then emp else _) with (mres (tarray tulong 5) qp).
  forward_call (tarray tulong 3, gv).
  all: try (solve [ simpl; split_and; try reflexivity; rep_lia ]).
  Intros cp. change (if eq_dec cp nullval then emp else _) with (mres (tarray tulong 3) cp).
  forward_call (tuint, gv).
  all: try (solve [ simpl; split_and; try reflexivity; rep_lia ]).
  Intros ep. change (if eq_dec ep nullval then emp else _) with (mres (tuint) ep).
  assert_PROP (is_pointer_or_null mp) as Nmp by (unfold mres; destruct (eq_dec mp nullval); entailer!).
  assert_PROP (is_pointer_or_null dp) as Ndp by (unfold mres; destruct (eq_dec dp nullval); entailer!).
  assert_PROP (is_pointer_or_null up) as Nup by (unfold mres; destruct (eq_dec up nullval); entailer!).
  assert_PROP (is_pointer_or_null bp) as Nbp by (unfold mres; destruct (eq_dec bp nullval); entailer!).
  assert_PROP (is_pointer_or_null rp) as Nrp by (unfold mres; destruct (eq_dec rp nullval); entailer!).
  assert_PROP (is_pointer_or_null tp) as Ntp by (unfold mres; destruct (eq_dec tp nullval); entailer!).
  assert_PROP (is_pointer_or_null sp) as Nsp by (unfold mres; destruct (eq_dec sp nullval); entailer!).
  assert_PROP (is_pointer_or_null pp) as Npp by (unfold mres; destruct (eq_dec pp nullval); entailer!).
  assert_PROP (is_pointer_or_null qp) as Nqp by (unfold mres; destruct (eq_dec qp nullval); entailer!).
  assert_PROP (is_pointer_or_null cp) as Ncp by (unfold mres; destruct (eq_dec cp nullval); entailer!).
  assert_PROP (is_pointer_or_null ep) as Nep by (unfold mres; destruct (eq_dec ep nullval); entailer!).
  forward_if (temp _t'18 (Vint (Int.repr (Z.b2z (isnul mp || isnul dp))))).
  { apply (mres_tc' (tarray tulong 18) mp _ TT). cancel. }
  { forward. entailer!. }
  { forward.
    all: try (solve [ entailer!; apply (mres_tc' (tarray tulong 41) dp _ TT); cancel ]).
    entailer!. rewrite null_test2 by auto. rewrite (isnul_false mp) by auto. reflexivity. }
  forward_if (temp _t'19 (Vint (Int.repr (Z.b2z (isnul mp || isnul dp || isnul up))))).
  { try b2z_hyp. forward. entailer!. rw_bools. reflexivity. }
  { try b2z_hyp. forward.
    all: try (solve [ entailer!; apply (mres_tc' (tarray tulong 64) up _ TT); cancel ]).
    entailer!. rewrite null_test2 by auto. rw_bools. reflexivity. }
  forward_if (temp _t'20 (Vint (Int.repr (Z.b2z (isnul mp || isnul dp || isnul up || isnul bp))))).
  { try b2z_hyp. forward. entailer!. rw_bools. reflexivity. }
  { try b2z_hyp. forward.
    all: try (solve [ entailer!; apply (mres_tc' (tarray tulong 64) bp _ TT); cancel ]).
    entailer!. rewrite null_test2 by auto. rw_bools. reflexivity. }
  forward_if (temp _t'21 (Vint (Int.repr (Z.b2z (isnul mp || isnul dp || isnul up || isnul bp || isnul rp))))).
  { try b2z_hyp. forward. entailer!. rw_bools. reflexivity. }
  { try b2z_hyp. forward.
    all: try (solve [ entailer!; apply (mres_tc' (tarray tulong 64) rp _ TT); cancel ]).
    entailer!. rewrite null_test2 by auto. rw_bools. reflexivity. }
  forward_if (temp _t'22 (Vint (Int.repr (Z.b2z (isnul mp || isnul dp || isnul up || isnul bp || isnul rp || isnul tp))))).
  { try b2z_hyp. forward. entailer!. rw_bools. reflexivity. }
  { try b2z_hyp. forward.
    all: try (solve [ entailer!; apply (mres_tc' (tarray tulong 9) tp _ TT); cancel ]).
    entailer!. rewrite null_test2 by auto. rw_bools. reflexivity. }
  forward_if (temp _t'23 (Vint (Int.repr (Z.b2z (isnul mp || isnul dp || isnul up || isnul bp || isnul rp || isnul tp || isnul sp))))).
  { try b2z_hyp. forward. entailer!. rw_bools. reflexivity. }
  { try b2z_hyp. forward.
    all: try (solve [ entailer!; apply (mres_tc' (t_states) sp _ TT); cancel ]).
    entailer!. rewrite null_test2 by auto. rw_bools. reflexivity. }
  forward_if (temp _t'24 (Vint (Int.repr (Z.b2z (isnul mp || isnul dp || isnul up || isnul bp || isnul rp || isnul tp || isnul sp || isnul pp))))).
  { try b2z_hyp. forward. entailer!. rw_bools. reflexivity. }
  { try b2z_hyp. forward.
    all: try (solve [ entailer!; apply (mres_tc' (tarray tulong 5) pp _ TT); cancel ]).
    entailer!. rewrite null_test2 by auto. rw_bools. reflexivity. }
  forward_if (temp _t'25 (Vint (Int.repr (Z.b2z (isnul mp || isnul dp || isnul up || isnul bp || isnul rp || isnul tp || isnul sp || isnul pp || isnul qp))))).
  { try b2z_hyp. forward. entailer!. rw_bools. reflexivity. }
  { try b2z_hyp. forward.
    all: try (solve [ entailer!; apply (mres_tc' (tarray tulong 5) qp _ TT); cancel ]).
    entailer!. rewrite null_test2 by auto. rw_bools. reflexivity. }
  forward_if (temp _t'26 (Vint (Int.repr (Z.b2z (isnul mp || isnul dp || isnul up || isnul bp || isnul rp || isnul tp || isnul sp || isnul pp || isnul qp || isnul cp))))).
  { try b2z_hyp. forward. entailer!. rw_bools. reflexivity. }
  { try b2z_hyp. forward.
    all: try (solve [ entailer!; apply (mres_tc' (tarray tulong 3) cp _ TT); cancel ]).
    entailer!. rewrite null_test2 by auto. rw_bools. reflexivity. }
  forward_if (temp _t'27 (Vint (Int.repr (Z.b2z (isnul mp || isnul dp || isnul up || isnul bp || isnul rp || isnul tp || isnul sp || isnul pp || isnul qp || isnul cp || isnul ep))))).
  { try b2z_hyp. forward. entailer!. rw_bools. reflexivity. }
  { try b2z_hyp. forward.
    all: try (solve [ entailer!; apply (mres_tc' (tuint) ep _ TT); cancel ]).
    entailer!. rewrite null_test2 by auto. rw_bools. reflexivity. }
  forward_if (PROP ((isnul mp || isnul dp || isnul up || isnul bp || isnul rp || isnul tp || isnul sp || isnul pp || isnul qp || isnul cp || isnul ep)%bool = false)
              LOCAL (temp _m (gv _law); temp _manifest mp; temp _decoded dp; temp _usable up; temp _blocked bp;
                     temp _reserved rp; temp _terminal tp; temp _states sp; temp _publication pp; temp _rescan qp;
                     temp _records cp; temp _decoder_record ep; gvars gv)
              SEP (mem_mgr gv; mres (tuint) ep; mres (tarray tulong 3) cp; mres (tarray tulong 5) qp; mres (tarray tulong 5) pp; mres (t_states) sp; mres (tarray tulong 9) tp; mres (tarray tulong 64) rp; mres (tarray tulong 64) bp; mres (tarray tulong 64) up; mres (tarray tulong 41) dp; mres (tarray tulong 18) mp; FRZL FR2)).
  { forward. Exists (Int.repr 0). entailer!. }
  { try b2z_hyp. forward. entailer!. }
  Intros. match goal with H: (_ || _)%bool = false |- _ => rename H into Hn end.
  repeat rewrite orb_false_iff in Hn.
  destruct Hn as [[[[[[[[[[Emp Edp] Eup] Ebp] Erp] Etp] Esp] Epp] Eqp] Ecp] Eep].
  rewrite (mres_ptr _ mp Emp), (mres_ptr _ dp Edp), (mres_ptr _ up Eup), (mres_ptr _ bp Ebp), (mres_ptr _ rp Erp), (mres_ptr _ tp Etp), (mres_ptr _ sp Esp), (mres_ptr _ pp Epp), (mres_ptr _ qp Eqp), (mres_ptr _ cp Ecp), (mres_ptr _ ep Eep).
  Intros. thaw FR2. thaw FR.
  assert_PROP (isptr mp /\ isptr dp /\ isptr up /\ isptr bp /\ isptr rp /\ isptr tp /\ isptr sp /\ isptr pp /\ isptr qp /\ isptr cp /\ isptr ep) as PP by entailer!.
  unfold u64_ok in *. rewrite ?Int64.unsigned_repr by rep_lia.
  rewrite ?Int64.Z_mod_modulus_eq. rewrite ?(Z.mod_small c0 Int64.modulus), ?(Z.mod_small t0 Int64.modulus) by rep_lia.
  rewrite ?call_mod. rewrite ?(low32 t0).
  eapply semax_pre; [ | apply (tail_init (TTl _) gv (mk_ptrs mp dp up bp rp tp sp pp qp cp ep) ((c0 mod 2 ^ 32) mod 7) (t0 mod 2 ^ 32)
                                   sel sm pub nx) ].
  - unfold ldrawn, objs0. cbn [p_manifest p_decoded p_usable p_blocked p_reserved p_terminal p_states p_publication
      p_rescan p_records p_decoder]. entailer!.
  - unfold ptrs_ok; cbn [p_manifest p_decoded p_usable p_blocked p_reserved p_terminal p_states p_publication
      p_rescan p_records p_decoder]. tauto.
  - apply call_range.
  - apply low32_range.
  - auto.
  - auto.
  - auto.
  - auto.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
