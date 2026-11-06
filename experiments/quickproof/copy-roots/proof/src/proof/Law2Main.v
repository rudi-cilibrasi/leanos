(* Law window_roots_isolated: the body of the harness's main, for any program p without global variables
   (the law's whole_prog has none), under the roots unit's compspecs, from the segment lemmas
   Law2Seg*.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Import LeanosRoots.proof.Defs.
Require Import LeanosRoots.proof.RootsSpecs.
Require Import LeanosRoots.proof.Law2Model.
Require Import LeanosRoots.proof.Law2Helpers.
Require Import LeanosRoots.proof.Law2MainDefs.
Require Import LeanosRoots.proof.Law2SegFill LeanosRoots.proof.Law2SegValid LeanosRoots.proof.Law2SegSlots
  LeanosRoots.proof.Law2SegCounts LeanosRoots.proof.Law2SegFinal.
Require LeanosRoots.roots.code.
Require Import LeanosRoots.harness.window_roots_isolated.code.
#[local] Existing Instance RootsSpecs.CS.
Local Open Scope bool_scope.

Lemma src_join: forall l1 l2 l3 l4 v,
  @field_at CS Tsh (Tstruct _qotom_root_pages noattr) (DOT _pml4) (longs l1) v * @field_at CS Tsh (Tstruct _qotom_root_pages noattr) (DOT _pdpt) (longs l2) v *
  @field_at CS Tsh (Tstruct _qotom_root_pages noattr) (DOT _pd) (longs l3) v * @field_at CS Tsh (Tstruct _qotom_root_pages noattr) (DOT _pt) (longs l4) v
  |-- data_at Tsh t_root (root_val (mkroot l1 l2 l3 l4)) v.
Proof. intros. unfold root_val. unfold_data_at (data_at _ _ _ v). cbn [pml4 pdpt pd pt]. cancel. Qed.

Lemma frames_len: forall (fl: list Z) v, Zlength fl = 16 ->
  data_at Tsh (tarray tulong 16) (longs fl) v |-- data_at Tsh (tarray tulong (Zlength fl)) (longs fl) v.
Proof. intros. rewrite H. auto. Qed.

Lemma pages_val: forall b l, word_ok b -> word_ok l ->
  Int64.divu (Int64.sub (Int64.repr l) (Int64.repr b)) (Int64.repr 4096) = Int64.repr (((l - b) mod W) / 4096).
Proof.
  intros. unfold Int64.divu. rewrite sub64_repr. rewrite Int64.unsigned_repr_eq.
  rewrite (Int64.unsigned_repr 4096) by rep_lia. reflexivity.
Qed.

Lemma pre_ok_facts: forall src sp kp fs n w, pre_ok src sp kp fs n w = true ->
  geometry_ok w = true /\ 1 <= n <= 16.
Proof.
  intros src sp kp fs n w H. unfold pre_ok in H.
  apply andb_prop in H; destruct H as [H Hinv].
  apply andb_prop in H; destruct H as [H _].
  apply andb_prop in H; destruct H as [_ Hgeo].
  split; auto.
  unfold inventory_ok in Hinv.
  apply andb_prop in Hinv; destruct Hinv as [Hinv _].
  apply andb_prop in Hinv; destruct Hinv as [Hinv _].
  apply andb_prop in Hinv; destruct Hinv as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Ltac apply_seg L :=
  first [ eapply semax_seq'; [ eapply semax_pre; [ | apply L ] | ]
        | apply -> seq_assoc; eapply semax_seq'; [ eapply semax_pre; [ | apply L ] | ] ].

Local Opaque idx.

(* Before a return: every value in SEP made an opaque variable, so the cancellation of the stack frame
   (data_at against data_at_) does not unify large values. *)
Ltac hide_vals :=
  repeat match goal with |- context [data_at _ _ ?v _] =>
    tryif is_var v then fail else (let X := fresh "X" in set (X := v); clearbody X) end.

Ltac weaken_lhs :=
  match goal with
  | |- ?A * ?B |-- _ => apply sepcon_derives; [ weaken_lhs | weaken_lhs ]
  | |- data_at _ _ _ _ |-- _ => apply data_at_data_at_
  | |- _ |-- _ => apply derives_refl
  end.

(* The stack frame at a return: every local is data_at_, the rest goes to TT. *)
(* An entailment between two states with the same PROP, LOCAL and SEP lists.  The SEP lists are compared
   syntactically first: a failed unification of two data_at items of one root type unfolds them, and cancel
   (or entailer!) on such items takes minutes even when their values are hidden. *)
Ltac same_frame :=
  apply andp_left2; unfold PROPx; apply andp_derives; [ apply derives_refl | ];
  unfold LOCALx; apply andp_derives; [ apply derives_refl | ];
  match goal with |- SEPx ?A |-- SEPx ?B => constr_eq A B; apply derives_refl end.
Ltac ret_frame :=
  apply andp_right; [ apply prop_right; reflexivity | ];
  eapply derives_trans; [ weaken_lhs | ]; cancel.

Lemma body_main_gen: forall p, QPprog_vars p = nil -> semax_body nil Gmain f_main (_main, main_spec_std p).
Proof.
  intros p Hp.
  start_function.
  rewrite Hp. change (globvars2pred gv []) with (emp: mpred).
  forward_call. Intros sp.
  forward_call. Intros kp.
  forward. forward.
  forward_call. Intros fp. forward.
  forward_call. Intros spp. forward.
  freeze FR := (data_at_ Tsh tint v_built) (data_at_ _ _ v_first) (data_at _ _ _ v_w) (data_at_ _ _ v_kept)
    (data_at_ _ _ v_frames) (data_at_ _ _ v_send) (data_at_ _ _ v_fetch) (data_at_ _ _ v_closed)
    (has_ext _).
  apply_seg (seg_loop1 gv v_source v_closed v_fetch v_send v_frames v_kept v_w v_first v_built sp kp (FRZL FR)). { entailer!. }
  Intros l1 l2 l3. thaw FR.
  freeze FA := (field_at _ _ (DOT _pml4) _ _) (field_at _ _ (DOT _pdpt) _ _) (field_at _ _ (DOT _pd) _ _).
  freeze FR := (FRZL FA) (data_at_ Tsh tint v_built) (data_at_ _ _ v_first) (data_at _ _ _ v_w)
    (data_at_ _ _ v_frames) (data_at_ _ _ v_send) (data_at_ _ _ v_fetch) (data_at_ _ _ v_closed)
    (has_ext _).
  apply_seg (seg_loop2 gv v_source v_closed v_fetch v_send v_frames v_kept v_w v_first v_built sp kp (FRZL FR)). { entailer!. }
  Intros l4. thaw FR. thaw FA.
  forward_call. Intros n.
  freeze FA := (field_at _ _ (DOT _pml4) _ _) (field_at _ _ (DOT _pdpt) _ _) (field_at _ _ (DOT _pd) _ _)
    (field_at _ _ (DOT _pt) _ _) (data_at _ _ _ v_kept).
  freeze FR := (FRZL FA) (data_at_ Tsh tint v_built) (data_at_ _ _ v_first) (data_at _ _ _ v_w)
    (data_at_ _ _ v_send) (data_at_ _ _ v_fetch) (data_at_ _ _ v_closed)
    (has_ext _).
  apply_seg (seg_loop3 gv v_source v_closed v_fetch v_send v_frames v_kept v_w v_first v_built sp kp n (FRZL FR)). { entailer!. }
  Intros fl. thaw FR. thaw FA.
  forward_call. Intros b. forward.
  forward_call. Intros l. forward.
  forward_call. Intros s. forward.
  forward_call. Intros c0. forward.
  forward_call. Intros c1. forward.
  forward_call. Intros c2. forward.
  forward_call. Intros c3. forward.
  forward_call. Intros u. forward.
  assert (Wsp: word_ok sp) by (unfold word_ok; lia). assert (Wkp: word_ok kp) by (unfold word_ok; lia).
  assert (Wn: word_ok n) by (unfold word_ok; lia).
  match goal with H: Zlength fl = 16 |- _ => rename H into Hfl end.
  match goal with H: words_ok fl |- _ => rename H into Wfl end.
  sep_apply (src_join l1 l2 l3 l4 v_source).
  sep_apply (frames_len fl v_frames Hfl).
  assert (Hr: root_ok (mkroot l1 l2 l3 l4)) by (unfold root_ok, LEAVES; cbn [pml4 pdpt pd pt]; repeat split; auto).
  assert (Hw: window_wf (mkwindow fp spp b l s))
    by (unfold window_wf, word_ok; cbn [w_fetch_phys w_send_phys w_base w_limit w_slot]; repeat split; rep_lia).
  assert (Hfr: counts_wf (mkcounts c0 c1 c2 c3))
    by (unfold counts_wf, word_ok; cbn [c_protected c_removed c_retained c_aliases]; repeat split; rep_lia).
  change (@data_at CS Tsh (Tstruct _frame_window noattr)
       (v_fetch, (v_send, (Vlong (Int64.repr fp), (Vlong (Int64.repr spp),
           (Vlong (Int64.repr b), (Vlong (Int64.repr l), Vlong (Int64.repr s))))))) v_w)
    with (data_at Tsh t_window (window_val v_fetch v_send (mkwindow fp spp b l s)) v_w).
  change (@data_at CS Tsh (Tstruct _qotom_root_build_result noattr)
       (Vlong (Int64.repr c0), (Vlong (Int64.repr c1), (Vlong (Int64.repr c2), Vlong (Int64.repr c3)))) v_first)
    with (data_at Tsh t_result (counts_val (mkcounts c0 c1 c2 c3)) v_first).
  assert (Hb: Int.min_signed <= Int.signed (Int.repr u) <= Int.max_signed) by apply Int.signed_range.
  rewrite <- (Int.repr_signed (Int.repr u)).
  forget (Int.signed (Int.repr u)) as built.
  freeze FR := (data_at _ _ _ v_kept) (data_at_ _ _ v_closed) (data_at_ _ _ v_fetch) (data_at_ _ _ v_send)
    (data_at _ _ _ v_first) (data_at _ _ _ v_built) (has_ext _).
  apply_seg (seg_valid gv v_source v_closed v_fetch v_send v_frames v_kept v_w v_first v_built (mkroot l1 l2 l3 l4) sp kp n fl (mkwindow fp spp b l s) (FRZL FR) Hr Wsp Wkp Wn Hfl Wfl Hw).
  { entailer!. }
  thaw FR.
  assert (HV0: pre_ok (mkroot l1 l2 l3 l4) sp kp fl n (mkwindow fp spp b l s) = true ->
               geometry_ok (mkwindow fp spp b l s) = true /\ n <= 16)
    by (intro HH; destruct (pre_ok_facts _ _ _ _ _ _ HH); split; [ auto | lia ]).
  unfold window_val.
  forward. forward. forward.
  change (@data_at CS Tsh t_window
       (v_fetch, (v_send, (Vlong (Int64.repr (w_fetch_phys (mkwindow fp spp b l s))),
         (Vlong (Int64.repr (w_send_phys (mkwindow fp spp b l s))), (Vlong (Int64.repr (w_base (mkwindow fp spp b l s))),
          (Vlong (Int64.repr (w_limit (mkwindow fp spp b l s))), Vlong (Int64.repr (w_slot (mkwindow fp spp b l s))))))))) v_w)
    with (data_at Tsh t_window (window_val v_fetch v_send (mkwindow fp spp b l s)) v_w).
  freeze FR := (data_at _ _ _ v_kept) (data_at_ _ _ v_closed) (data_at_ _ _ v_fetch) (data_at_ _ _ v_send)
    (data_at _ _ _ v_first) (data_at _ _ _ v_built) (has_ext _).
  apply_seg (seg_slots gv v_source v_closed v_fetch v_send v_frames v_kept v_w v_first v_built (mkroot l1 l2 l3 l4) sp kp n fl (mkwindow fp spp b l s)
               (pre_ok (mkroot l1 l2 l3 l4) sp kp fl n (mkwindow fp spp b l s)) (FRZL FR) Hr Wn Hfl Wfl Hw HV0).
  { entailer!. unfold pages_of. cbn [w_limit w_base]. unfold Int64.divu.
    rewrite Int64.unsigned_repr_eq, (Int64.unsigned_repr 4096) by rep_lia. reflexivity. }
  thaw FR.
  forward. forward.
  assert (HV1: (pre_ok (mkroot l1 l2 l3 l4) sp kp fl n (mkwindow fp spp b l s) &&
                slots_ok (mkroot l1 l2 l3 l4) (sublist 0 n fl) (mkwindow fp spp b l s)) = true -> n <= 16)
    by (intro HH; apply andb_prop in HH; destruct HH as [HH _]; destruct (pre_ok_facts _ _ _ _ _ _ HH); lia).
  freeze FR := (data_at _ _ _ v_kept) (data_at_ _ _ v_closed) (data_at_ _ _ v_fetch) (data_at_ _ _ v_send)
    (data_at _ _ _ v_w) (has_ext _).
  apply_seg (seg_counts gv v_source v_closed v_fetch v_send v_frames v_kept v_w v_first v_built (mkroot l1 l2 l3 l4) sp kp n built fl (mkwindow fp spp b l s) (mkcounts c0 c1 c2 c3)
               (pre_ok (mkroot l1 l2 l3 l4) sp kp fl n (mkwindow fp spp b l s) &&
                slots_ok (mkroot l1 l2 l3 l4) (sublist 0 n fl) (mkwindow fp spp b l s)) (FRZL FR)
               Hr Wn Hfl Wfl Hfr Hb HV1).
  { entailer!. }
  thaw FR.
  rewrite (valid_window_ok (mkroot l1 l2 l3 l4) sp kp fl n (mkwindow fp spp b l s) built (mkcounts c0 c1 c2 c3) Wsp Wkp Hw).
  rewrite !data_at__eq.
  forward_call (v_source, Tsh, mkroot l1 l2 l3 l4, sp, v_closed, default_val t_root, kp, v_frames, Tsh, fl, n,
                v_w, Tsh, v_fetch, default_val t_root, v_send, default_val t_root, mkwindow fp spp b l s,
                v_first, mkcounts c0 c1 c2 c3, v_built, built).
  Intros vret. destruct vret as [[[[[status k'] fe'] se'] r'] b']. simpl fst in *; simpl snd in *.
  match goal with H: 0 <= status <= 4 |- _ => rename H into Hst end.
  match goal with H: status = 0 <-> _ |- _ => rename H into Hiff end.
  match goal with H: status = 0 -> _ |- _ => rename H into Hpost end.
  forward_call (Int.one).
  { entailer!. match goal with |- context [b2z ?X] => destruct X eqn:Ewok end.
    - assert (status = 0) by (apply Hiff; auto). subst status. reflexivity.
    - assert (Hs0: status <> 0) by (intro HH; apply Hiff in HH; congruence).
      assert (Ez: Int.eq (Int.repr status) (Int.repr 0) = false).
      { unfold Int.eq. rewrite !Int.unsigned_repr by rep_lia. destruct (zeq status 0); [ contradiction | reflexivity ]. }
      rewrite Ez. reflexivity. }
  forward_if.
  { rewrite Hfl. deadvars!. hide_vals.
    forward. Exists (Int.repr 0). ret_frame. }
  assert (Hs0: status = 0).
  { unfold Int.zero in *.
    first [ assumption
          | match goal with H: Int.repr status = Int.repr 0 |- _ => apply int_repr_zero in H; [ exact H | lia ] end
          | match goal with H: Int.eq (Int.repr status) (Int.repr 0) = true |- _ =>
              apply Int.same_if_eq in H; apply int_repr_zero in H; [ exact H | lia ] end
          | match goal with H: negb (Int.eq (Int.repr status) (Int.repr 0)) = false |- _ =>
              apply negb_false_iff, Int.same_if_eq in H; apply int_repr_zero in H; [ exact H | lia ] end ]. }
  subst status.
  destruct (Hpost eq_refl) as (Ek & Efe & Ese & Eb' & Er'). subst k' fe' se' b' r'.
  assert (WOK: window_ok (mkroot l1 l2 l3 l4) sp kp fl n (mkwindow fp spp b l s) built (mkcounts c0 c1 c2 c3) = true)
    by (apply Hiff; reflexivity).
  rewrite <- (valid_window_ok _ _ _ _ _ _ _ _ Wsp Wkp Hw) in WOK.
  apply andb_prop in WOK. destruct WOK as [WOK HC]. apply andb_prop in WOK. destruct WOK as [HP HS].
  destruct (pre_ok_facts _ _ _ _ _ _ HP) as [HG Hn16].
  rewrite HP, HS in *. simpl andb in *.
  freeze FX := (data_at _ _ _ v_source) (data_at _ _ _ v_fetch) (data_at _ _ _ v_send) (data_at _ _ _ v_kept)
    (data_at _ _ _ v_frames) (data_at _ _ _ v_w) (data_at _ _ _ v_first) (data_at _ _ _ v_built).
  forward_call (v_closed, Tsh, closed_out (mkroot l1 l2 l3 l4) (sublist 0 n fl) kp, kp, 0).
  { repeat split; first [ apply closed_out_ok; auto | (unfold word_ok in *; rep_lia) ]. }
  forward_call (Int.one).
  { entailer!. unfold closed_out. rewrite tables_built. reflexivity. }
  thaw FX.
  freeze FX := (data_at _ _ _ v_source) (data_at _ _ _ v_closed) (data_at _ _ _ v_send) (data_at _ _ _ v_kept)
    (data_at _ _ _ v_frames) (data_at _ _ _ v_first) (data_at _ _ _ v_built).
  unfold window_val.
  forward.
  forward_call (v_fetch, Tsh, copy_out (mkroot l1 l2 l3 l4) (sublist 0 n fl) (window_aliases (mkwindow fp spp b l s) 1)
                 (w_fetch_phys (mkwindow fp spp b l s)), w_fetch_phys (mkwindow fp spp b l s), 0).
  { repeat split; first [ apply copy_out_ok; auto | (unfold word_ok in *; cbn [w_fetch_phys w_send_phys]; rep_lia) ]. }
  forward_call (Int.one).
  { entailer!. unfold copy_out. rewrite tables_built. reflexivity. }
  thaw FX.
  freeze FX := (data_at _ _ _ v_source) (data_at _ _ _ v_closed) (data_at _ _ _ v_fetch) (data_at _ _ _ v_kept)
    (data_at _ _ _ v_frames) (data_at _ _ _ v_first) (data_at _ _ _ v_built).
  forward.
  forward_call (v_send, Tsh, copy_out (mkroot l1 l2 l3 l4) (sublist 0 n fl) (window_aliases (mkwindow fp spp b l s) 0)
                 (w_send_phys (mkwindow fp spp b l s)), w_send_phys (mkwindow fp spp b l s), 0).
  { repeat split; first [ apply copy_out_ok; auto | (unfold word_ok in *; cbn [w_fetch_phys w_send_phys]; rep_lia) ]. }
  forward_call (Int.one).
  { entailer!. unfold copy_out. rewrite tables_built. reflexivity. }
  thaw FX.
  change (longs l4) with (longs (pt (mkroot l1 l2 l3 l4))).
  freeze FR := (data_at _ _ _ v_first) (data_at _ _ _ v_built) (has_ext _).
  drop_LOCALs [_t'53; _t'74; _t'52; _t'75; _t'51; _status; _valid].
  freeze FA := (data_at _ _ _ v_source) (data_at _ _ _ v_kept) (data_at _ _ _ v_closed) (data_at _ _ _ v_fetch)
    (data_at _ _ _ v_send) (data_at _ _ _ v_frames) (data_at _ _ _ v_w) (FRZL FR).
  thaw FA.
  apply_seg (seg_final gv v_source v_closed v_fetch v_send v_frames v_kept v_w v_first v_built (mkroot l1 l2 l3 l4) sp kp n
               (removed_count (sublist 0 n fl) (pt (mkroot l1 l2 l3 l4)))
               (retained_count (sublist 0 n fl) (pt (mkroot l1 l2 l3 l4))) fl (mkwindow fp spp b l s) (FRZL FR)
               Hr Hw HG Hfl Wfl ltac:(lia)).
  { unfold final_inv, window_val. hide_vals. same_frame. }
  unfold final_inv. Intros. thaw FR.
  clear Hiff HV0 HV1 HP HS HG Hw.
  forward.
  forward_call (Int.one).
  { entailer!. destruct (Z.eqb_spec built 0) as [Eb0 | Eb0]; [ reflexivity | ].
    assert (Ez: Int.eq (Int.repr built) (Int.repr 0) = false).
    { apply Int.eq_false. intro HH. apply Eb0. exact (int_repr_zero built Hb HH). }
    rewrite Ez. reflexivity. }
  assert (Er: exists X, (if built =? 0
      then result_val n (removed_count (sublist 0 n fl) (pt (mkroot l1 l2 l3 l4)))
             (retained_count (sublist 0 n fl) (pt (mkroot l1 l2 l3 l4))) (pages_of (mkwindow fp spp b l s))
      else counts_val (mkcounts c0 c1 c2 c3)) =
    result_val n (removed_count (sublist 0 n fl) (pt (mkroot l1 l2 l3 l4)))
      (retained_count (sublist 0 n fl) (pt (mkroot l1 l2 l3 l4))) X).
  { destruct (Z.eqb_spec built 0) as [E0 | E0]; [ eexists; reflexivity | ].
    rewrite counts_ok_nz in HC by auto. cbn [c_protected c_removed c_retained] in HC.
    apply andb_prop in HC. destruct HC as [HC HC3]. apply andb_prop in HC. destruct HC as [HC1 HC2].
    apply Z.eqb_eq in HC1, HC2, HC3. subst. exists c3. reflexivity. }
  destruct Er as [X Er]. rewrite Er. unfold result_val.
  assert (Rm := removed_le (sublist 0 n fl) (pt (mkroot l1 l2 l3 l4))).
  assert (Rt := retained_le (sublist 0 n fl) (pt (mkroot l1 l2 l3 l4))).
  rewrite (proj1 (proj2 (proj2 (proj2 Hr)))) in Rm, Rt.
  forward.
  forward_if (temp _t'58 (Vint Int.one)).
  { forward. forward. entailer!. rewrite Int64.eq_true. reflexivity. }
  { exfalso. match goal with H: Int64.repr _ <> Int64.repr _ |- _ => apply H; reflexivity end. }
  forward_if (temp _t'59 (Vint Int.one)).
  { forward. forward. entailer!. rewrite Int64.eq_true. reflexivity. }
  { exfalso. apply Int.one_not_zero. assumption. }
  forward_call (Int.one).
  rewrite Hfl. deadvars!. hide_vals.
  forward. Exists (Int.repr 0). ret_frame.
Qed.

