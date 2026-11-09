(* Law window_roots_isolated: main's pre-pass counts and the comparison with first. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Import LeanosRoots.proof.Defs.
Require Import LeanosRoots.proof.RootsSpecs.
Require Import LeanosRoots.proof.Law2Model.
Require Import LeanosRoots.proof.Law2Helpers.
Require Import LeanosRoots.proof.Law2MainDefs.
Require Import LeanosRoots.proof.Law2SegSlots.
Require LeanosRoots.roots.code.
Require Import LeanosRoots.harness.window_roots_isolated.code.
#[local] Existing Instance RootsSpecs.CS.
Local Open Scope bool_scope.

Lemma odd64: forall s, word_ok s -> Int64.and (Int64.repr s) (Int64.repr 1) = Int64.repr (if Z.odd s then 1 else 0).
Proof. intros. rewrite and64_repr, land1 by (unfold word_ok in *; lia). reflexivity. Qed.

Lemma frame64: forall s, word_ok s ->
  Int64.shru (Int64.and (Int64.repr s) (Int64.repr 4503599627366400)) (Int64.repr (Int.unsigned (Int.repr 12))) =
  Int64.repr (frame_of s).
Proof.
  intros. rewrite and64_repr, Int.unsigned_repr by rep_lia. rewrite shru64_repr by (try apply w_land; auto; lia).
  reflexivity.
Qed.

Lemma removed_snoc: forall inv (l: list Z) p, 0 <= p < Zlength l ->
  removed_count inv (sublist 0 (p + 1) l) = removed_count inv (sublist 0 p l) + (if removes inv (Znth p l) then 1 else 0).
Proof.
  intros. unfold removed_count. rewrite sublist_snoc by lia. rewrite filter_app, Zlength_app. simpl.
  destruct (removes inv (Znth p l)); reflexivity.
Qed.

Lemma retained_snoc: forall inv (l: list Z) p, 0 <= p < Zlength l ->
  retained_count inv (sublist 0 (p + 1) l) =
  retained_count inv (sublist 0 p l) + (if Z.odd (Znth p l) && negb (member (frame_of (Znth p l)) inv) then 1 else 0).
Proof.
  intros. unfold retained_count. rewrite sublist_snoc by lia. rewrite filter_app, Zlength_app. simpl.
  destruct (Z.odd (Znth p l) && negb (member (frame_of (Znth p l)) inv)); reflexivity.
Qed.

Lemma filter_le: forall {A} (f: A -> bool) l, Zlength (filter f l) <= Zlength l.
Proof.
  intros. induction l; simpl; [ lia | ]. destruct (f a); rewrite ?Zlength_cons; lia.
Qed.

Lemma removed_le: forall inv l, 0 <= removed_count inv l <= Zlength l.
Proof. intros. unfold removed_count. split; [ apply Zlength_nonneg | apply filter_le ]. Qed.
Lemma retained_le: forall inv l, 0 <= retained_count inv l <= Zlength l.
Proof. intros. unfold retained_count. split; [ apply Zlength_nonneg | apply filter_le ]. Qed.

Ltac contra := b2z_hyps; first [ discriminate
  | (exfalso; match goal with H: _ <> _ |- _ => apply H; reflexivity end)
  | (exfalso; apply Int.one_not_zero; assumption) ].

Lemma repr64_one_zero: Int64.repr 1 <> Int64.repr 0.
Proof. intro H. apply repr64_inj in H; [ lia | unfold word_ok; rep_lia | unfold word_ok; rep_lia ]. Qed.

Ltac oddcase :=
  n64; rewrite ?land1 in * by (unfold word_ok in *; lia);
  match goal with
  | |- context [Z.odd ?x] => let Eo := fresh "Eo" in destruct (Z.odd x) eqn:Eo
  | H: context [Z.odd ?x] |- _ => let Eo := fresh "Eo" in destruct (Z.odd x) eqn:Eo
  end;
  try (exfalso; match goal with
    | H: Int64.repr ?a <> Int64.repr ?a |- _ => apply H; reflexivity
    | H: Int64.repr 1 = Int64.repr 0 |- _ => apply repr64_one_zero; exact H
    end).

Lemma ret_when_removed: forall inv s, removes inv s = true ->
  (if Z.odd s && negb (member (frame_of s) inv) then 1 else 0) = 0.
Proof. intros inv s H. unfold removes in H. apply andb_prop in H. destruct H as [-> ->]. reflexivity. Qed.
Lemma ret_when_kept_odd: forall inv s, removes inv s = false -> Z.odd s = true ->
  (if Z.odd s && negb (member (frame_of s) inv) then 1 else 0) = 1.
Proof. intros inv s H Ho. unfold removes in H. rewrite Ho in *. simpl in H. rewrite H. reflexivity. Qed.
Lemma ret_when_even: forall inv s, Z.odd s = false ->
  (if Z.odd s && negb (member (frame_of s) inv) then 1 else 0) = 0 /\ removes inv s = false.
Proof. intros inv s Ho. unfold removes. rewrite Ho. split; reflexivity. Qed.

Lemma counts_ok_nz: forall src inv n built fr, built <> 0 ->
  counts_ok src inv n built fr = (c_protected fr =? n) && (c_removed fr =? removed_count inv (pt src)) &&
                                 (c_retained fr =? retained_count inv (pt src)).
Proof. intros. unfold counts_ok. rewrite (proj2 (Z.eqb_neq _ _)) by auto. reflexivity. Qed.

Lemma int_repr_zero: forall a, Int.min_signed <= a <= Int.max_signed -> Int.repr a = Int.repr 0 -> a = 0.
Proof. intros a Ha E. apply (f_equal Int.signed) in E. rewrite !Int.signed_repr in E by rep_lia. auto. Qed.

Ltac negb_hyps :=
  repeat match goal with
  | Hc: negb _ = true |- _ => apply negb_true_iff in Hc
  | Hc: negb _ = false |- _ => apply negb_false_iff in Hc
  end.

Lemma seg_counts: forall {Espec: OracleKind} (gv: globals) (v_source v_closed v_fetch v_send v_frames v_kept v_w v_first v_built: val) (src: root) (sp kp n built: Z) (fl: list Z) (w: window)
    (fr: counts) (V1: bool) (F: mpred),
  root_ok src -> word_ok n -> Zlength fl = 16 -> words_ok fl -> counts_wf fr ->
  Int.min_signed <= built <= Int.max_signed -> (V1 = true -> n <= 16) ->
  semax Dm
    (PROP () LOCAL (temp _retained (Vlong (Int64.repr 0)); temp _removed (Vlong (Int64.repr 0));
                    temp _valid (Vint (Int.repr (b2z V1))); temp _pages (Vlong (Int64.repr (pages_of w)));
                    temp _n (Vlong (Int64.repr n)); temp _source_phys (Vlong (Int64.repr sp));
                    temp _closed_phys (Vlong (Int64.repr kp)); lvar _built tint v_built; lvar _first (Tstruct _qotom_root_build_result noattr) v_first; lvar _w (Tstruct _frame_window noattr) v_w; lvar _kept (tarray tulong 4096) v_kept; lvar _frames (tarray tulong 16) v_frames; lvar _send (Tstruct _qotom_root_pages noattr) v_send; lvar _fetch (Tstruct _qotom_root_pages noattr) v_fetch; lvar _closed (Tstruct _qotom_root_pages noattr) v_closed; lvar _source (Tstruct _qotom_root_pages noattr) v_source; gvars gv)
     SEP (data_at Tsh t_root (root_val src) v_source; data_at Tsh (tarray tulong (Zlength fl)) (longs fl) v_frames;
          data_at Tsh tint (Vint (Int.repr built)) v_built; data_at Tsh t_result (counts_val fr) v_first; F))
    s_counts
    (normal_ret_assert
     (PROP () LOCAL (temp _retained (Vlong (Int64.repr (if V1 then retained_count (sublist 0 n fl) (pt src) else 0)));
                     temp _removed (Vlong (Int64.repr (if V1 then removed_count (sublist 0 n fl) (pt src) else 0)));
                     temp _valid (Vint (Int.repr (b2z (V1 && counts_ok src (sublist 0 n fl) n built fr))));
                     temp _pages (Vlong (Int64.repr (pages_of w)));
                     temp _n (Vlong (Int64.repr n)); temp _source_phys (Vlong (Int64.repr sp));
                     temp _closed_phys (Vlong (Int64.repr kp)); lvar _built tint v_built; lvar _first (Tstruct _qotom_root_build_result noattr) v_first; lvar _w (Tstruct _frame_window noattr) v_w; lvar _kept (tarray tulong 4096) v_kept; lvar _frames (tarray tulong 16) v_frames; lvar _send (Tstruct _qotom_root_pages noattr) v_send; lvar _fetch (Tstruct _qotom_root_pages noattr) v_fetch; lvar _closed (Tstruct _qotom_root_pages noattr) v_closed; lvar _source (Tstruct _qotom_root_pages noattr) v_source; gvars gv)
      SEP (data_at Tsh t_root (root_val src) v_source; data_at Tsh (tarray tulong (Zlength fl)) (longs fl) v_frames;
           data_at Tsh tint (Vint (Int.repr built)) v_built; data_at Tsh t_result (counts_val fr) v_first; F))).
Proof.
  intros until F. intros Hr Hn Hfl Wfl Hfr Hb HV.
  unfold s_counts, Dm. simplify_func_tycontext. abbreviate_semax.
  destruct V1.
  2: { forward_if (PROP () LOCAL (temp _retained (Vlong (Int64.repr 0)); temp _removed (Vlong (Int64.repr 0));
                    temp _valid (Vint (Int.repr (b2z false))); temp _pages (Vlong (Int64.repr (pages_of w)));
                    temp _n (Vlong (Int64.repr n)); temp _source_phys (Vlong (Int64.repr sp));
                    temp _closed_phys (Vlong (Int64.repr kp)); lvar _built tint v_built; lvar _first (Tstruct _qotom_root_build_result noattr) v_first; lvar _w (Tstruct _frame_window noattr) v_w; lvar _kept (tarray tulong 4096) v_kept; lvar _frames (tarray tulong 16) v_frames; lvar _send (Tstruct _qotom_root_pages noattr) v_send; lvar _fetch (Tstruct _qotom_root_pages noattr) v_fetch; lvar _closed (Tstruct _qotom_root_pages noattr) v_closed; lvar _source (Tstruct _qotom_root_pages noattr) v_source; gvars gv)
     SEP (data_at Tsh t_root (root_val src) v_source; data_at Tsh (tarray tulong (Zlength fl)) (longs fl) v_frames;
          data_at Tsh tint (Vint (Int.repr built)) v_built; data_at Tsh t_result (counts_val fr) v_first; F)).
       { contra. }
       { forward. entailer!. } }
  set (inv := sublist 0 n fl).
  specialize (HV eq_refl).
  destruct Hr as (Lm & Lp & Ld & Lt & Wm & Wp & Wd & Wt).
  forward_if (PROP () LOCAL (temp _retained (Vlong (Int64.repr (retained_count inv (pt src))));
                    temp _removed (Vlong (Int64.repr (removed_count inv (pt src))));
                    temp _valid (Vint (Int.repr (b2z (counts_ok src inv n built fr))));
                    temp _pages (Vlong (Int64.repr (pages_of w)));
                    temp _n (Vlong (Int64.repr n)); temp _source_phys (Vlong (Int64.repr sp));
                    temp _closed_phys (Vlong (Int64.repr kp)); lvar _built tint v_built; lvar _first (Tstruct _qotom_root_build_result noattr) v_first; lvar _w (Tstruct _frame_window noattr) v_w; lvar _kept (tarray tulong 4096) v_kept; lvar _frames (tarray tulong 16) v_frames; lvar _send (Tstruct _qotom_root_pages noattr) v_send; lvar _fetch (Tstruct _qotom_root_pages noattr) v_fetch; lvar _closed (Tstruct _qotom_root_pages noattr) v_closed; lvar _source (Tstruct _qotom_root_pages noattr) v_source; gvars gv)
     SEP (data_at Tsh t_root (root_val src) v_source; data_at Tsh (tarray tulong (Zlength fl)) (longs fl) v_frames;
          data_at Tsh tint (Vint (Int.repr built)) v_built; data_at Tsh t_result (counts_val fr) v_first; F)).
  2: { contra. }
  forward_for_simple_bound 4096
    (EX p: Z, (PROP ()
     LOCAL (temp _retained (Vlong (Int64.repr (retained_count inv (sublist 0 p (pt src)))));
            temp _removed (Vlong (Int64.repr (removed_count inv (sublist 0 p (pt src)))));
            temp _valid (Vint (Int.repr (b2z true))); temp _pages (Vlong (Int64.repr (pages_of w)));
            temp _n (Vlong (Int64.repr n)); temp _source_phys (Vlong (Int64.repr sp));
            temp _closed_phys (Vlong (Int64.repr kp)); lvar _built tint v_built; lvar _first (Tstruct _qotom_root_build_result noattr) v_first; lvar _w (Tstruct _frame_window noattr) v_w; lvar _kept (tarray tulong 4096) v_kept; lvar _frames (tarray tulong 16) v_frames; lvar _send (Tstruct _qotom_root_pages noattr) v_send; lvar _fetch (Tstruct _qotom_root_pages noattr) v_fetch; lvar _closed (Tstruct _qotom_root_pages noattr) v_closed; lvar _source (Tstruct _qotom_root_pages noattr) v_source; gvars gv)
     SEP (data_at Tsh t_root (root_val src) v_source; data_at Tsh (tarray tulong (Zlength fl)) (longs fl) v_frames;
          data_at Tsh tint (Vint (Int.repr built)) v_built; data_at Tsh t_result (counts_val fr) v_first; F)
     : environ -> mpred)).
  { entailer!. }
  { rename i into p. unfold root_val. unfold LEAVES in *.
    assert (Ws := words_Znth (pt src) p Wt ltac:(lia)).
    assert (R1 := removed_le inv (sublist 0 p (pt src))). assert (R2 := retained_le inv (sublist 0 p (pt src))).
    rewrite Zlength_sublist in R1, R2 by lia.
    forward.
    all: try (entailer!; first [ lia | (rewrite Znth_longs by lia; exact I) ]).
    rewrite Znth_longs by lia.
    remember (Znth p (pt src)) as s eqn:Es.
    forward_if (temp _t'46 (Vint (Int.repr (b2z (removes inv s))))).
    { forward_call (frame_of s, v_frames, Tsh, fl, n).
      { entailer!. rewrite shru64_repr by (first [ apply w_land; auto | lia ]). reflexivity. }
      { split; [ apply frame_of_word; auto | unfold word_ok in *; lia ]. }
      forward. oddcase. bdone. unfold removes. rewrite Eo. reflexivity. }
    { forward. oddcase. bdone. unfold removes. rewrite Eo. reflexivity. }
    forward_if (PROP () LOCAL (temp _p (Vlong (Int64.repr p));
            temp _retained (Vlong (Int64.repr (retained_count inv (sublist 0 (p + 1) (pt src)))));
            temp _removed (Vlong (Int64.repr (removed_count inv (sublist 0 (p + 1) (pt src)))));
            temp _valid (Vint (Int.repr (b2z true))); temp _pages (Vlong (Int64.repr (pages_of w)));
            temp _n (Vlong (Int64.repr n)); temp _source_phys (Vlong (Int64.repr sp));
            temp _closed_phys (Vlong (Int64.repr kp)); lvar _built tint v_built; lvar _first (Tstruct _qotom_root_build_result noattr) v_first; lvar _w (Tstruct _frame_window noattr) v_w; lvar _kept (tarray tulong 4096) v_kept; lvar _frames (tarray tulong 16) v_frames; lvar _send (Tstruct _qotom_root_pages noattr) v_send; lvar _fetch (Tstruct _qotom_root_pages noattr) v_fetch; lvar _closed (Tstruct _qotom_root_pages noattr) v_closed; lvar _source (Tstruct _qotom_root_pages noattr) v_source; gvars gv)
     SEP (data_at Tsh t_root (longs (pml4 src), (longs (pdpt src), (longs (pd src), longs (pt src)))) v_source;
          data_at Tsh (tarray tulong (Zlength fl)) (longs fl) v_frames;
          data_at Tsh tint (Vint (Int.repr built)) v_built; data_at Tsh t_result (counts_val fr) v_first; F)).
    { b2z_hyps.
      match goal with H: removes _ _ = true |- _ => rename H into Hrm end.
      forward. rewrite removed_snoc, retained_snoc by lia. rewrite <- Es.
      rewrite Hrm, (ret_when_removed inv s Hrm), Z.add_0_r. entailer!. }
    { forward_if (PROP () LOCAL (temp _p (Vlong (Int64.repr p));
            temp _retained (Vlong (Int64.repr (retained_count inv (sublist 0 (p + 1) (pt src)))));
            temp _removed (Vlong (Int64.repr (removed_count inv (sublist 0 (p + 1) (pt src)))));
            temp _valid (Vint (Int.repr (b2z true))); temp _pages (Vlong (Int64.repr (pages_of w)));
            temp _n (Vlong (Int64.repr n)); temp _source_phys (Vlong (Int64.repr sp));
            temp _closed_phys (Vlong (Int64.repr kp)); lvar _built tint v_built; lvar _first (Tstruct _qotom_root_build_result noattr) v_first; lvar _w (Tstruct _frame_window noattr) v_w; lvar _kept (tarray tulong 4096) v_kept; lvar _frames (tarray tulong 16) v_frames; lvar _send (Tstruct _qotom_root_pages noattr) v_send; lvar _fetch (Tstruct _qotom_root_pages noattr) v_fetch; lvar _closed (Tstruct _qotom_root_pages noattr) v_closed; lvar _source (Tstruct _qotom_root_pages noattr) v_source; gvars gv)
     SEP (data_at Tsh t_root (longs (pml4 src), (longs (pdpt src), (longs (pd src), longs (pt src)))) v_source;
          data_at Tsh (tarray tulong (Zlength fl)) (longs fl) v_frames;
          data_at Tsh tint (Vint (Int.repr built)) v_built; data_at Tsh t_result (counts_val fr) v_first; F)).
      { b2z_hyps.
        match goal with H: removes _ _ = false |- _ => rename H into Hrf end.
        oddcase. forward. rewrite removed_snoc, retained_snoc by lia. rewrite <- Es.
        rewrite Hrf, (ret_when_kept_odd inv s Hrf Eo), Z.add_0_r. entailer!. }
      { b2z_hyps.
        match goal with H: removes _ _ = false |- _ => rename H into Hrf end.
        oddcase. forward. rewrite removed_snoc, retained_snoc by lia. rewrite <- Es.
        destruct (ret_when_even inv s Eo) as [E1 E2]. rewrite E1, E2, !Z.add_0_r. entailer!. } } }
  rewrite !sublist_same by (unfold LEAVES in *; lia).
  assert (R1 := removed_le inv (pt src)). assert (R2 := retained_le inv (pt src)).
  unfold LEAVES in *. rewrite Lt in R1, R2.
  destruct Hfr as (Wc0 & Wc1 & Wc2 & Wc3).
  forward.
  forward_if (temp _t'48 (Vint (Int.repr (b2z (negb (counts_ok src inv n built fr)))))).
  { assert (Hb0: built <> 0) by (intro; subst; auto).
    unfold counts_val, result_val.
    forward.
    forward_if (temp _t'49 (Vint (Int.repr (b2z (negb ((c_protected fr =? n) && (c_removed fr =? removed_count inv (pt src)))))))).
    { forward. bdone. match goal with Hc: Int64.repr _ <> Int64.repr _ |- _ => apply repr64_neq in Hc;
        rewrite (proj2 (Z.eqb_neq _ _) Hc) end. reflexivity. }
    { forward. forward. bdone.
      try match goal with Hc: Int64.eq _ _ = true |- _ => apply Int64.same_if_eq in Hc end.
      match goal with Hc: Int64.repr _ = Int64.repr _ |- _ =>
        apply repr64_inj in Hc; [ rewrite (proj2 (Z.eqb_eq _ _) Hc) | auto | auto ] end.
      rewrite cmpu_ne64, eq64_w; [ reflexivity | .. ]; unfold word_ok in *; rep_lia. }
    forward_if (temp _t'48 (Vint (Int.repr (b2z (negb (counts_ok src inv n built fr)))))).
    { forward. bdone. rewrite counts_ok_nz by auto.
      negb_hyps. match goal with Hc: (_ && _) = false |- _ => rewrite Hc end. reflexivity. }
    { forward. forward. forward. bdone. rewrite counts_ok_nz by auto.
      negb_hyps. match goal with Hc: (_ && _) = true |- _ => rewrite Hc end.
      rewrite cmpu_ne64, eq64_w; [ reflexivity | .. ]; unfold word_ok in *; rep_lia. }
    all: try entailer!. }
  { forward. bdone;
    try (match goal with Hc: Int.repr built = _ |- _ => unfold Int.zero in Hc; apply int_repr_zero in Hc; [ subst built | auto ] end;
         reflexivity). }
  forward_if.
  { forward. entailer!; b2z_hyps; negb_hyps;
    try (match goal with Hc: counts_ok _ _ _ _ _ = false |- _ => rewrite Hc end; reflexivity). }
  { forward. entailer!; b2z_hyps; negb_hyps;
    try (match goal with Hc: counts_ok _ _ _ _ _ = true |- _ => rewrite Hc end; reflexivity). }
Qed.
