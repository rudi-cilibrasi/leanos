(* Law window_roots_isolated: main's window-frame membership and zero-slot loop. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Import LeanosRoots.proof.Defs.
Require Import LeanosRoots.proof.RootsSpecs.
Require Import LeanosRoots.proof.Law2Model.
Require Import LeanosRoots.proof.Law2Helpers.
Require Import LeanosRoots.proof.Law2MainDefs.
Require LeanosRoots.roots.code.
Require Import LeanosRoots.harness.window_roots_isolated.code.
#[local] Existing Instance RootsSpecs.CS.
Local Open Scope bool_scope.

Lemma shr_add_val: forall b i, word_ok b -> 0 <= i -> Z.shiftr b 12 + i <= Int64.max_unsigned ->
  Int64.add (Int64.shru (Int64.repr b) (Int64.repr (Int.unsigned (Int.repr 12)))) (Int64.repr i) =
  Int64.repr (Z.shiftr b 12 + i).
Proof. intros. rewrite Int.unsigned_repr by rep_lia. rewrite shru64_repr by (auto; lia). apply add64_repr. Qed.

Lemma b2z_zero: forall b, Int.repr (b2z b) = Int.zero -> b = false.
Proof. intros b H. destruct b; [ exfalso; apply Int.one_not_zero; exact H | reflexivity ]. Qed.
Lemma b2z_nonzero: forall b, Int.repr (b2z b) <> Int.zero -> b = true.
Proof. intros b H. destruct b; [ reflexivity | exfalso; apply H; reflexivity ]. Qed.

Ltac b2z_hyps :=
  repeat match goal with
  | H: Int.repr (b2z _) = Int.zero |- _ => apply b2z_zero in H
  | H: Int.repr (b2z _) <> Int.zero |- _ => apply b2z_nonzero in H
  end.

Lemma seg_slots: forall {Espec: OracleKind} (gv: globals) (v_source v_closed v_fetch v_send v_frames v_kept v_w v_first v_built: val) (src: root) (sp kp n: Z) (fl: list Z) (w: window) (V0: bool)
    (F: mpred),
  root_ok src -> word_ok n -> Zlength fl = 16 -> words_ok fl -> window_wf w ->
  (V0 = true -> geometry_ok w = true /\ n <= 16) ->
  semax Dm
    (PROP () LOCAL (temp _valid (Vint (Int.repr (b2z V0))); temp _pages (Vlong (Int64.repr (pages_of w)));
                    temp _n (Vlong (Int64.repr n)); temp _source_phys (Vlong (Int64.repr sp));
                    temp _closed_phys (Vlong (Int64.repr kp)); lvar _built tint v_built; lvar _first (Tstruct _qotom_root_build_result noattr) v_first; lvar _w (Tstruct _frame_window noattr) v_w; lvar _kept (tarray tulong 4096) v_kept; lvar _frames (tarray tulong 16) v_frames; lvar _send (Tstruct _qotom_root_pages noattr) v_send; lvar _fetch (Tstruct _qotom_root_pages noattr) v_fetch; lvar _closed (Tstruct _qotom_root_pages noattr) v_closed; lvar _source (Tstruct _qotom_root_pages noattr) v_source; gvars gv)
     SEP (data_at Tsh t_root (root_val src) v_source; data_at Tsh (tarray tulong (Zlength fl)) (longs fl) v_frames;
          data_at Tsh t_window (window_val v_fetch v_send w) v_w; F))
    s_slots
    (normal_ret_assert
     (PROP () LOCAL (temp _valid (Vint (Int.repr (b2z (V0 && slots_ok src (sublist 0 n fl) w))));
                     temp _pages (Vlong (Int64.repr (pages_of w)));
                     temp _n (Vlong (Int64.repr n)); temp _source_phys (Vlong (Int64.repr sp));
                     temp _closed_phys (Vlong (Int64.repr kp)); lvar _built tint v_built; lvar _first (Tstruct _qotom_root_build_result noattr) v_first; lvar _w (Tstruct _frame_window noattr) v_w; lvar _kept (tarray tulong 4096) v_kept; lvar _frames (tarray tulong 16) v_frames; lvar _send (Tstruct _qotom_root_pages noattr) v_send; lvar _fetch (Tstruct _qotom_root_pages noattr) v_fetch; lvar _closed (Tstruct _qotom_root_pages noattr) v_closed; lvar _source (Tstruct _qotom_root_pages noattr) v_source; gvars gv)
      SEP (data_at Tsh t_root (root_val src) v_source; data_at Tsh (tarray tulong (Zlength fl)) (longs fl) v_frames;
           data_at Tsh t_window (window_val v_fetch v_send w) v_w; F))).
Proof.
  intros until F. intros Hr Hn Hfl Wfl Hw HV.
  unfold s_slots, Dm. simplify_func_tycontext. abbreviate_semax.
  forward_if (temp _valid (Vint (Int.repr (b2z (V0 && slots_ok src (sublist 0 n fl) w))))).
  { destruct (HV H) as [Gw Hn16].
    destruct (geometry_facts w Hw Gw) as (Gm & Gb & Gl & Gp & Gpl & Gs & Gsp & Gf).
    assert (Sb: 0 <= Z.shiftr (w_base w) 12) by (apply Z.shiftr_nonneg; lia).
    destruct Hr as (Lm & Lp & Ld & Lt & Wm & Wp & Wd & Wt).
    rewrite H.
    forward_for_simple_bound (pages_of w)
      (EX i: Z, (PROP ()
       LOCAL (temp _valid (Vint (Int.repr (b2z (forallb (slot_ok src (sublist 0 n fl) w) (idx i)))));
              temp _pages (Vlong (Int64.repr (pages_of w)));
              temp _n (Vlong (Int64.repr n)); temp _source_phys (Vlong (Int64.repr sp));
              temp _closed_phys (Vlong (Int64.repr kp)); lvar _built tint v_built; lvar _first (Tstruct _qotom_root_build_result noattr) v_first; lvar _w (Tstruct _frame_window noattr) v_w; lvar _kept (tarray tulong 4096) v_kept; lvar _frames (tarray tulong 16) v_frames; lvar _send (Tstruct _qotom_root_pages noattr) v_send; lvar _fetch (Tstruct _qotom_root_pages noattr) v_fetch; lvar _closed (Tstruct _qotom_root_pages noattr) v_closed; lvar _source (Tstruct _qotom_root_pages noattr) v_source; gvars gv)
       SEP (data_at Tsh t_root (root_val src) v_source; data_at Tsh (tarray tulong (Zlength fl)) (longs fl) v_frames;
            data_at Tsh t_window (window_val v_fetch v_send w) v_w; F) : environ -> mpred)).
    { entailer!. }
    { unfold window_val. forward.
      forward_call (Z.shiftr (w_base w) 12 + i, v_frames, Tsh, fl, n).
      { entailer!. simpl. rewrite shr_add_val by (unfold window_wf, word_ok in *; rep_lia). reflexivity. }
      { unfold word_ok in *. split; rep_lia. }
      forward_if (temp _t'45 (Vint (Int.repr (b2z (negb (slot_ok src (sublist 0 n fl) w i)))))).
      { b2z_hyps. forward. entailer!. unfold slot_ok.
        match goal with Hm: member _ _ = false |- _ => rewrite Hm end. reflexivity. }
      { b2z_hyps. forward. unfold root_val.
        assert (Wsi := words_Znth (pt src) (w_slot w + i) Wt ltac:(unfold LEAVES in *; lia)).
        forward.
        all: try (entailer!; first [ (unfold LEAVES in *; lia)
                                   | (rewrite Znth_longs by (unfold LEAVES in *; lia); exact I) ]).
        rewrite Znth_longs by (unfold LEAVES in *; lia).
        forward. bdone. unfold slot_ok. match goal with Hm: member _ _ = true |- _ => rewrite Hm end.
        rewrite cmpu_ne64, eq64_w by (auto; unfold word_ok; rep_lia). reflexivity. }
      forward_if.
      { forward. entailer!. rewrite forallb_idx_snoc by lia.
        destruct (slot_ok src (sublist 0 n fl) w i); [ discriminate | ]. rewrite andb_false_r. reflexivity. }
      { forward. entailer!. rewrite forallb_idx_snoc by lia.
        destruct (slot_ok src (sublist 0 n fl) w i); [ | discriminate ]. rewrite andb_true_r. reflexivity. } }
    entailer!; unfold slots_ok; rewrite H; reflexivity. }
  { forward. rewrite H. entailer!. }
Qed.
