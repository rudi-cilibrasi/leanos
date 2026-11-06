(* Law window_roots_isolated: main's fill loops (source's non-leaf tables, its leaves and kept, the
   inventory). *)
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

Lemma seg_loop1: forall {Espec: OracleKind} (gv: globals) (v_source v_closed v_fetch v_send v_frames v_kept v_w v_first v_built: val) (sp kp: Z) (F: mpred),
  semax Dm
    (PROP () LOCAL (temp _source_phys (Vlong (Int64.repr sp)); temp _closed_phys (Vlong (Int64.repr kp)); lvar _built tint v_built; lvar _first (Tstruct _qotom_root_build_result noattr) v_first; lvar _w (Tstruct _frame_window noattr) v_w; lvar _kept (tarray tulong 4096) v_kept; lvar _frames (tarray tulong 16) v_frames; lvar _send (Tstruct _qotom_root_pages noattr) v_send; lvar _fetch (Tstruct _qotom_root_pages noattr) v_fetch; lvar _closed (Tstruct _qotom_root_pages noattr) v_closed; lvar _source (Tstruct _qotom_root_pages noattr) v_source; gvars gv)
     SEP (data_at_ Tsh (Tstruct _qotom_root_pages noattr) v_source; F))
    s_loop1
    (normal_ret_assert (EX l1: list Z, EX l2: list Z, EX l3: list Z, (
      PROP (Zlength l1 = 512; Zlength l2 = 512; Zlength l3 = 512; words_ok l1; words_ok l2; words_ok l3)
      LOCAL (temp _source_phys (Vlong (Int64.repr sp)); temp _closed_phys (Vlong (Int64.repr kp)); lvar _built tint v_built; lvar _first (Tstruct _qotom_root_build_result noattr) v_first; lvar _w (Tstruct _frame_window noattr) v_w; lvar _kept (tarray tulong 4096) v_kept; lvar _frames (tarray tulong 16) v_frames; lvar _send (Tstruct _qotom_root_pages noattr) v_send; lvar _fetch (Tstruct _qotom_root_pages noattr) v_fetch; lvar _closed (Tstruct _qotom_root_pages noattr) v_closed; lvar _source (Tstruct _qotom_root_pages noattr) v_source; gvars gv)
      SEP (@field_at CS Tsh (Tstruct _qotom_root_pages noattr) (DOT _pml4) (longs l1) v_source; @field_at CS Tsh (Tstruct _qotom_root_pages noattr) (DOT _pdpt) (longs l2) v_source;
           @field_at CS Tsh (Tstruct _qotom_root_pages noattr) (DOT _pd) (longs l3) v_source; @field_at_ CS Tsh (Tstruct _qotom_root_pages noattr) (DOT _pt) v_source; F)
      : environ -> mpred))).
Proof.
  intros. unfold s_loop1, Dm. simplify_func_tycontext. abbreviate_semax.
  rewrite data_at__eq. unfold_data_at (data_at _ _ _ v_source).
  freeze FR := F (field_at _ _ (DOT LeanosRoots.roots.code._pt) _ _).
  forward_for_simple_bound 512
    (EX i: Z, EX l1: list Z, EX l2: list Z, EX l3: list Z, (
     PROP (Zlength l1 = i; Zlength l2 = i; Zlength l3 = i; words_ok l1; words_ok l2; words_ok l3)
     LOCAL (temp _source_phys (Vlong (Int64.repr sp)); temp _closed_phys (Vlong (Int64.repr kp)); lvar _built tint v_built; lvar _first (Tstruct _qotom_root_build_result noattr) v_first; lvar _w (Tstruct _frame_window noattr) v_w; lvar _kept (tarray tulong 4096) v_kept; lvar _frames (tarray tulong 16) v_frames; lvar _send (Tstruct _qotom_root_pages noattr) v_send; lvar _fetch (Tstruct _qotom_root_pages noattr) v_fetch; lvar _closed (Tstruct _qotom_root_pages noattr) v_closed; lvar _source (Tstruct _qotom_root_pages noattr) v_source; gvars gv)
     SEP (@field_at CS Tsh (Tstruct _qotom_root_pages noattr) (DOT _pml4) (longs l1 ++ Zrepeat Vundef (512 - i)) v_source;
          @field_at CS Tsh (Tstruct _qotom_root_pages noattr) (DOT _pdpt) (longs l2 ++ Zrepeat Vundef (512 - i)) v_source;
          @field_at CS Tsh (Tstruct _qotom_root_pages noattr) (DOT _pd) (longs l3 ++ Zrepeat Vundef (512 - i)) v_source; FRZL FR)
     : environ -> mpred)).
  { Exists (@nil Z) (@nil Z) (@nil Z). entailer!. repeat split; constructor. }
  { forward_call. Intros x1. forward.
    forward_call. Intros x2. forward.
    forward_call. Intros x3. forward.
    Exists (l1 ++ [x1]) (l2 ++ [x2]) (l3 ++ [x3]). rewrite !longs_app1.
    assert (Ls: forall (l: list Z) x, Zlength l = i ->
      upd_Znth i (longs l ++ Zrepeat Vundef (512 - i)) (Vlong (Int64.repr x)) =
      (longs l ++ [Vlong (Int64.repr x)]) ++ Zrepeat Vundef (512 - (i + 1))).
    { intros l x Hl. unfold longs. list_solve. }
    rewrite !Ls by auto.
    assert (words_ok (l1 ++ [x1]) /\ words_ok (l2 ++ [x2]) /\ words_ok (l3 ++ [x3])) as (?&?&?)
      by (repeat split; apply words_app1; auto).
    assert (Zlength (l1 ++ [x1]) = i + 1 /\ Zlength (l2 ++ [x2]) = i + 1 /\ Zlength (l3 ++ [x3]) = i + 1) as (?&?&?)
      by (rewrite !Zlength_app, !Zlength_cons, !Zlength_nil; lia).
    entailer!. }
  Intros l1 l2 l3. Exists l1 l2 l3.
  change (Zrepeat Vundef (512 - 512)) with (@nil val). rewrite !app_nil_r.
  thaw FR. entailer!.
Qed.


Lemma seg_loop2: forall {Espec: OracleKind} (gv: globals) (v_source v_closed v_fetch v_send v_frames v_kept v_w v_first v_built: val) (sp kp: Z) (F: mpred),
  semax Dm
    (PROP () LOCAL (temp _source_phys (Vlong (Int64.repr sp)); temp _closed_phys (Vlong (Int64.repr kp)); lvar _built tint v_built; lvar _first (Tstruct _qotom_root_build_result noattr) v_first; lvar _w (Tstruct _frame_window noattr) v_w; lvar _kept (tarray tulong 4096) v_kept; lvar _frames (tarray tulong 16) v_frames; lvar _send (Tstruct _qotom_root_pages noattr) v_send; lvar _fetch (Tstruct _qotom_root_pages noattr) v_fetch; lvar _closed (Tstruct _qotom_root_pages noattr) v_closed; lvar _source (Tstruct _qotom_root_pages noattr) v_source; gvars gv)
     SEP (@field_at_ CS Tsh (Tstruct _qotom_root_pages noattr) (DOT _pt) v_source; data_at_ Tsh (tarray tulong 4096) v_kept; F))
    s_loop2
    (normal_ret_assert (EX l4: list Z, (
      PROP (Zlength l4 = 4096; words_ok l4)
      LOCAL (temp _source_phys (Vlong (Int64.repr sp)); temp _closed_phys (Vlong (Int64.repr kp)); lvar _built tint v_built; lvar _first (Tstruct _qotom_root_build_result noattr) v_first; lvar _w (Tstruct _frame_window noattr) v_w; lvar _kept (tarray tulong 4096) v_kept; lvar _frames (tarray tulong 16) v_frames; lvar _send (Tstruct _qotom_root_pages noattr) v_send; lvar _fetch (Tstruct _qotom_root_pages noattr) v_fetch; lvar _closed (Tstruct _qotom_root_pages noattr) v_closed; lvar _source (Tstruct _qotom_root_pages noattr) v_source; gvars gv)
      SEP (@field_at CS Tsh (Tstruct _qotom_root_pages noattr) (DOT _pt) (longs l4) v_source; data_at Tsh (tarray tulong 4096) (longs l4) v_kept; F)
      : environ -> mpred))).
Proof.
  intros. unfold s_loop2, Dm. simplify_func_tycontext. abbreviate_semax.
  unfold field_at_. rewrite data_at__eq.
  freeze FR := F.
  forward_for_simple_bound 4096
    (EX i: Z, EX l4: list Z, (
     PROP (Zlength l4 = i; words_ok l4)
     LOCAL (temp _source_phys (Vlong (Int64.repr sp)); temp _closed_phys (Vlong (Int64.repr kp)); lvar _built tint v_built; lvar _first (Tstruct _qotom_root_build_result noattr) v_first; lvar _w (Tstruct _frame_window noattr) v_w; lvar _kept (tarray tulong 4096) v_kept; lvar _frames (tarray tulong 16) v_frames; lvar _send (Tstruct _qotom_root_pages noattr) v_send; lvar _fetch (Tstruct _qotom_root_pages noattr) v_fetch; lvar _closed (Tstruct _qotom_root_pages noattr) v_closed; lvar _source (Tstruct _qotom_root_pages noattr) v_source; gvars gv)
     SEP (@field_at CS Tsh (Tstruct _qotom_root_pages noattr) (DOT _pt) (longs l4 ++ Zrepeat Vundef (4096 - i)) v_source;
          data_at Tsh (tarray tulong 4096) (longs l4 ++ Zrepeat Vundef (4096 - i)) v_kept; FRZL FR)
     : environ -> mpred)).
  { Exists (@nil Z). entailer!. constructor. }
  { forward_call. Intros x. forward.
    assert (Ls: forall (l: list Z) y, Zlength l = i ->
      upd_Znth i (longs l ++ Zrepeat Vundef (4096 - i)) (Vlong (Int64.repr y)) =
      (longs l ++ [Vlong (Int64.repr y)]) ++ Zrepeat Vundef (4096 - (i + 1))).
    { intros l y Hl. unfold longs. list_solve. }
    rewrite Ls by auto.
    assert (Ez: forall d, @Znth val d i ((longs l4 ++ [Vlong (Int64.repr x)]) ++ Zrepeat Vundef (4096 - (i + 1))) =
                Vlong (Int64.repr x)) by (intros d; unfold longs; list_solve).
    forward.
    { rewrite Ez. entailer!. }
    rewrite Ez. forward.
    rewrite Ls by auto.
    Exists (l4 ++ [x]). rewrite longs_app1.
    assert (words_ok (l4 ++ [x])) by (apply words_app1; auto).
    assert (Zlength (l4 ++ [x]) = i + 1) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    entailer!. }
  Intros l4. Exists l4.
  change (Zrepeat Vundef (4096 - 4096)) with (@nil val). rewrite !app_nil_r.
  thaw FR. entailer!.
Qed.

Lemma seg_loop3: forall {Espec: OracleKind} (gv: globals) (v_source v_closed v_fetch v_send v_frames v_kept v_w v_first v_built: val) (sp kp n: Z) (F: mpred),
  semax Dm
    (PROP () LOCAL (temp _n (Vlong (Int64.repr n)); temp _source_phys (Vlong (Int64.repr sp));
                    temp _closed_phys (Vlong (Int64.repr kp)); lvar _built tint v_built; lvar _first (Tstruct _qotom_root_build_result noattr) v_first; lvar _w (Tstruct _frame_window noattr) v_w; lvar _kept (tarray tulong 4096) v_kept; lvar _frames (tarray tulong 16) v_frames; lvar _send (Tstruct _qotom_root_pages noattr) v_send; lvar _fetch (Tstruct _qotom_root_pages noattr) v_fetch; lvar _closed (Tstruct _qotom_root_pages noattr) v_closed; lvar _source (Tstruct _qotom_root_pages noattr) v_source; gvars gv)
     SEP (data_at_ Tsh (tarray tulong 16) v_frames; F))
    s_loop3
    (normal_ret_assert (EX fl: list Z, (
      PROP (Zlength fl = 16; words_ok fl)
      LOCAL (temp _n (Vlong (Int64.repr n)); temp _source_phys (Vlong (Int64.repr sp));
             temp _closed_phys (Vlong (Int64.repr kp)); lvar _built tint v_built; lvar _first (Tstruct _qotom_root_build_result noattr) v_first; lvar _w (Tstruct _frame_window noattr) v_w; lvar _kept (tarray tulong 4096) v_kept; lvar _frames (tarray tulong 16) v_frames; lvar _send (Tstruct _qotom_root_pages noattr) v_send; lvar _fetch (Tstruct _qotom_root_pages noattr) v_fetch; lvar _closed (Tstruct _qotom_root_pages noattr) v_closed; lvar _source (Tstruct _qotom_root_pages noattr) v_source; gvars gv)
      SEP (data_at Tsh (tarray tulong 16) (longs fl) v_frames; F)
      : environ -> mpred))).
Proof.
  intros. unfold s_loop3, Dm. simplify_func_tycontext. abbreviate_semax.
  rewrite data_at__eq.
  freeze FR := F.
  forward_for_simple_bound 16
    (EX i: Z, EX fl: list Z, (
     PROP (Zlength fl = i; words_ok fl)
     LOCAL (temp _n (Vlong (Int64.repr n)); temp _source_phys (Vlong (Int64.repr sp));
            temp _closed_phys (Vlong (Int64.repr kp)); lvar _built tint v_built; lvar _first (Tstruct _qotom_root_build_result noattr) v_first; lvar _w (Tstruct _frame_window noattr) v_w; lvar _kept (tarray tulong 4096) v_kept; lvar _frames (tarray tulong 16) v_frames; lvar _send (Tstruct _qotom_root_pages noattr) v_send; lvar _fetch (Tstruct _qotom_root_pages noattr) v_fetch; lvar _closed (Tstruct _qotom_root_pages noattr) v_closed; lvar _source (Tstruct _qotom_root_pages noattr) v_source; gvars gv)
     SEP (data_at Tsh (tarray tulong 16) (longs fl ++ Zrepeat Vundef (16 - i)) v_frames; FRZL FR)
     : environ -> mpred)).
  { Exists (@nil Z). entailer!. constructor. }
  { forward_call. Intros x. forward.
    Exists (fl ++ [x]). rewrite longs_app1.
    assert (Ls: upd_Znth i (longs fl ++ Zrepeat Vundef (16 - i)) (Vlong (Int64.repr x)) =
      (longs fl ++ [Vlong (Int64.repr x)]) ++ Zrepeat Vundef (16 - (i + 1))) by (unfold longs; list_solve).
    rewrite Ls.
    assert (words_ok (fl ++ [x])) by (apply words_app1; auto).
    assert (Zlength (fl ++ [x]) = i + 1) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    entailer!. }
  Intros fl. Exists fl.
  change (Zrepeat Vundef (16 - 16)) with (@nil val). rewrite !app_nil_r.
  thaw FR. entailer!.
Qed.

