(* Law window_roots_isolated: main's per-page assertions on the built roots. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Import LeanosRoots.proof.Defs.
Require Import LeanosRoots.proof.RootsSpecs.
Require Import LeanosRoots.proof.Law2Model.
Require Import LeanosRoots.proof.Law2Helpers.
Require Import LeanosRoots.proof.Law2MainDefs.
Require Import LeanosRoots.proof.Law2SegSlots.
Require Import LeanosRoots.proof.Law2SegCounts.
Require LeanosRoots.roots.code.
Require Import LeanosRoots.harness.window_roots_isolated.code.
#[local] Existing Instance RootsSpecs.CS.
Local Open Scope bool_scope.

Lemma alias_int: forall b sl p, word_ok b -> word_ok sl -> sl <= p < 4096 -> Z.shiftr b 12 + (p - sl) <= 4097 ->
  Int64.or (Int64.or (Int64.shl (Int64.add (Int64.shru (Int64.repr b) (Int64.repr (Int.unsigned (Int.repr 12))))
                                            (Int64.sub (Int64.repr p) (Int64.repr sl)))
                                (Int64.repr (Int.unsigned (Int.repr 12))))
                     (Int64.repr 1)) (Int64.shl (Int64.repr 1) (Int64.repr (Int.unsigned (Int.repr 63)))) =
  Int64.repr (Z.lor (Z.lor ((Z.shiftr b 12 + (p - sl)) * 4096) 1) NX).
Proof.
  intros b sl p Hb Hs Hp Hf. rewrite !Int.unsigned_repr by rep_lia.
  rewrite shru64_repr by (auto; lia). rewrite sub64_repr, add64_repr, !shl64_repr by lia.
  rewrite !or64_repr. reflexivity.
Qed.

Definition final_inv (gv: globals) (v_source v_closed v_fetch v_send v_frames v_kept v_w v_first v_built: val) (src: root) (sp kp n rm rt: Z) (fl: list Z) (w: window) (F: mpred) : environ -> mpred :=
  PROP ()
  LOCAL (temp _retained (Vlong (Int64.repr rt)); temp _removed (Vlong (Int64.repr rm));
         temp _pages (Vlong (Int64.repr (pages_of w))); temp _n (Vlong (Int64.repr n));
         temp _source_phys (Vlong (Int64.repr sp)); temp _closed_phys (Vlong (Int64.repr kp)); lvar _built tint v_built; lvar _first (Tstruct _qotom_root_build_result noattr) v_first; lvar _w (Tstruct _frame_window noattr) v_w; lvar _kept (tarray tulong 4096) v_kept; lvar _frames (tarray tulong 16) v_frames; lvar _send (Tstruct _qotom_root_pages noattr) v_send; lvar _fetch (Tstruct _qotom_root_pages noattr) v_fetch; lvar _closed (Tstruct _qotom_root_pages noattr) v_closed; lvar _source (Tstruct _qotom_root_pages noattr) v_source; gvars gv)
  SEP (data_at Tsh t_root (root_val src) v_source; data_at Tsh (tarray tulong 4096) (longs (pt src)) v_kept;
       data_at Tsh t_root (root_val (closed_out src (sublist 0 n fl) kp)) v_closed;
       data_at Tsh t_root (root_val (copy_out src (sublist 0 n fl) (window_aliases w 1) (w_fetch_phys w))) v_fetch;
       data_at Tsh t_root (root_val (copy_out src (sublist 0 n fl) (window_aliases w 0) (w_send_phys w))) v_send;
       data_at Tsh (tarray tulong (Zlength fl)) (longs fl) v_frames;
       data_at Tsh t_window (window_val v_fetch v_send w) v_w; F).

Ltac uns64 :=
  repeat match goal with Hc: context [Int64.unsigned (Int64.repr ?a)] |- _ =>
    rewrite (Int64.unsigned_repr a) in Hc by (unfold window_wf, word_ok in *; rep_lia) end.

Lemma seg_final: forall {Espec: OracleKind} (gv: globals) (v_source v_closed v_fetch v_send v_frames v_kept v_w v_first v_built: val) (src: root) (sp kp n rm rt: Z) (fl: list Z) (w: window) (F: mpred),
  root_ok src -> window_wf w -> geometry_ok w = true -> Zlength fl = 16 -> words_ok fl -> 0 <= n <= 16 ->
  semax Dm (final_inv gv v_source v_closed v_fetch v_send v_frames v_kept v_w v_first v_built src sp kp n rm rt fl w F) s_final
    (normal_ret_assert (final_inv gv v_source v_closed v_fetch v_send v_frames v_kept v_w v_first v_built src sp kp n rm rt fl w F)).
Proof.
  intros until F. intros Hr Hw G Hfl Wfl Hn.
  unfold final_inv, s_final, Dm. simplify_func_tycontext. abbreviate_semax.
  pose proof (closed_out_ok src (sublist 0 n fl) kp Hr) as Hk.
  pose proof (copy_out_ok src (sublist 0 n fl) (window_aliases w 1) (w_fetch_phys w) Hr) as Hf.
  pose proof (copy_out_ok src (sublist 0 n fl) (window_aliases w 0) (w_send_phys w) Hr) as Hs.
  destruct (geometry_facts w Hw G) as (Gm & Gb & Gl & Gp & Gpl & Gs & Gsp & Gf).
  forward_for_simple_bound 4096
    (EX p: Z, (PROP ()
  LOCAL (temp _retained (Vlong (Int64.repr rt)); temp _removed (Vlong (Int64.repr rm));
         temp _pages (Vlong (Int64.repr (pages_of w))); temp _n (Vlong (Int64.repr n));
         temp _source_phys (Vlong (Int64.repr sp)); temp _closed_phys (Vlong (Int64.repr kp)); lvar _built tint v_built; lvar _first (Tstruct _qotom_root_build_result noattr) v_first; lvar _w (Tstruct _frame_window noattr) v_w; lvar _kept (tarray tulong 4096) v_kept; lvar _frames (tarray tulong 16) v_frames; lvar _send (Tstruct _qotom_root_pages noattr) v_send; lvar _fetch (Tstruct _qotom_root_pages noattr) v_fetch; lvar _closed (Tstruct _qotom_root_pages noattr) v_closed; lvar _source (Tstruct _qotom_root_pages noattr) v_source; gvars gv)
  SEP (data_at Tsh t_root (root_val src) v_source; data_at Tsh (tarray tulong 4096) (longs (pt src)) v_kept;
       data_at Tsh t_root (root_val (closed_out src (sublist 0 n fl) kp)) v_closed;
       data_at Tsh t_root (root_val (copy_out src (sublist 0 n fl) (window_aliases w 1) (w_fetch_phys w))) v_fetch;
       data_at Tsh t_root (root_val (copy_out src (sublist 0 n fl) (window_aliases w 0) (w_send_phys w))) v_send;
       data_at Tsh (tarray tulong (Zlength fl)) (longs fl) v_frames;
       data_at Tsh t_window (window_val v_fetch v_send w) v_w; F) : environ -> mpred)).
  { entailer!. }
  { rename i into p.
    pose proof Hr as Hr0. destruct Hr0 as (Lm & Lp & Ld & Lt & Wm & Wp & Wd & Wt).
    destruct Hk as (Km & Kp & Kd & Kt & KWm & KWp & KWd & KWt).
    destruct Hf as (Fm & Fp & Fd & Ft & FWm & FWp & FWd & FWt).
    destruct Hs as (Sm & Sp & Sd & St & SWm & SWp & SWd & SWt).
    unfold LEAVES in *.
    assert (Ws := words_Znth (pt src) p Wt ltac:(lia)).
    unfold root_val, window_val.
    freeze FX := (data_at _ _ _ v_closed) (data_at _ _ _ v_fetch) (data_at _ _ _ v_send).
    forward.
    all: try (entailer!; first [ lia | (rewrite Znth_longs by lia; exact I) ]).
    rewrite Znth_longs by lia.
    freeze FY := (data_at _ _ _ v_source).
    forward.
    all: try (entailer!; first [ lia | (rewrite Znth_longs by lia; exact I) ]).
    rewrite Znth_longs by lia.
    thaw FY. thaw FX.
    forward_call (Int.one).
    { entailer!. rewrite Int64.eq_true. reflexivity. }
    remember (Znth p (pt src)) as s eqn:Es.
    forward_if (temp _t'54 (Vint (Int.repr (b2z (removes (sublist 0 n fl) s))))).
    { forward_call (frame_of s, v_frames, Tsh, fl, n).
      { entailer!. rewrite shru64_repr by (first [ apply w_land; auto | lia ]). reflexivity. }
      { repeat split; first [ apply frame_of_word; assumption | (unfold word_ok in *; rep_lia) ]. }
      forward. oddcase. bdone. unfold removes. rewrite Eo. reflexivity. }
    { forward. oddcase. bdone. unfold removes. rewrite Eo. reflexivity. }
    forward.
    forward_if (temp _t'56 (Vlong (Int64.repr (closed_leaf (sublist 0 n fl) s)))).
    { b2z_hyps. match goal with H: removes _ _ = true |- _ => rename H into Hrm end.
      forward. unfold closed_leaf. rewrite Hrm. entailer!. }
    { b2z_hyps. match goal with H: removes _ _ = false |- _ => rename H into Hrm end.
      forward. unfold closed_leaf. rewrite Hrm. entailer!. }
    forward.
    assert (Ck: Znth p (pt (closed_out src (sublist 0 n fl) kp)) = closed_leaf (sublist 0 n fl) s) by (rewrite closed_pt by lia; subst s; auto).
    assert (Wc := words_Znth _ p KWt ltac:(lia)).
    assert (Ezk: forall d, @Znth val d p (longs (pt (closed_out src (sublist 0 n fl) kp))) =
                           Vlong (Int64.repr (closed_leaf (sublist 0 n fl) s))).
    { intros d. unfold longs. rewrite Znth_map by lia. rewrite Ck. reflexivity. }
    freeze FX := (data_at _ _ _ v_source) (data_at _ _ _ v_fetch) (data_at _ _ _ v_send).
    forward.
    all: try rewrite Ezk.
    all: try solve [ entailer! | entailer!; lia ].
    thaw FX.
    forward_call (Int.one).
    { entailer!. rewrite Int64.eq_true. reflexivity. }
    forward.
    forward_if (temp _t'57 (Vint (Int.repr (b2z ((w_slot w <=? p) && (p <? w_slot w + pages_of w)))))).
    { uns64. forward. forward. bdone. rewrite cmpu_lt64, ltu64_w by (unfold window_wf, word_ok in *; rep_lia).
      rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
    { uns64. forward. bdone. rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity. }
    forward_if.
    { b2z_hyps. match goal with H: (_ && _) = true |- _ => rename H into Hin end.
      pose proof Hin as Hin'. apply andb_prop in Hin'. destruct Hin' as [Hi1 Hi2].
      apply Z.leb_le in Hi1. apply Z.ltb_lt in Hi2.
      forward. forward. forward.
      rewrite alias_int by (unfold window_wf, word_ok in *; lia).
      assert (Ezf: forall d, @Znth val d p (longs (pt (copy_out src (sublist 0 n fl) (window_aliases w 1) (w_fetch_phys w)))) =
        Vlong (Int64.repr (Z.lor (Z.lor (Z.lor ((Z.shiftr (w_base w) 12 + (p - w_slot w)) * 4096) 1) NX) 2))).
      { intros d. unfold longs. rewrite Znth_map by lia. rewrite copy_pt by (auto; unfold LEAVES; lia).
        rewrite Hin. rewrite alias_leaf_value by (auto; lia). reflexivity. }
      assert (Ezs: forall d, @Znth val d p (longs (pt (copy_out src (sublist 0 n fl) (window_aliases w 0) (w_send_phys w)))) =
        Vlong (Int64.repr (Z.lor (Z.lor ((Z.shiftr (w_base w) 12 + (p - w_slot w)) * 4096) 1) NX))).
      { intros d. unfold longs. rewrite Znth_map by lia. rewrite copy_pt by (auto; unfold LEAVES; lia).
        rewrite Hin. rewrite alias_leaf_value by (auto; lia). change (0 =? 0) with true. cbv iota.
        rewrite Z.lor_0_r. reflexivity. }
      freeze FX := (data_at _ _ _ v_source) (data_at _ _ _ v_closed) (data_at _ _ _ v_send).
      forward.
      all: try rewrite Ezf.
      all: try solve [ entailer! | entailer!; lia ].
      thaw FX.
      forward_call (Int.one).
      { entailer!. rewrite ?or64_repr. rewrite Int64.eq_true. reflexivity. }
      freeze FX := (data_at _ _ _ v_source) (data_at _ _ _ v_closed) (data_at _ _ _ v_fetch).
      forward.
      all: try rewrite Ezs.
      all: try solve [ entailer! | entailer!; lia ].
      thaw FX.
      forward_call (Int.one).
      { entailer!. rewrite Int64.eq_true. reflexivity. }
      entailer!. }
    { b2z_hyps. match goal with H: (_ && _) = false |- _ => rename H into Hin end.
      assert (Ezf: forall d, @Znth val d p (longs (pt (copy_out src (sublist 0 n fl) (window_aliases w 1) (w_fetch_phys w)))) =
                             Vlong (Int64.repr (closed_leaf (sublist 0 n fl) s))).
      { intros d. unfold longs. rewrite Znth_map by lia. rewrite copy_pt by (auto; unfold LEAVES; lia).
        rewrite Hin. subst s. reflexivity. }
      assert (Ezs: forall d, @Znth val d p (longs (pt (copy_out src (sublist 0 n fl) (window_aliases w 0) (w_send_phys w)))) =
                             Vlong (Int64.repr (closed_leaf (sublist 0 n fl) s))).
      { intros d. unfold longs. rewrite Znth_map by lia. rewrite copy_pt by (auto; unfold LEAVES; lia).
        rewrite Hin. subst s. reflexivity. }
      freeze FX := (data_at _ _ _ v_source) (data_at _ _ _ v_closed) (data_at _ _ _ v_send).
      forward.
      all: try rewrite Ezf.
      all: try solve [ entailer! | entailer!; lia ].
      thaw FX.
      forward_call (Int.one).
      { entailer!. rewrite Int64.eq_true. reflexivity. }
      freeze FX := (data_at _ _ _ v_source) (data_at _ _ _ v_closed) (data_at _ _ _ v_fetch).
      forward.
      all: try rewrite Ezs.
      all: try solve [ entailer! | entailer!; lia ].
      thaw FX.
      forward_call (Int.one).
      { entailer!. rewrite Int64.eq_true. reflexivity. }
      entailer!. } }
  entailer!.
Qed.
