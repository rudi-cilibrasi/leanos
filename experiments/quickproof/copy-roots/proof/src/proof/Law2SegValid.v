(* Law window_roots_isolated: main's restatement of the first thirteen conjuncts of valid. *)
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

Ltac side := try first [ assumption | (unfold window_wf, word_ok in *; rep_lia) | (unfold window_wf, word_ok in *; tauto) ].
Ltac chain_then := bdone; match goal with H: ?X = true |- (?X && _) = _ => rewrite H; reflexivity end.
Ltac chain_else := bdone; match goal with H: ?X = false |- (?X && _) = _ => rewrite H; reflexivity end.

Lemma seg_valid: forall {Espec: OracleKind} (gv: globals) (v_source v_closed v_fetch v_send v_frames v_kept v_w v_first v_built: val) (src: root) (sp kp n: Z) (fl: list Z) (w: window) (F: mpred),
  root_ok src -> word_ok sp -> word_ok kp -> word_ok n -> Zlength fl = 16 -> words_ok fl -> window_wf w ->
  semax Dm
    (PROP () LOCAL (temp _n (Vlong (Int64.repr n)); temp _source_phys (Vlong (Int64.repr sp));
                    temp _closed_phys (Vlong (Int64.repr kp)); lvar _built tint v_built; lvar _first (Tstruct _qotom_root_build_result noattr) v_first; lvar _w (Tstruct _frame_window noattr) v_w; lvar _kept (tarray tulong 4096) v_kept; lvar _frames (tarray tulong 16) v_frames; lvar _send (Tstruct _qotom_root_pages noattr) v_send; lvar _fetch (Tstruct _qotom_root_pages noattr) v_fetch; lvar _closed (Tstruct _qotom_root_pages noattr) v_closed; lvar _source (Tstruct _qotom_root_pages noattr) v_source; gvars gv)
     SEP (data_at Tsh t_root (root_val src) v_source; data_at Tsh (tarray tulong (Zlength fl)) (longs fl) v_frames;
          data_at Tsh t_window (window_val v_fetch v_send w) v_w; F))
    s_valid
    (normal_ret_assert
     (PROP () LOCAL (temp _valid (Vint (Int.repr (b2z (pre_ok src sp kp fl n w))));
                     temp _n (Vlong (Int64.repr n)); temp _source_phys (Vlong (Int64.repr sp));
                     temp _closed_phys (Vlong (Int64.repr kp)); lvar _built tint v_built; lvar _first (Tstruct _qotom_root_build_result noattr) v_first; lvar _w (Tstruct _frame_window noattr) v_w; lvar _kept (tarray tulong 4096) v_kept; lvar _frames (tarray tulong 16) v_frames; lvar _send (Tstruct _qotom_root_pages noattr) v_send; lvar _fetch (Tstruct _qotom_root_pages noattr) v_fetch; lvar _closed (Tstruct _qotom_root_pages noattr) v_closed; lvar _source (Tstruct _qotom_root_pages noattr) v_source; gvars gv)
      SEP (data_at Tsh t_root (root_val src) v_source; data_at Tsh (tarray tulong (Zlength fl)) (longs fl) v_frames;
           data_at Tsh t_window (window_val v_fetch v_send w) v_w; F))).
Proof.
  intros. unfold s_valid, Dm. simplify_func_tycontext. abbreviate_semax.
  unfold window_val.
  forward_call sp. side.
  forward_if (temp _t'20 (Vint (Int.repr (b2z (phys_ok sp && phys_ok kp))))).
  { forward_call kp. all: side. forward. chain_then. }
  { forward. chain_else. }
  forward_if (temp _t'22 (Vint (Int.repr (b2z (phys_ok sp && phys_ok kp && phys_ok (w_fetch_phys w)))))).
  { forward. forward_call (w_fetch_phys w). all: side. forward. chain_then. }
  { forward. chain_else. }
  forward_if (temp _t'24 (Vint (Int.repr (b2z (phys_ok sp && phys_ok kp && phys_ok (w_fetch_phys w) && phys_ok (w_send_phys w)))))).
  { forward. forward_call (w_send_phys w). all: side. forward. chain_then. }
  { forward. chain_else. }
  forward_if (temp _t'26 (Vint (Int.repr (b2z (phys_ok sp && phys_ok kp && phys_ok (w_fetch_phys w) && phys_ok (w_send_phys w) && apart sp kp))))).
  { forward_call (sp, kp). all: side. forward. chain_then. }
  { forward. chain_else. }
  forward_if (temp _t'28 (Vint (Int.repr (b2z (phys_ok sp && phys_ok kp && phys_ok (w_fetch_phys w) && phys_ok (w_send_phys w) && apart sp kp && apart sp (w_fetch_phys w)))))).
  { forward. forward_call (sp, w_fetch_phys w). all: side. forward. chain_then. }
  { forward. chain_else. }
  forward_if (temp _t'30 (Vint (Int.repr (b2z (phys_ok sp && phys_ok kp && phys_ok (w_fetch_phys w) && phys_ok (w_send_phys w) && apart sp kp && apart sp (w_fetch_phys w) && apart sp (w_send_phys w)))))).
  { forward. forward_call (sp, w_send_phys w). all: side. forward. chain_then. }
  { forward. chain_else. }
  forward_if (temp _t'32 (Vint (Int.repr (b2z (phys_ok sp && phys_ok kp && phys_ok (w_fetch_phys w) && phys_ok (w_send_phys w) && apart sp kp && apart sp (w_fetch_phys w) && apart sp (w_send_phys w) && apart kp (w_fetch_phys w)))))).
  { forward. forward_call (kp, w_fetch_phys w). all: side. forward. chain_then. }
  { forward. chain_else. }
  forward_if (temp _t'34 (Vint (Int.repr (b2z (phys_ok sp && phys_ok kp && phys_ok (w_fetch_phys w) && phys_ok (w_send_phys w) && apart sp kp && apart sp (w_fetch_phys w) && apart sp (w_send_phys w) && apart kp (w_fetch_phys w) && apart kp (w_send_phys w)))))).
  { forward. forward_call (kp, w_send_phys w). all: side. forward. chain_then. }
  { forward. chain_else. }
  forward_if (temp _t'36 (Vint (Int.repr (b2z (phys_ok sp && phys_ok kp && phys_ok (w_fetch_phys w) && phys_ok (w_send_phys w) && apart sp kp && apart sp (w_fetch_phys w) && apart sp (w_send_phys w) && apart kp (w_fetch_phys w) && apart kp (w_send_phys w) && apart (w_fetch_phys w) (w_send_phys w)))))).
  { forward. forward. forward_call (w_fetch_phys w, w_send_phys w). all: side. forward. chain_then. }
  { forward. chain_else. }
  forward_if (temp _t'38 (Vint (Int.repr (b2z (phys_ok sp && phys_ok kp && phys_ok (w_fetch_phys w) && phys_ok (w_send_phys w) && apart sp kp && apart sp (w_fetch_phys w) && apart sp (w_send_phys w) && apart kp (w_fetch_phys w) && apart kp (w_send_phys w) && apart (w_fetch_phys w) (w_send_phys w) && geometry_ok w))))).
  { forward. forward. forward. forward_call w. all: side. forward. chain_then. }
  { forward. chain_else. }
  forward_if (temp _t'40 (Vint (Int.repr (b2z (phys_ok sp && phys_ok kp && phys_ok (w_fetch_phys w) && phys_ok (w_send_phys w) && apart sp kp && apart sp (w_fetch_phys w) && apart sp (w_send_phys w) && apart kp (w_fetch_phys w) && apart kp (w_send_phys w) && apart (w_fetch_phys w) (w_send_phys w) && geometry_ok w && ancestors_ok src sp))))).
  { forward_call (v_source, Tsh, src, sp, 32). all: side. forward. chain_then. }
  { forward. chain_else. }
  forward_if (temp _t'42 (Vint (Int.repr (b2z (phys_ok sp && phys_ok kp && phys_ok (w_fetch_phys w) && phys_ok (w_send_phys w) && apart sp kp && apart sp (w_fetch_phys w) && apart sp (w_send_phys w) && apart kp (w_fetch_phys w) && apart kp (w_send_phys w) && apart (w_fetch_phys w) (w_send_phys w) && geometry_ok w && ancestors_ok src sp && inventory_ok fl n))))).
  { forward_call (v_frames, Tsh, fl, n). all: side. forward. chain_then. }
  { forward. chain_else. }
  forward.
  entailer!; try reflexivity.
Qed.
