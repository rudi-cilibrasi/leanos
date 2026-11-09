(* Law capabilities_adversarial: main after the call, when the walker returned ARGUMENT. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosCaps.harness.capabilities_adversarial.code.
Require Import LeanosCaps.proof.Defs.
Require LeanosCaps.proof.CapsSpecs.
Require Import LeanosCaps.proof.AdvProg LeanosCaps.proof.AdvWalk LeanosCaps.proof.AdvFacts LeanosCaps.proof.AdvSpecs
  LeanosCaps.proof.AdvLib LeanosCaps.proof.AdvMainDefs.
Local Open Scope Z_scope.

Lemma tail_arg {Espec: OracleKind} gv v_initial v_d v_snapshot v_result v_header_offsets v_masks
    bus dev fn ws cnt ro (rb ib sb qb: bool) (rest: list (reptype CapsSpecs.t_cap)):
  isptr v_snapshot -> isptr v_result -> isptr v_d ->
  0 <= ro <= Byte.max_unsigned -> 0 <= cnt <= Int.max_unsigned ->
  Zlength rest = 48 ->
  (rb || ib || sb || negb (args_ok dev fn ws))%bool = true ->
  forall Delta R c, Delta = Delta0 -> R = Post0 -> c = s_after_call ->
  semax Delta
    (PROP ()
     LOCAL (temp _status (Vint (Int.repr 1)); temp _invalid (Vint (Int.repr 1));
            temp _prior_count (Vint (Int.repr cnt));
            temp _result_arg (if qb then nullval else v_result);
            temp _snapshot_arg (if sb then nullval else v_snapshot);
            temp _result_offset (Vint (Int.repr ro));
            lvar _masks (tarray tuint 4) v_masks; lvar _header_offsets (tarray tuchar 4) v_header_offsets;
            lvar _result t_res v_result; lvar _snapshot t_snap v_snapshot; lvar _d t_device v_d;
            lvar _initial t_header v_initial; gvars gv)
     SEP (data_at Tsh t_header (hdr_val bus dev fn ws) v_initial;
          Dev_adv v_d (bus, dev, fn) nil;
          data_at Tsh CapsSpecs.t_snapshot
            (Vint (Int.repr (if sb then cnt else 0)), if sb then Zrepeat (Vundef, Vundef) 48 else rest) v_snapshot;
          data_at Tsh CapsSpecs.t_result
            (Vint (Int.repr (if qb then 0 else 1)), Vint (Int.repr (if qb then ro else 0))) v_result;
          TT; data_at_ Tsh (tarray tuint 4) v_masks; data_at_ Tsh (tarray tuchar 4) v_header_offsets; has_ext tt))
    c R.
Proof.
  intros until c. intros -> -> ->.
  unfold s_after_call.
  start_tail.
  (* status in range *)
  forward_if (temp _t'22 (Vint Int.one)).
  { forward. entailer!. }
  { exfalso. match goal with N: _ |- _ => solve [ apply N; reflexivity | inv N ] end. }
  gp_call.
  (* the result record *)
  forward.
  forward_if (temp _offset (Vint (Int.repr (if qb then ro else 0)))).
  { tc_sel. }
  { match goal with E: (if _ then nullval else _) <> nullval |- _ => apply sel_ne_null in E end. subst qb.
    fw. gp_call. fw. all: try entailer!. }
  { match goal with E: (if _ then nullval else _) = nullval |- _ => apply sel_eq_null in E; [ | auto ] end. subst qb.
    fw. forward_if (temp _t'23 (Vint Int.one)).
    { fw. fw. all: try (entailer!; rewrite Int.eq_true; reflexivity). }
    { exfalso. match goal with N: _ |- _ => solve [ apply N; reflexivity ] end. }
    gp_call. all: try entailer!. }
  gp_call.
  (* the snapshot's count *)
  forward_if (temp _t'24 (Vint (Int.repr (if sb then cnt else 0)))).
  { tc_sel. }
  { match goal with E: (if _ then nullval else _) = nullval |- _ => apply sel_eq_null in E; [ | auto ] end. subst sb.
    forward. all: try entailer!. }
  { match goal with E: (if _ then nullval else _) <> nullval |- _ => apply sel_ne_null in E end. subst sb.
    forward_if (temp _t'24 (Vint (Int.repr 0))).
    { exfalso. match goal with N: _ |- _ => solve [ inv N ] end. }
    { forward. forward. all: try entailer!. }
    all: try entailer!. }
  fw.
  gp_call.
  (* status == 1 *)
  forward_if.
  { unfold Dev_adv. Intros offs oks vals. unfold dev_val. rewrite Zlength_nil.
    fw.
    forward_if (temp _t'25 (Vint Int.one)).
    { forward_if (temp _t'25 (Vint Int.one)).
      { tc_sel. }
      { forward. all: try entailer!. }
      { match goal with E: (if _ then nullval else _) <> nullval |- _ => apply sel_ne_null in E end. subst qb.
        forward. forward. all: try entailer!. }
      all: try entailer!. }
    { exfalso. match goal with N: _ |- _ => solve [ apply N; reflexivity ] end. }
    gp_call.
    free_locals v_initial v_d v_snapshot v_result.
    forward.
    Exists (Int.repr 0). entailer!. }
  { exfalso. match goal with N: _ |- _ => solve [ apply N; reflexivity ] end. }
Qed.
