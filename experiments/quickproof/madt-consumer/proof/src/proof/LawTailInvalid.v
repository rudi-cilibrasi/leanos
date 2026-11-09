(* Law consumer_obligations: main's checks after a call of madt_bind with invalid arguments: the input-bounds
   rejection, and the oracle main kept (never called). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosMadt.harness.consumer_obligations.code.
Require Import LeanosMadt.proof.Defs.
Require Import LeanosMadt.proof.MadtSpecs.
Require Import LeanosMadt.proof.LawProg LeanosMadt.proof.LawDefs LeanosMadt.proof.LawFacts LeanosMadt.proof.LawLib
  LeanosMadt.proof.LawSplit LeanosMadt.proof.LawMainLib LeanosMadt.proof.LawMainDefs.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Ltac ptr_tc := entailer!; apply sel_tc_test; [ entailer! | auto ].
Ltac ptr_val := rewrite ?sel_cmp_ne, ?sel_cmp_eq by auto;
  repeat match goal with b: bool |- _ => destruct b end; cbn [negb andb orb Z.b2z] in *;
  try discriminate; try reflexivity.

(* Free main's locals before it returns. *)
Ltac free_locals := sep_apply (data_at_data_at_ Tsh t_result); sep_apply (data_at_data_at_ Tsh t_obs).

Lemma span_valid_ptr: forall sh k (vs: list val) q, readable_share sh -> 0 < k ->
  data_at sh (tarray tuchar k) vs q |-- valid_pointer q.
Proof. intros. apply data_at_valid_ptr; [ apply readable_nonidentity; auto | simpl; lia ]. Qed.

Lemma tail_invalid {Espec: OracleKind} gv q v_out v_observation n ob s (eb obb qb: bool) k (vs: list val):
  isptr q -> isptr v_out -> isptr v_observation -> 0 < k ->
  (qb || eb || obb || negb (length_ok n))%bool = true -> os_byte s = 0 -> os_word s = 0 ->
  forall Delta R c, Delta = Delta0 -> R = Post0 -> c = s_after_call ->
  semax Delta
    (PROP ()
     LOCAL (temp _status (vl 1); temp _out_arg (sel qb v_out); temp _observation_arg (sel obb v_observation);
            temp _entries_arg (sel eb q); temp _valid_length (Vint (Int.repr (Z.b2z (length_ok n))));
            temp _o (gv _oracle); lvar _out t_result v_out; lvar _observation t_obs v_observation; gvars gv)
     SEP (ofields (gv _oracle) q n ob s;
          @data_at LCS Tsh t_result (if qb then (vl 7, (vl 7, (vl 7, (vl 7, (vl 7, vl 7))))) else result_val (reject 1 0 44))
            v_out;
          @data_at LCS Tsh t_obs (obs_val ob) v_observation; data_at sh1 (tarray tuchar k) vs q; TT))
    c R.
Proof.
  intros Pq Po Pob Hk Inv Hb Hw Delta R c -> -> ->.
  unfold s_after_call. start_tail.
  unfold ofields. rewrite Hb, Hw. Intros.
  destruct qb.
  - (* no result record *)
    forward_if (PROP (False) LOCAL () SEP ()).
    { if1. if1. gp.
      free_locals. forward. Exists (Int.repr 0). entailer!. }
    { else_false. }
  - (* a result record *)
    match goal with |- semax _ ?Pre _ _ => forward_if Pre end.
    { exfalso. unfold sel in *. subst v_out. contradiction. }
    { forward. entailer!. }
    unfold result_val, reject. cbv beta iota.
    forward. if1. gp.
    forward_if (temp _t'35 (Vint (Int.repr (Z.b2z (eb || obb)%bool)))).
    { apply sel_tc_test; [ | auto ]. entailer!.
      sep_apply (span_valid_ptr sh1 (Zlength vs) vs q sh1_readable Hk). entailer!. }
    { apply sel_eq_null in H; [ subst eb | auto ]. forward. entailer!. }
    { apply sel_ne_null in H. subst eb. forward; [ entailer!; apply sel_tc_test; [ entailer! | auto ] | ].
      entailer!. ptr_val. }
    forward_if (temp _t'36 (Vint Int.one)).
    { forward. entailer!. }
    { try b2z_hyp. apply orb_false_iff in H as [E1 E2]. subst eb obb. cbn in Inv. apply negb_true_iff in Inv.
      forward. entailer!. rewrite Inv. reflexivity. }
    forward_if (PROP (False) LOCAL () SEP ()).
    { if1. if1. if1. if1. gp. if1. if1. gp.
      free_locals. forward. Exists (Int.repr 0). entailer!. }
    { else_false. }
Qed.
