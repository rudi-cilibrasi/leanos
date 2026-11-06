(* Law consumer_obligations: main's checks of the finish's bound after a valid call whose policy was accepted. *)
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

(* Freeze every SEP item but the oracle's fields named in L and main's result record. *)
Ltac keep_res x L :=
  lazymatch x with
  | field_at _ _ (StructField ?f :: nil) _ _ => lazymatch L with context [f] => constr:(true) | _ => constr:(false) end
  | data_at _ t_result _ _ => constr:(true)
  | _ => constr:(false)
  end.
Ltac idx_res R L i :=
  lazymatch R with
  | nil => constr:(@nil Z)
  | ?x :: ?R' =>
      let rest := idx_res R' L (Z.succ i) in
      let k := keep_res x L in
      lazymatch k with true => rest | false => let i' := eval cbn in i in constr:(i' :: rest) end
  end.
Ltac freeze_res L F :=
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
    let I := idx_res R L 0 in freeze_tac I F
  end.

Ltac else_false' :=
  first [ else_false
        | exfalso; match goal with E: Int.repr 1 = Int.zero |- _ => exact (Int.one_not_zero E) end ].

(* A value chosen by a boolean b the C computed: both cases, the impossible one by its branch condition. *)
Ltac if_b b :=
  destruct b;
  first [ reflexivity
        | exfalso; match goal with E: _ <> _ |- _ => apply E; reflexivity end
        | exfalso; match goal with E: Int64.repr _ = _ |- _ => vm_compute in E; discriminate E end ].

Ltac free_locals := sep_apply (data_at_data_at_ Tsh t_result); sep_apply (data_at_data_at_ Tsh t_obs).

(* The prefixes of main's tests of the bound. *)
Definition bac1 (b: list Z) : bool := (Znth 0 b =? 1) && (Znth 1 b =? 1).
Definition bac2 (ob: observation) (b: list Z) : bool := bac1 b && (Znth 2 b =? o_executing ob).
Definition bac3 (ob: observation) (st b: list Z) : bool := bac2 ob b && (Znth 3 b =? Znth 6 st).
Definition bac4 (ob: observation) (st b: list Z) : bool := bac3 ob st b && (Znth 4 b =? o_apic_base ob).
Definition fo1 (b: list Z) : bool := (Znth 0 b =? 1) && (Znth 5 b =? 0).
(* bool_fin for main's checks: the branch conditions as facts, then only the boolean facts reverted into the goal
   and the given definitions unfolded there (the large facts of the context stay folded). *)
Ltac bool_fin_loc U :=
  change Int64.zero with (Int64.repr 0) in *; change Int64.one with (Int64.repr 1) in *;
  uns64_hyps;
  repeat match goal with
  | E: Int64.repr _ = Int64.repr _ |- _ => apply repr64_inj in E; [ | rep_lia | rep_lia ]
  | E: Int64.repr _ <> Int64.repr _ |- _ => apply repr64_neq in E
  | E: Int.repr (Z.b2z ?b) <> Int.zero |- _ =>
      assert (b = true) by (destruct b; [ reflexivity | exfalso; apply E; reflexivity ]); clear E
  | E: Int.repr (Z.b2z ?b) = Int.zero |- _ =>
      assert (b = false) by (destruct b; [ exfalso; exact (Int.one_not_zero E) | reflexivity ]); clear E
  | E: context [Int64.eq (Int64.repr ?a) (Int64.repr ?b)] |- _ => rewrite (Int64_eq_repr a b) in E by rep_lia
  | E: context [Int64.ltu (Int64.repr ?a) (Int64.repr ?b)] |- _ => rewrite (Int64_ltu_repr a b) in E by rep_lia
  end;
  unfold bool2val, Int64.cmpu; cbv beta iota;
  repeat match goal with
  | E: ?b = true |- _ => match type of b with bool => revert E end
  | E: ?b = false |- _ => match type of b with bool => revert E end
  end;
  U;
  rewrite ?Int.unsigned_repr by rep_lia;
  repeat match goal with
  | |- context [Int64.eq (Int64.repr ?a) (Int64.repr ?b)] => rewrite (Int64_eq_repr a b) by rep_lia
  | |- context [Int64.ltu (Int64.repr ?a) (Int64.repr ?b)] => rewrite (Int64_ltu_repr a b) by rep_lia
  end;
  cmp_atoms;
  intros; try discriminate; try (exfalso; lia); try reflexivity.
Ltac bool_fin2 := bool_fin_loc ltac:(unfold bac4, bac3, bac2, bac1, fo1, bacc, four_b).

Lemma fa_bound: forall v q,
  field_at Ews t_oracle (DOT _bound) v q = data_at Ews (tarray tulong 6) v (field_address t_oracle (DOT _bound) q).
Proof. intros. rewrite field_at_data_at. reflexivity. Qed.

(* The statement of main after the policy's check. *)
Definition s_tv2 : statement := ltac:(
  let b := eval cbv delta [f_main] beta iota zeta in (fn_body f_main) in
  match b with
  | context [Ssequence (Ssequence ?c52 (Sifthenelse (Etempvar _t'52 tint) ?th Sskip)) ?rest] =>
      exact (Ssequence rest (Sreturn (Some (Econst_int (Int.repr 0) tint))))
  end).

Lemma tail_v2 {Espec: OracleKind} gv v_out v_observation bs ob s p stt d off a cc bb:
  isptr v_out -> isptr v_observation -> ost_ok s -> obs_ok ob ->
  main_ok (bs, ob) (stt, d, off, a, cc, bb) s -> os_rejected s = 0 -> walk_b bs = true ->
  pacc (os_policy s) = true ->
  forall Delta R c, Delta = Delta0 -> R = Post0 -> c = s_tv2 ->
  semax Delta
    (PROP ()
     LOCAL (temp _status (vl stt); temp _o (gv _oracle);
            lvar _out t_result v_out; lvar _observation t_obs v_observation; gvars gv)
     SEP (ofields (gv _oracle) p (Zlength bs) ob s;
          @data_at LCS Tsh t_result (vl stt, (vl d, (vl off, (vl a, (vl cc, vl bb))))) v_out;
          @data_at LCS Tsh t_obs (obs_val ob) v_observation; TT))
    c R.
Proof.
  intros Po Pob Hok Hob M R0 Wb Pa Delta R c -> -> ->.
  unfold s_tv2. start_tail.
  unfold main_ok in M. destruct M as (Mst & Mz & _ & Mok). destruct (Mok R0) as (Mb & Moff & _ & Mw).
  destruct (Mw Wb) as (Mph & _ & Mpa). destruct (Mpa Pa) as (Mwo & Mbt & Mbf).
  pose proof Hok as (Rph & Rby & Rwo & Rco & Rre & Lst & Lan & Lnm & Lpo & Lbo & Fst & Fan & Fnm & Fpo & Fbo).
  pose proof Hob as (Oe & Oc & Oa & Oab & Os & Or).
  unfold u64_ok in Rph, Rby, Rwo, Rco, Rre, Oe, Oc, Oa, Oab, Os, Or.
  rng_list (os_bound s) 6. rng_list (os_state s) 7.
  unfold ofields. rewrite Mph, Mwo. Intros.
  assert_PROP (headptr (gv _oracle)) as HO by entailer!.
  freeze_res [_phase; _word; _bound; _executing; _state; _apic_base] F1.
  (* phase 3, word 0 *)
  if1. gp. deadvars!.
  rewrite fa_bound, (fa_offset (gv _oracle) _bound HO ltac:(lnf)).
  change (nested_field_offset t_oracle (DOT _bound)) with 392.
  forward.
  set (bd := os_bound s) in *. set (st := os_state s) in *.
  forward.
  forward_if (temp _t'61 (Vint (Int.repr (Z.b2z (bac1 bd))))).
  { forward. forward. entailer!. bool_fin2. }
  { forward. entailer!. bool_fin2. }
  forward_if (temp _t'62 (Vint (Int.repr (Z.b2z (bac2 ob bd))))).
  { forward. forward. forward. entailer!. bool_fin2. }
  { forward. entailer!. bool_fin2. }
  forward_if (temp _t'63 (Vint (Int.repr (Z.b2z (bac3 ob st bd))))).
  { forward. forward. forward. entailer!. bool_fin2. }
  { forward. entailer!. bool_fin2. }
  forward_if (temp _t'64 (Vint (Int.repr (Z.b2z (bac4 ob st bd))))).
  { forward. forward. forward. entailer!. bool_fin2. }
  { forward. entailer!. bool_fin2. }
  forward_if (temp _t'65 (Vint (Int.repr (Z.b2z (bacc ob st bd))))).
  { forward. forward. entailer!. bool_fin2. }
  { forward. entailer!. bool_fin2. }
  destruct (bacc ob st bd) eqn:Ba.
  - (* the finish accepted: the bound published *)
    destruct (Mbt Ba) as (E0 & Ed & Ea & Ec & Eb). subst stt d a cc bb.
    forward_if (PROP (False) LOCAL () SEP ()).
    { if1. gp. if1. if1. gp.
      thaw F1. free_locals. forward. Exists (Int.repr 0). entailer!. }
    { else_false'. }
  - destruct (Mbf Ba) as (Es & Ed).
    match goal with |- semax _ ?Pre _ _ => forward_if Pre end.
    { else_false'. }
    { forward. entailer!. }
    forward.
    forward_if (temp _t'66 (Vint (Int.repr (Z.b2z (fo1 bd))))).
    { forward. forward. entailer!. bool_fin2. }
    { forward. entailer!. bool_fin2. }
    forward_if (temp _t'67 (Vint (Int.repr (Z.b2z (four_b bd))))).
    { forward. forward_if (temp _t'67 (Vint (Int.repr (Z.b2z (four_b bd))))).
      { forward. entailer!. bool_fin2. }
      { forward. forward. forward. entailer!. bool_fin2. }
      entailer!. }
    { forward. entailer!. bool_fin2. }
    forward.
    forward_if (temp _t'68 (Vint (Int.repr (if four_b bd then 4 else 3)))).
    { forward. entailer!. if_b (four_b bd). }
    { forward. entailer!. if_b (four_b bd). }
    forward_if (temp _t'69 (Vint Int.one)).
    { forward_if (temp _t'70 (vl (if four_b bd then Znth 2 bd else 0))).
      { forward. forward. entailer!. if_b (four_b bd). }
      { forward. entailer!. if_b (four_b bd). }
      forward. forward. entailer!. try subst d. destruct (four_b bd); cmp_close. }
    { exfalso. match goal with E: _ <> _ |- _ => apply E end. try subst stt. destruct (four_b bd); reflexivity. }
    gp. thaw F1. free_locals. forward. Exists (Int.repr 0). entailer!.
Qed.
