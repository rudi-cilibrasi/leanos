(* The body of wifi_source_admitted: the || chain of the frame-source tests with an early `return 0`, then the
   && chain of the empty-policy tests. *)
Require Import VST.floyd.proofauto.
Require Import LeanosDeviceProgramImage.device_program.code.
Require Import LeanosDeviceProgramImage.proof.Specs.
Require Import LeanosDeviceProgramImage.proof.BodyLookup.
Require Import LeanosDeviceProgramImage.proof.BodyPolicy.
Require Import LeanosDeviceProgramImage.proof.BodyAdmit.
Require Import LeanosDeviceProgramImage.proof.BodyShape.
#[local] Existing Instance Specs.CS.
Local Open Scope Z_scope.

Lemma repr_m1: Int.repr (-1) = Int.repr 4294967295.
Proof. apply Int.eqm_samerepr. exists (-1). reflexivity. Qed.

Lemma bool_src: forall a b c d e f g h i j k l m n : bool,
  (a && b && c && d && e && negb f && g && h && i && j && k && l && m && n)%bool =
  (negb (negb a || negb b || negb c || negb d || negb e || f || negb g || negb h) &&
   (i && j && k && l && m && n))%bool.
Proof. intros. destruct a, b, c, d, e, f, g, h; reflexivity. Qed.

Lemma source_and: forall T P M,
  let o1 := (negb (tg_bus T =? 0) || negb (tg_dev T =? 0))%bool in
  let o2 := (o1 || negb (tg_fn T =? 0))%bool in
  let o3 := (o2 || negb (tg_id T =? 4294967295))%bool in
  let o4 := (o3 || negb (tg_window T =? pl_window M))%bool in
  let o5 := (o4 || (pl_present P =? 0))%bool in
  let o6 := (o5 || negb (pl_sink_count P =? 0))%bool in
  let o7 := (o6 || negb (pl_desc_count P =? 0))%bool in
  let c1 := ((pl_window P <=? pl_window M) && (pl_dma P =? 0))%bool in
  let c2 := (c1 && (pl_cfg_read P =? 0))%bool in
  let c3 := (c2 && (pl_cfg_write P =? 0))%bool in
  let c4 := (c3 && (pl_cmd_clear P =? 0))%bool in
  let c5 := (c4 && (pl_cmd_set P =? 0))%bool in
  source T P M = (negb o7 && c5)%bool.
Proof.
  intros. subst o1 o2 o3 o4 o5 o6 o7 c1 c2 c3 c4 c5. unfold source. apply bool_src.
Qed.

Lemma z64_b2z: forall x, u64_ok x ->
  bool2val (Int64.eq (Int64.repr x) (Int64.repr 0)) = Vint (Int.repr (Z.b2z (x =? 0))).
Proof.
  intros x X. unfold u64_ok in X. destruct (Z.eqb_spec x 0) as [-> | N]; [ reflexivity | ].
  rewrite Int64.eq_false; [ reflexivity | ]. intros E. apply N.
  apply (f_equal Int64.unsigned) in E. rewrite !Int64.unsigned_repr in E by rep_lia. exact E.
Qed.

Lemma bool2val_b2z: forall b, bool2val b = Vint (Int.repr (Z.b2z b)).
Proof. intros [ | ]; reflexivity. Qed.

Ltac rjoin c := unfold target_val, policy_val, policy_rep; entailer!;
  rewrite ?z64_b2z by (unfold u64_ok; rep_lia); cjoin c;
  rewrite ?u32_eq by (unfold u32_ok; rep_lia); rewrite ?bool2val_b2z; reflexivity.

Ltac rjoin_le c := unfold target_val, policy_val, policy_rep; entailer!;
  match goal with H: _ |- _ => rewrite ?Int.unsigned_repr in H by rep_lia end;
  try unfold c;
  first [ rewrite (proj2 (Z.leb_le _ _)) by lia | rewrite (proj2 (Z.leb_gt _ _)) by lia ];
  cbn [andb]; rewrite ?notbool_b2z, ?zbool_b2z by (unfold u32_ok; rep_lia); try reflexivity.

Lemma body_wifi_source_admitted : semax_body Vprog Gprog f_wifi_source_admitted source_admitted_spec.
Proof.
  start_function.
  rename H into TW, H0 into PB, H1 into MB.
  pose proof TW as (Tb & Td & Tf & Ti & Tw & Tr).
  pose proof PB as (PW & _ & _). pose proof PW as (Ppr & Pdm & Pwn & Pcr & Pcw & Pcc & Pcs & Psc & _ & _ & Pdc & _).
  pose proof MB as (MW & _ & _). pose proof MW as (_ & _ & Mwn & _).
  unfold u32_ok, u64_ok in Tb, Td, Tf, Ti, Tw, Tr, Ppr, Pdm, Pwn, Pcr, Pcw, Pcc, Pcs, Psc, Pdc, Mwn.
  pose proof (source_and T P M) as AND. cbv zeta in AND.
  set (o1 := (negb (tg_bus T =? 0) || negb (tg_dev T =? 0))%bool) in *.
  set (o2 := (o1 || negb (tg_fn T =? 0))%bool) in *.
  set (o3 := (o2 || negb (tg_id T =? 4294967295))%bool) in *.
  set (o4 := (o3 || negb (tg_window T =? pl_window M))%bool) in *.
  set (o5 := (o4 || (pl_present P =? 0))%bool) in *.
  set (o6 := (o5 || negb (pl_sink_count P =? 0))%bool) in *.
  set (o7 := (o6 || negb (pl_desc_count P =? 0))%bool) in *.
  set (c1 := ((pl_window P <=? pl_window M) && (pl_dma P =? 0))%bool) in *.
  set (c2 := (c1 && (pl_cfg_read P =? 0))%bool) in *.
  set (c3 := (c2 && (pl_cfg_write P =? 0))%bool) in *.
  set (c4 := (c3 && (pl_cmd_clear P =? 0))%bool) in *.
  set (c5 := (c4 && (pl_cmd_set P =? 0))%bool) in *.
  unfold target_val, policy_val, policy_rep.
  forward.
  forward_if (PROP () LOCAL (temp _t'1 (Vint (Int.repr (Z.b2z o1))); temp _t tp; temp _p pp; temp _max mp)
              SEP (data_at tsh t_target (target_val T) tp; data_at psh t_policy (policy_val P) pp;
                   data_at msh t_policy (policy_val M) mp)).
  { forward. rjoin o1. }
  { forward. forward. rjoin o1. }
  unfold target_val, policy_val, policy_rep.
  forward_if (PROP () LOCAL (temp _t'2 (Vint (Int.repr (Z.b2z o2))); temp _t tp; temp _p pp; temp _max mp)
              SEP (data_at tsh t_target (target_val T) tp; data_at psh t_policy (policy_val P) pp;
                   data_at msh t_policy (policy_val M) mp)).
  { forward. rjoin o2. }
  { forward. forward. rjoin o2. }
  unfold target_val, policy_val, policy_rep.
  forward_if (PROP () LOCAL (temp _t'3 (Vint (Int.repr (Z.b2z o3))); temp _t tp; temp _p pp; temp _max mp)
              SEP (data_at tsh t_target (target_val T) tp; data_at psh t_policy (policy_val P) pp;
                   data_at msh t_policy (policy_val M) mp)).
  { forward. rjoin o3. }
  { forward. forward. rewrite repr_m1 in *. rjoin o3. }
  unfold target_val, policy_val, policy_rep.
  forward_if (PROP () LOCAL (temp _t'4 (Vint (Int.repr (Z.b2z o4))); temp _t tp; temp _p pp; temp _max mp)
              SEP (data_at tsh t_target (target_val T) tp; data_at psh t_policy (policy_val P) pp;
                   data_at msh t_policy (policy_val M) mp)).
  { forward. rjoin o4. }
  { forward. forward. forward. rjoin o4. }
  unfold target_val, policy_val, policy_rep.
  forward_if (PROP () LOCAL (temp _t'5 (Vint (Int.repr (Z.b2z o5))); temp _t tp; temp _p pp; temp _max mp)
              SEP (data_at tsh t_target (target_val T) tp; data_at psh t_policy (policy_val P) pp;
                   data_at msh t_policy (policy_val M) mp)).
  { forward. rjoin o5. }
  { forward. forward. rjoin o5. }
  unfold target_val, policy_val, policy_rep.
  forward_if (PROP () LOCAL (temp _t'6 (Vint (Int.repr (Z.b2z o6))); temp _t tp; temp _p pp; temp _max mp)
              SEP (data_at tsh t_target (target_val T) tp; data_at psh t_policy (policy_val P) pp;
                   data_at msh t_policy (policy_val M) mp)).
  { forward. rjoin o6. }
  { forward. forward. rjoin o6. }
  unfold target_val, policy_val, policy_rep.
  forward_if (PROP () LOCAL (temp _t'7 (Vint (Int.repr (Z.b2z o7))); temp _t tp; temp _p pp; temp _max mp)
              SEP (data_at tsh t_target (target_val T) tp; data_at psh t_policy (policy_val P) pp;
                   data_at msh t_policy (policy_val M) mp)).
  { forward. rjoin o7. }
  { forward. forward. rjoin o7. }
  forward_if.
  { forward. entailer!. rewrite AND, H. reflexivity. }
  unfold target_val, policy_val, policy_rep.
  forward. forward.
  forward_if (PROP () LOCAL (temp _t'8 (Vint (Int.repr (Z.b2z c1))); temp _t tp; temp _p pp; temp _max mp)
              SEP (data_at tsh t_target (target_val T) tp; data_at psh t_policy (policy_val P) pp;
                   data_at msh t_policy (policy_val M) mp)).
  { forward. forward. rjoin_le c1. }
  { forward. rjoin_le c1. }
  unfold target_val, policy_val, policy_rep.
  forward_if (PROP () LOCAL (temp _t'9 (Vint (Int.repr (Z.b2z c2))); temp _t tp; temp _p pp; temp _max mp)
              SEP (data_at tsh t_target (target_val T) tp; data_at psh t_policy (policy_val P) pp;
                   data_at msh t_policy (policy_val M) mp)).
  { forward. forward. rjoin c2. }
  { forward. rjoin c2. }
  unfold target_val, policy_val, policy_rep.
  forward_if (PROP () LOCAL (temp _t'10 (Vint (Int.repr (Z.b2z c3))); temp _t tp; temp _p pp; temp _max mp)
              SEP (data_at tsh t_target (target_val T) tp; data_at psh t_policy (policy_val P) pp;
                   data_at msh t_policy (policy_val M) mp)).
  { forward. forward. rjoin c3. }
  { forward. rjoin c3. }
  unfold target_val, policy_val, policy_rep.
  forward_if (PROP () LOCAL (temp _t'11 (Vint (Int.repr (Z.b2z c4))); temp _t tp; temp _p pp; temp _max mp)
              SEP (data_at tsh t_target (target_val T) tp; data_at psh t_policy (policy_val P) pp;
                   data_at msh t_policy (policy_val M) mp)).
  { forward. forward. rjoin c4. }
  { forward. rjoin c4. }
  unfold target_val, policy_val, policy_rep.
  forward_if (PROP () LOCAL (temp _t'12 (Vint (Int.repr (Z.b2z c5))); temp _t tp; temp _p pp; temp _max mp)
              SEP (data_at tsh t_target (target_val T) tp; data_at psh t_policy (policy_val P) pp;
                   data_at msh t_policy (policy_val M) mp)).
  { forward. forward. rjoin c5. }
  { forward. rjoin c5. }
  forward.
  entailer!. rewrite AND, H. reflexivity.
Qed.
