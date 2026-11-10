(* The bodies of the two admission shapes of wifi-exec.h: wifi_service_admitted (the || chain of the target
   comparisons and the presence test, then wifi_policy_within) and wifi_source_admitted (the || chain of the
   frame-source tests, then the && chain of the empty-policy tests). *)
Require Import VST.floyd.proofauto.
Require Import LeanosDeviceProgramImage.device_program.code.
Require Import LeanosDeviceProgramImage.proof.Specs.
Require Import LeanosDeviceProgramImage.proof.BodyLookup.
Require Import LeanosDeviceProgramImage.proof.BodyPolicy.
Require Import LeanosDeviceProgramImage.proof.BodyAdmit.
#[local] Existing Instance Specs.CS.
Local Open Scope Z_scope.

(* The joins of an || chain (o_k = o_(k-1) || test) and of an && chain (c_k = c_(k-1) && test). *)
Lemma zeq_b2z: forall a b, bool2val (zeq a b) = Vint (Int.repr (Z.b2z (a =? b))).
Proof. intros. destruct (zeq a b), (Z.eqb_spec a b); try lia; reflexivity. Qed.
Lemma zneq_b2z: forall a b, bool2val (negb (zeq a b)) = Vint (Int.repr (Z.b2z (negb (a =? b)))).
Proof. intros. destruct (zeq a b), (Z.eqb_spec a b); try lia; reflexivity. Qed.

Lemma notbool_b2z: forall x, u32_ok x ->
  bool2val (negb (negb (Int.eq (Int.repr x) Int.zero))) = Vint (Int.repr (Z.b2z (x =? 0))).
Proof. intros. rewrite negb_involutive. change Int.zero with (Int.repr 0). rewrite u32_eq by (auto; unfold u32_ok; rep_lia).
  destruct (x =? 0); reflexivity. Qed.
Lemma zbool_b2z: forall x, u32_ok x ->
  bool2val (Int.eq (Int.repr x) Int.zero) = Vint (Int.repr (Z.b2z (x =? 0))).
Proof. intros. change Int.zero with (Int.repr 0). rewrite u32_eq by (auto; unfold u32_ok; rep_lia).
  destruct (x =? 0); reflexivity. Qed.

Ltac cjoin c :=
  unfold c;
  repeat match goal with
  | H: ?a <> ?b |- context [?a =? ?b] => rewrite (proj2 (Z.eqb_neq a b) H)
  | H: ?a = ?b |- context [?a =? ?b] => rewrite (proj2 (Z.eqb_eq a b) H)
  | H: @eq bool ?o true |- context [?o] => rewrite H
  | H: @eq bool ?o false |- context [?o] => rewrite H
  end; cbn [orb andb negb];
  rewrite ?zneq_b2z, ?zeq_b2z;
  rewrite ?notbool_b2z, ?zbool_b2z by (unfold u32_ok; rep_lia); try reflexivity.

Ltac sjoin c := unfold target_val, policy_val, policy_rep; entailer!; cjoin c.

Lemma service_or: forall T P W,
  let o1 := (negb (tg_bus T =? tg_bus W) || negb (tg_dev T =? tg_dev W))%bool in
  let o2 := (o1 || negb (tg_fn T =? tg_fn W))%bool in
  let o3 := (o2 || negb (tg_id T =? tg_id W))%bool in
  let o4 := (o3 || negb (tg_window T =? tg_window W))%bool in
  let o5 := (o4 || negb (tg_bar T =? tg_bar W))%bool in
  let o6 := (o5 || (pl_present P =? 0))%bool in
  negb o6 = (target_eqb T W && negb (pl_present P =? 0))%bool.
Proof.
  intros. subst o1 o2 o3 o4 o5 o6. unfold target_eqb.
  destruct (tg_bus T =? tg_bus W), (tg_dev T =? tg_dev W), (tg_fn T =? tg_fn W), (tg_id T =? tg_id W),
    (tg_window T =? tg_window W), (tg_bar T =? tg_bar W), (pl_present P =? 0); reflexivity.
Qed.

Lemma body_wifi_service_admitted : semax_body Vprog Gprog f_wifi_service_admitted service_admitted_spec.
Proof.
  start_function.
  rename H into TW, H0 into PB, H1 into WW, H2 into MB.
  pose proof TW as (Tb & Td & Tf & Ti & Tw & Tr). pose proof WW as (Wb & Wd & Wf & Wi & Ww & Wr).
  pose proof PB as (PW & _ & _). pose proof PW as (Ppr & _).
  unfold u32_ok in Tb, Td, Tf, Ti, Tw, Tr, Wb, Wd, Wf, Wi, Ww, Wr, Ppr.
  pose proof (service_or T P W) as OR. cbv zeta in OR.
  set (o1 := (negb (tg_bus T =? tg_bus W) || negb (tg_dev T =? tg_dev W))%bool) in *.
  set (o2 := (o1 || negb (tg_fn T =? tg_fn W))%bool) in *.
  set (o3 := (o2 || negb (tg_id T =? tg_id W))%bool) in *.
  set (o4 := (o3 || negb (tg_window T =? tg_window W))%bool) in *.
  set (o5 := (o4 || negb (tg_bar T =? tg_bar W))%bool) in *.
  set (o6 := (o5 || (pl_present P =? 0))%bool) in *.
  unfold target_val. rewrite (policy_val_eq P). unfold pol_tuple.
  forward. forward.
  forward_if (PROP () LOCAL (temp _t'1 (Vint (Int.repr (Z.b2z o1))); temp _t tp; temp _p pp; temp _want wp;
                             temp _max mp)
              SEP (data_at tsh t_target (target_val T) tp; data_at psh t_policy (policy_val P) pp;
                   data_at wsh t_target (target_val W) wp; data_at msh t_policy (policy_val M) mp)).
  { forward. sjoin o1. }
  { forward. forward. forward. sjoin o1. }
  unfold target_val. rewrite (policy_val_eq P). unfold pol_tuple.
  forward_if (PROP () LOCAL (temp _t'2 (Vint (Int.repr (Z.b2z o2))); temp _t tp; temp _p pp; temp _want wp;
                             temp _max mp)
              SEP (data_at tsh t_target (target_val T) tp; data_at psh t_policy (policy_val P) pp;
                   data_at wsh t_target (target_val W) wp; data_at msh t_policy (policy_val M) mp)).
  { forward. sjoin o2. }
  { forward. forward. forward. sjoin o2. }
  unfold target_val. rewrite (policy_val_eq P). unfold pol_tuple.
  forward_if (PROP () LOCAL (temp _t'3 (Vint (Int.repr (Z.b2z o3))); temp _t tp; temp _p pp; temp _want wp;
                             temp _max mp)
              SEP (data_at tsh t_target (target_val T) tp; data_at psh t_policy (policy_val P) pp;
                   data_at wsh t_target (target_val W) wp; data_at msh t_policy (policy_val M) mp)).
  { forward. sjoin o3. }
  { forward. forward. forward. sjoin o3. }
  unfold target_val. rewrite (policy_val_eq P). unfold pol_tuple.
  forward_if (PROP () LOCAL (temp _t'4 (Vint (Int.repr (Z.b2z o4))); temp _t tp; temp _p pp; temp _want wp;
                             temp _max mp)
              SEP (data_at tsh t_target (target_val T) tp; data_at psh t_policy (policy_val P) pp;
                   data_at wsh t_target (target_val W) wp; data_at msh t_policy (policy_val M) mp)).
  { forward. sjoin o4. }
  { forward. forward. forward. sjoin o4. }
  unfold target_val. rewrite (policy_val_eq P). unfold pol_tuple.
  forward_if (PROP () LOCAL (temp _t'5 (Vint (Int.repr (Z.b2z o5))); temp _t tp; temp _p pp; temp _want wp;
                             temp _max mp)
              SEP (data_at tsh t_target (target_val T) tp; data_at psh t_policy (policy_val P) pp;
                   data_at wsh t_target (target_val W) wp; data_at msh t_policy (policy_val M) mp)).
  { forward. sjoin o5. }
  { forward. forward. forward. sjoin o5. }
  unfold target_val. rewrite (policy_val_eq P). unfold pol_tuple.
  forward_if (PROP () LOCAL (temp _t'6 (Vint (Int.repr (Z.b2z o6))); temp _t tp; temp _p pp; temp _want wp;
                             temp _max mp)
              SEP (data_at tsh t_target (target_val T) tp; data_at psh t_policy (policy_val P) pp;
                   data_at wsh t_target (target_val W) wp; data_at msh t_policy (policy_val M) mp)).
  { forward. sjoin o6. }
  { forward. forward. sjoin o6. }
  forward_if.
  { forward. entailer!. unfold service. rewrite H in OR. cbn in OR. rewrite <- OR. reflexivity. }
  forward_call (psh, pp, P, msh, mp, M).
  forward.
  entailer!. unfold service. rewrite H in OR. cbn in OR. rewrite <- OR. reflexivity.
Qed.
