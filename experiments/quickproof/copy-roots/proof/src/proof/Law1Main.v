(* Law copy_roots_exact: the body of the harness's main (harness/copy_roots_exact.c), for any program p
   without global variables (whole_prog is one).  The roots are framed out (freeze) around each call, load
   and store: VST's cancellation otherwise tries to unify the target with every other 45056-byte root. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosRoots.proof.Defs.
Require Import LeanosRoots.proof.RootsSpecs.
Require Import LeanosRoots.proof.Law1Specs.
Require Import LeanosRoots.proof.Law1Pure.
Require Import LeanosRoots.proof.Law1Small.
Require Import LeanosRoots.harness.copy_roots_exact.code.
Local Open Scope Z_scope.

Lemma fill_step: forall (a: list Z) x i k, Zlength a = i -> 0 < k ->
  upd_Znth i (longs a ++ Zrepeat Vundef k) (Vlong (Int64.repr x)) = longs (a ++ [x]) ++ Zrepeat Vundef (k - 1).
Proof. intros. subst i. unfold longs. rewrite map_app. list_solve. Qed.
Lemma dr_root: forall sh p, data_at_ sh (Tstruct _qotom_root_pages noattr) p = data_at_ sh t_root p.
Proof. reflexivity. Qed.
Ltac zsimp := bhyp; repeat match goal with
  | H: ?b <> 0 |- context [?b =? 0] => rewrite (proj2 (Z.eqb_neq b 0) H)
  | H: ?b = 0 |- context [?b =? 0] => rewrite (proj2 (Z.eqb_eq b 0) H)
  end.
Ltac ptrstep b v :=
  forward; [ destruct (b =? 0); entailer! | ];
  entailer!; zsimp; destruct (b =? 0) eqn:?; [ reflexivity | ];
  match goal with H: field_compatible _ _ v |- _ => apply field_compatible_isptr in H end;
  destruct v; try contradiction; reflexivity.
Ltac falsestep := forward; entailer!; match goal with H: ?x = false |- context [?x] => rewrite H; reflexivity end.
Lemma body_main: forall p, QPprog_vars p = nil -> semax_body Vharness Gharness f_main (_main, main_spec_std p).
Proof.
  intros p Hp. start_function. rewrite Hp. change (globvars2pred gv nil) with (@emp mpred _ _).
  rewrite !dr_root.
  forward_call. Intros sp. forward_call. Intros kp. forward_call. Intros cp.
  freeze FR := (data_at_ _ _ v_result) (data_at_ _ _ v_aliases) (data_at_ _ _ v_frames) (data_at_ _ _ v_copy0)
     (data_at_ _ _ v_copy) (data_at_ _ _ v_closed0) (data_at_ _ _ v_closed) (data_at_ _ _ v_source0) (has_ext _).
  forward_call (v_source). Intros src.
  thaw FR.
  freeze FR := (data_at_ _ _ v_result) (data_at_ _ _ v_aliases) (data_at_ _ _ v_frames) (data_at_ _ _ v_copy0)
     (data_at_ _ _ v_copy) (data_at_ _ _ v_closed0) (data_at _ _ _ v_source) (data_at_ _ _ v_source0) (has_ext _).
  forward_call (v_closed). Intros kv. thaw FR.
  freeze FR := (data_at_ _ _ v_result) (data_at_ _ _ v_aliases) (data_at_ _ _ v_frames) (data_at_ _ _ v_copy0)
     (data_at _ _ _ v_closed) (data_at_ _ _ v_closed0) (data_at _ _ _ v_source) (data_at_ _ _ v_source0) (has_ext _).
  forward_call (v_copy). Intros cv. thaw FR.
  forward_call. Intros n.
  freeze FR := (data_at _ _ _ v_copy) (data_at_ _ _ v_result) (data_at_ _ _ v_aliases) (data_at_ _ _ v_copy0)
     (data_at _ _ _ v_closed) (data_at_ _ _ v_closed0) (data_at _ _ _ v_source) (data_at_ _ _ v_source0) (has_ext _).
  forward_for_simple_bound 16
    (@exp (environ -> mpred) _ Z (fun i => EX fs: list Z,
     PROP (Zlength fs = i; words_ok fs)
     LOCAL (temp _n (Vlong (Int64.repr n)); temp _source_phys (Vlong (Int64.repr sp)); temp _closed_phys (Vlong (Int64.repr kp)); temp _copy_phys (Vlong (Int64.repr cp)); lvar _result (Tstruct _qotom_root_build_result noattr) v_result; lvar _aliases (tarray (Tstruct _qotom_copy_alias noattr) 2) v_aliases; lvar _frames (tarray tulong 16) v_frames; lvar _copy0 (Tstruct _qotom_root_pages noattr) v_copy0; lvar _copy (Tstruct _qotom_root_pages noattr) v_copy; lvar _closed0 (Tstruct _qotom_root_pages noattr) v_closed0; lvar _closed (Tstruct _qotom_root_pages noattr) v_closed; lvar _source0 (Tstruct _qotom_root_pages noattr) v_source0; lvar _source (Tstruct _qotom_root_pages noattr) v_source; gvars gv)
     SEP (data_at Tsh (tarray tulong 16) (longs fs ++ Zrepeat Vundef (16 - i)) v_frames; FRZL FR))).
  - Exists (@nil Z). entailer!. constructor.
  - forward_call. Intros x. forward.
    Exists (fs ++ [x]). rewrite (fill_step _ _ i) by lia. replace (16 - i - 1) with (16 - (i + 1)) by lia.
    entailer!. unfold words_ok in *. rewrite Zlength_app, Zlength_cons, Zlength_nil. split; [ lia | ].
    apply Forall_app; split; auto; repeat constructor; unfold word_ok; lia.
  - Intros fs. change (Zrepeat Vundef (16 - 16)) with (@nil val). rewrite app_nil_r.
  thaw FR. forward_call. Intros m.
  freeze FR := (data_at _ _ _ v_copy) (data_at_ _ _ v_result) (data_at _ _ _ v_frames) (data_at_ _ _ v_copy0)
     (data_at _ _ _ v_closed) (data_at_ _ _ v_closed0) (data_at _ _ _ v_source) (data_at_ _ _ v_source0) (has_ext _).
  forward_for_simple_bound 2
    (@exp (environ -> mpred) _ Z (fun i => @exp (environ -> mpred) _ (list alias) (fun al =>
     PROP (Zlength al = i; Forall alias_wf al)
     LOCAL (temp _m (Vlong (Int64.repr m)); temp _n (Vlong (Int64.repr n)); temp _source_phys (Vlong (Int64.repr sp)); temp _closed_phys (Vlong (Int64.repr kp)); temp _copy_phys (Vlong (Int64.repr cp)); lvar _result (Tstruct _qotom_root_build_result noattr) v_result; lvar _aliases (tarray (Tstruct _qotom_copy_alias noattr) 2) v_aliases; lvar _frames (tarray tulong 16) v_frames; lvar _copy0 (Tstruct _qotom_root_pages noattr) v_copy0; lvar _copy (Tstruct _qotom_root_pages noattr) v_copy; lvar _closed0 (Tstruct _qotom_root_pages noattr) v_closed0; lvar _closed (Tstruct _qotom_root_pages noattr) v_closed; lvar _source0 (Tstruct _qotom_root_pages noattr) v_source0; lvar _source (Tstruct _qotom_root_pages noattr) v_source; gvars gv)
     SEP (data_at Tsh (tarray t_alias 2) (map alias_val al ++ Zrepeat (default_val t_alias) (2 - i)) v_aliases; FRZL FR)))).
  { Exists (@nil alias). entailer!. }
  { forward_call. Intros pg. forward. forward_call. Intros fr. forward. forward_call. Intros wr. forward.
    Exists (al ++ [mkalias pg fr wr]). entailer!.
    { split; [ rewrite Zlength_app, Zlength_cons, Zlength_nil; lia | ].
      apply Forall_app; split; auto. repeat constructor; simpl; unfold word_ok; lia. }
    apply derives_refl'. f_equal.
    rewrite !upd_Znth_same by (rewrite ?upd_Znth_Zlength by list_solve; list_solve).
    cbn [fst snd]. rewrite map_app. list_solve. }
  Intros al. change (Zrepeat (default_val t_alias) (2 - 2)) with (@nil (reptype t_alias)). rewrite app_nil_r.
  thaw FR.
  freeze FR := (data_at _ _ _ v_copy) (data_at _ _ _ v_aliases) (data_at _ _ _ v_frames) (data_at_ _ _ v_copy0)
     (data_at _ _ _ v_closed) (data_at_ _ _ v_closed0) (data_at _ _ _ v_source) (data_at_ _ _ v_source0) (has_ext _).
  forward_call. Intros r0. forward. forward_call. Intros r1. forward.
  forward_call. Intros r2. forward. forward_call. Intros r3. forward.
  forward. forward. forward. forward.
  thaw FR.
  freeze FR := (data_at _ _ _ v_copy) (data_at _ _ _ v_aliases) (data_at _ _ _ v_frames) (data_at_ _ _ v_copy0)
     (data_at _ _ _ v_closed) (data_at_ _ _ v_closed0) (data_at _ _ _ v_result) (has_ext _).
  rewrite ?dr_root. focus_SEP 2. forward_call (v_source0, v_source, Tsh, src).
  thaw FR.
  freeze FR := (data_at _ _ _ v_copy) (data_at _ _ _ v_aliases) (data_at _ _ _ v_frames) (data_at_ _ _ v_copy0)
     (data_at _ _ _ v_source) (data_at _ _ _ v_source0) (data_at _ _ _ v_result) (has_ext _).
  focus_SEP 2. forward_call (v_closed0, v_closed, Tsh, kv).
  thaw FR.
  freeze FR := (data_at _ _ _ v_closed) (data_at _ _ _ v_aliases) (data_at _ _ _ v_frames) (data_at _ _ _ v_closed0)
     (data_at _ _ _ v_source) (data_at _ _ _ v_source0) (data_at _ _ _ v_result) (has_ext _).
  rewrite ?dr_root.
  focus_SEP 2. forward_call (v_copy0, v_copy, Tsh, cv).
  thaw FR.
  forward_call. Intros b0.
  forward_if (temp _t'15 (if Z.eqb b0 0 then nullval else v_source)).
  { forward. entailer!. }
  { forward. entailer!. rewrite (proj2 (Z.eqb_neq b0 0)) by auto. reflexivity. }
  forward.
  forward_call. Intros b1.
  forward_if (temp _t'17 (if Z.eqb b1 0 then nullval else v_closed)).
  { forward. entailer!. }
  { forward. entailer!. rewrite (proj2 (Z.eqb_neq b1 0)) by auto. reflexivity. }
  forward.
  forward_call. Intros b2.
  forward_if (temp _t'19 (if Z.eqb b2 0 then nullval else v_copy)).
  { forward. entailer!. }
  { forward. entailer!. rewrite (proj2 (Z.eqb_neq b2 0)) by auto. reflexivity. }
  forward.
  forward_call. Intros b3.
  forward_if (temp _t'21 (if Z.eqb b3 0 then nullval else v_frames)).
  { forward. entailer!. }
  { forward. entailer!. rewrite (proj2 (Z.eqb_neq b3 0)) by auto. reflexivity. }
  forward.
  forward_call. Intros b4.
  forward_if (temp _t'23 (if Z.eqb b4 0 then nullval else v_aliases)).
  { forward. entailer!. }
  { forward. entailer!. rewrite (proj2 (Z.eqb_neq b4 0)) by auto. reflexivity. }
  forward.
  forward_call. Intros b5.
  forward_if (temp _t'25 (if Z.eqb b5 0 then nullval else v_result)).
  { forward. entailer!. }
  { forward. entailer!. rewrite (proj2 (Z.eqb_neq b5 0)) by auto. reflexivity. }
  forward.
  forward_if (temp _t'26 (Vint (Int.repr (b2z (negb (b0 =? 0) && negb (b1 =? 0))%bool)))).
  { destruct (b0 =? 0); entailer!. }
  { assert (N0: (b0 =? 0) = false) by (destruct (b0 =? 0); [ exfalso; apply H21; reflexivity | reflexivity ]).
    forward.
    { destruct (b1 =? 0); entailer!. }
    entailer!.
    rewrite N0. destruct (b1 =? 0); [ reflexivity | ].
    match goal with H: field_compatible _ _ v_closed |- _ => apply field_compatible_isptr in H end.
    destruct v_closed; try contradiction; reflexivity. }
  { assert_PROP (isptr v_source) as Pv by entailer!.
    forward. entailer!.
    destruct (b0 =? 0) eqn:E; [ reflexivity | rewrite H21 in Pv; contradiction ]. }
  forward_if (temp _t'27 (Vint (Int.repr (b2z (negb (b0 =? 0) && negb (b1 =? 0) && negb (b2 =? 0))%bool)))).
  { ptrstep b2 v_copy. }
  { forward. entailer!. zsimp.
    match goal with H: ?x = false |- context [?x] => rewrite H; reflexivity end. }
  forward_if (temp _t'28 (Vint (Int.repr (b2z (negb (b0 =? 0) && negb (b1 =? 0) && negb (b2 =? 0) && negb (b3 =? 0))%bool)))).
  { ptrstep b3 v_frames. }
  { falsestep. }
  forward_if (temp _t'29 (Vint (Int.repr (b2z (negb (b0 =? 0) && negb (b1 =? 0) && negb (b2 =? 0) && negb (b3 =? 0) && negb (b4 =? 0))%bool)))).
  { ptrstep b4 v_aliases. }
  { falsestep. }
  forward_if (temp _t'30 (Vint (Int.repr (b2z (negb (b0 =? 0) && negb (b1 =? 0) && negb (b2 =? 0) && negb (b3 =? 0) && negb (b4 =? 0) && negb (b5 =? 0))%bool)))).
  { ptrstep b5 v_result. }
  { falsestep. }
  forward_if (temp _t'31 (Vint (Int.repr (b2z (negb (b0 =? 0) && negb (b1 =? 0) && negb (b2 =? 0) && negb (b3 =? 0) && negb (b4 =? 0) && negb (b5 =? 0) && phys_ok sp)%bool)))).
  { forward_call (sp). forward. entailer!. match goal with H: ?x = true |- context [?x] => rewrite H end.
    destruct (phys_ok sp); reflexivity. }
  { falsestep. }
  forward_if (temp _t'33 (Vint (Int.repr (b2z (negb (b0 =? 0) && negb (b1 =? 0) && negb (b2 =? 0) && negb (b3 =? 0) && negb (b4 =? 0) && negb (b5 =? 0) && phys_ok sp && phys_ok kp)%bool)))).
  { forward_call (kp). forward. entailer!. match goal with H: ?x = true |- context [?x] => rewrite H end.
    destruct (phys_ok kp); reflexivity. }
  { falsestep. }
  forward_if (temp _t'35 (Vint (Int.repr (b2z (negb (b0 =? 0) && negb (b1 =? 0) && negb (b2 =? 0) && negb (b3 =? 0) && negb (b4 =? 0) && negb (b5 =? 0) && phys_ok sp && phys_ok kp && phys_ok cp)%bool)))).
  { forward_call (cp). forward. entailer!. match goal with H: ?x = true |- context [?x] => rewrite H end.
    destruct (phys_ok cp); reflexivity. }
  { falsestep. }
  forward_if (temp _t'37 (Vint (Int.repr (b2z (negb (b0 =? 0) && negb (b1 =? 0) && negb (b2 =? 0) && negb (b3 =? 0) && negb (b4 =? 0) && negb (b5 =? 0) && phys_ok sp && phys_ok kp && phys_ok cp && disjoint sp kp)%bool)))).
  { assert (Ba: sp <= 2 ^ 52 - ROOT_BYTES /\ kp <= 2 ^ 52 - ROOT_BYTES)
      by (bhyp; unfold phys_ok in *; bhyp; lia).
    forward_call (sp, kp). forward. entailer!. match goal with H: ?x = true |- context [?x] => rewrite H end.
    destruct (disjoint sp kp); reflexivity. }
  { falsestep. }
  forward_if (temp _t'39 (Vint (Int.repr (b2z (negb (b0 =? 0) && negb (b1 =? 0) && negb (b2 =? 0) && negb (b3 =? 0) && negb (b4 =? 0) && negb (b5 =? 0) && phys_ok sp && phys_ok kp && phys_ok cp && disjoint sp kp && disjoint sp cp)%bool)))).
  { assert (Ba: sp <= 2 ^ 52 - ROOT_BYTES /\ cp <= 2 ^ 52 - ROOT_BYTES)
      by (bhyp; unfold phys_ok in *; bhyp; lia).
    forward_call (sp, cp). forward. entailer!. match goal with H: ?x = true |- context [?x] => rewrite H end.
    destruct (disjoint sp cp); reflexivity. }
  { falsestep. }
  forward_if (temp _t'41 (Vint (Int.repr (b2z (negb (b0 =? 0) && negb (b1 =? 0) && negb (b2 =? 0) && negb (b3 =? 0) && negb (b4 =? 0) && negb (b5 =? 0) && phys_ok sp && phys_ok kp && phys_ok cp && disjoint sp kp && disjoint sp cp && disjoint kp cp)%bool)))).
  { assert (Ba: kp <= 2 ^ 52 - ROOT_BYTES /\ cp <= 2 ^ 52 - ROOT_BYTES)
      by (bhyp; unfold phys_ok in *; bhyp; lia).
    forward_call (kp, cp). forward. entailer!. match goal with H: ?x = true |- context [?x] => rewrite H end.
    destruct (disjoint kp cp); reflexivity. }
  { falsestep. }
Opaque tables_ok inventory_ok aliases_ok build_ok ancestors_ok.
freeze FR := (data_at _ _ _ v_source0) (data_at _ _ _ v_closed) (data_at _ _ _ v_closed0) (data_at _ _ _ v_copy) (data_at _ _ _ v_copy0) (data_at _ _ _ v_frames) (data_at _ _ _ v_aliases) (data_at _ _ _ v_result) (has_ext _).
forward_if (temp _t'43 (Vint (Int.repr (b2z (negb (b0 =? 0) && negb (b1 =? 0) && negb (b2 =? 0) && negb (b3 =? 0) && negb (b4 =? 0) && negb (b5 =? 0) && phys_ok sp && phys_ok kp && phys_ok cp && disjoint sp kp && disjoint sp cp && disjoint kp cp && tables_ok src sp 32)%bool)))).
{
forward_call (v_source, Tsh, src, sp, 32).
all: try (unfold word_ok in *; rep_lia).
forward.
entailer!.
match goal with H: ?x = true |- context [?x] => rewrite H end.
destruct (tables_ok src sp 32); reflexivity.
}
{
falsestep.
}
thaw FR.
assert (R16: forall sh v q, data_at sh (tarray tulong 16) v q = data_at sh (tarray tulong (Zlength fs)) v q) by (intros; rewrite H6; reflexivity).
assert (R2: forall sh v q, data_at sh (tarray t_alias 2) v q = data_at sh (tarray t_alias (Zlength al)) v q) by (intros; rewrite H9; reflexivity).
rewrite R16, R2.
freeze FR := (data_at _ _ _ v_source) (data_at _ _ _ v_source0) (data_at _ _ _ v_closed) (data_at _ _ _ v_closed0) (data_at _ _ _ v_copy) (data_at _ _ _ v_copy0) (data_at _ _ _ v_aliases) (data_at _ _ _ v_result) (has_ext _).
forward_if (temp _t'45 (Vint (Int.repr (b2z (negb (b0 =? 0) && negb (b1 =? 0) && negb (b2 =? 0) && negb (b3 =? 0) && negb (b4 =? 0) && negb (b5 =? 0) && phys_ok sp && phys_ok kp && phys_ok cp && disjoint sp kp && disjoint sp cp && disjoint kp cp && tables_ok src sp 32 && inventory_ok fs n)%bool)))).
{
forward_call (v_frames, Tsh, fs, n).
all: try (unfold word_ok in *; rep_lia).
forward.
entailer!.
match goal with H: ?x = true |- context [?x] => rewrite H end.
destruct (inventory_ok fs n); reflexivity.
}
{
falsestep.
}
thaw FR.
freeze FR := (data_at _ _ _ v_source0) (data_at _ _ _ v_closed) (data_at _ _ _ v_closed0) (data_at _ _ _ v_copy) (data_at _ _ _ v_copy0) (data_at _ _ _ v_result) (has_ext _).
forward_if (temp _t'47 (Vint (Int.repr (b2z (negb (b0 =? 0) && negb (b1 =? 0) && negb (b2 =? 0) && negb (b3 =? 0) && negb (b4 =? 0) && negb (b5 =? 0) && phys_ok sp && phys_ok kp && phys_ok cp && disjoint sp kp && disjoint sp cp && disjoint kp cp && tables_ok src sp 32 && inventory_ok fs n && aliases_ok src (sublist 0 n fs) al m)%bool)))).
{
Transparent inventory_ok.
assert (Hn: 1 <= n <= Zlength fs) by (bhyp; unfold inventory_ok in *; bhyp; lia).
Opaque inventory_ok.
forward_call (v_aliases, Tsh, al, m, v_source, Tsh, src, v_frames, Tsh, fs, n).
all: try (unfold word_ok in *; rep_lia).
forward.
entailer!.
match goal with H: ?x = true |- context [?x] => rewrite H end.
destruct (aliases_ok src (sublist 0 n fs) al m); reflexivity.
}
{
falsestep.
}
thaw FR.
forward.
assert (MS: forall sh (t: type) (v: reptype t) (q P: val), isptr P -> (q = nullval \/ q = P) -> data_at sh t v P = (maybe_at sh t v q * (if Val.eq q nullval then data_at sh t v P else emp))%logic).
{
intros sh t v q P HP [-> | ->]; unfold maybe_at.
- rewrite !if_true by auto.
rewrite emp_sepcon.
reflexivity.
- destruct P; try contradiction.
rewrite !if_false by discriminate.
rewrite sepcon_emp.
reflexivity.
}
assert (RA: data_at Tsh (tarray t_alias (Zlength al)) (map alias_val al) v_aliases = data_at Tsh (tarray t_alias (Zlength al + Zlength (@nil (reptype t_alias)))) (map alias_val al ++ []) v_aliases) by (rewrite app_nil_r, Zlength_nil, Z.add_0_r; reflexivity).
assert (RR: data_at Tsh (Tstruct _qotom_root_build_result noattr) (Vlong (Int64.repr r0), (Vlong (Int64.repr r1), (Vlong (Int64.repr r2), Vlong (Int64.repr r3)))) v_result = data_at Tsh t_result (result_val r0 r1 r2 r3) v_result) by reflexivity.
rewrite RA, RR.
assert_PROP (isptr v_source /\ isptr v_closed /\ isptr v_copy /\ isptr v_frames /\ isptr v_aliases /\ isptr v_result) as PP by entailer!.
destruct PP as (Ps & Pk & Pc & Pf & Pa & Pr).
rewrite (MS Tsh t_root (root_val src) (if b0 =? 0 then nullval else v_source) v_source Ps) by (destruct (b0 =? 0); auto).
rewrite (MS Tsh t_root (root_val kv) (if b1 =? 0 then nullval else v_closed) v_closed Pk) by (destruct (b1 =? 0); auto).
rewrite (MS Tsh t_root (root_val cv) (if b2 =? 0 then nullval else v_copy) v_copy Pc) by (destruct (b2 =? 0); auto).
rewrite (MS Tsh (tarray tulong (Zlength fs)) (longs fs) (if b3 =? 0 then nullval else v_frames) v_frames Pf) by (destruct (b3 =? 0); auto).
rewrite (MS Tsh (tarray t_alias (Zlength al + Zlength (@nil (reptype t_alias)))) (map alias_val al ++ []) (if b4 =? 0 then nullval else v_aliases) v_aliases Pa) by (destruct (b4 =? 0); auto).
rewrite (MS Tsh t_result (result_val r0 r1 r2 r3) (if b5 =? 0 then nullval else v_result) v_result Pr) by (destruct (b5 =? 0); auto).
repeat flatten_sepcon_in_SEP.
freeze FR := (data_at _ _ _ v_source0) (data_at _ _ _ v_closed0) (data_at _ _ _ v_copy0) (has_ext _) (if Val.eq (if b0 =? 0 then nullval else v_source) nullval then _ else _) (if Val.eq (if b1 =? 0 then nullval else v_closed) nullval then _ else _) (if Val.eq (if b2 =? 0 then nullval else v_copy) nullval then _ else _) (if Val.eq (if b3 =? 0 then nullval else v_frames) nullval then _ else _) (if Val.eq (if b4 =? 0 then nullval else v_aliases) nullval then _ else _) (if Val.eq (if b5 =? 0 then nullval else v_result) nullval then _ else _).
forward_call (if b0 =? 0 then nullval else v_source, Tsh, src, sp, if b1 =? 0 then nullval else v_closed, root_val kv, kp, if b2 =? 0 then nullval else v_copy, root_val cv, cp, if b3 =? 0 then nullval else v_frames, Tsh, fs, n, if b4 =? 0 then nullval else v_aliases, Tsh, al, @nil (reptype t_alias), m, if b5 =? 0 then nullval else v_result, result_val r0 r1 r2 r3).
{ repeat match goal with |- _ /\ _ => split end; try (rewrite H9; rep_lia); match goal with |- is_pointer_or_null (if ?c then _ else _) => destruct c; [ simpl; auto | apply isptr_is_pointer_or_null; assumption ] end. }
Intros status.
thaw FR.
assert (MJ: forall sh (t: type) (v v': reptype t) (q P: val), (q = nullval \/ q = P) -> (q = nullval -> v' = v) -> (maybe_at sh t v' q * (if Val.eq q nullval then data_at sh t v P else emp))%logic |-- data_at sh t v' P).
{
intros sh t v v' q P [-> | ->] E; unfold maybe_at.
- rewrite !if_true by auto.
rewrite E by auto.
rewrite emp_sepcon.
apply derives_refl.
- destruct (Val.eq P nullval) as [EQ | NE].
+ rewrite E by auto.
rewrite emp_sepcon.
apply derives_refl.
+ rewrite sepcon_emp.
apply derives_refl.
}
match goal with Hi: status = 0 <-> _ |- _ => rename Hi into Hst end.
sep_apply (MJ Tsh t_root (root_val src) (root_val src) (if b0 =? 0 then nullval else v_source) v_source ltac:(destruct (b0 =? 0); auto) ltac:(intros; reflexivity)).
sep_apply (MJ Tsh t_root (root_val kv) (if status =? 0 then root_val (closed_out src (sublist 0 n fs) kp) else root_val kv) (if b1 =? 0 then nullval else v_closed) v_closed ltac:(destruct (b1 =? 0); auto) ltac:(intro Hq; destruct (Z.eqb_spec status 0) as [S0 | S0]; [ exfalso; apply Hst in S0; destruct S0 as (A1 & A2 & A3 & A4 & A5 & A6 & A7); apply A2; exact Hq | reflexivity ])).
sep_apply (MJ Tsh t_root (root_val cv) (if status =? 0 then root_val (copy_out src (sublist 0 n fs) (sublist 0 m al) cp) else root_val cv) (if b2 =? 0 then nullval else v_copy) v_copy ltac:(destruct (b2 =? 0); auto) ltac:(intro Hq; destruct (Z.eqb_spec status 0) as [S0 | S0]; [ exfalso; apply Hst in S0; destruct S0 as (A1 & A2 & A3 & A4 & A5 & A6 & A7); apply A3; exact Hq | reflexivity ])).
sep_apply (MJ Tsh (tarray tulong (Zlength fs)) (longs fs) (longs fs) (if b3 =? 0 then nullval else v_frames) v_frames ltac:(destruct (b3 =? 0); auto) ltac:(intros; reflexivity)).
sep_apply (MJ Tsh (tarray t_alias (Zlength al + Zlength (@nil (reptype t_alias)))) (map alias_val al ++ []) (map alias_val al ++ []) (if b4 =? 0 then nullval else v_aliases) v_aliases ltac:(destruct (b4 =? 0); auto) ltac:(intros; reflexivity)).
sep_apply (MJ Tsh t_result (result_val r0 r1 r2 r3) (if status =? 0 then result_val n (removed_count (sublist 0 n fs) (pt src)) (retained_count (sublist 0 n fs) (pt src)) m else result_val r0 r1 r2 r3) (if b5 =? 0 then nullval else v_result) v_result ltac:(destruct (b5 =? 0); auto) ltac:(intro Hq; destruct (Z.eqb_spec status 0) as [S0 | S0]; [ exfalso; apply Hst in S0; destruct S0 as (A1 & A2 & A3 & A4 & A5 & A6 & A7); apply A6; exact Hq | reflexivity ])).
rewrite <- RA.
remember (negb (b0 =? 0) && negb (b1 =? 0) && negb (b2 =? 0) && negb (b3 =? 0) && negb (b4 =? 0) && negb (b5 =? 0) && phys_ok sp && phys_ok kp && phys_ok cp && disjoint sp kp && disjoint sp cp && disjoint kp cp && tables_ok src sp 32 && inventory_ok fs n && aliases_ok src (sublist 0 n fs) al m)%bool as vb eqn:Evb.
assert (Ns: v_source <> nullval) by (intro E; rewrite E in Ps; inversion Ps).
assert (Nk: v_closed <> nullval) by (intro E; rewrite E in Pk; inversion Pk).
assert (Nc: v_copy <> nullval) by (intro E; rewrite E in Pc; inversion Pc).
assert (Nf: v_frames <> nullval) by (intro E; rewrite E in Pf; inversion Pf).
assert (Na: v_aliases <> nullval) by (intro E; rewrite E in Pa; inversion Pa).
assert (Nr: v_result <> nullval) by (intro E; rewrite E in Pr; inversion Pr).
assert (VS: status = 0 <-> vb = true).
{
rewrite Hst, Evb.
Transparent build_ok.
unfold build_ok.
rewrite ancestors_tables.
destruct (b0 =? 0), (b1 =? 0), (b2 =? 0), (b3 =? 0), (b4 =? 0), (b5 =? 0); simpl; intuition congruence.
}
Opaque build_ok.
clear Evb.
match goal with Hr: 0 <= status <= 4 |- _ => rename Hr into Hs4 end.
assert (St: status = 0 \/ status = 1 \/ status = 2 \/ status = 3 \/ status = 4) by lia.
assert (VF: status <> 0 -> vb = false) by (intro Hn; destruct vb; [ exfalso; apply Hn; apply VS; reflexivity | reflexivity ]).
freeze FR := (data_at _ _ _ v_source) (data_at _ _ _ v_source0) (data_at _ _ _ v_closed) (data_at _ _ _ v_closed0) (data_at _ _ _ v_copy) (data_at _ _ _ v_copy0) (data_at _ _ _ v_frames) (data_at _ _ _ v_aliases) (data_at _ _ _ v_result) (has_ext _).
forward_call (Int.one).
{
entailer!.
destruct St as [-> | [-> | [-> | [-> | ->]]]]; [ rewrite (proj1 VS eq_refl) | rewrite VF by lia .. ]; reflexivity.
}
forward_if (temp _t'50 (Vint Int.one)).
{
forward.
entailer!.
destruct St as [-> | [-> | [-> | [-> | ->]]]]; reflexivity.
}
{
exfalso.
destruct St as [-> | [-> | [-> | [-> | ->]]]]; discriminate.
}
forward_call (Int.one).
thaw FR.
freeze FR := (data_at _ _ _ v_closed) (data_at _ _ _ v_closed0) (data_at _ _ _ v_copy) (data_at _ _ _ v_copy0) (data_at _ _ _ v_frames) (data_at _ _ _ v_aliases) (data_at _ _ _ v_result) (has_ext _).
forward_call (v_source, v_source0, Tsh, Tsh, src).
forward_call (Int.one).
thaw FR.
forward_if.
{
assert (S1: status <> 0) by assumption.
rewrite (proj2 (Z.eqb_neq status 0) S1).
cbv beta iota.
freeze FR := (data_at _ _ _ v_source) (data_at _ _ _ v_source0) (data_at _ _ _ v_copy) (data_at _ _ _ v_copy0) (data_at _ _ _ v_frames) (data_at _ _ _ v_aliases) (data_at _ _ _ v_result) (has_ext _).
forward_call (v_closed, v_closed0, Tsh, Tsh, kv).
forward_call (Int.one).
thaw FR.
freeze FR := (data_at _ _ _ v_source) (data_at _ _ _ v_source0) (data_at _ _ _ v_closed) (data_at _ _ _ v_closed0) (data_at _ _ _ v_frames) (data_at _ _ _ v_aliases) (data_at _ _ _ v_result) (has_ext _).
forward_call (v_copy, v_copy0, Tsh, Tsh, cv).
forward_call (Int.one).
thaw FR.
unfold result_val.
freeze FR := (data_at _ _ _ v_source) (data_at _ _ _ v_source0) (data_at _ _ _ v_closed) (data_at _ _ _ v_closed0) (data_at _ _ _ v_copy) (data_at _ _ _ v_copy0) (data_at _ _ _ v_frames) (data_at _ _ _ v_aliases) (has_ext _).
forward.
forward_if (temp _t'54 (Vint Int.one)).
{
forward.
forward.
entailer!.
}
{
exfalso.
match goal with H: ?x <> ?x |- _ => apply H; reflexivity end.
}
forward_if (temp _t'55 (Vint Int.one)).
{
forward.
forward.
entailer!.
}
{
exfalso.
match goal with H: ?x = ?y |- _ => discriminate H end.
}
forward_if (temp _t'56 (Vint Int.one)).
{
forward.
forward.
entailer!.
}
{
exfalso.
match goal with H: ?x = ?y |- _ => discriminate H end.
}
forward_call (Int.one).
thaw FR.
rewrite <- R16, <- R2.
sep_apply (data_at_data_at_ Tsh t_root (root_val src) v_source).
sep_apply (data_at_data_at_ Tsh t_root (root_val src) v_source0).
freeze F := (data_at_ _ _ v_source) (data_at_ _ _ v_source0) (data_at _ _ _ v_closed0) (data_at _ _ _ v_copy) (data_at _ _ _ v_copy0) (data_at _ _ _ v_frames) (data_at _ _ _ v_aliases) (data_at _ _ _ v_result) (has_ext _).
sep_apply (data_at_data_at_ Tsh t_root (root_val kv) v_closed).
thaw F.
freeze F := (data_at_ _ _ v_source) (data_at_ _ _ v_source0) (data_at_ _ _ v_closed) (data_at _ _ _ v_copy) (data_at _ _ _ v_copy0) (data_at _ _ _ v_frames) (data_at _ _ _ v_aliases) (data_at _ _ _ v_result) (has_ext _).
sep_apply (data_at_data_at_ Tsh t_root (root_val kv) v_closed0).
thaw F.
freeze F := (data_at_ _ _ v_source) (data_at_ _ _ v_source0) (data_at_ _ _ v_closed) (data_at_ _ _ v_closed0) (data_at _ _ _ v_copy0) (data_at _ _ _ v_frames) (data_at _ _ _ v_aliases) (data_at _ _ _ v_result) (has_ext _).
sep_apply (data_at_data_at_ Tsh t_root (root_val cv) v_copy).
thaw F.
freeze F := (data_at_ _ _ v_source) (data_at_ _ _ v_source0) (data_at_ _ _ v_closed) (data_at_ _ _ v_closed0) (data_at_ _ _ v_copy) (data_at _ _ _ v_frames) (data_at _ _ _ v_aliases) (data_at _ _ _ v_result) (has_ext _).
sep_apply (data_at_data_at_ Tsh t_root (root_val cv) v_copy0).
thaw F.
freeze F := (data_at_ _ _ v_source) (data_at_ _ _ v_source0) (data_at_ _ _ v_closed) (data_at_ _ _ v_closed0) (data_at_ _ _ v_copy) (data_at_ _ _ v_copy0) (data_at _ _ _ v_aliases) (data_at _ _ _ v_result) (has_ext _).
sep_apply (data_at_data_at_ Tsh (tarray tulong 16) (longs fs) v_frames).
thaw F.
freeze F := (data_at_ _ _ v_source) (data_at_ _ _ v_source0) (data_at_ _ _ v_closed) (data_at_ _ _ v_closed0) (data_at_ _ _ v_copy) (data_at_ _ _ v_copy0) (data_at_ _ _ v_frames) (data_at _ _ _ v_result) (has_ext _).
sep_apply (data_at_data_at_ Tsh (tarray t_alias 2) (map alias_val al) v_aliases).
thaw F.
freeze F := (data_at_ _ _ v_source) (data_at_ _ _ v_source0) (data_at_ _ _ v_closed) (data_at_ _ _ v_closed0) (data_at_ _ _ v_copy) (data_at_ _ _ v_copy0) (data_at_ _ _ v_frames) (data_at_ _ _ v_aliases) (has_ext _).
sep_apply (data_at_data_at_ Tsh t_result (Vlong (Int64.repr r0), (Vlong (Int64.repr r1), (Vlong (Int64.repr r2), Vlong (Int64.repr r3)))) v_result).
thaw F.
forward.
Exists (Int.repr 0).
entailer!.
}
{
assert (S0: status = 0) by (first [ assumption | lia ]).
rewrite (proj2 (Z.eqb_eq status 0) S0).
cbv beta iota.
Transparent build_ok inventory_ok aliases_ok.
assert (BO: build_ok src sp kp cp fs n al m = true) by (apply Hst in S0; tauto).
assert (Hinv: inventory_ok fs n = true) by (unfold build_ok in BO; repeat (apply andb_prop in BO; destruct BO as [BO ?]); assumption).
assert (Hali: aliases_ok src (sublist 0 n fs) al m = true) by (unfold build_ok in BO; apply andb_prop in BO; destruct BO as [_ BO]; exact BO).
assert (Hn16: 1 <= n <= 16) by (clear - Hinv; unfold inventory_ok in Hinv; bhyp; lia).
assert (Hm2: 1 <= m <= 2) by (clear - Hali; unfold aliases_ok in Hali; bhyp; lia).
Opaque build_ok inventory_ok aliases_ok.
assert (RS: root_ok src) by assumption.
destruct RS as (L1 & L2 & L3 & L4 & W1 & W2 & W3 & W4).
unfold LEAVES in L4.
assert (ZC: forall q, 0 <= q < 4096 -> Znth q (pt (closed_out src (sublist 0 n fs) kp)) = closed_leaf (sublist 0 n fs) (Znth q (pt src))) by (intros q Hq; unfold closed_out, built_root; cbn [pt]; rewrite Znth_map by lia; reflexivity).
assert (ZP: forall q, 0 <= q < 4096 -> Znth q (pt (copy_out src (sublist 0 n fs) (sublist 0 m al) cp)) = pick (sublist 0 m al) q (closed_leaf (sublist 0 n fs) (Znth q (pt src)))) by (intros q Hq; unfold copy_out, built_root; cbn [pt]; rewrite Znth_install by (rewrite Zlength_map; lia); rewrite Znth_map by lia; reflexivity).
assert (OKC: root_ok (closed_out src (sublist 0 n fs) kp)) by (apply root_ok_closed; auto).
assert (OKP: root_ok (copy_out src (sublist 0 n fs) (sublist 0 m al) cp)) by (apply root_ok_copy; auto).
Opaque closed_out copy_out removed_count retained_count.
freeze FR := (data_at _ _ _ v_source) (data_at _ _ _ v_source0) (data_at _ _ _ v_closed0) (data_at _ _ _ v_copy) (data_at _ _ _ v_copy0) (data_at _ _ _ v_frames) (data_at _ _ _ v_aliases) (data_at _ _ _ v_result) (has_ext _).
forward_call (v_closed, Tsh, closed_out src (sublist 0 n fs) kp, kp, 0).
all: try (unfold word_ok in *; rep_lia).
forward_call (Int.one).
Transparent closed_out tables_ok.
all: try (entailer!; unfold closed_out; rewrite tables_ok_built; reflexivity).
Opaque closed_out tables_ok.
thaw FR.
freeze FR := (data_at _ _ _ v_source) (data_at _ _ _ v_source0) (data_at _ _ _ v_closed) (data_at _ _ _ v_closed0) (data_at _ _ _ v_copy0) (data_at _ _ _ v_frames) (data_at _ _ _ v_aliases) (data_at _ _ _ v_result) (has_ext _).
forward_call (v_copy, Tsh, copy_out src (sublist 0 n fs) (sublist 0 m al) cp, cp, 0).
all: try (unfold word_ok in *; rep_lia).
forward_call (Int.one).
Transparent copy_out tables_ok.
all: try (entailer!; unfold copy_out; rewrite tables_ok_built; reflexivity).
Opaque copy_out tables_ok.
thaw FR.
forward.
forward.
assert (FW: forall s, word_ok s -> word_ok (frame_of s)).
{
intros s Hs.
pose proof (land_word s ADDRESS_MASK Hs) as Hl.
unfold frame_of, word_ok in *.
rewrite Z.shiftr_div_pow2 by lia.
change (2 ^ 12) with 4096.
split; [ apply Z.div_pos; lia | ].
apply Z.le_trans with (Z.land s ADDRESS_MASK); [ apply Z.div_le_upper_bound; lia | lia ].
}
assert (SH: forall s, word_ok s -> Int64.shru (Int64.and (Int64.repr s) (Int64.repr 4503599627366400)) (Int64.repr 12) = Int64.repr (frame_of s)).
{
intros s Hs.
rewrite and_repr.
unfold Int64.shru.
rewrite (Int64.unsigned_repr (Z.land _ _)) by (apply land_word; auto).
rewrite (Int64.unsigned_repr 12) by rep_lia.
reflexivity.
}
assert (OD: forall s, Int64.and (Int64.repr s) (Int64.repr 1) = Int64.repr (if Z.odd s then 1 else 0)).
{
intros s.
rewrite and_repr, land_1.
reflexivity.
}
assert (PA: forall (l1 l2: list alias) q d, pick (l1 ++ l2) q d = pick l2 q (pick l1 q d)).
{
induction l1 as [ | a t IH ]; intros; simpl; auto.
}
assert (LM: forall x a b c, Int64.repr (Z.lor (Z.lor (Z.lor (x mod W) a) b) c) = Int64.repr (Z.lor (Z.lor (Z.lor x a) b) c)).
{
intros.
apply Int64.same_bits_eq.
intros i Hi.
rewrite !Int64.testbit_repr by lia.
rewrite !Z.lor_spec.
unfold W.
change Int64.modulus with (2 ^ 64).
rewrite Z.mod_pow2_bits_low; auto.
change Int64.zwordsize with 64 in Hi.
lia.
}
assert (AL: forall pg fr wr, 0 <= fr <= Int64.max_unsigned -> 0 <= wr <= 1 -> Int64.or (Int64.or (Int64.or (Int64.shl (Int64.repr fr) (Int64.repr 12)) (Int64.repr 1)) (Int64.shl (Int64.repr 1) (Int64.repr 63))) (Int64.repr (if wr =? 1 then 2 else 0)) = Int64.repr (alias_leaf (mkalias pg fr wr))).
{
intros pg fr wr Hf Hw.
unfold alias_leaf; cbn [a_frame a_writable].
unfold Int64.shl.
rewrite (Int64.unsigned_repr fr) by lia.
rewrite (Int64.unsigned_repr 12) by rep_lia.
rewrite (Int64.unsigned_repr 1) by rep_lia.
rewrite (Int64.unsigned_repr 63) by rep_lia.
rewrite !or_repr.
rewrite LM.
rewrite (Z.shiftl_mul_pow2 fr 12) by lia.
change (2 ^ 12) with 4096.
change (Z.shiftl 1 63) with NX.
f_equal.
f_equal.
destruct (Z.eqb_spec wr 1), (Z.eqb_spec wr 0); try lia; reflexivity.
}
freeze FR := (data_at _ _ _ v_source0) (data_at _ _ _ v_closed0) (data_at _ _ _ v_copy0) (data_at _ _ _ v_result) (has_ext _).
forward_for_simple_bound 4096 (@exp (environ -> mpred) _ Z (fun j => PROP () LOCAL (temp _removed (Vlong (Int64.repr (removed_count (sublist 0 n fs) (sublist 0 j (pt src))))); temp _retained (Vlong (Int64.repr (retained_count (sublist 0 n fs) (sublist 0 j (pt src))))); temp _m (Vlong (Int64.repr m)); temp _n (Vlong (Int64.repr n)); lvar _result (Tstruct _qotom_root_build_result noattr) v_result; lvar _aliases (tarray (Tstruct _qotom_copy_alias noattr) 2) v_aliases; lvar _frames (tarray tulong 16) v_frames; lvar _copy0 (Tstruct _qotom_root_pages noattr) v_copy0; lvar _copy (Tstruct _qotom_root_pages noattr) v_copy; lvar _closed0 (Tstruct _qotom_root_pages noattr) v_closed0; lvar _closed (Tstruct _qotom_root_pages noattr) v_closed; lvar _source0 (Tstruct _qotom_root_pages noattr) v_source0; lvar _source (Tstruct _qotom_root_pages noattr) v_source; gvars gv) SEP (data_at Tsh t_root (root_val src) v_source; data_at Tsh t_root (root_val (closed_out src (sublist 0 n fs) kp)) v_closed; data_at Tsh t_root (root_val (copy_out src (sublist 0 n fs) (sublist 0 m al) cp)) v_copy; data_at Tsh (tarray tulong (Zlength fs)) (longs fs) v_frames; data_at Tsh (tarray t_alias (Zlength al)) (map alias_val al) v_aliases; FRZL FR))).
{
entailer!.
}
assert (Ws: word_ok (Znth i (pt src))) by (apply word_Znth; auto; lia).
freeze F1 := (data_at _ _ _ v_closed) (data_at _ _ _ v_copy) (data_at _ _ _ v_frames) (data_at _ _ _ v_aliases) (FRZL FR).
forward.
{ match goal with |- context [tc_val tulong (Znth i ?L)] => change L with (longs (pt src)) end. entailer!. rewrite Znth_longs by lia. simpl; auto. }
match goal with |- context [temp _s (Znth i ?L)] => change L with (longs (pt src)) end.
rewrite Znth_longs by lia.
thaw F1.
forward_if (temp _t'59 (Vint (Int.repr (b2z (removes (sublist 0 n fs) (Znth i (pt src))))))).
{
match goal with H: Int64.and _ _ <> _ |- _ => rewrite OD in H end.
assert (Odd: Z.odd (Znth i (pt src)) = true) by (destruct (Z.odd (Znth i (pt src))); [ reflexivity | exfalso; match goal with H: Int64.repr 0 <> Int64.repr 0 |- _ => apply H; reflexivity end ]).
freeze F2 := (data_at _ _ _ v_source) (data_at _ _ _ v_closed) (data_at _ _ _ v_copy) (data_at _ _ _ v_aliases) (FRZL FR).
forward_call (frame_of (Znth i (pt src)), v_frames, Tsh, fs, n).
all: try (entailer!; rewrite SH by auto; reflexivity).
all: try (apply FW; auto).
all: try (unfold word_ok in *; rep_lia).
entailer!.
simpl.
do 3 f_equal. unfold Int64.shru. rewrite (Int64.unsigned_repr (Z.land _ _)) by (apply land_word; auto). rewrite (Int64.unsigned_repr 12) by rep_lia. reflexivity.
thaw F2.
forward.
entailer!.
unfold removes.
rewrite Odd.
destruct (member (frame_of (Znth i (pt src))) (sublist 0 n fs)); reflexivity.
}
{
match goal with H: Int64.and _ _ = _ |- _ => rewrite OD in H end.
assert (Odd: Z.odd (Znth i (pt src)) = false) by (match goal with H: Int64.repr (if Z.odd _ then 1 else 0) = Int64.zero |- _ => revert H end; destruct (Z.odd (Znth i (pt src))); intro HH; [ apply (f_equal Int64.unsigned) in HH; vm_compute in HH; discriminate HH | reflexivity ]).
forward.
entailer!.
unfold removes.
rewrite Odd.
reflexivity.
}
forward.
forward_if (temp _t'61 (Vlong (Int64.repr (closed_leaf (sublist 0 n fs) (Znth i (pt src)))))).
{
forward.
entailer!.
unfold closed_leaf.
match goal with H: removes _ _ = true |- _ => rewrite H end.
reflexivity.
}
{
forward.
entailer!.
unfold closed_leaf.
match goal with H: removes _ _ = false |- _ => rewrite H end.
reflexivity.
}
forward.
freeze F1 := (data_at _ _ _ v_source) (data_at _ _ _ v_copy) (data_at _ _ _ v_frames) (data_at _ _ _ v_aliases) (FRZL FR).
forward.
{ match goal with |- context [tc_val tulong (Znth i ?L)] => change L with (longs (pt (closed_out src (sublist 0 n fs) kp))) end. entailer!. rewrite Znth_longs by (destruct OKC as (_&_&_&LK&_); unfold LEAVES in LK; lia). simpl; auto. }
match goal with |- context [temp _t'74 (Znth i ?L)] => change L with (longs (pt (closed_out src (sublist 0 n fs) kp))) end.
rewrite Znth_longs by (destruct OKC as (_&_&_&LK&_); unfold LEAVES in LK; lia).
rewrite ZC by lia.
thaw F1.
freeze FA := (data_at _ _ _ v_source) (data_at _ _ _ v_closed) (data_at _ _ _ v_copy) (data_at _ _ _ v_frames) (data_at _ _ _ v_aliases) (FRZL FR).
forward_call (Int.one).
all: try (entailer!; rewrite ?Int64.eq_true; reflexivity).
forward.
thaw FA.
assert (AOK: forall k, 0 <= k < m -> alias_ok src (sublist 0 n fs) (Znth k al) = true).
{
intros k Hk.
Transparent aliases_ok.
unfold aliases_ok in Hali.
Opaque aliases_ok.
apply andb_prop in Hali; destruct Hali as [Hali _].
apply andb_prop in Hali; destruct Hali as [Hali _].
apply andb_prop in Hali; destruct Hali as [_ Hf].
rewrite forallb_forall in Hf.
replace (Znth k al) with (Znth k (sublist 0 m al)) by (rewrite Znth_sublist by lia; f_equal; lia).
apply Hf.
apply Znth_In.
rewrite Zlength_sublist by lia.
lia.
}
freeze FA := (data_at _ _ _ v_source) (data_at _ _ _ v_closed) (data_at _ _ _ v_copy) (data_at _ _ _ v_frames) (FRZL FR).
forward_for_simple_bound m (@exp (environ -> mpred) _ Z (fun k => PROP () LOCAL (temp _copy_want (Vlong (Int64.repr (pick (sublist 0 k al) i (closed_leaf (sublist 0 n fs) (Znth i (pt src)))))); temp _gone (Vint (Int.repr (b2z (removes (sublist 0 n fs) (Znth i (pt src)))))); temp _s (Vlong (Int64.repr (Znth i (pt src)))); temp _p (Vlong (Int64.repr i)); temp _removed (Vlong (Int64.repr (removed_count (sublist 0 n fs) (sublist 0 i (pt src))))); temp _retained (Vlong (Int64.repr (retained_count (sublist 0 n fs) (sublist 0 i (pt src))))); temp _m (Vlong (Int64.repr m)); temp _n (Vlong (Int64.repr n)); lvar _result (Tstruct _qotom_root_build_result noattr) v_result; lvar _aliases (tarray (Tstruct _qotom_copy_alias noattr) 2) v_aliases; lvar _frames (tarray tulong 16) v_frames; lvar _copy0 (Tstruct _qotom_root_pages noattr) v_copy0; lvar _copy (Tstruct _qotom_root_pages noattr) v_copy; lvar _closed0 (Tstruct _qotom_root_pages noattr) v_closed0; lvar _closed (Tstruct _qotom_root_pages noattr) v_closed; lvar _source0 (Tstruct _qotom_root_pages noattr) v_source0; lvar _source (Tstruct _qotom_root_pages noattr) v_source; gvars gv) SEP (data_at Tsh (tarray t_alias (Zlength al)) (map alias_val al) v_aliases; FRZL FA))).
{
entailer!.
}
assert (Ak := AOK i0 H23).
destruct (Znth i0 al) as [pg fr wr] eqn:Ek.
unfold alias_ok in Ak. cbn [a_page a_frame a_writable] in Ak. unfold LEAVES in Ak.
assert (Wk: alias_wf (Znth i0 al)) by (apply (Forall_Znth al alias_wf); auto; lia).
rewrite Ek in Wk. destruct Wk as (Wp & Wf & Ww). cbn [a_page a_frame a_writable] in Wp, Wf, Ww.
assert (Hpg: pg < 4096 /\ wr <= 1) by (repeat (apply andb_prop in Ak; destruct Ak as [Ak ?]); split; [ apply Z.ltb_lt | apply Z.leb_le ]; assumption).
forward.
{ rewrite Znth_alias_val, Ek, alias_val_eq by lia. cbv iota. entailer!. }
rewrite Znth_alias_val, Ek, alias_val_eq by lia.
cbv iota.
forward_if (temp _copy_want (Vlong (Int64.repr (pick (sublist 0 (i0 + 1) al) i (closed_leaf (sublist 0 n fs) (Znth i (pt src))))))).
{
w64.
subst pg.
forward.
{ rewrite Znth_alias_val, Ek, alias_val_eq by lia. cbv iota. entailer!. }
rewrite Znth_alias_val, Ek, alias_val_eq by lia.
cbv iota.
forward_if (temp _t'62 (Vlong (Int64.repr (if wr =? 1 then 2 else 0)))).
{ forward. entailer!. w64. subst wr. reflexivity. }
{ forward. entailer!. w64. rewrite (proj2 (Z.eqb_neq wr 1)) by auto. reflexivity. }
forward.
{ rewrite Znth_alias_val, Ek, alias_val_eq by lia. cbv iota. entailer!. }
rewrite Znth_alias_val, Ek, alias_val_eq by lia.
cbv iota.
forward.
entailer!.
rewrite (AL i fr wr) by (unfold word_ok in *; lia).
rewrite (sublist_last_1 0 i0 al) by lia.
rewrite PA, Ek.
cbn [pick a_page].
rewrite Z.eqb_refl.
reflexivity.
}
{ forward. entailer!. w64. rewrite (sublist_last_1 0 i0 al) by lia. rewrite PA, Ek. cbn [pick a_page]. rewrite (proj2 (Z.eqb_neq pg i)) by auto. reflexivity. }
entailer!.
thaw FA.
freeze F1 := (data_at _ _ _ v_source) (data_at _ _ _ v_closed) (data_at _ _ _ v_frames) (data_at _ _ _ v_aliases) (FRZL FR).
forward.
{
match goal with |- context [tc_val tulong (Znth i ?L)] => change L with (longs (pt (copy_out src (sublist 0 n fs) (sublist 0 m al) cp))) end.
entailer!.
rewrite Znth_longs by (destruct OKP as (_&_&_&LK&_); unfold LEAVES in LK; lia).
simpl; auto.
}
match goal with |- context [temp _t'70 (Znth i ?L)] => change L with (longs (pt (copy_out src (sublist 0 n fs) (sublist 0 m al) cp))) end.
rewrite Znth_longs by (destruct OKP as (_&_&_&LK&_); unfold LEAVES in LK; lia).
rewrite ZP by lia.
thaw F1.
freeze FA := (data_at _ _ _ v_source) (data_at _ _ _ v_closed) (data_at _ _ _ v_copy) (data_at _ _ _ v_frames) (data_at _ _ _ v_aliases) (FRZL FR).
forward_call (Int.one).
all: try (entailer!; rewrite ?Int64.eq_true; reflexivity).
Transparent removed_count retained_count.
forward_if (PROP () LOCAL (temp _p (Vlong (Int64.repr i)); temp _removed (Vlong (Int64.repr (removed_count (sublist 0 n fs) (sublist 0 (i + 1) (pt src))))); temp _retained (Vlong (Int64.repr (retained_count (sublist 0 n fs) (sublist 0 (i + 1) (pt src))))); temp _m (Vlong (Int64.repr m)); temp _n (Vlong (Int64.repr n)); lvar _result (Tstruct _qotom_root_build_result noattr) v_result; lvar _aliases (tarray (Tstruct _qotom_copy_alias noattr) 2) v_aliases; lvar _frames (tarray tulong 16) v_frames; lvar _copy0 (Tstruct _qotom_root_pages noattr) v_copy0; lvar _copy (Tstruct _qotom_root_pages noattr) v_copy; lvar _closed0 (Tstruct _qotom_root_pages noattr) v_closed0; lvar _closed (Tstruct _qotom_root_pages noattr) v_closed; lvar _source0 (Tstruct _qotom_root_pages noattr) v_source0; lvar _source (Tstruct _qotom_root_pages noattr) v_source; gvars gv) SEP (FRZL FA)).
{
forward.
entailer!.
unfold removed_count, retained_count.
rewrite !(filter_step _ (pt src) i) by lia.
match goal with H: removes _ _ = true |- _ => rewrite H; unfold removes in H; apply andb_prop in H; destruct H as [Ho Hm] end.
rewrite Ho, Hm.
simpl.
split; f_equal; f_equal; lia.
}
forward_if (PROP () LOCAL (temp _p (Vlong (Int64.repr i)); temp _removed (Vlong (Int64.repr (removed_count (sublist 0 n fs) (sublist 0 (i + 1) (pt src))))); temp _retained (Vlong (Int64.repr (retained_count (sublist 0 n fs) (sublist 0 (i + 1) (pt src))))); temp _m (Vlong (Int64.repr m)); temp _n (Vlong (Int64.repr n)); lvar _result (Tstruct _qotom_root_build_result noattr) v_result; lvar _aliases (tarray (Tstruct _qotom_copy_alias noattr) 2) v_aliases; lvar _frames (tarray tulong 16) v_frames; lvar _copy0 (Tstruct _qotom_root_pages noattr) v_copy0; lvar _copy (Tstruct _qotom_root_pages noattr) v_copy; lvar _closed0 (Tstruct _qotom_root_pages noattr) v_closed0; lvar _closed (Tstruct _qotom_root_pages noattr) v_closed; lvar _source0 (Tstruct _qotom_root_pages noattr) v_source0; lvar _source (Tstruct _qotom_root_pages noattr) v_source; gvars gv) SEP (FRZL FA)).
{
forward.
entailer!.
unfold removed_count, retained_count.
rewrite !(filter_step _ (pt src) i) by lia.
assert (Od: Z.odd (Znth i (pt src)) = true) by (match goal with H: Int64.repr (Z.land _ 1) <> _ |- _ => rewrite land_1 in H; revert H end; destruct (Z.odd (Znth i (pt src))); intro HH; [ reflexivity | exfalso; apply HH; reflexivity ]).
match goal with H: removes _ _ = false |- _ => rewrite H; unfold removes in H; rewrite Od in H; simpl in H; rewrite H end.
rewrite Od. simpl. split; f_equal; f_equal; lia.
}
{ forward. entailer!. unfold removed_count, retained_count. rewrite !(filter_step _ (pt src) i) by lia.
assert (Od: Z.odd (Znth i (pt src)) = false) by (match goal with H: Int64.repr (Z.land _ 1) = Int64.zero |- _ => rewrite land_1 in H; revert H end; destruct (Z.odd (Znth i (pt src))); intro HH; [ apply (f_equal Int64.unsigned) in HH; vm_compute in HH; discriminate HH | reflexivity ]).
match goal with H: removes _ _ = false |- _ => rewrite H end. rewrite Od. simpl. split; f_equal; f_equal; lia. }
thaw FA.
Opaque removed_count retained_count.
entailer!.
rewrite (sublist_same 0 4096 (pt src)) by lia.
thaw FR.
unfold result_val.
freeze FR := (data_at _ _ _ v_source) (data_at _ _ _ v_source0) (data_at _ _ _ v_closed) (data_at _ _ _ v_closed0) (data_at _ _ _ v_copy) (data_at _ _ _ v_copy0) (data_at _ _ _ v_frames) (data_at _ _ _ v_aliases) (has_ext _).
forward.
forward_if (temp _t'63 (Vint Int.one)).
{
forward.
forward.
entailer!.
all: try (unfold Int64.cmpu; rewrite Int64.eq_true; reflexivity).
}
{
exfalso.
match goal with H: ?x <> ?x |- _ => apply H; reflexivity end.
}
forward_if (temp _t'64 (Vint Int.one)).
{
forward.
forward.
entailer!.
all: try (unfold Int64.cmpu; rewrite Int64.eq_true; reflexivity).
}
{
exfalso.
match goal with H: ?x = ?y |- _ => discriminate H end.
}
forward_if (temp _t'65 (Vint Int.one)).
{
forward.
forward.
entailer!.
all: try (unfold Int64.cmpu; rewrite Int64.eq_true; reflexivity).
}
{
exfalso.
match goal with H: ?x = ?y |- _ => discriminate H end.
}
forward_call (Int.one).
thaw FR.
rewrite <- R16, <- R2.
freeze F := (data_at _ _ _ v_source0) (data_at _ _ _ v_closed) (data_at _ _ _ v_closed0) (data_at _ _ _ v_copy) (data_at _ _ _ v_copy0) (data_at _ _ _ v_frames) (data_at _ _ _ v_aliases) (data_at _ _ _ v_result) (has_ext _).
sep_apply (data_at_data_at_ Tsh t_root (root_val src) v_source).
thaw F.
freeze F := (data_at_ _ _ v_source) (data_at _ _ _ v_closed) (data_at _ _ _ v_closed0) (data_at _ _ _ v_copy) (data_at _ _ _ v_copy0) (data_at _ _ _ v_frames) (data_at _ _ _ v_aliases) (data_at _ _ _ v_result) (has_ext _).
sep_apply (data_at_data_at_ Tsh t_root (root_val src) v_source0).
thaw F.
freeze F := (data_at_ _ _ v_source) (data_at_ _ _ v_source0) (data_at _ _ _ v_closed0) (data_at _ _ _ v_copy) (data_at _ _ _ v_copy0) (data_at _ _ _ v_frames) (data_at _ _ _ v_aliases) (data_at _ _ _ v_result) (has_ext _).
sep_apply (data_at_data_at_ Tsh t_root (root_val (closed_out src (sublist 0 n fs) kp)) v_closed).
thaw F.
freeze F := (data_at_ _ _ v_source) (data_at_ _ _ v_source0) (data_at_ _ _ v_closed) (data_at _ _ _ v_copy) (data_at _ _ _ v_copy0) (data_at _ _ _ v_frames) (data_at _ _ _ v_aliases) (data_at _ _ _ v_result) (has_ext _).
sep_apply (data_at_data_at_ Tsh t_root (root_val kv) v_closed0).
thaw F.
freeze F := (data_at_ _ _ v_source) (data_at_ _ _ v_source0) (data_at_ _ _ v_closed) (data_at_ _ _ v_closed0) (data_at _ _ _ v_copy0) (data_at _ _ _ v_frames) (data_at _ _ _ v_aliases) (data_at _ _ _ v_result) (has_ext _).
sep_apply (data_at_data_at_ Tsh t_root (root_val (copy_out src (sublist 0 n fs) (sublist 0 m al) cp)) v_copy).
thaw F.
freeze F := (data_at_ _ _ v_source) (data_at_ _ _ v_source0) (data_at_ _ _ v_closed) (data_at_ _ _ v_closed0) (data_at_ _ _ v_copy) (data_at _ _ _ v_frames) (data_at _ _ _ v_aliases) (data_at _ _ _ v_result) (has_ext _).
sep_apply (data_at_data_at_ Tsh t_root (root_val cv) v_copy0).
thaw F.
freeze F := (data_at_ _ _ v_source) (data_at_ _ _ v_source0) (data_at_ _ _ v_closed) (data_at_ _ _ v_closed0) (data_at_ _ _ v_copy) (data_at_ _ _ v_copy0) (data_at _ _ _ v_aliases) (data_at _ _ _ v_result) (has_ext _).
sep_apply (data_at_data_at_ Tsh (tarray tulong 16) (longs fs) v_frames).
thaw F.
freeze F := (data_at_ _ _ v_source) (data_at_ _ _ v_source0) (data_at_ _ _ v_closed) (data_at_ _ _ v_closed0) (data_at_ _ _ v_copy) (data_at_ _ _ v_copy0) (data_at_ _ _ v_frames) (data_at _ _ _ v_result) (has_ext _).
sep_apply (data_at_data_at_ Tsh (tarray t_alias 2) (map alias_val al) v_aliases).
thaw F.
freeze F := (data_at_ _ _ v_source) (data_at_ _ _ v_source0) (data_at_ _ _ v_closed) (data_at_ _ _ v_closed0) (data_at_ _ _ v_copy) (data_at_ _ _ v_copy0) (data_at_ _ _ v_frames) (data_at_ _ _ v_aliases) (has_ext _).
sep_apply (data_at_data_at_ Tsh t_result (Vlong (Int64.repr n), (Vlong (Int64.repr (removed_count (sublist 0 n fs) (pt src))), (Vlong (Int64.repr (retained_count (sublist 0 n fs) (pt src))), Vlong (Int64.repr m)))) v_result).
thaw F.
forward.
Exists (Int.repr 0).
entailer!.
}
Qed.
