(* Law window_roots_isolated: main's context, its statements that the segment lemmas prove, and the
   representations main's proof uses. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Import LeanosRoots.proof.Defs.
Require Import LeanosRoots.proof.RootsSpecs.
Require Import LeanosRoots.proof.Law2Model.
Require Import LeanosRoots.proof.Law2Helpers.
Require Import LeanosRoots.harness.window_roots_isolated.code.
#[local] Existing Instance RootsSpecs.CS.

Definition Gmain : funspecs :=
  [h_member_spec; h_phys_ok_spec; h_apart_spec; h_table_spec; h_tables_at_spec; h_inventory_ok_spec;
   h_geometry_ok_spec; window_build_spec; nondet_size_spec; nondet_u32_spec; gp_assert_spec].

Definition Dm : tycontext := func_tycontext f_main nil Gmain nil.

Definition s_loop1 : statement := ltac:(let b := eval cbv delta [f_main] in f_main in
  match b with context [Ssequence (Sset _i ?e) (Sloop ?x ?y)] => exact (Ssequence (Sset _i e) (Sloop x y)) end).
Definition s_loop2 : statement := ltac:(let b := eval cbv delta [f_main] in f_main in
  match b with context [Ssequence (Sset _i__1 ?e) (Sloop ?x ?y)] => exact (Ssequence (Sset _i__1 e) (Sloop x y)) end).
Definition s_loop3 : statement := ltac:(let b := eval cbv delta [f_main] in f_main in
  match b with context [Ssequence (Sset _i__2 ?e) (Sloop ?x ?y)] => exact (Ssequence (Sset _i__2 e) (Sloop x y)) end).
Definition s_valid : statement := ltac:(let b := eval cbv delta [f_main] in f_main in
  match b with context [Ssequence ?x (Sset _valid (Etempvar _t'42 tint))] =>
    exact (Ssequence x (Sset _valid (Etempvar _t'42 tint))) end).
Definition s_slots : statement := ltac:(let b := eval cbv delta [f_main] in f_main in
  match b with context [Sifthenelse (Etempvar _valid tint) (Ssequence (Sset _i__3 ?e) ?l) Sskip] =>
    exact (Sifthenelse (Etempvar _valid tint) (Ssequence (Sset _i__3 e) l) Sskip) end).
Definition s_counts : statement := ltac:(let b := eval cbv delta [f_main] in f_main in
  match b with context [Sifthenelse (Etempvar _valid tint) (Ssequence (Ssequence (Sset _p ?e) ?l) ?r) Sskip] =>
    exact (Sifthenelse (Etempvar _valid tint) (Ssequence (Ssequence (Sset _p e) l) r) Sskip) end).
Definition s_final : statement := ltac:(let b := eval cbv delta [f_main] in f_main in
  match b with context [Ssequence (Sset _p__1 ?e) (Sloop ?x ?y)] => exact (Ssequence (Sset _p__1 e) (Sloop x y)) end).

Definition root_part (a b c d: list val) : reptype t_root := (a, (b, (c, d))).

Lemma words_app1: forall l x, words_ok l -> 0 <= x <= Int64.max_unsigned -> words_ok (l ++ [x]).
Proof. intros. apply Forall_app. split; auto. Qed.

Lemma longs_app1: forall l x, longs (l ++ [x]) = longs l ++ [Vlong (Int64.repr x)].
Proof. intros. unfold longs. rewrite map_app. reflexivity. Qed.

Lemma Zlength_longs': forall l, Zlength (longs l) = Zlength l.
Proof. intros. unfold longs. apply Zlength_map. Qed.
