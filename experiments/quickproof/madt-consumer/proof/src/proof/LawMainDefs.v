(* Law consumer_obligations: what the parts of the proof of main share: main's context, its return assertion, the
   statement after the call of madt_bind (the checks), and the entry tactic of the tail lemmas. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import LeanosMadt.harness.consumer_obligations.code.
Require Import LeanosMadt.proof.Defs.
Require Import LeanosMadt.proof.MadtSpecs.
Require Import LeanosMadt.proof.LawProg LeanosMadt.proof.LawDefs.
Local Open Scope Z_scope.
#[export] Existing Instance LawProg.LCS.

Definition Gmain : funspecs :=
  [any_u64_spec; records_ok_spec; madt_bind_spec Ora_law;
   nondet_u8_spec; nondet_size_spec; nondet_bytes_spec; gp_assert_spec; (_quickproof_malloc, malloc_spec')].

(* main's type context and return assertion, as start_function makes them. *)
Definition Delta0 : tycontext := func_tycontext f_main Vlaw Gmain nil.
Definition Post0 : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* The statement of main after `status = madt_bind(...)` (then main's final return, which VST keeps as the rest
   of the outer sequence). *)
Definition s_after_call : statement := ltac:(
  let b := eval cbv delta [f_main] beta iota zeta in (fn_body f_main) in
  match b with
  | context [Ssequence (Ssequence (Scall (Some _t'25) _ _) (Sset _status (Etempvar _t'25 tulong))) ?rest] =>
      exact (Ssequence rest (Sreturn (Some (Econst_int (Int.repr 0) tint))))
  end).

(* Enter a tail lemma: VST's canonical form of the goal, as start_function leaves it. *)
Ltac start_tail :=
  unfold Delta0, Post0;
  repeat match goal with
  | |- context [Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s) Sskip] => fold (Swhile e s)
  | |- context [Ssequence ?s1 (Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s2) ?s3) ] =>
      match s3 with
      | Sset ?i _ => match s1 with Sset ?i' _ => unify i i' | Sskip => idtac end
      end;
      fold (Sfor s1 e s2 s3)
  end;
  simplify_func_tycontext;
  abbreviate_semax.

(* The statement of main from `o->entries = entries` (the oracle's setup, the record walk, the call and the
   checks), then main's final return. *)
Definition s_init : statement := ltac:(
  let b := eval cbv delta [f_main] beta iota zeta in (fn_body f_main) in
  match b with
  | context [Ssequence (Sassign (Efield (Ederef (Etempvar _o ?t1) ?t2) _entries ?t3) (Etempvar _entries ?t4)) ?rest] =>
      exact (Ssequence (Ssequence (Sassign (Efield (Ederef (Etempvar _o t1) t2) _entries t3) (Etempvar _entries t4)) rest)
                       (Sreturn (Some (Econst_int (Int.repr 0) tint))))
  end).

(* The statement of main from the call of madt_bind, then main's final return. *)
Definition s_call : statement := ltac:(
  let b := eval cbv delta [f_main] beta iota zeta in (fn_body f_main) in
  match b with
  | context [Ssequence (Ssequence (Scall (Some _t'25) ?f ?a) (Sset _status (Etempvar _t'25 tulong))) ?rest] =>
      exact (Ssequence (Ssequence (Ssequence (Scall (Some _t'25) f a) (Sset _status (Etempvar _t'25 tulong))) rest)
                       (Sreturn (Some (Econst_int (Int.repr 0) tint))))
  end).
