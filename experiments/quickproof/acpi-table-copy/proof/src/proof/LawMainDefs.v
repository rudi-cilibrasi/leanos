(* Law table_copy_exact: what the parts of the proof of main share: main's context, its return assertion, the
   statements from each cut point of main's body (then main's final return), and the entry tactic. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import LeanosAcpi.harness.table_copy_exact.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.LawProg LeanosAcpi.proof.LawDefs LeanosAcpi.proof.LawOra LeanosAcpi.proof.LawVerdict
  LeanosAcpi.proof.LawMainLib.
Local Open Scope Z_scope.
#[export] Existing Instance LawProg.LCS.

Definition Gmain : funspecs :=
  [any_u64_spec; stop_spec; begin_sdt_spec; madt_verdict_spec'; padded_spec; firmware_spec; pipeline_spec Ora_law;
   nondet_u32_spec; nondet_bytes_spec; gp_assert_spec; (_quickproof_malloc, malloc_spec')].

Definition Vmain : varspecs :=
  [(sl2, tarray tschar 5); (sl1, tarray tschar 5); (sl3, tarray tschar 5); (_law, t_law)].

(* main's type context and return assertion, as start_function makes them. *)
Definition Delta0 : tycontext := func_tycontext f_main Vmain Gmain nil.
Definition Post0 : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

Definition main_body : statement := ltac:(let b := eval cbv delta [f_main] beta iota zeta in (fn_body f_main) in exact b).

(* main from nondet_bytes(m->header, 36) on. *)
Definition s_bytes : statement := ltac:(
  let b := eval cbv delta [main_body] in main_body in
  match b with
  | context [Ssequence (Ssequence (Sset _t'135 ?e) ?c) ?rest] =>
      exact (Ssequence (Ssequence (Ssequence (Sset _t'135 e) c) rest) (Sreturn (Some (Econst_int (Int.repr 0) tint))))
  end).

(* main from its loop that zeroes the copy slots on. *)
Definition s_slots0 : statement := ltac:(
  let b := eval cbv delta [main_body] in main_body in
  match b with
  | context [Ssequence (Ssequence (Sset _t (Econst_int (Int.repr 0) tint)) ?l) ?rest] =>
      exact (Ssequence (Ssequence (Ssequence (Sset _t (Econst_int (Int.repr 0) tint)) l) rest)
                       (Sreturn (Some (Econst_int (Int.repr 0) tint))))
  end).

(* main from m->root_done = 0 on. *)
Definition s_fields : statement := ltac:(
  let b := eval cbv delta [main_body] in main_body in
  match b with
  | context [Ssequence (Sassign (Efield ?e _root_done tuint) ?v) ?rest] =>
      exact (Ssequence (Ssequence (Sassign (Efield e _root_done tuint) v) rest)
                       (Sreturn (Some (Econst_int (Int.repr 0) tint))))
  end).

(* main from the call of acpi_pipeline on. *)
Definition s_call : statement := ltac:(
  let b := eval cbv delta [main_body] in main_body in
  match b with
  | context [Ssequence (Ssequence (Ssequence (Sset _t'106 ?e) ?c) ?d) ?rest] =>
      exact (Ssequence (Ssequence (Ssequence (Ssequence (Sset _t'106 e) c) d) rest)
                       (Sreturn (Some (Econst_int (Int.repr 0) tint))))
  end).

(* main from its check of the header scratch on. *)
Definition s_bytes_check : statement := ltac:(
  let b := eval cbv delta [main_body] in main_body in
  match b with
  | context [Ssequence (Ssequence (Sset _i__3 ?e) ?l) ?rest] =>
      exact (Ssequence (Ssequence (Ssequence (Sset _i__3 e) l) rest) (Sreturn (Some (Econst_int (Int.repr 0) tint))))
  end).

(* main from its check of the result's root on. *)
Definition s_root_check : statement := ltac:(
  let b := eval cbv delta [main_body] in main_body in
  match b with
  | context [Ssequence (Ssequence (Sset _t'77 ?e) ?c) ?rest] =>
      exact (Ssequence (Ssequence (Ssequence (Sset _t'77 e) c) rest) (Sreturn (Some (Econst_int (Int.repr 0) tint))))
  end).

(* main from its check of the copy slots on. *)
Definition s_slots_check : statement := ltac:(
  let b := eval cbv delta [main_body] in main_body in
  match b with
  | context [Ssequence (Ssequence (Sset _t__1 ?e) ?l) ?rest] =>
      exact (Ssequence (Ssequence (Ssequence (Sset _t__1 e) l) rest) (Sreturn (Some (Econst_int (Int.repr 0) tint))))
  end).

(* main from its check of the status (OK or not) on. *)
Definition s_status_check : statement := ltac:(
  let b := eval cbv delta [main_body] in main_body in
  match b with
  | context [Ssequence (Sifthenelse (Ebinop Cop.One (Etempvar _status tint) ?z tint) ?th Sskip) ?rest] =>
      exact (Ssequence (Ssequence (Sifthenelse (Ebinop Cop.One (Etempvar _status tint) z tint) th Sskip) rest)
                       (Sreturn (Some (Econst_int (Int.repr 0) tint))))
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
