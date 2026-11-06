(* Law enumeration_exact: what the parts of the proof of main share: main's context, its tail after the scan
   (the statement that remains after `status = enum_scan(...)`), and tactics. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosEnum.harness.enumeration_exact.code.
Require Import LeanosEnum.proof.Defs.
Require LeanosEnum.proof.EnumSpecs.
Require Import LeanosEnum.proof.LawProg LeanosEnum.proof.LawRun LeanosEnum.proof.LawSpecs LeanosEnum.proof.LawSplit
  LeanosEnum.proof.LawLib.
Local Open Scope Z_scope.
#[export] Existing Instance LawProg.LCS.

Definition Gmain : funspecs :=
  [device_read_spec; EnumSpecs.enum_scan_spec Dev_exact; nondet_u8_spec; nondet_u32_spec; gp_assert_spec].

Definition t_snap := Tstruct _pci_enumeration_snapshot noattr.
Definition t_res := Tstruct _pci_enumeration_result noattr.

(* main's type context and return assertion, as start_function makes them. *)
Definition Delta0 : tycontext := func_tycontext f_main nil Gmain nil.
Definition Post0 : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* The statement of main after `status = enum_scan(...)` (then main's final return, which VST keeps as the
   rest of the outer sequence). *)
Definition s_after_call : statement := ltac:(
  let b := eval cbv delta [f_main] beta iota zeta in (fn_body f_main) in
  match b with
  | context [Ssequence (Ssequence (Scall (Some _t'12) _ _) (Sset _status (Etempvar _t'12 tint))) ?rest] =>
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

(* Rewrite the goal with the boolean facts of the context. *)
Ltac bsubst :=
  repeat match goal with
  | E: ?c = ?b |- context [?c] => match type of c with bool => rewrite E end
  end;
  simpl orb.

(* The value of (bool)(arg == NULL) for an argument p or NULL. *)
Ltac ptr_bool :=
  entailer!; bsubst;
  match goal with |- context [if ?b then nullval else ?p] =>
    destruct b; [ reflexivity | destruct p; try contradiction; reflexivity ] end.

Ltac tc_sel := entailer!; apply sel_tc_test; [ entailer! | auto ].

(* A check of the harness whose condition is 1 (or computes to it). *)
Ltac gp_call := forward_call (Int.one); try solve [ entailer!; simpl; rewrite ?Int.eq_true; reflexivity ].

Ltac free1 t p :=
  match goal with |- context [@data_at _ Tsh t ?v p] => sep_apply (data_at_data_at_ Tsh t v p) end.

(* located = result_arg != NULL. *)
Lemma sel_ne_val: forall (b: bool) p, isptr p ->
  force_val (sem_binary_operation' Cop.One (tptr (Tstruct _pci_enumeration_result noattr)) (tptr tvoid)
               (if b then nullval else p) (eval_cast tint (tptr tvoid) (Vint (Int.repr 0)))) =
  Vint (Int.repr (b2z (negb b))).
Proof. intros [|] p P; [ reflexivity | destruct p; try contradiction; reflexivity ]. Qed.
