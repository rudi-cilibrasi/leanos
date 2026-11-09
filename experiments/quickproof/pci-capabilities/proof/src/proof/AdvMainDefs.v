(* Law capabilities_adversarial: what the parts of the proof of main share: main's context, its tails (the statement
   that remains at each point where the proof hands over to a lemma), and tactics. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosCaps.harness.capabilities_adversarial.code.
Require Import LeanosCaps.proof.Defs.
Require LeanosCaps.proof.CapsSpecs.
Require Import LeanosCaps.proof.AdvProg LeanosCaps.proof.AdvWalk LeanosCaps.proof.AdvFacts LeanosCaps.proof.AdvSpecs
  LeanosCaps.proof.AdvLib.
Local Open Scope Z_scope.
#[export] Existing Instance AdvProg.LCS.

Definition Gmain : funspecs :=
  [device_read_spec; named_pointer_spec; CapsSpecs.caps_collect_spec Dev_adv;
   nondet_u8_spec; nondet_u32_spec; gp_assert_spec].

Definition t_snap := Tstruct _pci_capability_snapshot noattr.
Definition t_res := Tstruct _pci_capability_result noattr.

(* main's type context and return assertion, as start_function makes them. *)
Definition Delta0 : tycontext := func_tycontext f_main nil Gmain nil.
Definition Post0 : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* The statement of main after `status = caps_collect(...)` (then main's final return, which VST keeps as the
   rest of the outer sequence). *)
Definition s_after_call : statement := ltac:(
  let b := eval cbv delta [f_main] beta iota zeta in (fn_body f_main) in
  match b with
  | context [Ssequence (Ssequence (Scall (Some _t'21) _ _) (Sset _status (Etempvar _t'21 tint))) ?rest] =>
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

(* Ranges of the words the harness computes. *)
Ltac rng := first [ rep_lia | apply land_range; first [ rep_lia | apply shiftr_range; rep_lia ] ].

(* A comparison of the harness as the boolean of the model. *)
Ltac bool_fin :=
  bsubst;
  rewrite ?shru_and_repr by rep_lia;
  rewrite ?Int_ltu_repr by rng;
  rewrite ?Int_eq_repr by rng;
  repeat match goal with
  | |- context [zlt ?a ?b] => destruct (zlt a b)
  | |- context [?a <? ?b] => destruct (Z.ltb_spec a b)
  | |- context [?a =? ?b] => destruct (Z.eqb_spec a b)
  end; try lia; reflexivity.

Ltac tc_sel := entailer!; apply sel_tc_test; [ entailer! | auto ].

(* A check of the harness whose condition is 1 (or computes to it). *)
Ltac gp_call := forward_call (Int.one); try solve [ entailer!; simpl; rewrite ?Int.eq_true; reflexivity ].

(* Before main returns: every local variable as data_at_ of its declared type, which return frees. *)
Lemma locals_frame: forall (hd: reptype t_header) (dv: reptype t_device) (sn: reptype CapsSpecs.t_snapshot)
    (rs: reptype CapsSpecs.t_result) (mk: list val) (ho: list val) v_initial v_d v_snapshot v_result v_masks
    v_header_offsets,
  (data_at Tsh t_header hd v_initial * data_at Tsh t_device dv v_d * data_at Tsh CapsSpecs.t_snapshot sn v_snapshot *
   data_at Tsh CapsSpecs.t_result rs v_result * data_at Tsh (tarray tuint 4) mk v_masks *
   data_at Tsh (tarray tuchar 4) ho v_header_offsets)%logic |--
  (data_at_ Tsh (Tstruct _pci_enumeration_header noattr) v_initial * data_at_ Tsh (Tstruct _device noattr) v_d *
   data_at_ Tsh (Tstruct _pci_capability_snapshot noattr) v_snapshot *
   data_at_ Tsh (Tstruct _pci_capability_result noattr) v_result *
   data_at_ Tsh (tarray tuint 4) v_masks * data_at_ Tsh (tarray tuchar 4) v_header_offsets)%logic.
Proof.
  intros. repeat apply sepcon_derives; apply data_at_data_at_.
Qed.

(* Free the struct locals before a return: their contents no longer matter. *)
Ltac free1 t p :=
  match goal with |- context [@data_at _ Tsh t ?v p] => sep_apply (data_at_data_at_ Tsh t v p) end.
Ltac free_locals v_initial v_d v_snapshot v_result :=
  free1 t_header v_initial; free1 t_device v_d; free1 CapsSpecs.t_snapshot v_snapshot;
  free1 CapsSpecs.t_result v_result;
  unfold t_header, t_device, CapsSpecs.t_snapshot, CapsSpecs.t_result.
