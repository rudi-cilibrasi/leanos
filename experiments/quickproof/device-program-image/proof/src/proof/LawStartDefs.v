(* Law image_exact: what the parts of the proof of start_case share: struct wifi_vm as its fields (its policy at
   offset 32 and its target at offset 368 as their own objects). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import LeanosDeviceProgramImage.harness.image_exact.code.
Require Import LeanosDeviceProgramImage.proof.Defs.
Require Import LeanosDeviceProgramImage.proof.LawProg LeanosDeviceProgramImage.proof.LawSpecs.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Definition vm_fields (sh: share) (p: val) (code blob n blen win: val) (pv: policy_t) (tv: target_t)
    (rs ss: list val) (sp pc steps: val) : mpred :=
  (field_at sh t_vm (DOT _code_base) code p * field_at sh t_vm (DOT _blob) blob p *
   field_at sh t_vm (DOT _n) n p * field_at sh t_vm (DOT _blob_len) blen p *
   field_at sh t_vm (DOT _window) win p * spacer sh 28 32 p *
   data_at sh t_policy pv (offset_val 32 p) * data_at sh t_target tv (offset_val 368 p) *
   field_at sh t_vm (DOT _r) rs p * field_at sh t_vm (DOT _stack) ss p *
   field_at sh t_vm (DOT _sp) sp p * field_at sh t_vm (DOT _pc) pc p * field_at sh t_vm (DOT _steps) steps p)%logic.

Lemma vm_addr: forall p f, field_compatible t_vm nil p -> in_members f (co_members (get_co _wifi_vm)) ->
  field_address t_vm (DOT f) p = offset_val (nested_field_offset t_vm (DOT f)) p.
Proof.
  intros p f FC M. unfold field_address. rewrite if_true; [ reflexivity | ].
  apply field_compatible_cons; split; [ exact M | exact FC ].
Qed.

Definition vm_fields0 (sh: share) (p: val) (code blob n blen win: val) (pv: policy_t) (tv: target_t)
    (rs ss: list val) (sp pc steps: val) : mpred :=
  (field_at sh t_vm (DOT _code_base) code p * field_at sh t_vm (DOT _blob) blob p *
   field_at sh t_vm (DOT _n) n p * field_at sh t_vm (DOT _blob_len) blen p *
   field_at sh t_vm (DOT _window) win p * spacer sh 28 32 p *
   field_at sh t_vm (DOT _pol) pv p * field_at sh t_vm (DOT _target) tv p *
   field_at sh t_vm (DOT _r) rs p * field_at sh t_vm (DOT _stack) ss p *
   field_at sh t_vm (DOT _sp) sp p * field_at sh t_vm (DOT _pc) pc p * field_at sh t_vm (DOT _steps) steps p)%logic.

Lemma vm_split0: forall sh p (code blob n blen win: val) (pv: policy_t) (tv: target_t) (rs ss: list val)
    (sp pc steps: val),
  data_at sh t_vm (code, (blob, (n, (blen, (win, (pv, (tv, (rs, (ss, (sp, (pc, steps))))))))))) p =
  vm_fields0 sh p code blob n blen win pv tv rs ss sp pc steps.
Proof.
  intros. unfold_data_at (data_at _ _ _ p). unfold vm_fields0. rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma vm_split: forall sh p (code blob n blen win: val) (pv: policy_t) (tv: target_t) (rs ss: list val)
    (sp pc steps: val), field_compatible t_vm nil p ->
  data_at sh t_vm (code, (blob, (n, (blen, (win, (pv, (tv, (rs, (ss, (sp, (pc, steps))))))))))) p =
  vm_fields sh p code blob n blen win pv tv rs ss sp pc steps.
Proof.
  intros. rewrite vm_split0. unfold vm_fields0, vm_fields.
  rewrite (field_at_data_at sh t_vm (DOT _pol)), (field_at_data_at sh t_vm (DOT _target)).
  rewrite (vm_addr p _pol), (vm_addr p _target)
    by (auto; unfold in_members; simpl; repeat (first [ left; reflexivity | right ])).
  reflexivity.
Qed.

Definition tg_default : target_t := (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, Vundef))))).
Definition pol_default : policy_t :=
  (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Zrepeat Vundef 8,
   (Vundef, Zrepeat (Vundef, (Vundef, (Vundef, Vundef))) 16)))))))))).

Lemma vm_default: default_val t_vm =
  (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (pol_default, (tg_default, (Zrepeat Vundef 16,
   (Zrepeat Vundef 16, (Vundef, (Vundef, Vundef))))))))))).
Proof. reflexivity. Qed.

Lemma pol_default_eq: pol_default = default_val t_policy.
Proof. reflexivity. Qed.

Lemma tg_default_eq: tg_default = default_val t_target.
Proof. reflexivity. Qed.

(* The 262144-byte objects (the unit's scratch, the law's saved copy) behind opaque names, so that no tactic
   unfolds their default value (a list of 262144 entries). *)
Definition scr_ (sh: share) (p: val) : mpred := data_at_ sh (tarray tuchar SCRATCH) p.
Definition scr (sh: share) (l: list val) (p: val) : mpred := data_at sh (tarray tuchar SCRATCH) l p.

Lemma scr__eq: forall sh p, scr_ sh p = data_at_ sh (tarray tuchar SCRATCH) p.
Proof. reflexivity. Qed.

Lemma scr_eq: forall sh l p, scr sh l p = data_at sh (tarray tuchar SCRATCH) l p.
Proof. reflexivity. Qed.

Lemma data_at__tuchar: forall sh n p, data_at_ sh (tarray tuchar n) p = data_at sh (tarray tuchar n) (Zrepeat Vundef n) p.
Proof. intros. rewrite data_at__eq. reflexivity. Qed.

Lemma scr_start: forall sh p (S: list Z),
  scr_ sh p = data_at sh (tarray tuchar SCRATCH) (bytes_val (sublist 0 0 S) ++ Zrepeat Vundef (SCRATCH - 0)) p.
Proof.
  intros. rewrite scr__eq, (data_at__tuchar sh SCRATCH p). rewrite Z.sub_0_r, sublist_nil, app_nil_l. reflexivity.
Qed.

Lemma scr_end: forall (S: list Z), Zlength S = SCRATCH ->
  bytes_val (sublist 0 SCRATCH S) ++ Zrepeat Vundef (SCRATCH - SCRATCH) = bytes_val S.
Proof. intros. rewrite Z.sub_diag, Zrepeat_0, app_nil_r, sublist_same by lia. reflexivity. Qed.

Lemma upd_sub_map {A B} {da: Inhabitant A} {db: Inhabitant B}: forall (f: A -> B) (l: list A) i n (u: B),
  0 <= i < n -> Zlength l = n ->
  upd_Znth i (map f (sublist 0 i l) ++ Zrepeat u (n - i)) (f (Znth i l)) =
  map f (sublist 0 (i + 1) l) ++ Zrepeat u (n - (i + 1)).
Proof. intros. list_solve. Qed.

Lemma scr__local_facts: forall sh p, scr_ sh p |-- !! isptr p.
Proof.
  intros. rewrite scr__eq. eapply derives_trans; [ apply data_at__local_facts | ].
  apply prop_derives. intros FC. apply field_compatible_isptr in FC. exact FC.
Qed.

Lemma scr_local_facts: forall sh l p, scr sh l p |-- !! isptr p.
Proof.
  intros. rewrite scr_eq. eapply derives_trans; [ apply data_at_local_facts | ].
  apply prop_derives. intros [FC _]. apply field_compatible_isptr in FC. exact FC.
Qed.

Lemma scr__valid_pointer: forall sh p, sepalg.nonidentity sh -> scr_ sh p |-- valid_pointer p.
Proof. intros. rewrite scr__eq. apply data_at__valid_ptr; auto. unfold SCRATCH; simpl; lia. Qed.

Lemma scr_valid_pointer: forall sh l p, sepalg.nonidentity sh -> scr sh l p |-- valid_pointer p.
Proof. intros. rewrite scr_eq. apply data_at_valid_ptr; auto. unfold SCRATCH; simpl; lia. Qed.

#[export] Hint Resolve scr__local_facts scr_local_facts : saturate_local.
#[export] Hint Resolve scr__valid_pointer scr_valid_pointer : valid_pointer.

Global Opaque scr_ scr.

(* ---------------------------------------------------------------------- *)
(* start_case from the call of dp_start on.                               *)
(* ---------------------------------------------------------------------- *)

Definition sc_delta : tycontext := func_tycontext f_start_case Vlaw Glaw nil.

Definition sc_post (gv: globals) (msh: share) (lv: law_t) (m: val) (ish: share) (image: val) (bs: list Z)
    : ret_assert :=
  normal_ret_assert
    (@sepcon (environ -> mpred) _ _
      ((PROP ( )
        RETURN ( ) SEP (mem_mgr gv; data_at msh t_law lv m;
                        data_at ish (tarray tuchar (Zlength bs)) (bytes_val bs) image; TT))%argsassert)
      (stackframe_of f_start_case)).

Definition sc_body : statement := ltac:(let b := eval cbv delta [f_start_case] beta iota zeta in (fn_body f_start_case)
  in exact b).

Definition s_sc_rest : statement := ltac:(
  let b := eval cbv delta [sc_body] in sc_body in
  match b with
  | context [Ssequence (Ssequence (Ssequence (Sset _t'65 ?e) ?c) ?st) ?rest] =>
      exact (Ssequence (Ssequence (Ssequence (Sset _t'65 e) c) st) rest)
  end).

Definition s_sc_bad : statement := ltac:(
  let b := eval cbv delta [sc_body] in sc_body in
  match b with
  | context [Sifthenelse (Etempvar _t'26 tint) ?bad _] => exact bad
  end).

Definition s_sc_good : statement := ltac:(
  let b := eval cbv delta [sc_body] in sc_body in
  match b with
  | context [Sifthenelse (Etempvar _t'26 tint) _ ?good] => exact good
  end).

Ltac start_sc_part :=
  unfold sc_delta, sc_post, s_sc_rest, s_sc_bad, s_sc_good;
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

(* The executor state before wifi_start. *)
Definition vm0 (n0 b0 w0: Z) (P0: policy) (T0: target) (rs ss: list Z) (sp0 pc0 st0: Z) : vmstate :=
  mk_vm nullval nullval n0 b0 w0 P0 T0 rs ss sp0 pc0 st0.

(* The join after the two branches: what the stack comparison needs. *)
Definition sc_join (gv: globals) (msh: share) (lv: law_t) (m: val) (ish: share) (image: val) (bs: list Z)
    (vm prior: val) (ss: list Z) : environ -> mpred :=
  (PROP ()
   LOCAL (temp _vm vm; temp _prior prior; gvars gv; temp _m m; temp _image image)
   SEP (mem_mgr gv; data_at msh t_law lv m; data_at ish (tarray tuchar (Zlength bs)) (bytes_val bs) image;
        field_at Ews t_vm (DOT _stack) (map (fun w => Vint (Int.repr w)) ss) vm;
        field_at Ews t_vm (DOT _stack) (map (fun w => Vint (Int.repr w)) ss) prior; TT))%assert.
