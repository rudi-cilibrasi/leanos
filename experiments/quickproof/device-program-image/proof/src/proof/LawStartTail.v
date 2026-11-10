(* Law image_exact: start_case when the start succeeds, from the check of the registers on: the registers, sp, pc
   and steps are zero and the scratch is all zero. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import LeanosDeviceProgramImage.harness.image_exact.code.
Require Import LeanosDeviceProgramImage.proof.Defs.
Require LeanosDeviceProgramImage.proof.Specs.
Require Import LeanosDeviceProgramImage.proof.LawProg LeanosDeviceProgramImage.proof.LawSpecs
  LeanosDeviceProgramImage.proof.LawLib LeanosDeviceProgramImage.proof.LawLaw
  LeanosDeviceProgramImage.proof.LawSplit LeanosDeviceProgramImage.proof.LawStartDefs.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.
Local Opaque decode le32 header_status start_status start.

(* The good branch from its comparison of the code pointer to its end. *)
Definition s_good_tail : statement := ltac:(
  let b := eval cbv delta [s_sc_good] in s_sc_good in
  match b with
  | context [Ssequence (Ssequence (Sset ?t ?e) ?c) ?rest] =>
      match e with context [_code_base] => exact (Ssequence (Ssequence (Sset t e) c) rest) end
  end).

Lemma image_wvp: forall sh bs image i, readable_share sh -> 0 <= i <= Zlength bs -> 0 < Zlength bs ->
  data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) image |-- weak_valid_pointer (offset_val i image).
Proof.
  intros. eapply derives_trans; [ apply data_at_memory_block | ].
  replace (sizeof (tarray tuchar (Zlength bs))) with (Zlength bs) by (simpl; lia).
  apply memory_block_weak_valid_pointer; [ lia | lia | apply readable_nonidentity; auto ].
Qed.

Transparent denote_tc_test_eq.
Lemma tc_eq_same: forall (P: mpred) b o i, P |-- weak_valid_pointer (offset_val i (Vptr b o)) ->
  P |-- denote_tc_test_eq (offset_val i (Vptr b o)) (offset_val i (Vptr b o)).
Proof.
  intros P b o i W. simpl offset_val in *. unfold denote_tc_test_eq. simpl. unfold test_eq_ptrs.
  unfold sameblock. destruct (peq b b); [ | contradiction ]. simpl.
  apply andp_right; exact W.
Qed.
Opaque denote_tc_test_eq.

#[local] Hint Extern 2 (data_at _ (tarray tuchar _) _ _ |-- weak_valid_pointer (offset_val _ _)) =>
  (apply image_wvp; [ auto | rep_lia | rep_lia ]) : valid_pointer.

Ltac eq_true_branch := entailer!; rewrite ?Int.eq_true, ?Int64.eq_true; reflexivity.
Ltac eq_false_branch :=
  exfalso;
  match goal with
  | H: ?a <> ?a |- _ => apply H; reflexivity
  | H: Int.repr ?a <> Int.repr ?a |- _ => apply H; reflexivity
  | H: Int64.repr ?a <> Int64.repr ?a |- _ => apply H; reflexivity
  | H: Int.repr 1 = Int.zero |- _ => inversion H
  | H: Int.repr 1 = Int.repr 0 |- _ => inversion H
  end.
Ltac gp_one := forward_call (Int.repr 1);
  try (match goal with |- ENTAIL _, _ |-- _ => idtac end;
       entailer!; rewrite ?Int.eq_true, ?Int64.eq_true; reflexivity).

Lemma sc_good_tail {Espec: OracleKind}: forall gv msh m lv (cl cp: val) (pv: policy_t) (T: target) (H N B: Z) ish image
    (bs: list Z) vm prior saved (ss: list Z),
  lv = (cl, (Vint (Int.repr (Zlength bs)), (cp, (Vint (Int.repr 0), (Vint (Int.repr H),
         (target_val T, (pv, (Vint (Int.repr N), (Vint (Int.repr B), Vint (Int.repr 0)))))))))) ->
  readable_share msh -> readable_share ish -> Zlength ss = 16 ->
  16 <= H -> 0 <= N -> H + 16 * N <= Zlength bs -> Zlength bs <= Int.max_unsigned ->
  semax sc_delta
   (PROP ()
    LOCAL (temp _status (Vint (Int.repr 0)); temp _scratch (gv _wifi_scratch); temp _saved saved;
           temp _prior prior; temp _vm vm; gvars gv; temp _m m; temp _image image)
    SEP (mem_mgr gv; data_at msh t_law lv m; data_at ish (tarray tuchar (Zlength bs)) (bytes_val bs) image;
         field_at Ews t_vm (DOT _code_base) (offset_val H image) vm;
         field_at Ews t_vm (DOT _blob) (offset_val (H + 16 * N) image) vm;
         field_at Ews t_vm (DOT _r) (words_val (Zrepeat 0 16)) vm;
         field_at Ews t_vm (DOT _sp) (Vint (Int.repr 0)) vm; field_at Ews t_vm (DOT _pc) (Vint (Int.repr 0)) vm;
         field_at Ews t_vm (DOT _steps) (Vlong (Int64.repr 0)) vm;
         field_at Ews t_vm (DOT _stack) (words_val ss) vm; field_at Ews t_vm (DOT _stack) (words_val ss) prior;
         scr Ews (Zrepeat (Vint (Int.repr 0)) SCRATCH) (gv _wifi_scratch);
         TT))
   s_good_tail
   (overridePost (sc_join gv msh lv m ish image bs vm prior ss) (sc_post gv msh lv m ish image bs)).
Proof.
  intros until ss. intros Elv SH SH0 Lss H16 WN HN Hlen.
  unfold s_good_tail. start_sc_part.
  rewrite Elv.
  assert_PROP (isptr image) as Pimg by entailer!.
  destruct image as [ | | | | | bi oi]; try contradiction.
  forward. forward.
  forward_call (Int.repr 1).
  { apply tc_eq_same. auto 50 with valid_pointer. }
  forward. forward. forward.
  forward_call (Int.repr 1).
  { match goal with |- context [Vptr bi (Ptrofs.add oi (Ptrofs.repr ?x))] =>
      change (Vptr bi (Ptrofs.add oi (Ptrofs.repr x))) with (offset_val x (Vptr bi oi)) end.
    apply tc_eq_same. auto 50 with valid_pointer. }
  rewrite <- Elv.
  change (words_val (Zrepeat 0 16)) with (Zrepeat (Vint (Int.repr 0)) 16).
  forward_for_simple_bound 16 (EX i: Z,
    PROP ()
    LOCAL (temp _status (Vint (Int.repr 0)); temp _scratch (gv _wifi_scratch); temp _saved saved;
           temp _prior prior; temp _vm vm; gvars gv; temp _m m; temp _image (Vptr bi oi))
    SEP (mem_mgr gv;
         data_at msh t_law lv m;
         data_at ish (tarray tuchar (Zlength bs)) (bytes_val bs) (Vptr bi oi);
         field_at Ews t_vm (DOT _r) (Zrepeat (Vint (Int.repr 0)) 16) vm;
         field_at Ews t_vm (DOT _sp) (Vint (Int.repr 0)) vm; field_at Ews t_vm (DOT _pc) (Vint (Int.repr 0)) vm;
         field_at Ews t_vm (DOT _steps) (Vlong (Int64.repr 0)) vm;
         field_at Ews t_vm (DOT _stack) (words_val ss) vm; field_at Ews t_vm (DOT _stack) (words_val ss) prior;
         scr Ews (Zrepeat (Vint (Int.repr 0)) SCRATCH) (gv _wifi_scratch);
         TT))%assert.
  { entailer!. }
  { forward; try (match goal with |- ENTAIL _, _ |-- _ => idtac end; entailer!; rewrite Znth_Zrepeat by lia; simpl; auto).
    try rewrite Znth_Zrepeat by lia. gp_one. }
  forward.
  forward_if (temp _t'24 (Vint (Int.repr 1))).
  { forward. forward. eq_true_branch. }
  { eq_false_branch. }
  forward_if (temp _t'25 (Vint (Int.repr 1))).
  { forward. forward. eq_true_branch. }
  { eq_false_branch. }
  gp_one.
  rewrite scr_eq.
  remember SCRATCH as SC eqn:ESC.
  assert (HSC: 262144 <= SC <= 262144) by (subst; unfold SCRATCH; lia). clear ESC.
  forward_for_simple_bound 262144 (EX i: Z,
    PROP ()
    LOCAL (temp _status (Vint (Int.repr 0)); temp _scratch (gv _wifi_scratch); temp _saved saved;
           temp _prior prior; temp _vm vm; gvars gv; temp _m m; temp _image (Vptr bi oi))
    SEP (mem_mgr gv;
         data_at msh t_law lv m;
         data_at ish (tarray tuchar (Zlength bs)) (bytes_val bs) (Vptr bi oi);
         field_at Ews t_vm (DOT _stack) (words_val ss) vm; field_at Ews t_vm (DOT _stack) (words_val ss) prior;
         data_at Ews (tarray tuchar SC) (Zrepeat (Vint (Int.repr 0)) SC) (gv _wifi_scratch);
         TT))%assert.
  { entailer!. }
  { forward.
    all: try (match goal with |- ENTAIL _, _ |-- _ => idtac end; entailer!).
    all: try (change Byte.max_unsigned with 255; rewrite Int.unsigned_repr by rep_lia; lia).
    all: try (match goal with |- semax _ _ _ _ => fail 1 | |- _ =>
                rewrite ?Znth_Zrepeat by lia; simpl; rewrite ?Int.unsigned_repr by rep_lia; rep_lia end).
    try rewrite Znth_Zrepeat by lia. gp_one. }
  unfold sc_join. entailer!.
Qed.
