(* Law image_exact: start_case when the law's reading says the start fails: every check of that branch. *)
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

Lemma sc_bad {Espec: OracleKind}: forall gv msh m lv ish image bs vm prior saved n0 b0 w0 P0 (pv': policy_t)
    (tv': target_t) rs ss sp0 pc0 st0 (S: list Z),
  readable_share msh -> readable_share ish -> field_compatible t_vm nil vm ->
  u32_ok n0 -> u32_ok b0 -> u32_ok w0 -> Zlength rs = 16 -> Forall u32_ok rs -> u32_ok sp0 -> u32_ok pc0 ->
  u64_ok st0 -> Zlength S = SCRATCH -> Forall (fun b => 0 <= b <= Byte.max_unsigned) S ->
  semax sc_delta
   (PROP ()
    LOCAL (temp _status (Vint (Int.repr 2)); temp _scratch (gv _wifi_scratch); temp _saved saved;
           temp _prior prior; temp _vm vm; gvars gv; temp _m m; temp _image image)
    SEP (data_at ish (tarray tuchar (Zlength bs)) (bytes_val bs) image;
         data_at Ews t_vm (vm_rep nullval nullval n0 b0 w0 pv' tv' (words_val rs) (words_val ss) sp0 pc0 st0) vm;
         scr Ews (bytes_val S) (gv _wifi_scratch); mem_mgr gv; data_at msh t_law lv m; scr Ews (bytes_val S) saved;
         vm_fields Ews prior Vundef Vundef (Vint (Int.repr n0)) (Vint (Int.repr b0)) (Vint (Int.repr w0))
           (policy_val P0) (default_val t_target) (words_val rs) (words_val ss) (Vint (Int.repr sp0))
           (Vint (Int.repr pc0)) (Vlong (Int64.repr st0));
         TT))
   s_sc_bad
   (overridePost (sc_join gv msh lv m ish image bs vm prior ss) (sc_post gv msh lv m ish image bs)).
Proof.
  intros until S. intros SH SH0 FCvm Wn Wb Ww Lrs Frs Wsp Wpc Wst LS FS.
  start_sc_part.
  unfold vm_rep. rewrite vm_split by auto. unfold vm_fields. Intros.
  freeze FRD := (data_at _ t_policy _ (offset_val 32 vm)) (data_at _ t_target _ (offset_val 368 vm))
    (data_at _ t_policy _ (offset_val 32 prior)) (data_at _ t_target _ (offset_val 368 prior))
    (data_at _ (tarray tuchar (Zlength bs)) _ image) (mem_mgr gv) (data_at msh t_law _ m).
  gp_one.
  forward.
  forward_if (temp _t'16 (Vint (Int.repr 1))).
  { forward. forward. eq_true_branch. }
  { eq_false_branch. }
  gp_one.
  forward. forward.
  forward_if (temp _t'17 (Vint (Int.repr 1))).
  { forward. forward. forward. eq_true_branch. }
  { eq_false_branch. }
  forward_if (temp _t'18 (Vint (Int.repr 1))).
  { forward. forward. forward. eq_true_branch. }
  { eq_false_branch. }
  gp_one.
  freeze FE1 := (FRZL FRD) (field_at _ _ (DOT _code_base) _ vm) (field_at _ _ (DOT _blob) _ vm)
    (field_at _ _ (DOT _n) _ vm) (field_at _ _ (DOT _blob_len) _ vm) (field_at _ _ (DOT _window) _ vm)
    (spacer _ _ _ vm) (field_at _ _ (DOT _stack) _ vm) (field_at _ _ (DOT _sp) _ vm) (field_at _ _ (DOT _pc) _ vm).
  freeze FE2 := (field_at _ _ (DOT _steps) _ vm) (scr _ _ (gv _wifi_scratch)) (scr _ _ saved)
    (field_at _ _ (DOT _code_base) _ prior) (field_at _ _ (DOT _blob) _ prior) (field_at _ _ (DOT _n) _ prior)
    (field_at _ _ (DOT _blob_len) _ prior) (field_at _ _ (DOT _window) _ prior) (spacer _ _ _ prior)
    (field_at _ _ (DOT _stack) _ prior).
  freeze FE3 := (field_at _ _ (DOT _sp) _ prior) (field_at _ _ (DOT _pc) _ prior) (field_at _ _ (DOT _steps) _ prior) TT.
  forward_for_simple_bound 16 (EX i: Z,
    PROP ()
    LOCAL (temp _status (Vint (Int.repr 2)); temp _scratch (gv _wifi_scratch); temp _saved saved;
           temp _prior prior; temp _vm vm; gvars gv; temp _m m; temp _image image)
    SEP (FRZL FE1; FRZL FE2; FRZL FE3; field_at Ews t_vm (DOT _r) (words_val rs) vm;
         field_at Ews t_vm (DOT _r) (words_val rs) prior))%assert.
  { entailer!. }
  { forward. forward. gp_one. }
  thaw FE3. thaw FE2. thaw FE1.
  forward. forward.
  forward_if (temp _t'19 (Vint (Int.repr 1))).
  { forward. forward. forward. eq_true_branch. }
  { eq_false_branch. }
  forward_if (temp _t'20 (Vint (Int.repr 1))).
  { forward. forward. forward. eq_true_branch. }
  { eq_false_branch. }
  gp_one.
  freeze FF1 := (FRZL FRD) (field_at _ _ (DOT _code_base) _ vm) (field_at _ _ (DOT _blob) _ vm)
    (field_at _ _ (DOT _n) _ vm) (field_at _ _ (DOT _blob_len) _ vm) (field_at _ _ (DOT _window) _ vm)
    (spacer _ _ _ vm) (field_at _ _ (DOT _stack) _ vm) (field_at _ _ (DOT _sp) _ vm) (field_at _ _ (DOT _pc) _ vm).
  freeze FF2 := (field_at _ _ (DOT _steps) _ vm) (field_at _ _ (DOT _r) _ vm) (field_at _ _ (DOT _r) _ prior)
    (field_at _ _ (DOT _code_base) _ prior) (field_at _ _ (DOT _blob) _ prior) (field_at _ _ (DOT _n) _ prior)
    (field_at _ _ (DOT _blob_len) _ prior) (field_at _ _ (DOT _window) _ prior) (spacer _ _ _ prior)
    (field_at _ _ (DOT _stack) _ prior).
  freeze FF3 := (field_at _ _ (DOT _sp) _ prior) (field_at _ _ (DOT _pc) _ prior) (field_at _ _ (DOT _steps) _ prior) TT.
  rewrite !scr_eq.
  remember SCRATCH as SC eqn:ESC.
  assert (HSC: 262144 <= SC <= 262144) by (subst; unfold SCRATCH; lia). clear ESC.
  assert (SB: forall j, 0 <= j < SC -> 0 <= Znth j S <= Byte.max_unsigned)
    by (intros; apply (proj1 (Forall_Znth _ _) FS); lia).
  forward_for_simple_bound 262144 (EX i: Z,
    PROP ()
    LOCAL (temp _status (Vint (Int.repr 2)); temp _scratch (gv _wifi_scratch); temp _saved saved;
           temp _prior prior; temp _vm vm; gvars gv; temp _m m; temp _image image)
    SEP (FRZL FF1; FRZL FF2; FRZL FF3; data_at Ews (tarray tuchar SC) (bytes_val S) (gv _wifi_scratch);
         data_at Ews (tarray tuchar SC) (bytes_val S) saved))%assert.
  { entailer!. }
  { forward; try (match goal with |- ENTAIL _, _ |-- _ => idtac end; entailer!; pose proof (SB i ltac:(lia)); rewrite ?Int.unsigned_repr by rep_lia; rep_lia).
    forward; try (match goal with |- ENTAIL _, _ |-- _ => idtac end; entailer!; pose proof (SB i ltac:(lia)); rewrite ?Int.unsigned_repr by rep_lia; rep_lia).
    gp_one. }
  thaw FF3. thaw FF2. thaw FF1. thaw FRD.
  unfold sc_join. entailer!.
Qed.
