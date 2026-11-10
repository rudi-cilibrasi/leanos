(* The body of wifi_start: the header into &vm->target, &vm->pol and the local hdr, the size test, the fields,
   the registers, then the scratch (BodyScratch). *)
Require Import VST.floyd.proofauto.
Require Import LeanosDeviceProgramImage.device_program.code.
Require Import LeanosDeviceProgramImage.proof.Specs.
Require Import LeanosDeviceProgramImage.proof.BodyVm.
Require Import LeanosDeviceProgramImage.proof.BodyScratch.
Require Import LeanosDeviceProgramImage.proof.BodyLookup.
Require Import LeanosDeviceProgramImage.proof.HdDefs.
#[local] Existing Instance Specs.CS.
Local Open Scope Z_scope.

Lemma start_none: forall bs, decode bs = None -> start bs = None.
Proof. intros bs D. unfold start. rewrite D. reflexivity. Qed.

Ltac vm_fold_tac :=
  match goal with |- context [field_at ?sh t_vm (DOT _code_base) ?code ?p] =>
  match goal with |- context [field_at _ t_vm (DOT _blob) ?blob p] =>
  match goal with |- context [field_at _ t_vm (DOT _n) ?n p] =>
  match goal with |- context [field_at _ t_vm (DOT _blob_len) ?bl p] =>
  match goal with |- context [field_at _ t_vm (DOT _window) ?w p] =>
  match goal with |- context [field_at _ t_vm (DOT _pol) ?pol p] =>
  match goal with |- context [field_at _ t_vm (DOT _target) ?tg p] =>
  match goal with |- context [field_at _ t_vm (DOT _r) ?r p] =>
  match goal with |- context [field_at _ t_vm (DOT _stack) ?st p] =>
  match goal with |- context [field_at _ t_vm (DOT _sp) ?sp p] =>
  match goal with |- context [field_at _ t_vm (DOT _pc) ?pc p] =>
  match goal with |- context [field_at _ t_vm (DOT _steps) ?steps p] =>
  match goal with FC: field_compatible t_vm [] p |- _ =>
    sep_apply (vm_fold sh code blob n bl w pol tg r st sp pc steps p FC)
  end end end end end end end end end end end end end.

Lemma divu_val: forall x, 0 <= x <= Int.max_unsigned -> Int.unsigned (Int.divu (Int.repr x) (Int.repr 16)) = x / 16.
Proof.
  intros x X. unfold Int.divu. rewrite (Int.unsigned_repr x), (Int.unsigned_repr 16) by rep_lia.
  apply Int.unsigned_repr. split; [ apply Z.div_pos; lia | ].
  apply Z.le_trans with x; [ apply Z.div_le_upper_bound; lia | lia ].
Qed.

Lemma add_ptr_uint: forall p k, isptr p -> 0 <= k <= Int.max_unsigned ->
  force_val (sem_add_ptr_int tuchar Unsigned p (Vint (Int.repr k))) = offset_val k p.
Proof.
  intros p k P K. destruct p; try contradiction. simpl. f_equal. f_equal.
  unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by rep_lia.
  rewrite ptrofs_mul_repr. f_equal. lia.
Qed.

Lemma add_ptr_long: forall p a, isptr p ->
  force_val (sem_add_ptr_long tuchar p (Vlong (Int64.repr a))) = offset_val a p.
Proof.
  intros p a P. destruct p; try contradiction. simpl. f_equal. f_equal.
  unfold Ptrofs.of_int64. rewrite ptrofs_mul_repr. rewrite Z.mul_1_l.
  apply Ptrofs.eqm_samerepr. unfold Ptrofs.eqm. rewrite Int64.unsigned_repr_eq.
  change Int64.modulus with Ptrofs.modulus. apply Zbits.eqmod_sym. apply Zbits.eqmod_mod. apply Ptrofs.modulus_pos.
Qed.

Ltac remove_r R :=
  match R with
  | field_at _ t_vm (DOT _r) _ _ :: ?rest => constr:(rest)
  | ?a :: ?rest => let r' := remove_r rest in constr:(a :: r')
  end.

Lemma body_wifi_start : semax_body Vprog Gprog f_wifi_start wifi_start_spec.
Proof.
  start_function.
  rename H into IOK, H0 into VW, H1 into LS.
  pose proof IOK as (LB & U8).
  assert_PROP (field_compatible t_vm [] vmp) as FCv by entailer!.
  assert_PROP (field_compatible (tarray tuchar (Zlength bs)) [] image) as FCi by entailer!.
  assert (PI: isptr image) by (destruct FCi; auto).
  forward.
  rewrite (vm_val_eq V0), vm_fields by auto. Intros.
  rewrite vm_target_at, vm_pol_at by auto.
  sep_apply (data_at_data_at_ wsh t_target (target_val (vm_target V0)) (offset_val 368 vmp)).
  sep_apply (data_at_data_at_ Tsh tuint (Vint (Int.repr 0)) v_hdr).
  pose proof VW as (_ & _ & _ & PW & _).
  forward_call (sh, image, bs, wsh, offset_val 368 vmp, wsh, offset_val 32 vmp, vm_pol V0, Tsh, v_hdr).
  Intros vret. destruct vret as [[tv pv] hv]. cbn [fst snd] in *. rename H into HP.
  rewrite <- vm_target_at, <- vm_pol_at by auto.
  destruct (decode bs) as [[[T P] H] | ] eqn:DEC.
  2: { assert (HS: header_status bs = BAD) by (unfold header_status; rewrite DEC; reflexivity).
       rewrite HS. forward_if.
       2: { exfalso. change Int.zero with (Int.repr 0) in H. apply repr_inj_unsigned in H; unfold BAD in *; rep_lia. }
       vm_fold_tac. forward.
       Exists (vm_tuple (vm_code V0) (vm_blob V0) (Vint (Int.repr (vm_n V0))) (Vint (Int.repr (vm_blob_len V0)))
                 (Vint (Int.repr (vm_window V0))) pv tv (words_val (vm_r V0)) (words_val (vm_stack V0))
                 (Vint (Int.repr (vm_sp V0))) (Vint (Int.repr (vm_pc V0))) (Vlong (Int64.repr (vm_steps V0)))) sc.
       entailer!.
       unfold start_post, start_status. rewrite start_none by auto.
       split; [ split; [ exists pv, tv; reflexivity | reflexivity ] | reflexivity ]. }
  unfold header_post in HP. rewrite DEC in HP. destruct HP as (-> & -> & ->).
  destruct (decode_wf bs T P H U8 DEC) as (TW & DW & HR).
  assert (HS: header_status bs = 0) by (unfold header_status; rewrite DEC; reflexivity).
  rewrite HS.
  forward_if; [ exfalso; apply H0; reflexivity | ].
  assert (W: forall k, u32_ok (le32 bs k)) by (intros; apply le32_range; auto).
  assert (Wr: forall k, 0 <= le32 bs k <= Int.max_unsigned) by (intros; apply W).
  pose proof (Wr 8) as W8. pose proof (Wr 12) as W12.
  forward_call (sh, image, bs, 8).
  forward_call (sh, image, bs, 12).
  forward.
  fif_t _t'4 (Vint (Int.repr (Z.b2z (((Zlength bs - H) / 16 <? le32 bs 8) ||
                                       negb (le32 bs 12 =? Zlength bs - H - 16 * le32 bs 8))%bool))).
  { forward. entailer!. rewrite divu_val in H1 by lia. rewrite (proj2 (Z.ltb_lt _ _) H1). reflexivity. }
  { forward. forward. entailer!. rewrite divu_val in H1 by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [orb].
    assert (N16: 16 * le32 bs 8 <= Zlength bs - H)
      by (pose proof (Z.mul_div_le (Zlength bs - H) 16 ltac:(lia)); lia).
    rewrite (Z.mul_comm (le32 bs 8) 16). rewrite u32_eq by (unfold u32_ok; rep_lia). rewrite bool2val_b2z'.
    reflexivity. }
  forward_if.
  { assert (SF: sizes_ok bs H = false).
    { change (let (q, _) := Z.div_eucl (Zlength bs - H) 16 in q) with ((Zlength bs - H) / 16) in *.
      match goal with HH: (_ || _)%bool = true |- _ => revert HH end. unfold sizes_ok. rewrite Z.leb_antisym.
      destruct ((Zlength bs - H) / 16 <? le32 bs 8), (le32 bs 12 =? Zlength bs - H - 16 * le32 bs 8); cbn; congruence. }
    vm_fold_tac. forward.
    Exists (vm_tuple (vm_code V0) (vm_blob V0) (Vint (Int.repr (vm_n V0))) (Vint (Int.repr (vm_blob_len V0)))
              (Vint (Int.repr (vm_window V0))) (policy_val (store P (vm_pol V0))) (target_val T)
              (words_val (vm_r V0)) (words_val (vm_stack V0))
              (Vint (Int.repr (vm_sp V0))) (Vint (Int.repr (vm_pc V0))) (Vlong (Int64.repr (vm_steps V0)))) sc.
    entailer!.
    unfold start_post, start_status, start. rewrite DEC, SF.
    split; [ split; [ eexists; eexists; reflexivity | reflexivity ] | reflexivity ]. }
  assert (ST: start bs = Some (T, P, H, le32 bs 8, le32 bs 12)).
  { unfold start. rewrite DEC.
    change (let (q, _) := Z.div_eucl (Zlength bs - H) 16 in q) with ((Zlength bs - H) / 16) in *.
    match goal with HH: (_ || _)%bool = false |- _ => revert HH end.
    unfold sizes_ok. rewrite Z.leb_antisym.
    destruct ((Zlength bs - H) / 16 <? le32 bs 8), (le32 bs 12 =? Zlength bs - H - 16 * le32 bs 8); cbn; congruence. }
  unfold target_val.
  forward. forward. forward. forward.
  forward. forward.
  forward. forward.
  rewrite add_ptr_uint by (auto; rep_lia).
  rewrite (Int.unsigned_repr (le32 bs 8)) by rep_lia. rewrite Int.signed_repr by rep_lia.
  rewrite mul64_repr, add_ptr_long by (destruct image; try contradiction; simpl; auto). rewrite offset_offset_val.
  rewrite (Z.mul_comm (le32 bs 8) 16).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    let R' := remove_r R in
    forward_for_simple_bound 16 (EX i: Z, PROPx P (LOCALx Q (SEPx
      (field_at wsh t_vm (DOT _r) (Zrepeat (Vint (Int.repr 0)) i ++ sublist i 16 (words_val (vm_r V0))) vmp :: R'))))%assert
  end.
  { rewrite Zrepeat_0, app_nil_l, sublist_same by (rewrite ?Zlength_map; pose proof VW as (_&_&_&_&_&Lr&_); lia).
    entailer!. }
  { forward. rewrite zero_step by (rewrite ?Zlength_map; pose proof VW as (_&_&_&_&_&Lr&_); lia). entailer!. }
  rewrite sublist_nil, app_nil_r.
  forward. forward. forward.
  vm_fold_tac.
  eapply semax_pre; [ | apply (st_scratch gv sh image bs wsh vmp V0 ssh sc v_hdr T P H (le32 bs 8) (le32 bs 12));
                        first [ reflexivity | assumption ] ].
  entailer!.
Qed.
