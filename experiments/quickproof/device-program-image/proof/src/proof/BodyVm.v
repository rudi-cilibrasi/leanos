(* struct wifi_vm as its fields, proved once: wifi_start passes &vm->target and &vm->pol to the header and
   writes the other fields one by one. *)
Require Import VST.floyd.proofauto.
Require Import LeanosDeviceProgramImage.device_program.code.
Require Import LeanosDeviceProgramImage.proof.Specs.
#[local] Existing Instance Specs.CS.
Local Open Scope Z_scope.

Definition vm_tuple (code blob n bl w: val) (pol: policy_t) (tg: target_t) (r st: list val) (sp pc steps: val)
  : vm_t := (code, (blob, (n, (bl, (w, (pol, (tg, (r, (st, (sp, (pc, steps))))))))))).

Lemma vm_val_eq: forall V, vm_val V =
  vm_tuple (vm_code V) (vm_blob V) (Vint (Int.repr (vm_n V))) (Vint (Int.repr (vm_blob_len V)))
    (Vint (Int.repr (vm_window V))) (policy_val (vm_pol V)) (target_val (vm_target V)) (words_val (vm_r V))
    (words_val (vm_stack V)) (Vint (Int.repr (vm_sp V))) (Vint (Int.repr (vm_pc V)))
    (Vlong (Int64.repr (vm_steps V))).
Proof. reflexivity. Qed.

Lemma vm_fields: forall sh code blob n bl w pol tg r st sp pc steps p,
  field_compatible t_vm [] p ->
  data_at sh t_vm (vm_tuple code blob n bl w pol tg r st sp pc steps) p =
  (field_at sh t_vm (DOT _code_base) code p * field_at sh t_vm (DOT _blob) blob p *
   field_at sh t_vm (DOT _n) n p * field_at sh t_vm (DOT _blob_len) bl p *
   field_at sh t_vm (DOT _window) w p * spacer sh 28 32 p *
   field_at sh t_vm (DOT _pol) pol p * field_at sh t_vm (DOT _target) tg p *
   field_at sh t_vm (DOT _r) r p * field_at sh t_vm (DOT _stack) st p *
   field_at sh t_vm (DOT _sp) sp p * field_at sh t_vm (DOT _pc) pc p *
   field_at sh t_vm (DOT _steps) steps p)%logic.
Proof.
  intros. unfold vm_tuple, t_vm. unfold_data_at (data_at _ _ _ p).
  apply pred_ext; cancel.
Qed.

Lemma vm_fold: forall sh code blob n bl w pol tg r st sp pc steps p,
  field_compatible t_vm [] p ->
  (field_at sh t_vm (DOT _code_base) code p * field_at sh t_vm (DOT _blob) blob p *
   field_at sh t_vm (DOT _n) n p * field_at sh t_vm (DOT _blob_len) bl p *
   field_at sh t_vm (DOT _window) w p * spacer sh 28 32 p *
   field_at sh t_vm (DOT _pol) pol p * field_at sh t_vm (DOT _target) tg p *
   field_at sh t_vm (DOT _r) r p * field_at sh t_vm (DOT _stack) st p *
   field_at sh t_vm (DOT _sp) sp p * field_at sh t_vm (DOT _pc) pc p *
   field_at sh t_vm (DOT _steps) steps p)%logic |--
  data_at sh t_vm (vm_tuple code blob n bl w pol tg r st sp pc steps) p.
Proof. intros. rewrite vm_fields by auto. apply derives_refl. Qed.

Lemma vm_target_at: forall sh tg p, field_compatible t_vm [] p ->
  field_at sh t_vm (DOT _target) tg p = data_at sh t_target tg (offset_val 368 p).
Proof.
  intros. rewrite field_at_data_at. rewrite field_compatible_field_address by auto with field_compatible.
  reflexivity.
Qed.

Lemma vm_pol_at: forall sh pol p, field_compatible t_vm [] p ->
  field_at sh t_vm (DOT _pol) pol p = data_at sh t_policy pol (offset_val 32 p).
Proof.
  intros. rewrite field_at_data_at. rewrite field_compatible_field_address by auto with field_compatible.
  reflexivity.
Qed.
