(* Law image_exact: what the proof of main needs: the program's globals (law and wifi_scratch, both Init_space)
   as their objects, and struct law as its fields. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosDeviceProgramImage.harness.image_exact.code.
Require LeanosDeviceProgramImage.device_program.code.
Require Import LeanosDeviceProgramImage.proof.Defs.
Require Import LeanosDeviceProgramImage.proof.LawProg LeanosDeviceProgramImage.proof.LawSpecs
  LeanosDeviceProgramImage.proof.LawStartDefs.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Definition law_fields (sh: share) (p: val) (c len cp: val) (w: law_image_t) : mpred :=
  (field_at sh t_law (DOT _call) c p * field_at sh t_law (DOT _length) len p *
   field_at sh t_law (DOT _copy) cp p * field_at sh t_law (DOT _want) w p)%logic.

Lemma law_split: forall sh p (c len cp: val) (w: law_image_t),
  data_at sh t_law (c, (len, (cp, w))) p = law_fields sh p c len cp w.
Proof.
  intros. unfold_data_at (data_at _ _ _ p). unfold law_fields. rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma law_fold: forall sh p (c len cp: val) (w: law_image_t),
  (field_at sh t_law (DOT _call) c p * field_at sh t_law (DOT _length) len p *
   field_at sh t_law (DOT _copy) cp p * field_at sh t_law (DOT _want) w p)%logic
  |-- data_at sh t_law (c, (len, (cp, w))) p.
Proof. intros. rewrite law_split. unfold law_fields. apply derives_refl. Qed.

Lemma law_globals: forall gv, headptr (gv _law) -> headptr (gv _wifi_scratch) ->
  globvars2pred gv [(_wifi_scratch, LeanosDeviceProgramImage.device_program.code.v_wifi_scratch); (_law, v_law)]
  |-- (data_at_ Ews t_law (gv _law) * scr_ Ews (gv _wifi_scratch))%logic.
Proof.
  intros gv HL HS. unfold globvars2pred, globvar2pred. simpl. rewrite !sepcon_emp.
  assert (FL: field_compatible t_law nil (gv _law)).
  { apply headptr_field_compatible; auto;
      first [ reflexivity | exact I | (vm_compute; reflexivity) | (apply la_env_cs_sound; reflexivity) ]. }
  assert (FS: field_compatible (tarray tuchar SCRATCH) nil (gv _wifi_scratch)).
  { apply headptr_field_compatible; auto;
      first [ reflexivity | exact I | (vm_compute; reflexivity) | (apply la_env_cs_sound; reflexivity) ]. }
  sep_apply (mapsto_zeros_memory_block Ews 262144 (gv _wifi_scratch)); [ auto | ].
  sep_apply (mapsto_zeros_memory_block Ews 400 (gv _law)); [ auto | ].
  change 400 with (sizeof t_law). rewrite (memory_block_data_at_ Ews t_law) by auto.
  rewrite scr__eq. change 262144 with (sizeof (tarray tuchar SCRATCH)).
  rewrite (memory_block_data_at_ Ews (tarray tuchar SCRATCH)) by auto.
  cancel.
Qed.
