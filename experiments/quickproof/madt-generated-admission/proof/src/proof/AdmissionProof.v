(* The body proof of madt_generated_admission (include/madt_generated_admission.h): the envelope from the start
   of an admission, on OK the entries (envelope_end of an admission is begin_entries) into the local
   admitted_apic_id, on OK the result with admission_args (entries_end of an admission asks it), whose status
   and APIC ID the admission returns. *)
Require Import VST.floyd.proofauto.
Require Import LeanosMadtAdmission.madt_admission.code.
Require Import LeanosMadtAdmission.proof.Defs.
Require Import LeanosMadtAdmission.proof.MgaSpecs.
Require Import LeanosMadtAdmission.proof.InternalSpecs.
Require Import LeanosMadtAdmission.proof.BodyLemmas.
#[local] Existing Instance MgaSpecs.CS.
Local Open Scope Z_scope.

Lemma body_madt_generated_admission (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_madt_generated_admission (generated_admission_spec Ora).
Proof.
  start_function.
  match goal with H: i_call x = FAdmission |- _ => rename H into Hc end.
  match goal with H: inputs_ok x |- _ => rename H into Hok end.
  pose proof Hok as (Ulen & Lbytes & Ubytes & Uex & Largs & Uargs & Uprior).
  assert (Hs: run x (start x) nil = Some (envelope_from x 0 initial_envelope))
    by (unfold start; rewrite Hc; reflexivity).
  forward_call (gv, x, @nil answer, bp, sh).
  Intros vret. destruct vret as [hs st]. cbn [fst snd app] in *.
  match goal with H: run _ _ hs = _ |- _ => rename H into He end.
  forward_if (st = S_OK).
  { (* the envelope rejects *)
    z64. forward.
    Exists hs st 0. rewrite (proj2 (Z.eqb_neq st S_OK)) by exact H. entailer!.
    try match goal with |- _ /\ u32_ok _ => split; [ | unfold u32_ok; rep_lia ] end.
    apply returns_return. rewrite He. unfold envelope_end. rewrite (proj2 (Z.eqb_neq st S_OK)) by exact H.
    reflexivity. }
  { forward. entailer!. }
  Intros. subst st.
  assert (He': run x (start x) hs = Some (begin_entries x)) by (rewrite He; unfold envelope_end; rewrite Hc; reflexivity).
  forward.
  forward_call (gv, x, hs, bp, sh, v_admitted_apic_id, Tsh, vi 0).
  Intros vret. destruct vret as [[hs2 st2] id]. cbn [fst snd] in *.
  match goal with H: run _ _ (hs ++ hs2) = _ |- _ => rename H into Hn end.
  forward_if (st2 = S_OK).
  { (* the entries reject *)
    z64. forward.
    Exists (hs ++ hs2) st2 0. rewrite (proj2 (Z.eqb_neq st2 S_OK)) by exact H. entailer!.
    try match goal with |- _ /\ u32_ok _ => split; [ | unfold u32_ok; rep_lia ] end.
    apply returns_return. rewrite Hn. rewrite ent_end_reject by exact H. reflexivity. }
  { forward. entailer!. }
  Intros. subst st2. rewrite Z.eqb_refl in *.
  assert (Hr: run x (start x) (hs ++ hs2) = Some (Go (ExpectResult (admission_args x id) nil)))
    by (rewrite Hn; unfold entries_end; rewrite Hc; reflexivity).
  assert (Ua: Forall u64_ok (admission_args x id)).
  { unfold admission_args. repeat constructor; try u64. }
  forward.
  forward_call (gv, x, hs ++ hs2, admission_args x id, rp, rsh, vi (i_prior x)).
  { (* the casts of admitted_apic_id and executing_apic_id to uint64_t *)
    entailer!. unfold admission_args, vi, vl. simpl.
    rewrite !Int.unsigned_repr by (unfold u32_ok in *; rep_lia). reflexivity. }
  Intros vret. destruct vret as [[hs3 st3] id3]. cbn [fst snd] in *.
  match goal with H: run _ _ ((hs ++ hs2) ++ hs3) = _ |- _ => rename H into Hf end.
  forward.
  Exists ((hs ++ hs2) ++ hs3) st3 id3.
  entailer!.
  { apply returns_return. exact Hf. }
  destruct (st3 =? S_OK); apply derives_refl.
Qed.
