(* The body proofs of the four wrappers of patch/madt_admission_unit.c, each one call: from the start of its
   function (Defs.start) to the header function's end, which for that function is a return (envelope_end,
   entries_end, result_end), so `returns` holds. *)
Require Import VST.floyd.proofauto.
Require Import LeanosMadtAdmission.madt_admission.code.
Require Import LeanosMadtAdmission.proof.Defs.
Require Import LeanosMadtAdmission.proof.MgaSpecs.
Require Import LeanosMadtAdmission.proof.InternalSpecs.
#[local] Existing Instance MgaSpecs.CS.
Local Open Scope Z_scope.

Lemma body_madt_envelope (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_madt_envelope (envelope_spec Ora).
Proof.
  start_function.
  match goal with H: i_call x = FEnvelope |- _ => rename H into Hc end.
  assert (Hs: run x (start x) nil = Some (envelope_from x 0 initial_envelope))
    by (unfold start; rewrite Hc; reflexivity).
  forward_call (gv, x, @nil answer, bp, sh).
  Intros vret. destruct vret as [hs st]. cbn [fst snd app] in *.
  match goal with H: run _ _ hs = _ |- _ => rename H into He end.
  forward.
  Exists hs st. entailer!.
  apply returns_return. rewrite He. unfold envelope_end. rewrite Hc.
  destruct (st =? S_OK) eqn:E; [ apply Z.eqb_eq in E; rewrite E | ]; reflexivity.
Qed.

Lemma body_madt_entries (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_madt_entries (entries_spec Ora).
Proof.
  start_function.
  match goal with H: i_call x = FEntries |- _ => rename H into Hc end.
  assert (Hs: run x (start x) nil = Some (begin_entries x)) by (unfold start; rewrite Hc; reflexivity).
  forward_call (gv, x, @nil answer, bp, sh, rp, rsh, vi (i_prior x)).
  Intros vret. destruct vret as [[hs st] id]. cbn [fst snd app] in *.
  match goal with H: run _ _ hs = _ |- _ => rename H into Hn end.
  forward.
  Exists hs st id. entailer!.
  { apply returns_return. rewrite Hn. unfold entries_end. rewrite Hc.
    destruct (st =? S_OK) eqn:E; [ apply Z.eqb_eq in E; rewrite E | ]; reflexivity. }
  destruct (st =? S_OK); apply derives_refl.
Qed.

Lemma body_madt_result (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_madt_result (result_spec Ora).
Proof.
  start_function.
  match goal with H: i_call x = FResult |- _ => rename H into Hc end.
  match goal with H: inputs_ok x |- _ => pose proof H as (Ulen & Lbytes & Ubytes & Uex & Largs & Uargs & Uprior) end.
  assert (Hs: run x (start x) nil = Some (Go (ExpectResult (i_args x) nil)))
    by (unfold start; rewrite Hc; reflexivity).
  forward_call (gv, x, @nil answer, i_args x, rp, rsh, vi (i_prior x)).
  Intros vret. destruct vret as [[hs st] id]. cbn [fst snd app] in *.
  match goal with H: run _ _ hs = _ |- _ => rename H into Hr end.
  forward.
  Exists hs st id. entailer!.
  { apply returns_return. rewrite Hr. reflexivity. }
  destruct (st =? S_OK); apply derives_refl.
Qed.

Lemma body_madt_admission (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_madt_admission (admission_spec Ora).
Proof.
  start_function.
  forward_call (gv, x, bp, sh, rp, rsh).
  Intros vret. destruct vret as [[h st] id]. cbn [fst snd] in *.
  forward.
  Exists h st id. entailer!.
Qed.
