(* Law image_exact: the bodies of the harness's small helpers word_at, any_target, any_u64, same_target and
   same_desc. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import LeanosDeviceProgramImage.harness.image_exact.code.
Require Import LeanosDeviceProgramImage.proof.Defs.
Require Import LeanosDeviceProgramImage.proof.LawProg LeanosDeviceProgramImage.proof.LawSpecs
  LeanosDeviceProgramImage.proof.LawLib.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Lemma body_word_at : semax_body Vlaw Glaw f_word_at word_at_spec.
Proof.
  start_function.
  destruct H1 as [Hlen F].
  assert (B0 := Forall_u8_Znth bs k F ltac:(lia)).
  assert (B1 := Forall_u8_Znth bs (k + 1) F ltac:(lia)).
  assert (B2 := Forall_u8_Znth bs (k + 2) F ltac:(lia)).
  assert (B3 := Forall_u8_Znth bs (k + 3) F ltac:(lia)).
  forward; [ entailer!; rep_lia | ].
  forward; [ entailer!; rep_lia | ].
  forward; [ entailer!; rep_lia | ].
  forward; [ entailer!; rep_lia | ].
  forward.
  entailer!.
  rewrite le32_or by (unfold u8_ok; rep_lia). reflexivity.
Qed.

Lemma body_any_target : semax_body Vlaw Glaw f_any_target any_target_spec.
Proof.
  start_function.
  forward_call. Intros a1. forward.
  forward_call. Intros a2. forward.
  forward_call. Intros a3. forward.
  forward_call. Intros a4. forward.
  forward_call. Intros a5. forward.
  forward_call. Intros a6. forward.
  Exists (mk_target a1 a2 a3 a4 a5 a6).
  entailer!.
  unfold target_wf, u32_ok; simpl; tauto.
Qed.

Lemma body_any_u64 : semax_body Vlaw Glaw f_any_u64 any_u64_spec.
Proof.
  start_function.
  rewrite <- seq_assoc. forward_call. Intros hi. forward.
  rewrite <- seq_assoc. forward_call. Intros lo. forward.
  forward.
  Exists (Int64.unsigned (Int64.or (Int64.shl (Int64.repr hi) (Int64.repr 32)) (Int64.repr lo))).
  entailer!. split; [ apply Int64.unsigned_range_2 | rewrite Int64.repr_unsigned; reflexivity ].
Qed.

Lemma body_same_target : semax_body Vlaw Glaw f_same_target same_target_spec.
Proof.
  start_function.
  destruct H as (A1 & A2 & A3 & A4 & A5 & A6). destruct H0 as (B1 & B2 & B3 & B4 & B5 & B6).
  unfold target_val, target_eqb.
  forward. forward.
  forward_if (temp _t'1 (Vint (Int.repr (Z.b2z ((tg_bus A =? tg_bus B) && (tg_dev A =? tg_dev B))%bool)))).
  { forward. forward. forward. entailer!. bfix. bfin. }
  { forward. entailer!. bfix. bfin. }
  forward_if (temp _t'2 (Vint (Int.repr (Z.b2z ((tg_bus A =? tg_bus B) && (tg_dev A =? tg_dev B) &&
     (tg_fn A =? tg_fn B))%bool)))).
  { forward. forward. forward. entailer!. bfix. bfin. }
  { forward. entailer!. bfix. bfin. }
  forward_if (temp _t'3 (Vint (Int.repr (Z.b2z ((tg_bus A =? tg_bus B) && (tg_dev A =? tg_dev B) &&
     (tg_fn A =? tg_fn B) && (tg_id A =? tg_id B))%bool)))).
  { forward. forward. forward. entailer!. bfix. bfin. }
  { forward. entailer!. bfix. bfin. }
  forward_if (temp _t'4 (Vint (Int.repr (Z.b2z ((tg_bus A =? tg_bus B) && (tg_dev A =? tg_dev B) &&
     (tg_fn A =? tg_fn B) && (tg_id A =? tg_id B) && (tg_window A =? tg_window B))%bool)))).
  { forward. forward. forward. entailer!. bfix. bfin. }
  { forward. entailer!. bfix. bfin. }
  forward_if (temp _t'5 (Vint (Int.repr (Z.b2z ((tg_bus A =? tg_bus B) && (tg_dev A =? tg_dev B) &&
     (tg_fn A =? tg_fn B) && (tg_id A =? tg_id B) && (tg_window A =? tg_window B) &&
     (tg_bar A =? tg_bar B))%bool)))).
  { forward. forward. forward. entailer!. bfix. bfin. }
  { forward. entailer!. bfix. bfin. }
  forward.
Qed.

Lemma body_same_desc : semax_body Vlaw Glaw f_same_desc same_desc_spec.
Proof.
  start_function.
  destruct H as (A1 & A2 & A3 & A4). destruct H0 as (B1 & B2 & B3 & B4).
  unfold desc_val, desc_eqb.
  forward. forward.
  forward_if (temp _t'1 (Vint (Int.repr (Z.b2z ((ds_trb A =? ds_trb B) && (ds_start A =? ds_start B))%bool)))).
  { forward. forward. forward. entailer!. bfix. bfin. }
  { forward. entailer!. bfix. bfin. }
  forward_if (temp _t'2 (Vint (Int.repr (Z.b2z ((ds_trb A =? ds_trb B) && (ds_start A =? ds_start B) &&
     (ds_count A =? ds_count B))%bool)))).
  { forward. forward. forward. entailer!. bfix. bfin. }
  { forward. entailer!. bfix. bfin. }
  forward_if (temp _t'3 (Vint (Int.repr (Z.b2z ((ds_trb A =? ds_trb B) && (ds_start A =? ds_start B) &&
     (ds_count A =? ds_count B) && (ds_stride A =? ds_stride B))%bool)))).
  { forward. forward. forward. entailer!. bfix. bfin. }
  { forward. entailer!. bfix. bfin. }
  forward.
Qed.
