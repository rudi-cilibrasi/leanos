(* Law image_exact: read_image after the target and policy are read: the status, header length, N and B, and the
   start status. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import LeanosDeviceProgramImage.harness.image_exact.code.
Require Import LeanosDeviceProgramImage.proof.Defs.
Require Import LeanosDeviceProgramImage.proof.LawProg LeanosDeviceProgramImage.proof.LawSpecs
  LeanosDeviceProgramImage.proof.LawLib LeanosDeviceProgramImage.proof.LawSplit
  LeanosDeviceProgramImage.proof.LawReadDefs.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Lemma start_status_eq: forall bs T P H, decode bs = Some (T, P, H) ->
  start_status bs = if sizes_ok bs H then 0 else BAD.
Proof. intros. unfold start_status, start. rewrite H0. destruct (sizes_ok bs H); reflexivity. Qed.

(* read_image's postcondition as the tail (the last statement of the body) has it. *)
Definition ri_npost (sh: share) (b: val) (bs: list Z) (wsh: share) (r: val) : ret_assert :=
  normal_ret_assert
    (@sepcon (environ -> mpred) _ _
      ((EX (st hl : val) (tv : target_t) (pv : policy_t) (nv blv sst : val),
        PROP (reading_ok bs st hl tv pv nv blv sst)
        RETURN ( ) SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) b;
                        data_at wsh t_law_image (law_image_val st hl tv pv nv blv sst) r))%argsassert)
      (stackframe_of f_read_image)).

Lemma ri_tail {Espec: OracleKind}: forall sh b bs wsh r,
  readable_share sh -> writable_share wsh -> image_ok bs -> field_compatible t_law_image nil r ->
  semax ri_delta (ri_join sh b bs wsh r) s_tail (ri_npost sh b bs wsh r).
Proof.
  intros sh b bs wsh r SH WSH IM FCr.
  unfold ri_npost. start_part. unfold ri_join. Intros T P H ss ds.
  destruct IM as [Hlen F].
  pose proof (decode_wf bs T P H F H0) as (TW & PW & HR).
  unfold ri_rep, pol_fields. Intros.
  forward. forward.
  forward_call (sh, b, bs, 8). { repeat split; auto; lia. }
  forward.
  forward_call (sh, b, bs, 12). { repeat split; auto; lia. }
  forward.
  forward.
  assert (Wn: u32_ok (le32 bs 8)) by (apply le32_range; auto).
  assert (Wb: u32_ok (le32 bs 12)) by (apply le32_range; auto).
  assert (E1: Int.divu (Int.sub (Int.repr (Zlength bs)) (Int.repr H)) (Int.repr 16) =
              Int.repr ((Zlength bs - H) / 16)).
  { rewrite sub_repr, divu_u32 by (unfold u32_ok; rep_lia). reflexivity. }
  assert (R1: 0 <= (Zlength bs - H) / 16 <= Int.max_unsigned).
  { split; [ apply Z.div_pos; lia | ]. apply Z.le_trans with (Zlength bs - H); [ apply Z.div_le_upper_bound; lia | lia ]. }
  forward_if (temp _t'41 (Vint (Int.repr (Z.b2z (sizes_ok bs H))))).
  - forward. forward. forward. entailer!.
    rewrite E1 in *. bfix.
    assert (0 <= Zlength bs - H - 16 * le32 bs 8 <= Int.max_unsigned).
    { assert (16 * le32 bs 8 <= Zlength bs - H). { pose proof (Z.mul_div_le (Zlength bs - H) 16). lia. }
      unfold u32_ok in *; rep_lia. }
    rewrite Int_eq_u32 by (unfold u32_ok in *; lia).
    unfold sizes_ok. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
  - forward. entailer!.
    rewrite E1 in *. bfix.
    unfold sizes_ok. rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
  - forward_if.
    + forward. ri_exists. rewrite ri_rep_eq by exact FCr. unfold ri_rep, pol_fields. entailer!.
      bfix. unfold reading_ok, header_status. rewrite H0. split; [ reflexivity | split ].
      * erewrite start_status_eq by eauto. rewrite H1. reflexivity.
      * repeat split; auto. exists ss, ds. reflexivity.
    + forward. ri_exists. rewrite ri_rep_eq by exact FCr. unfold ri_rep, pol_fields. entailer!.
      bfix. unfold reading_ok, header_status. rewrite H0. split; [ reflexivity | split ].
      * erewrite start_status_eq by eauto. rewrite H1. reflexivity.
      * repeat split; auto. exists ss, ds. reflexivity.
Qed.
