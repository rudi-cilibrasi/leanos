(* Law image_exact: read_image for version 3: the flags, policy window and sink checks, the policy and its sinks,
   and (LawReadDesc) the descriptor map. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import LeanosDeviceProgramImage.harness.image_exact.code.
Require Import LeanosDeviceProgramImage.proof.Defs.
Require Import LeanosDeviceProgramImage.proof.LawProg LeanosDeviceProgramImage.proof.LawSpecs
  LeanosDeviceProgramImage.proof.LawLib LeanosDeviceProgramImage.proof.LawSplit
  LeanosDeviceProgramImage.proof.LawFacts LeanosDeviceProgramImage.proof.LawReadDefs
  LeanosDeviceProgramImage.proof.LawReadDesc.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.
Local Opaque Z.shiftr Z.land.

(* The state at the branch on version 3: the target read, the policy's scalars 0, at 32. *)
Definition ri_pre3 (sh: share) (b: val) (bs: list Z) (wsh: share) (r: val) : environ -> mpred :=
  (PROP (v3_ok bs)
   LOCAL (temp _window (Vint (Int.repr (le32 bs 24))); temp _p (offset_val 32 r); temp _b b;
          temp _len (Vint (Int.repr (Zlength bs))); temp _r r)
   SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) b;
        ri_rep wsh r (Vint (Int.repr 2)) Vundef (target_val (target_of bs)) z32 z32 z32 z64 z64 z32 z32 z32
          (Zrepeat Vundef 8) z32 (Zrepeat udesc 16) Vundef Vundef (Vint (Int.repr 2))))%assert.

Lemma upd_sub_fill {A B} {da: Inhabitant A} {db: Inhabitant B}: forall (f: A -> B) (l: list A) i n (u: B),
  0 <= i < n -> i < Zlength l ->
  upd_Znth i (map f (sublist 0 i l) ++ Zrepeat u (n - i)) (f (Znth i l)) =
  map f (sublist 0 (i + 1) l) ++ Zrepeat u (n - (i + 1)).
Proof. intros. list_solve. Qed.

Lemma le64_eq: forall bs k, le64 bs k = le32 bs k + le32 bs (k + 4) * 4294967296.
Proof. reflexivity. Qed.

Lemma cfg_val: forall bs k k', k' = k + 4 -> Forall u8_ok bs ->
  Int64.or (Int64.shl (Int64.repr (Int.unsigned (Int.repr (le32 bs k')))) (Int64.repr (Int.unsigned (Int.repr 32))))
    (Int64.repr (Int.unsigned (Int.repr (le32 bs k)))) = Int64.repr (le64 bs k).
Proof.
  intros bs k k' E F. subst k'. pose proof (le32_range bs k F). pose proof (le32_range bs (k + 4) F). unfold u32_ok in *.
  rewrite !Int.unsigned_repr by rep_lia. rewrite or64_hi_lo by (unfold u32_ok; lia). reflexivity.
Qed.

Lemma ri_v3 {Espec: OracleKind}: forall sh b bs wsh r,
  readable_share sh -> writable_share wsh -> image_ok bs -> field_compatible t_law_image nil r ->
  semax ri_delta (ri_pre3 sh b bs wsh r) s_v3 (overridePost (ri_join sh b bs wsh r) (ri_post sh b bs wsh r)).
Proof.
  intros sh b bs wsh r SH WSH IM FCr.
  start_part. unfold ri_pre3. Intros.
  rename H into V3. pose proof IM as [Hlen F]. pose proof V3 as [[[HD1 HD2] [_ L23]] [TOK VER]].
  rewrite VER in L23. simpl in L23.
  assert (W: forall k, u32_ok (le32 bs k)) by (intros; apply le32_range; auto).
  pose proof (W 32) as W32. pose proof (W 64) as W64. pose proof (W 36) as W36. pose proof (W 24) as W24.
  unfold ri_rep, pol_fields. Intros.
  forward_call (sh, b, bs, 32).
  forward_call (sh, b, bs, 64).
  forward_if (temp _t'18 (Vint (Int.repr (Z.b2z ((3 <? le32 bs 32) || (le32 bs 36 <? le32 bs 24))%bool)))).
  { forward. entailer!. bfix. bdec. }
  { forward_call (sh, b, bs, 36). forward. entailer!. bfix. bdec. }
  forward_if (temp _t'20 (Vint (Int.repr (Z.b2z ((3 <? le32 bs 32) || (le32 bs 36 <? le32 bs 24) ||
    (8 <? le32 bs 64))%bool)))).
  { forward. entailer!. bfix. bdec. }
  { forward. entailer!. bfix. bdec. }
  forward_if (temp _t'21 (Vint (Int.repr (Z.b2z ((3 <? le32 bs 32) || (le32 bs 36 <? le32 bs 24) ||
    (8 <? le32 bs 64) || (Zlength bs <? 68 + 4 * le32 bs 64))%bool)))).
  { forward. entailer!. bfix. bdec. }
  { forward. entailer!. bfix. bsplit.
    bdec. }
  forward_if.
  { bfix. ri_ret FCr.
    assert (D: decode bs = None).
    { apply dec_v3_bad; auto.
      destruct (Z.ltb_spec 3 (le32 bs 32)); [ left; lia | ].
      destruct (Z.ltb_spec (le32 bs 36) (le32 bs 24)); [ right; left; lia | ].
      destruct (Z.ltb_spec 8 (le32 bs 64)); [ right; right; left; lia | ].
      destruct (Z.ltb_spec (Zlength bs) (68 + 4 * le32 bs 64)); [ right; right; right; lia | ].
      match goal with H: (_ || _)%bool = true |- _ => simpl in H; discriminate end. }
    unfold reading_ok, header_status, start_status, start. rewrite D. auto. }
  bfix. bsplit.
  assert (V3s: v3s_ok bs) by (split; [ exact V3 | repeat split; lia ]).
  forward.
  forward.
  forward_call (sh, b, bs, 36). forward.
  forward_call (sh, b, bs, 44). forward_call (sh, b, bs, 40). forward.
  forward_call (sh, b, bs, 52). forward_call (sh, b, bs, 48). forward.
  forward_call (sh, b, bs, 56). forward.
  forward_call (sh, b, bs, 60). forward.
  forward.
  rewrite (cfg_val bs 40 44), (cfg_val bs 48 52) by (auto; lia).
  rewrite and_u32 by (unfold u32_ok in *; rep_lia).
  set (S := le32 bs 64) in *.
  assert (LS: Zlength (sinks_at bs S) = S) by (apply Zlength_sinks_at; unfold u32_ok in *; lia).
  forward_for_simple_bound S (EX i: Z,
    PROP ()
    LOCAL (temp _sinks (Vint (Int.repr S)); temp _flags (Vint (Int.repr (le32 bs 32)));
           temp _p (offset_val 32 r); temp _b b; temp _len (Vint (Int.repr (Zlength bs))); temp _r r)
    SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes_val bs) b;
         ri_rep wsh r (Vint (Int.repr 2)) Vundef (target_val (target_of bs))
           (Vint (Int.repr 1)) (Vint (Int.repr (Z.land (le32 bs 32) 1))) (Vint (Int.repr (le32 bs 36)))
           (Vlong (Int64.repr (le64 bs 40))) (Vlong (Int64.repr (le64 bs 48))) (Vint (Int.repr (le32 bs 56)))
           (Vint (Int.repr (le32 bs 60))) (Vint (Int.repr S))
           (words_val (sublist 0 i (sinks_at bs S)) ++ Zrepeat Vundef (8 - i)) z32 (Zrepeat udesc 16)
           Vundef Vundef (Vint (Int.repr 2))))%assert.
  { unfold ri_rep, pol_fields. entailer!. }
  { unfold ri_rep, pol_fields. Intros.
    forward_call (sh, b, bs, 68 + 4 * i).
    forward.
    rewrite <- (Znth_sinks_at bs S i) by lia.
    rewrite (upd_sub_fill (fun w => Vint (Int.repr w)) (sinks_at bs S) i 8) by lia.
    unfold ri_rep, pol_fields. entailer!. }
  rewrite sublist_same by lia.
  forward.
  assert (WF: u32_ok (Z.land (le32 bs 32) 2)) by (apply land_u32; unfold u32_ok in *; lia).
  forward_if.
  - rewrite and_u32 in H3 by (unfold u32_ok in *; rep_lia). apply repr_neq_e in H3.
    eapply semax_pre; [ | apply ri_desc; auto ].
    unfold ri_predesc. entailer!.
  - rewrite and_u32 in H3 by (unfold u32_ok in *; rep_lia).
    apply repr_u32_inj in H3; [ | auto | unfold u32_ok; rep_lia ].
    forward.
    Exists (target_of bs) (v3_policy bs S 0 nil) (68 + 4 * S) (Zrepeat Vundef (8 - S)) (Zrepeat udesc 16).
    unfold v3_policy;
      cbn [pl_present pl_dma pl_window pl_cfg_read pl_cfg_write pl_cmd_clear pl_cmd_set pl_sink_count
           pl_sinks pl_desc_count pl_descs].
    simpl map. rewrite app_nil_l. unfold z32.
    entailer!. apply dec_v3_nodesc; auto.
Qed.
