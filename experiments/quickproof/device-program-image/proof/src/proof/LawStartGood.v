(* Law image_exact: start_case when the law's reading says the start succeeds: every check of that branch. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import LeanosDeviceProgramImage.harness.image_exact.code.
Require Import LeanosDeviceProgramImage.proof.Defs.
Require LeanosDeviceProgramImage.proof.Specs.
Require Import LeanosDeviceProgramImage.proof.LawProg LeanosDeviceProgramImage.proof.LawSpecs
  LeanosDeviceProgramImage.proof.LawLib LeanosDeviceProgramImage.proof.LawLaw
  LeanosDeviceProgramImage.proof.LawSplit LeanosDeviceProgramImage.proof.LawStartDefs
  LeanosDeviceProgramImage.proof.LawStartTail.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Lemma target_eqb_refl: forall T, target_eqb T T = true.
Proof. intros. unfold target_eqb. rewrite !Z.eqb_refl. reflexivity. Qed.

Lemma start_some: forall bs T P H N B, start bs = Some (T, P, H, N, B) ->
  decode bs = Some (T, P, H) /\ N = le32 bs 8 /\ B = le32 bs 12 /\ sizes_ok bs H = true.
Proof.
  intros bs T P H N B E. unfold start in E. destruct (decode bs) as [[[T' P'] H']|] eqn:D; [ | discriminate ].
  destruct (sizes_ok bs H') eqn:SZ; [ | discriminate ]. inversion E; subst. auto.
Qed.

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
Ltac unfocus :=
  match goal with |- context [?A -* ?B] => sep_apply (modus_ponens_wand A B) end.

Lemma sc_good {Espec: OracleKind}: forall gv msh m lv cl cp pv ish image bs vm prior saved n0 b0 w0 P0 T0 rs ss
    sp0 pc0 st0 (S: list Z) T P H N B,
  lv = (cl, (Vint (Int.repr (Zlength bs)), (cp, (Vint (Int.repr 0), (Vint (Int.repr H),
           (target_val T, (pv, (Vint (Int.repr N), (Vint (Int.repr B), Vint (Int.repr 0)))))))))) ->
  readable_share msh -> readable_share ish -> image_ok bs -> field_compatible t_vm nil vm ->
  start bs = Some (T, P, H, N, B) -> pol_declares P pv -> policy_wf P0 ->
  Zlength ss = 16 -> Zlength S = SCRATCH -> Forall (fun b => 0 <= b <= Byte.max_unsigned) S ->
  semax sc_delta
   (PROP ()
    LOCAL (temp _status (Vint (Int.repr 0)); temp _scratch (gv _wifi_scratch); temp _saved saved;
           temp _prior prior; temp _vm vm; gvars gv; temp _m m; temp _image image)
    SEP (data_at ish (tarray tuchar (Zlength bs)) (bytes_val bs) image;
         data_at Ews t_vm (vm_val (started image (vm0 n0 b0 w0 P0 T0 rs ss sp0 pc0 st0) T P H N B)) vm;
         scr Ews (Zrepeat (Vint (Int.repr 0)) SCRATCH) (gv _wifi_scratch); mem_mgr gv;
         data_at msh t_law lv m;
         scr Ews (bytes_val S) saved;
         vm_fields Ews prior Vundef Vundef (Vint (Int.repr n0)) (Vint (Int.repr b0)) (Vint (Int.repr w0))
           (policy_val P0) (default_val t_target) (words_val rs) (words_val ss) (Vint (Int.repr sp0))
           (Vint (Int.repr pc0)) (Vlong (Int64.repr st0));
         TT))
   s_sc_good
   (overridePost (sc_join gv msh lv m ish image bs vm prior ss) (sc_post gv msh lv m ish image bs)).
Proof.
  intros until B. intros Elv SH SH0 IM FCvm ST PD WP0 Lss LS FS. subst lv.
  destruct (start_some bs T P H N B ST) as (D & EN & EB & SZ).
  destruct IM as [Hlen F].
  pose proof (decode_wf bs T P H F D) as (TW & PW & HR).
  start_sc_part.
  unfold vm_val, started, vm0, vm_rep;
    cbn [vm_code vm_blob vm_n vm_blob_len vm_window vm_pol vm_target vm_r vm_stack vm_sp vm_pc vm_steps].
  rewrite vm_split by auto. unfold vm_fields. Intros.
  gp_one.
  assert_PROP (field_compatible t_law (DOT _want DOT _t) m /\ field_compatible t_law (DOT _want DOT _pol) m)
    as FCtp by (entailer!; split; auto with field_compatible).
  destruct FCtp as [FCt FCp].
  match goal with |- context [data_at msh t_law ?lv m] => sep_apply (want_t_focus msh lv m) end.
  unfold lv_t; simpl fst; simpl snd. Intros.
  forward_call (Ews, offset_val 368 vm, T, msh, field_address t_law (DOT _want DOT _t) m, T).
  rewrite target_eqb_refl. unfocus.
  gp_one.
  match goal with |- context [data_at msh t_law ?lv m] => sep_apply (want_pol_focus msh lv m) end.
  unfold lv_pol; simpl fst; simpl snd. Intros.
  forward_call (Ews, offset_val 32 vm, msh, field_address t_law (DOT _want DOT _pol) m, pv, Ews, offset_val 32 prior,
    P, P0).
  unfocus.
  destruct TW as (T1 & T2 & T3 & T4 & T5 & T6).
  forward. forward.
  forward_if (temp _t'22 (Vint (Int.repr 1))).
  { forward. forward. forward. eq_true_branch. }
  { eq_false_branch. }
  forward_if (temp _t'23 (Vint (Int.repr 1))).
  { forward. forward. forward. eq_true_branch. }
  { eq_false_branch. }
  gp_one.
  assert (SZ': N <= (Zlength bs - H) / 16 /\ B = Zlength bs - H - 16 * N).
  { unfold sizes_ok in SZ. subst N B. apply andb_true_iff in SZ as [A1 A2].
    apply Z.leb_le in A1. apply Z.eqb_eq in A2. auto. }
  destruct SZ' as [SZ1 SZ2].
  assert (WN: 0 <= N) by (subst N; pose proof (le32_range bs 8 F); unfold u32_ok in *; lia).
  assert (HN: H + 16 * N <= Zlength bs) by (pose proof (Z.mul_div_le (Zlength bs - H) 16); lia).
  eapply semax_pre; [ | apply (sc_good_tail gv msh m (cl, (Vint (Int.repr (Zlength bs)), (cp, (Vint (Int.repr 0),
    (Vint (Int.repr H), (target_val T, (pv, (Vint (Int.repr N), (Vint (Int.repr B), Vint (Int.repr 0))))))))))
    cl cp pv T H N B ish image bs vm prior saved ss); auto; try lia ].
  unfold vm_fields. entailer!.
Qed.
