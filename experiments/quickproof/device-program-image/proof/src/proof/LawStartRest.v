(* Law image_exact: start_case from the call of dp_start on: the call, the branch on the law's reading
   (LawStartBad, LawStartGood) and the comparison of the stacks. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import LeanosDeviceProgramImage.harness.image_exact.code.
Require Import LeanosDeviceProgramImage.proof.Defs.
Require LeanosDeviceProgramImage.proof.Specs.
Require Import LeanosDeviceProgramImage.proof.LawProg LeanosDeviceProgramImage.proof.LawSpecs
  LeanosDeviceProgramImage.proof.LawLib LeanosDeviceProgramImage.proof.LawLaw
  LeanosDeviceProgramImage.proof.LawSplit LeanosDeviceProgramImage.proof.LawStartDefs
  LeanosDeviceProgramImage.proof.LawStartBad LeanosDeviceProgramImage.proof.LawStartGood.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Lemma start_header: forall bs, start_status bs = 0 -> header_status bs = 0.
Proof.
  intros bs E. unfold start_status, start in E. unfold header_status.
  destruct (decode bs) as [[[T P] H]|]; [ reflexivity | discriminate ].
Qed.

Lemma header_status_range: forall bs, 0 <= header_status bs <= 2.
Proof. intros. unfold header_status. destruct (decode bs); unfold BAD; lia. Qed.

Lemma start_status_range: forall bs, 0 <= start_status bs <= 2.
Proof. intros. unfold start_status. destruct (start bs); unfold BAD; lia. Qed.

Lemma start_ok: forall bs, start_status bs = 0 -> exists T P H N B, start bs = Some (T, P, H, N, B).
Proof.
  intros bs E. unfold start_status in E. destruct (start bs) as [[[[[T P] H] N] B]|]; [ eauto 6 | discriminate ].
Qed.

Lemma start_bad: forall bs, start_status bs <> 0 -> start bs = None.
Proof. intros bs E. unfold start_status in E. destruct (start bs); [ contradiction | reflexivity ]. Qed.

Lemma start_status_2: forall bs, start_status bs <> 0 -> start_status bs = 2.
Proof. intros bs E. unfold start_status in *. destruct (start bs); [ contradiction | reflexivity ]. Qed.

Lemma start_status_0: forall bs, start bs = None -> start_status bs = 2.
Proof. intros bs E. unfold start_status. rewrite E. reflexivity. Qed.

Local Opaque decode le32 header_status start_status start.

Lemma sc_rest {Espec: OracleKind}: forall gv msh m lv ish image bs vm prior saved n0 b0 w0 P0 T0 rs ss sp0 pc0 st0
    (S: list Z),
  readable_share msh -> readable_share ish -> image_ok bs -> law_reads bs lv ->
  field_compatible t_vm nil vm -> field_compatible t_vm nil prior ->
  u32_ok n0 -> u32_ok b0 -> u32_ok w0 -> policy_wf P0 -> target_wf T0 -> Zlength rs = 16 -> Forall u32_ok rs ->
  Zlength ss = 16 -> Forall u32_ok ss -> u32_ok sp0 -> u32_ok pc0 -> u64_ok st0 -> Zlength S = SCRATCH ->
  Forall (fun b => 0 <= b <= Byte.max_unsigned) S ->
  semax sc_delta
   (PROP ()
    LOCAL (temp _scratch (gv _wifi_scratch); temp _saved saved; temp _prior prior; temp _vm vm; gvars gv;
           temp _m m; temp _image image)
    SEP (mem_mgr gv; data_at msh t_law lv m; data_at ish (tarray tuchar (Zlength bs)) (bytes_val bs) image;
         scr Ews (bytes_val S) (gv _wifi_scratch); scr Ews (bytes_val S) saved;
         vm_fields Ews vm nullval nullval (Vint (Int.repr n0)) (Vint (Int.repr b0)) (Vint (Int.repr w0))
           (policy_val P0) (target_val T0) (words_val rs) (words_val ss) (Vint (Int.repr sp0))
           (Vint (Int.repr pc0)) (Vlong (Int64.repr st0));
         vm_fields Ews prior Vundef Vundef (Vint (Int.repr n0)) (Vint (Int.repr b0)) (Vint (Int.repr w0))
           (policy_val P0) (default_val t_target) (words_val rs) (words_val ss) (Vint (Int.repr sp0))
           (Vint (Int.repr pc0)) (Vlong (Int64.repr st0));
         TT))
   s_sc_rest (sc_post gv msh lv m ish image bs).
Proof.
  intros until S. intros SH SH0 IM LR FCvm FCpr Wn Wb Ww WP WT Lrs Frs Lss Fss Wsp Wpc Wst LS FS.
  start_sc_part.
  destruct lv as (cl & len & cp & st & hl & tv & pv & nv & blv & sst).
  destruct LR as [Elen RO]. subst len.
  forward.
  rewrite <- (vm_split Ews vm) by auto.
  change (nullval, (nullval, (Vint (Int.repr n0), (Vint (Int.repr b0), (Vint (Int.repr w0), (policy_val P0,
    (target_val T0, (words_val rs, (words_val ss, (Vint (Int.repr sp0), (Vint (Int.repr pc0),
     Vlong (Int64.repr st0))))))))))))
    with (vm_val (vm0 n0 b0 w0 P0 T0 rs ss sp0 pc0 st0)).
  rewrite scr_eq.
  rewrite (vm_cs Ews (vm_val (vm0 n0 b0 w0 P0 T0 rs ss sp0 pc0 st0)) vm), (bytes_cs ish (Zlength bs) (bytes_val bs) image),
    (bytes_cs Ews SCRATCH (bytes_val S) (gv _wifi_scratch)).
  assert (VW: vm_wf (vm0 n0 b0 w0 P0 T0 rs ss sp0 pc0 st0))
    by (unfold vm_wf, vm0, STACK_DEPTH;
        cbn [vm_code vm_blob vm_n vm_blob_len vm_window vm_pol vm_target vm_r vm_stack vm_sp vm_pc vm_steps]; tauto).
  freeze FRC := (mem_mgr gv) (data_at msh t_law _ m) (scr _ _ saved) (vm_fields _ prior _ _ _ _ _ _ _ _ _ _ _ _) TT.
  forward_call (gv, ish, image, bs, Ews, vm, vm0 n0 b0 w0 P0 T0 rs ss sp0 pc0 st0, Ews, bytes_val S).
  { rewrite Zlength_map; auto. }
  Intros vret. destruct vret as [vv sc']. simpl fst in *; simpl snd in *.
  change S.t_vm with t_vm. change S.t_scratch with (tarray tuchar SCRATCH).
  rewrite <- vm_cs, <- !bytes_cs.
  change (gv LeanosDeviceProgramImage.device_program.code._wifi_scratch) with (gv _wifi_scratch).
  forward.
  thaw FRC.
  destruct RO as (Est & Esst & RD). subst st sst.
  pose proof (header_status_range bs) as HSR. pose proof (start_status_range bs) as SSR.
  forward.
  forward_if (temp _t'26 (Vint (Int.repr (Z.b2z (negb (start_status bs =? 0)))))).
  { forward. entailer!. bfix.
    destruct (Z.eqb_spec (start_status bs) 0) as [E|E]; [ apply start_header in E; contradiction | reflexivity ]. }
  { forward. forward. entailer!.
    destruct (zeq (start_status bs) 0) as [E|E]; [ rewrite E | rewrite (proj2 (Z.eqb_neq _ _) E) ]; reflexivity. }
  forward_if (sc_join gv msh (cl, (Vint (Int.repr (Zlength bs)), (cp, (Vint (Int.repr (header_status bs)),
    (hl, (tv, (pv, (nv, (blv, Vint (Int.repr (start_status bs))))))))))) m ish image bs vm prior ss).
  - (* the start fails *)
    assert (SS: start_status bs <> 0).
    { first
      [ match goal with Hc: (start_status bs =? 0) = false |- _ => apply Z.eqb_neq; exact Hc end
      | bfix; match goal with Hc: negb (start_status bs =? 0) = true |- _ =>
          apply negb_true_iff, Z.eqb_neq in Hc; exact Hc end ]. }
    assert (SB0: start bs = None) by (apply start_bad; auto).
    assert (SS2: start_status bs = 2) by (apply start_status_0; auto).
    match goal with Hs: S.start_post _ _ _ _ _ _ |- _ => unfold S.start_post in Hs; rewrite SB0 in Hs;
      destruct Hs as [(pv' & tv' & Evv) Esc] end.
    subst vv sc'. rewrite <- (scr_eq Ews (bytes_val S) (gv _wifi_scratch)).
    unfold vm0; cbn [vm_code vm_blob vm_n vm_blob_len vm_window vm_r vm_stack vm_sp vm_pc vm_steps].
    eapply semax_pre; [ | apply (sc_bad gv msh m (cl, (Vint (Int.repr (Zlength bs)), (cp, (Vint (Int.repr (header_status bs)),
      (hl, (tv, (pv, (nv, (blv, Vint (Int.repr (start_status bs))))))))))) ish image bs vm prior saved n0 b0 w0 P0 pv' tv' rs ss sp0 pc0 st0 S);
                           auto ].
    rewrite SS2. entailer!.
  - (* the start succeeds *)
    assert (SS0: start_status bs = 0).
    { first
      [ match goal with Hc: (start_status bs =? 0) = true |- _ => apply Z.eqb_eq; exact Hc end
      | bfix; match goal with Hc: negb (start_status bs =? 0) = false |- _ =>
          apply negb_false_iff, Z.eqb_eq in Hc; exact Hc end ]. }
    destruct (start_ok bs SS0) as (T & P & Hd & N & B & SOK).
    pose proof (start_header bs SS0) as HS0.
    match goal with Hs: S.start_post _ _ _ _ _ _ |- _ => unfold S.start_post in Hs; rewrite SOK in Hs;
      destruct Hs as [Evv Esc] end.
    subst vv sc'. rewrite <- (scr_eq Ews (Zrepeat (Vint (Int.repr 0)) SCRATCH) (gv _wifi_scratch)).
    destruct (start_some bs T P Hd N B SOK) as (D & EN & EB & SZ).
    rewrite D in RD. cbv beta iota in RD. destruct RD as (Ehl & Etv & PD & Env & Eblv).
    assert (Elv: (cl, (Vint (Int.repr (Zlength bs)), (cp, (Vint (Int.repr (header_status bs)),
      (hl, (tv, (pv, (nv, (blv, Vint (Int.repr (start_status bs))))))))))) = (cl, (Vint (Int.repr (Zlength bs)), (cp, (Vint (Int.repr 0), (Vint (Int.repr Hd),
      (target_val T, (pv, (Vint (Int.repr N), (Vint (Int.repr B), Vint (Int.repr 0)))))))))))
      by (rewrite HS0, SS0, Ehl, Etv, Env, Eblv, <- EN, <- EB; reflexivity).
    eapply semax_pre; [ | apply (sc_good gv msh m (cl, (Vint (Int.repr (Zlength bs)), (cp, (Vint (Int.repr (header_status bs)),
      (hl, (tv, (pv, (nv, (blv, Vint (Int.repr (start_status bs))))))))))) cl cp pv ish image bs vm prior saved n0 b0 w0 P0 T0 rs ss
                                   sp0 pc0 st0 S T P Hd N B); auto ].
    rewrite SS0. entailer!.
  - (* the stacks *)
    unfold sc_join. Intros.
    forward_for_simple_bound 16 (EX i: Z,
      PROP ()
      LOCAL (temp _vm vm; temp _prior prior; gvars gv; temp _m m; temp _image image)
      SEP (mem_mgr gv; data_at msh t_law (cl, (Vint (Int.repr (Zlength bs)), (cp, (Vint (Int.repr (header_status bs)),
      (hl, (tv, (pv, (nv, (blv, Vint (Int.repr (start_status bs))))))))))) m;
           data_at ish (tarray tuchar (Zlength bs)) (bytes_val bs) image;
           field_at Ews t_vm (DOT _stack) (map (fun w => Vint (Int.repr w)) ss) vm;
           field_at Ews t_vm (DOT _stack) (map (fun w => Vint (Int.repr w)) ss) prior;
           TT))%assert.
    { entailer!. }
    { forward. forward. gp_one. }
    entailer!.
Qed.
