(* Law capabilities_complete: the body of main, under the compspecs of the law's whole program. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosCaps.proof.Defs.
Require LeanosCaps.proof.CapsSpecs.
Require Import LeanosCaps.proof.CompPure.
Require Import LeanosCaps.proof.CompProg LeanosCaps.proof.CompSpecs LeanosCaps.proof.CompLib.
Require Import LeanosCaps.harness.capabilities_complete.code.
Local Open Scope Z_scope.
#[local] Existing Instance LCS.

Definition Gmain : funspecs :=
  [space_read_spec; CapsSpecs.caps_collect_spec Dev_comp;
   nondet_u32_spec; nondet_u8_spec; gp_assume_spec; gp_assert_spec].

(* A load of an offset already planted. *)
Ltac ld_at :=
  forward;
  [ entailer!; rewrite vints_Znth by list_solve; exact I
  | rewrite ?vints_Znth by list_solve; rewrite ?Znth_snoc; rewrite ?Znth_app_l by lia ].

(* Rewrite the published header i (whatever the type its Znth is taken at). *)
Ltac rw_cap :=
  match goal with |- context [@Znth ?A ?d ?i (cap_vals ?W ?ats ++ ?rest)] =>
    let E := fresh in
    assert (E: @Znth A d i (cap_vals W ats ++ rest) =
               (Vint (Int.repr (Znth i ats)), Vint (Int.repr (Znth (Znth i ats / 4) W))))
      by (apply cap_vals_Znth; lia);
    rewrite E; clear E; cbv iota
  end.

Lemma body_main (p: QP.program function) (Hv: QPprog_vars p = nil):
  semax_body nil Gmain f_main (_main, main_spec_std p).
Proof.
  start_function.
  rewrite Hv. change (globvars2pred gv nil) with (@emp mpred _ _).
  (* The 64 words of s: any values. *)
  forward_for_simple_bound 64
    ((EX i: Z, EX ws: list Z,
     PROP (Zlength ws = i; Forall CapsSpecs.u32_ok ws)
     LOCAL (gvars gv; lvar _snapshot t_snapshot v_snapshot; lvar _initial t_header v_initial;
            lvar _at (tarray tuint 48) v_at; lvar _s t_space v_s)
     SEP (data_at Tsh t_space (Vundef, (Vundef, (Vundef,
            map (fun z => Vint (Int.repr z)) ws ++ Zrepeat Vundef (64 - i)))) v_s;
          data_at_ Tsh t_snapshot v_snapshot; data_at_ Tsh t_header v_initial;
          data_at_ Tsh (tarray tuint 48) v_at; has_ext tt))%assert).
  { Exists (@nil Z). entailer!. }
  { forward_call. Intros x. forward.
    Exists (ws ++ [x]). entailer!.
    - split; [ list_solve | apply Forall_app; split; [ assumption | constructor; [ assumption | constructor ] ] ].
    - apply derives_refl'. do 4 f_equal. list_solve. }
  Intros ws.
  assert (Z0: Zrepeat Vundef (64 - 64) = @nil val) by reflexivity. rewrite Z0, app_nil_r. clear Z0.
  (* n <= 48 offsets at[i], distinct, aligned, in [0x40, 0xfc]. *)
  forward_call. Intros n.
  forward_call. assume_hyps.
  freeze_except v_at v_at F1.
  forward_for_simple_bound n
    ((EX i: Z, EX ats: list Z,
      PROP (Zlength ats = i; Forall at_ok ats; NoDup ats)
      LOCAL (temp _n (Vint (Int.repr n)); gvars gv;
             lvar _snapshot t_snapshot v_snapshot; lvar _initial t_header v_initial;
             lvar _at (tarray tuint 48) v_at; lvar _s t_space v_s)
      SEP (FRZL F1; data_at Tsh (tarray tuint 48) (vints ats ++ Zrepeat Vundef (48 - i)) v_at))%assert).
  { Exists (@nil Z). entailer!. constructor. }
  { forward_call. Intros x.
    forward.
    replace (48 - i) with ((48 - (i + 1)) + 1) by lia. subst i.
    rewrite vints_snoc by lia.
    ld_at.
    forward_if (temp _t'4 (Vint (Int.repr (Z.b2z ((64 <=? x) && (x <=? 252))%bool)))).
    { ld_at. forward. assume_hyps. entailer!. bcase. }
    { forward. assume_hyps. entailer!. bcase. }
    forward_if (temp _t'5 (Vint (Int.repr (Z.b2z ((64 <=? x) && (x <=? 252) && (Z.land x 3 =? 0))%bool)))).
    { ld_at. forward. entailer!. bcase. }
    { forward. entailer!. bcase. }
    forward_call. assume_hyps.
    assert (Ax: at_ok x) by (split; [ lia | assumption ]).
    forward_for_simple_bound (Zlength ats)
      ((EX j: Z,
        PROP (forall k, 0 <= k < j -> Znth k ats <> x)
        LOCAL (temp _i__1 (Vint (Int.repr (Zlength ats))); temp _n (Vint (Int.repr n)); gvars gv;
               lvar _snapshot t_snapshot v_snapshot; lvar _initial t_header v_initial;
               lvar _at (tarray tuint 48) v_at; lvar _s t_space v_s)
        SEP (FRZL F1; data_at Tsh (tarray tuint 48) (vints (ats ++ [x]) ++ Zrepeat Vundef (48 - (Zlength ats + 1))) v_at))%assert).
    { entailer!; intros; lia. }
    { assert (Rj: at_ok (Znth i ats)) by (apply Forall_Znth; auto). destruct Rj as [Rj1 Rj2].
      ld_at. ld_at. forward_call. assume_hyps.
      assert (NEW: forall k, 0 <= k < i + 1 -> Znth k ats <> x).
      { intros k Hk. destruct (zeq k i); [ subst k; assumption | ].
        match goal with H: forall k, _ -> Znth k ats <> x |- _ => apply H; lia end. }
      entailer!. }
    Exists (ats ++ [x]). entailer!.
    split; [ | split ].
    - list_solve.
    - apply Forall_app. split; [ assumption | constructor; [ exact Ax | constructor ] ].
    - apply NoDup_snoc; [ assumption | ].
      intro I. apply In_Znth in I. destruct I as [k [Hk Ek]].
      match goal with H: forall k, _ -> Znth k ats <> x |- _ => apply (H k); [ lia | exact Ek ] end. }
  (* The headers at those offsets: linked in order, ended by 0, ids other than 0xff. *)
  Intros ats.
  thaw F1.
  freeze_except v_s v_at F2.
  forward_for_simple_bound n
    ((EX i: Z, EX W: list Z,
      PROP (Zlength W = 64; Forall CapsSpecs.u32_ok W; forall k, 0 <= k < i -> node_ok W ats k)
      LOCAL (temp _n (Vint (Int.repr n)); gvars gv;
             lvar _snapshot t_snapshot v_snapshot; lvar _initial t_header v_initial;
             lvar _at (tarray tuint 48) v_at; lvar _s t_space v_s)
      SEP (FRZL F2; data_at Tsh t_space (Vundef, (Vundef, (Vundef, map (fun z => Vint (Int.repr z)) W))) v_s;
           data_at Tsh (tarray tuint 48) (vints ats ++ Zrepeat Vundef (48 - n)) v_at))%assert).
  { Exists ws. entailer!; intros; lia. }
  { forward_call. Intros y.
    forward.
    forward_call.
    pose proof (land255_range y) as Rid.
    rewrite int_and in * by rep_lia.
    assume_hyps.
    forward_if (temp _t'7 (Vint (Int.repr (next_of ats i)))).
    { assume_hyps. ld_at. forward. entailer!. unfold next_of. bcase. }
    { assume_hyps. forward. entailer!. unfold next_of. bcase. }
    forward.
    ld_at. ld_at.
    assert (Aa: at_ok (Znth i ats)) by (apply Forall_Znth; [ assumption | lia ]).
    pose proof (at_quot_range _ Aa) as Qa. pose proof Aa as [Aa1 Aa2].
    assert (Ix: 0 <= Int.unsigned (Int.divu (Int.repr (Znth i ats)) (Int.repr 4)) < Zlength W)
      by (rewrite divu4 by rep_lia; lia).
    forward.
    assert (Uw: CapsSpecs.u32_ok (Znth (Znth i ats / 4) W)) by (apply Forall_Znth; [ assumption | lia ]).
    unfold CapsSpecs.u32_ok in Uw.
    pose proof (next_of_range ats i ltac:(assumption)) as Rn.
    forward.
    fold_div.
    rewrite plant_repr by lia.
    rewrite (upd_Znth_map (fun z => Vint (Int.repr z))).
    destruct (plant_step W ats i (Z.land y 255)) as [P1 [P2 P3]]; try assumption; try lia.
    Exists (upd_Znth (Znth i ats / 4) W (plant (Znth (Znth i ats / 4) W) (next_of ats i) (Z.land y 255))).
    entailer!. }
  (* The list head: the status bit and word 13 for n > 0; for n = 0 no list, either way. *)
  Intros W.
  assert (LK: links W ats).
  { apply links_of_nodes. intros k Hk. match goal with H: forall k, _ -> node_ok W ats k |- _ => apply H; lia end. }
  assert (U1: 0 <= Znth 1 W <= Int.max_unsigned) by (apply u32_Znth; auto; lia).
  assert (U13: 0 <= Znth 13 W <= Int.max_unsigned) by (apply u32_Znth; auto; lia).
  forward_if ((EX W1: list Z,
     PROP (Zlength W1 = 64; Forall CapsSpecs.u32_ok W1; links W1 ats; list_head (sublist 0 16 W1) = hd 0 ats)
     LOCAL (temp _n (Vint (Int.repr n)); gvars gv;
            lvar _snapshot t_snapshot v_snapshot; lvar _initial t_header v_initial;
            lvar _at (tarray tuint 48) v_at; lvar _s t_space v_s)
     SEP (FRZL F2; data_at Tsh t_space (Vundef, (Vundef, (Vundef, map (fun z => Vint (Int.repr z)) W1))) v_s;
          data_at Tsh (tarray tuint 48) (vints ats ++ Zrepeat Vundef (48 - n)) v_at))%assert).
  { assume_hyps.
    forward. forward.
    rewrite int_or by rep_lia. rewrite (upd_Znth_map (fun z => Vint (Int.repr z))).
    forward.
    rewrite (upd_Znth_diff 13 1) by lia.
    ld_at.
    assert (A0: at_ok (Znth 0 ats)) by (apply Forall_Znth; [ assumption | lia ]). pose proof A0 as [A01 A02].
    forward.
    rewrite not_255, int_and, int_or by first [ rep_lia | apply land_range; rep_lia ].
    rewrite (upd_Znth_map (fun z => Vint (Int.repr z))).
    destruct (head_set W ats) as [P1 [P2 [P3 P4]]]; try assumption; try lia.
    Exists (W_set W (Znth 0 ats)). unfold W_set in *. entailer!. }
  { assume_hyps.
    forward_call. Intros c.
    forward_if.
    { forward. forward.
      rewrite not_cap_bit, int_and by rep_lia. rewrite (upd_Znth_map (fun z => Vint (Int.repr z))).
      destruct (head_clear_bit W) as [P1 [P2 [P3 P4]]]; try assumption.
      assert (E0: ats = []) by (apply Zlength_nil_inv; lia). subst ats.
      Exists (W_clear_bit W). unfold W_clear_bit in *. entailer!. }
    { forward. forward.
      rewrite int_or by rep_lia. rewrite (upd_Znth_map (fun z => Vint (Int.repr z))).
      forward.
      rewrite (upd_Znth_diff 13 1) by lia.
      forward.
      rewrite not_255, int_and by rep_lia. rewrite (upd_Znth_map (fun z => Vint (Int.repr z))).
      destruct (head_clear_byte W) as [P1 [P2 [P3 P4]]]; try assumption.
      assert (E0: ats = []) by (apply Zlength_nil_inv; lia). subst ats.
      Exists (W_clear_byte W). unfold W_clear_byte in *. entailer!. } }
  (* The assume on the header type and the vendor (word 3 and word 0; their loads are kept opaque). *)
  Intros W1.
  assert (U3: 0 <= Znth 3 W1 <= Int.max_unsigned) by (apply u32_Znth; auto; lia).
  assert (U0: 0 <= Znth 0 W1 <= Int.max_unsigned) by (apply u32_Znth; auto; lia).
  forward.
  remember (Znth 3 W1) as w3 eqn:Ew3. remember (Znth 0 W1) as w0 eqn:Ew0.
  forward_if (temp _t'9 (Vint (Int.repr (Z.b2z (hdr_ok w3 w0))))).
  { forward. rewrite <- Ew0. forward. rewrite Ew0. rewrite htype_repr in * by assumption.
    entailer!. unfold hdr_ok. bcase. }
  { forward. rewrite htype_repr in * by assumption. entailer!. unfold hdr_ok. bcase. }
  forward_call.
  match goal with E: Int.repr (Z.b2z (hdr_ok w3 w0)) <> Int.zero |- _ => apply b2z_true in E; unfold hdr_ok in E end.
  assume_hyps. subst w3 w0.
  (* bus, device <= 31, function <= 7. *)
  forward_call. Intros b. forward.
  forward_call. Intros d. forward.
  forward_call. Intros f. forward.
  rewrite !zext8 by assumption.
  forward.
  forward_if (temp _t'13 (Vint (Int.repr (Z.b2z ((d <=? 31) && (f <=? 7))%bool)))).
  { forward. forward. entailer!. bcase. }
  { forward. entailer!. bcase. }
  forward_call. assume_hyps.
  (* The initial header: bus/device/function and the first 16 words. *)
  thaw F2.
  freeze_except v_s v_initial F3.
  sep_apply (header_undef v_initial).
  forward. forward.
  forward. forward.
  forward. forward.
  rewrite ?zext8 by assumption.
  forward_for_simple_bound 16
    ((EX i: Z,
      PROP ()
      LOCAL (temp _n (Vint (Int.repr n)); gvars gv;
             lvar _snapshot t_snapshot v_snapshot; lvar _initial t_header v_initial;
             lvar _at (tarray tuint 48) v_at; lvar _s t_space v_s)
      SEP (FRZL F3;
           data_at Tsh t_header (Vint (Int.repr b), (Vint (Int.repr d), (Vint (Int.repr f),
             map (fun z => Vint (Int.repr z)) (sublist 0 i W1) ++ Zrepeat Vundef (16 - i)))) v_initial;
           data_at Tsh t_space (Vint (Int.repr b), (Vint (Int.repr d), (Vint (Int.repr f),
             map (fun z => Vint (Int.repr z)) W1))) v_s))%assert).
  { entailer!. }
  { forward. forward. entailer!. apply derives_refl'. do 4 f_equal. list_solve. }
  assert (Z16: Zrepeat Vundef (16 - 16) = @nil val) by reflexivity. rewrite Z16, app_nil_r. clear Z16.
  (* The call: the device of the law holds the share sh_dev of s, main keeps sh_main. *)
  thaw F3.
  make_func_ptr _space_read.
  assert_PROP (isptr (gv _space_read) /\ isptr v_s /\ isptr v_initial /\ isptr v_snapshot) as Ptrs.
  { entailer!. }
  destruct Ptrs as [Pread [Ps [Pinit Psnap]]].
  sep_apply (read_ptr_result (gv _space_read) (Vundef, Vundef)).
  sep_apply (space_split b d f W1 v_s ltac:(assumption) ltac:(assumption)).
  sep_apply (header_to_maybe b d f (sublist 0 16 W1) v_initial Pinit).
  sep_apply (snapshot_to_maybe v_snapshot Psnap).
  forward_call (gv _space_read, v_s, v_initial, Tsh, b, d, f, sublist 0 16 W1, v_snapshot,
                     @default_val CapsSpecs.CS CapsSpecs.t_snapshot, nullval, (Vundef, Vundef)).
  { rewrite maybe_at_null, emp_sepcon. cancel. }
  { split; [ list_solve | apply Forall_sublist; assumption ]. }
  Intros vret. destruct vret as [[[[h st] off] caps] rest]. cbn [fst snd] in *.
  match goal with H: (if ?c then _ else _) |- _ =>
    replace c with false in H; [ cbv iota in H; rename H into Hw | ] end.
  2: { rewrite !isnull_ptr by assumption. rewrite args_ok_true by assumption. reflexivity. }
  (* After it: the device's words are main's (the kept share), so the walk read the planted list. *)
  sep_apply (dev_back b d f W1 h v_s ltac:(assumption) ltac:(assumption) ltac:(assumption)
                      ltac:(assumption) ltac:(assumption)).
  Intros.
  destruct (walk_planted W1 ats h st off caps) as [Est Ecaps]; try assumption; try lia.
  subst st caps.
  sep_apply (header_of_maybe b d f (sublist 0 16 W1) v_initial Pinit).
  sep_apply (snapshot_of_maybe (CapsSpecs.snapshot_val (Zlength (map (cap_of W1) ats))
                                  (map CapsSpecs.cap_val (map (cap_of W1) ats) ++ rest)) v_snapshot Psnap).
  unfold CapsSpecs.snapshot_val. rewrite map_cap_val, Zlength_map.
  (* The checks: status OK, count n, and each header's offset and raw word. *)
  forward_if (temp _t'15 (Vint Int.one)).
  { forward. forward. entailer!. }
  { exfalso. unfold S_OK in *. assume_hyps. first [ congruence | lia ]. }
  forward_call (Int.one).
  unfold sv.
  forward_for_simple_bound n
    ((EX i: Z,
      PROP ()
      LOCAL (temp _status (Vint (Int.repr S_OK)); temp _n (Vint (Int.repr n)); gvars gv;
             lvar _snapshot t_snapshot v_snapshot; lvar _initial t_header v_initial;
             lvar _at (tarray tuint 48) v_at; lvar _s t_space v_s)
      SEP (data_at Tsh t_snapshot (Vint (Int.repr (Zlength ats)), cap_vals W1 ats ++ rest) v_snapshot;
           data_at Tsh t_header (hv b d f (sublist 0 16 W1)) v_initial;
           data_at Tsh t_space (Vint (Int.repr b), (Vint (Int.repr d), (Vint (Int.repr f),
             map (fun z => Vint (Int.repr z)) W1))) v_s;
           CapsSpecs.maybe_read Dev_comp (gv _space_read); has_ext tt;
           data_at Tsh (tarray tuint 48) (vints ats ++ Zrepeat Vundef (48 - n)) v_at))%assert).
  { entailer!. }
  { assert (Ai: at_ok (Znth i ats)) by (apply Forall_Znth; [ assumption | lia ]). pose proof Ai as [Ai1 Ai2].
    pose proof (at_quot_range _ Ai) as Qi.
    assert (Ui: 0 <= Znth (Znth i ats / 4) W1 <= Int.max_unsigned) by (apply u32_Znth; auto; lia).
    forward.
    { rw_cap. entailer!. all: rep_lia. }
    rw_cap.
    ld_at.
    forward_if (temp _t'16 (Vint Int.one)).
    { forward.
      { rw_cap. entailer!. }
      rw_cap.
      ld_at.
      assert (Ix: 0 <= Int.unsigned (Int.divu (Int.repr (Znth i ats)) (Int.repr 4)) < Zlength W1)
        by (rewrite divu4 by rep_lia; lia).
      forward.
      forward.
      entailer!. }
    { exfalso. assume_hyps. first [ congruence | lia ]. }
    forward_call (Int.one).
    entailer!. }
  forward.
  Exists (Int.repr 0).
  entailer!.
Qed.
