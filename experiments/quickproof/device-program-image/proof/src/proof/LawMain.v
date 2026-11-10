(* Law image_exact: the body of the harness's main. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosDeviceProgramImage.harness.image_exact.code.
Require LeanosDeviceProgramImage.device_program.code.
Require Import LeanosDeviceProgramImage.proof.Defs.
Require Import LeanosDeviceProgramImage.proof.LawProg LeanosDeviceProgramImage.proof.LawSpecs
  LeanosDeviceProgramImage.proof.LawLib LeanosDeviceProgramImage.proof.LawSplit
  LeanosDeviceProgramImage.proof.LawStartDefs LeanosDeviceProgramImage.proof.LawMainDefs.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.
Local Opaque decode le32 header_status start_status start.

Definition li_init : law_image_t :=
  law_image_val Vundef Vundef (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, Vundef)))))
    pol_default Vundef Vundef Vundef.

Lemma law_default: default_val t_law = (Vundef, (Vundef, (Vundef, li_init))).
Proof. reflexivity. Qed.

Ltac nope H := first [ solve [ inversion H ] | solve [ exfalso; apply H; reflexivity ] | contradiction ].

Ltac ptr_nonnull p :=
  first
  [ match goal with H: isptr p |- _ => destruct p; try contradiction; reflexivity end
  | match goal with H: field_compatible _ _ p |- _ =>
      let I := fresh in pose proof (field_compatible_isptr _ _ _ H) as I; destruct p; try contradiction; reflexivity
    end
  | match goal with H: malloc_compatible _ p |- _ =>
      destruct p; try contradiction; reflexivity
    end ].

Lemma zext8: forall b, 0 <= b <= Byte.max_unsigned -> Int.zero_ext 8 (Int.repr b) = Int.repr b.
Proof.
  intros b B. unfold Int.zero_ext. rewrite Int.unsigned_repr by rep_lia.
  rewrite Zbits.Zzero_ext_mod by lia. rewrite Z.mod_small; [ reflexivity | ].
  change (two_p 8) with 256. rep_lia.
Qed.

Lemma body_main: forall p,
  QPprog_vars p = [(_wifi_scratch, LeanosDeviceProgramImage.device_program.code.v_wifi_scratch); (_law, v_law)] ->
  semax_body Vlaw Glaw f_main (_main, main_spec_std p).
Proof.
  intros p Hp. start_function. rewrite Hp.
  assert_PROP (headptr (gv _law) /\ headptr (gv _wifi_scratch)) as HH by entailer!.
  destruct HH as [HL HS].
  sep_apply (law_globals gv HL HS).
  sep_apply (create_mem_mgr gv).
  rewrite data_at__eq, law_default, law_split. unfold law_fields. Intros.
  forward.
  forward_call. Intros c.
  forward_if (temp _t'2 (Vint (Int.repr (Z.min c 4)))).
  { forward. entailer!. bfix. rewrite Z.min_l by lia. reflexivity. }
  { forward. entailer!. bfix. rewrite Z.min_r by lia. reflexivity. }
  assert (Rc: 0 <= Z.min c 4 <= 4) by lia.
  set (c' := Z.min c 4) in *. clearbody c'.
  forward. forward. forward. forward. forward.
  forward.
  forward_if.
  { bfix.
    sep_apply (law_fold Ews (gv _law)).
    forward_call (Ews, gv _law, (Vint (Int.repr c'), (Vint (Int.repr 0),
      (Vlong (Int64.repr (Int.signed (Int.repr 0))), (Vint (Int.repr 2),
        (fst (snd li_init), (fst (snd (snd li_init)), (fst (snd (snd (snd li_init))),
          (fst (snd (snd (snd (snd li_init)))), (fst (snd (snd (snd (snd (snd li_init))))),
            Vint (Int.repr 2)))))))))), c').
    forward. Exists (Int.repr 0). entailer!. }
  bfix.
  forward_call. Intros len. forward.
  forward.
  forward_call (tarray tuchar len, gv).
  { simpl sizeof. rep_lia. }
  Intros image. forward.
  forward.
  forward_call (tarray tuchar len, gv).
  { simpl sizeof. rep_lia. }
  Intros copy. forward.
  destruct (eq_dec image nullval) as [Ei|Ni].
  { subst image.
    forward_if (temp _t'6 (Vint (Int.repr 1))).
    { forward. entailer!. }
    { contradiction. }
    forward_if; [ | nope H2 ].
    forward. Exists (Int.repr 0). entailer!. }
  Intros.
  destruct (eq_dec copy nullval) as [Ec|Nc].
  { subst copy.
    forward_if (temp _t'6 (Vint (Int.repr 1))).
    { forward. entailer!. }
    { forward. forward. entailer!. }
    forward_if; [ | nope H2 ].
    forward. Exists (Int.repr 0). entailer!. }
  Intros.
  forward_if (temp _t'6 (Vint (Int.repr 0))).
  { contradiction. }
  { forward. forward. entailer!. ptr_nonnull copy. }
  forward_if; [ nope H2 | ].
  forward.
  forward_call (image, len, Ews).
  { rewrite if_false by auto. cancel. }
  Intros bs. rewrite if_false by auto.
  change (map (fun b => Vint (Int.repr b)) bs) with (bytes_val bs).
  match goal with H: Zlength bs = len |- _ => rename H into Lbs end.
  match goal with H: Forall _ bs |- _ => rename H into Fbs end.
  assert (SB: forall j, 0 <= j < len -> 0 <= Znth j bs <= Byte.max_unsigned)
    by (intros; apply (proj1 (Forall_Znth _ _) Fbs); lia).
  rewrite data_at__tuchar.
  freeze FM := (mem_mgr gv) (malloc_token _ _ copy) (malloc_token _ _ image) (field_at _ _ (DOT _call) _ _)
    (field_at _ _ (DOT _want) _ _) (scr_ _ _) (has_ext tt).
  forward.
  forward_loop (EX i: Z,
    PROP (0 <= i <= len)
    LOCAL (temp _i (Vint (Int.repr i)); temp _image image; temp _m (gv _law); gvars gv)
    SEP (FRZL FM; data_at Ews (tarray tuchar len) (bytes_val bs) image;
         data_at Ews (tarray tuchar len) (bytes_val (sublist 0 i bs) ++ Zrepeat Vundef (len - i)) copy;
         field_at Ews t_law (DOT _length) (Vint (Int.repr len)) (gv _law);
         field_at Ews t_law (DOT _copy) copy (gv _law)))%assert
  break: (PROP ()
    LOCAL (temp _image image; temp _m (gv _law); gvars gv)
    SEP (FRZL FM; data_at Ews (tarray tuchar len) (bytes_val bs) image;
         data_at Ews (tarray tuchar len) (bytes_val bs) copy;
         field_at Ews t_law (DOT _length) (Vint (Int.repr len)) (gv _law);
         field_at Ews t_law (DOT _copy) copy (gv _law)))%assert.
  { Exists 0. entailer!. rewrite app_nil_l. apply derives_refl. }
  { Intros i. forward. forward_if.
    - bfix. forward.
      forward; [ entailer!; pose proof (SB i ltac:(lia)); rewrite ?Int.unsigned_repr by rep_lia; rep_lia | ].
      forward.
      rewrite zext8 by (apply SB; lia).
      rewrite (upd_sub_map (fun b => Vint (Int.repr b)) bs i len) by lia.
      forward. Exists (i + 1). entailer!.
    - bfix. forward. entailer!.
      replace i with (Zlength bs) by lia. rewrite Z.sub_diag, Zrepeat_0, app_nil_r, sublist_same by lia.
      apply derives_refl. }
  forward. forward.
  thaw FM.
  rewrite (field_at_data_at Ews t_law (DOT _want)).
  change (nested_field_type t_law (DOT _want)) with t_law_image.
  match goal with |- context [data_at Ews t_law_image ?w (field_address t_law (DOT _want) (gv _law))] =>
    sep_apply (data_at_data_at_ Ews t_law_image w (field_address t_law (DOT _want) (gv _law))) end.
  rewrite <- Lbs.
  forward_call (Ews, copy, bs, Ews, field_address t_law (DOT _want) (gv _law)).
  { split; [ rep_lia | exact Fbs ]. }
  Intros vret. destruct vret as [[[[[[st hl] tv] pv] nv] blv] sst]. simpl fst in *; simpl snd in *.
  change t_law_image with (nested_field_type t_law (DOT _want)).
  rewrite <- (field_at_data_at Ews t_law (DOT _want)).
  forward.
  set (lv := (Vint (Int.repr c'), (Vint (Int.repr (Zlength bs)), (copy, law_image_val st hl tv pv nv blv sst)))).
  assert (LR: law_reads bs lv) by (split; auto).
  assert (IM: image_ok bs) by (split; [ rep_lia | exact Fbs ]).
  forward_if (PROP ()
    LOCAL (temp _image image; temp _m (gv _law); gvars gv)
    SEP (data_at Ews t_law lv (gv _law); data_at Ews (tarray tuchar (Zlength bs)) (bytes_val bs) image;
         data_at Ews (tarray tuchar (Zlength bs)) (bytes_val bs) copy; TT)).
  - sep_apply (law_fold Ews (gv _law)). fold lv.
    forward_call (Ews, gv _law, lv, Ews, image, bs).
    entailer!.
  - sep_apply (law_fold Ews (gv _law)). fold lv.
    rewrite scr__eq.
    forward_call (gv, Ews, gv _law, lv, Ews, image, bs).
    entailer!.
  - forward.
    forward_loop (EX i: Z,
      PROP (0 <= i <= Zlength bs)
      LOCAL (temp _i__1 (Vint (Int.repr i)); temp _image image; temp _m (gv _law); gvars gv)
      SEP (data_at Ews t_law lv (gv _law); data_at Ews (tarray tuchar (Zlength bs)) (bytes_val bs) image;
           data_at Ews (tarray tuchar (Zlength bs)) (bytes_val bs) copy; TT))%assert
    break: (PROP () LOCAL () SEP (TT))%assert.
    { Exists 0. entailer!. }
    { Intros i. unfold lv. forward. forward_if.
      - bfix.
        forward; try (match goal with |- ENTAIL _, _ |-- _ => idtac end;
          entailer!; pose proof (SB i ltac:(lia)); rewrite ?Int.unsigned_repr by rep_lia; rep_lia).
        forward.
        forward; try (match goal with |- ENTAIL _, _ |-- _ => idtac end;
          entailer!; pose proof (SB i ltac:(lia)); rewrite ?Int.unsigned_repr by rep_lia; rep_lia).
        forward_call (Int.repr 1).
        { entailer!. rewrite Int.eq_true. reflexivity. }
        forward. Exists (i + 1). entailer!.
      - forward. entailer!. }
    forward. Exists (Int.repr 0). entailer!.
Qed.
