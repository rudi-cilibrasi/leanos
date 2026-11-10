(* Law image_exact: the body of start_case. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import LeanosDeviceProgramImage.harness.image_exact.code.
Require Import LeanosDeviceProgramImage.proof.Defs.
Require LeanosDeviceProgramImage.proof.Specs.
Require Import LeanosDeviceProgramImage.proof.LawProg LeanosDeviceProgramImage.proof.LawSpecs
  LeanosDeviceProgramImage.proof.LawLib LeanosDeviceProgramImage.proof.LawLaw
  LeanosDeviceProgramImage.proof.LawSplit LeanosDeviceProgramImage.proof.LawStartDefs
  LeanosDeviceProgramImage.proof.LawStartRest.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.
Local Opaque decode le32 header_status start_status start.

Ltac nope H := first [ solve [ inversion H ] | solve [ exfalso; apply H; reflexivity ] | contradiction ].

Ltac ptr_nonnull p :=
  first
  [ match goal with H: isptr p |- _ => destruct p; try contradiction; reflexivity end
  | match goal with H: field_compatible _ _ p |- _ =>
      let I := fresh in pose proof (field_compatible_isptr _ _ _ H) as I; destruct p; try contradiction; reflexivity
    end ].

Lemma upd_fill {A} {d: Inhabitant A}: forall (l: list A) x i n (u: A), Zlength l = i -> i < n ->
  upd_Znth i (l ++ Zrepeat u (n - i)) x = (l ++ [x]) ++ Zrepeat u (n - (i + 1)).
Proof. intros. subst i. list_solve. Qed.

Lemma upd_sub_map {A B} {da: Inhabitant A} {db: Inhabitant B}: forall (f: A -> B) (l: list A) i n (u: B),
  0 <= i < n -> Zlength l = n ->
  upd_Znth i (map f (sublist 0 i l) ++ Zrepeat u (n - i)) (f (Znth i l)) =
  map f (sublist 0 (i + 1) l) ++ Zrepeat u (n - (i + 1)).
Proof. intros. list_solve. Qed.

Lemma zext8: forall b, 0 <= b <= Byte.max_unsigned -> Int.zero_ext 8 (Int.repr b) = Int.repr b.
Proof.
  intros b B. unfold Int.zero_ext. rewrite Int.unsigned_repr by rep_lia.
  rewrite Zbits.Zzero_ext_mod by lia. rewrite Z.mod_small; [ reflexivity | ].
  change (two_p 8) with 256. rep_lia.
Qed.

Lemma body_start_case : semax_body Vlaw Glaw f_start_case start_case_spec.
Proof.
  start_function.

  forward_call (t_vm, gv). Intros vm.
  forward_call (t_vm, gv). Intros prior.
  forward_call (tarray tuchar SCRATCH, gv).
  { change (sizeof (tarray tuchar SCRATCH)) with 262144. rep_lia. }
  Intros saved.
  rewrite <- (scr__eq Ews saved), <- (scr__eq Ews (gv _wifi_scratch)).
  destruct (eq_dec vm nullval) as [Ev|Nv].
  { subst vm.
    forward_if (temp _t'4 (Vint (Int.repr 1))).
    { forward. entailer!. }
    { contradiction. }
    forward_if (temp _t'5 (Vint (Int.repr 1))).
    { forward. entailer!. }
    { nope H1. }
    forward_if; [ | nope H1 ].
    forward. entailer!. }
  Intros.
  destruct (eq_dec prior nullval) as [Ep|Np].
  { subst prior.
    forward_if (temp _t'4 (Vint (Int.repr 1))).
    { forward. entailer!. }
    { forward. entailer!. }
    forward_if (temp _t'5 (Vint (Int.repr 1))).
    { forward. entailer!. }
    { nope H1. }
    forward_if; [ | nope H1 ].
    forward. entailer!. }
  Intros.
  destruct (eq_dec saved nullval) as [Es|Ns].
  { subst saved.
    forward_if (temp _t'4 (Vint (Int.repr 0))).
    { contradiction. }
    { forward. entailer!. ptr_nonnull prior. }
    forward_if (temp _t'5 (Vint (Int.repr 1))).
    { nope H1. }
    { forward. entailer!. }
    forward_if; [ | nope H1 ].
    forward. entailer!. }
  Intros.
  forward_if (temp _t'4 (Vint (Int.repr 0))).
  { contradiction. }
  { forward. entailer!. ptr_nonnull prior. }
  forward_if (temp _t'5 (Vint (Int.repr 0))).
  { nope H1. }
  { forward. entailer!. ptr_nonnull saved. }
  forward_if; [ nope H1 | ].
  assert_PROP (field_compatible t_vm nil vm /\ field_compatible t_vm nil prior) as FCv by entailer!.
  destruct FCv as [FCvm FCpr].
  rewrite (data_at__eq _ t_vm vm), (data_at__eq _ t_vm prior), vm_default, !vm_split by auto.
  unfold vm_fields. Intros.
  forward. forward.
  forward_call. Intros n0. forward.
  forward_call. Intros b0. forward.
  forward_call. Intros w0. forward.
  rewrite pol_default_eq, <- (data_at__eq _ t_policy (offset_val 32 vm)).
  forward_call (Ews, offset_val 32 vm, false). Intros P0.
  rewrite tg_default_eq, <- (data_at__eq _ t_target (offset_val 368 vm)).
  forward_call (Ews, offset_val 368 vm). Intros T0.
  freeze FR1 := (mem_mgr gv) (malloc_token _ _ saved) (scr_ _ saved) (malloc_token _ _ prior)
    (malloc_token _ _ vm) (data_at _ (tarray tuchar (Zlength bs)) _ image) (data_at msh t_law _ m)
    (scr_ _ (gv _wifi_scratch)).
  freeze FR2 := (field_at _ _ (DOT _code_base) _ prior) (field_at _ _ (DOT _blob) _ prior)
    (field_at _ _ (DOT _n) _ prior) (field_at _ _ (DOT _blob_len) _ prior) (field_at _ _ (DOT _window) _ prior)
    (spacer _ _ _ prior) (data_at _ t_policy _ (offset_val 32 prior)).
  freeze FR3 := (data_at _ t_target _ (offset_val 368 prior))
    (field_at _ _ (DOT _r) _ prior) (field_at _ _ (DOT _stack) _ prior) (field_at _ _ (DOT _sp) _ prior)
    (field_at _ _ (DOT _pc) _ prior) (field_at _ _ (DOT _steps) _ prior).
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval.
  freeze FR4 := (FRZL FR3) (FRZL FR2) (FRZL FR1) (data_at _ t_target _ (offset_val 368 vm))
    (data_at _ t_policy _ (offset_val 32 vm)) (field_at _ _ (DOT _code_base) _ vm) (field_at _ _ (DOT _blob) _ vm).
  freeze FR5 := (field_at _ _ (DOT _n) _ vm) (field_at _ _ (DOT _blob_len) _ vm) (field_at _ _ (DOT _window) _ vm)
    (spacer _ _ _ vm) (field_at _ _ (DOT _stack) _ vm) (field_at _ _ (DOT _sp) _ vm) (field_at _ _ (DOT _pc) _ vm).
  forward_for_simple_bound 16 (EX i: Z, EX rs: list Z,
    PROP (Zlength rs = i; Forall u32_ok rs)
    LOCAL (temp _saved saved; temp _prior prior; temp _vm vm; gvars gv; temp _m m; temp _image image)
    SEP (FRZL FR4; FRZL FR5; field_at Ews t_vm (DOT _r) (words_val rs ++ Zrepeat Vundef (16 - i)) vm;
         field_at Ews t_vm (DOT _steps) Vundef vm))%assert.
  { Exists (@nil Z). entailer!. }
  { forward_call. Intros x. forward.
    Exists (rs ++ [x]).
    rewrite (upd_fill (words_val rs) _ i 16) by (try rewrite Zlength_map; lia). rewrite map_app.
    entailer!.
    split; [ list_solve | apply Forall_app; split; [ auto | repeat constructor; unfold u32_ok; lia ] ]. }
  Intros rs. change (16 - 16) with 0. rewrite Zrepeat_0, app_nil_r.
  thaw FR5.
  freeze FR6 := (field_at _ _ (DOT _n) _ vm) (field_at _ _ (DOT _blob_len) _ vm) (field_at _ _ (DOT _window) _ vm)
    (spacer _ _ _ vm) (field_at _ _ (DOT _r) _ vm) (field_at _ _ (DOT _sp) _ vm) (field_at _ _ (DOT _pc) _ vm).
  forward_for_simple_bound 16 (EX i: Z, EX ss: list Z,
    PROP (Zlength ss = i; Forall u32_ok ss)
    LOCAL (temp _saved saved; temp _prior prior; temp _vm vm; gvars gv; temp _m m; temp _image image)
    SEP (FRZL FR4; FRZL FR6; field_at Ews t_vm (DOT _stack) (words_val ss ++ Zrepeat Vundef (16 - i)) vm;
         field_at Ews t_vm (DOT _steps) Vundef vm))%assert.
  { Exists (@nil Z). entailer!. }
  { forward_call. Intros x. forward.
    Exists (ss ++ [x]).
    rewrite (upd_fill (words_val ss) _ i 16) by (try rewrite Zlength_map; lia). rewrite map_app.
    entailer!.
    split; [ list_solve | apply Forall_app; split; [ auto | repeat constructor; unfold u32_ok; lia ] ]. }
  Intros ss. change (16 - 16) with 0. rewrite Zrepeat_0, app_nil_r.
  thaw FR6.
  forward_call. Intros sp0. forward.
  forward_call. Intros pc0. forward.
  forward_call. Intros st0. forward.
  thaw FR4. thaw FR3. thaw FR2.
  forward. forward. forward. forward. forward. forward.
  rewrite <- (data_at__eq _ t_policy (offset_val 32 prior)).
  forward_call (Ews, offset_val 32 prior, Ews, offset_val 32 vm, P0).
  freeze FR7 := (FRZL FR1) (data_at _ t_target _ (offset_val 368 vm)) (data_at _ t_policy _ (offset_val 32 vm))
    (field_at _ _ (DOT _code_base) _ vm) (field_at _ _ (DOT _blob) _ vm) (field_at _ _ (DOT _n) _ vm)
    (field_at _ _ (DOT _blob_len) _ vm).
  freeze FR8 := (field_at _ _ (DOT _window) _ vm) (spacer _ _ _ vm) (field_at _ _ (DOT _sp) _ vm)
    (field_at _ _ (DOT _pc) _ vm) (field_at _ _ (DOT _steps) _ vm) (field_at _ _ (DOT _stack) _ vm).
  freeze FR9 := (field_at _ _ (DOT _code_base) _ prior) (field_at _ _ (DOT _blob) _ prior)
    (field_at _ _ (DOT _n) _ prior) (field_at _ _ (DOT _blob_len) _ prior) (field_at _ _ (DOT _window) _ prior)
    (spacer _ _ _ prior) (data_at _ t_policy _ (offset_val 32 prior)).
  freeze FR10 := (data_at _ t_target _ (offset_val 368 prior)) (field_at _ _ (DOT _stack) _ prior)
    (field_at _ _ (DOT _sp) _ prior) (field_at _ _ (DOT _pc) _ prior) (field_at _ _ (DOT _steps) _ prior).
  forward_for_simple_bound 16 (EX i: Z,
    PROP ()
    LOCAL (temp _saved saved; temp _prior prior; temp _vm vm; gvars gv; temp _m m; temp _image image)
    SEP (FRZL FR7; FRZL FR8; FRZL FR9; FRZL FR10; field_at Ews t_vm (DOT _r) (words_val rs) vm;
         field_at Ews t_vm (DOT _r) (words_val (sublist 0 i rs) ++ Zrepeat Vundef (16 - i)) prior))%assert.
  { entailer!. }
  { forward. forward.
    rewrite (upd_sub_map (fun w => Vint (Int.repr w)) rs i 16) by lia.
    entailer!. }
  change (16 - 16) with 0. rewrite Zrepeat_0, app_nil_r, sublist_same by lia.
  thaw FR10. thaw FR9. thaw FR8. thaw FR7.
  freeze FR7 := (FRZL FR1) (data_at _ t_target _ (offset_val 368 vm)) (data_at _ t_policy _ (offset_val 32 vm))
    (field_at _ _ (DOT _code_base) _ vm) (field_at _ _ (DOT _blob) _ vm) (field_at _ _ (DOT _n) _ vm)
    (field_at _ _ (DOT _blob_len) _ vm).
  freeze FR11 := (field_at _ _ (DOT _window) _ vm) (spacer _ _ _ vm) (field_at _ _ (DOT _sp) _ vm)
    (field_at _ _ (DOT _pc) _ vm) (field_at _ _ (DOT _steps) _ vm) (field_at _ _ (DOT _r) _ vm).
  freeze FR9 := (field_at _ _ (DOT _code_base) _ prior) (field_at _ _ (DOT _blob) _ prior)
    (field_at _ _ (DOT _n) _ prior) (field_at _ _ (DOT _blob_len) _ prior) (field_at _ _ (DOT _window) _ prior)
    (spacer _ _ _ prior) (data_at _ t_policy _ (offset_val 32 prior)).
  freeze FR12 := (data_at _ t_target _ (offset_val 368 prior)) (field_at _ _ (DOT _r) _ prior)
    (field_at _ _ (DOT _sp) _ prior) (field_at _ _ (DOT _pc) _ prior) (field_at _ _ (DOT _steps) _ prior).
  forward_for_simple_bound 16 (EX i: Z,
    PROP ()
    LOCAL (temp _saved saved; temp _prior prior; temp _vm vm; gvars gv; temp _m m; temp _image image)
    SEP (FRZL FR7; FRZL FR11; FRZL FR9; FRZL FR12; field_at Ews t_vm (DOT _stack) (words_val ss) vm;
         field_at Ews t_vm (DOT _stack) (words_val (sublist 0 i ss) ++ Zrepeat Vundef (16 - i)) prior))%assert.
  { entailer!. }
  { forward. forward.
    rewrite (upd_sub_map (fun w => Vint (Int.repr w)) ss i 16) by lia.
    entailer!. }
  change (16 - 16) with 0. rewrite Zrepeat_0, app_nil_r, sublist_same by lia.
  thaw FR12. thaw FR9. thaw FR11. thaw FR7.
  forward. forward. forward. forward. forward. forward.
  thaw FR1.
  forward_call (gv).
  assert_PROP (isptr (gv _wifi_scratch)) as Psc by entailer!.
  freeze FRA := - (scr_ _ (gv _wifi_scratch)).
  rewrite scr__eq.
  forward_call (gv _wifi_scratch, SCRATCH, Ews).
  { rewrite if_false by (destruct (gv _wifi_scratch); try contradiction; discriminate). cancel. }
  Intros S. rewrite if_false by (destruct (gv _wifi_scratch); try contradiction; discriminate).
  change (map (fun b => Vint (Int.repr b)) S) with (bytes_val S).
  rewrite <- scr_eq. thaw FRA.
  match goal with H: Zlength S = SCRATCH |- _ => rename H into LS end.
  freeze FRB := - (scr_ _ saved) (scr _ _ (gv _wifi_scratch)).
  rewrite (scr_start Ews saved S), scr_eq.
  remember SCRATCH as SC eqn:ESC.
  assert (HSC: 262144 <= SC <= 262144) by (subst; unfold SCRATCH; lia). clear ESC.
  match goal with H: Forall _ S |- _ => rename H into FS end.
  assert (SB: forall j, 0 <= j < SC -> 0 <= Znth j S <= Byte.max_unsigned)
    by (intros; apply (proj1 (Forall_Znth _ _) FS); lia).
  forward_for_simple_bound 262144 (EX i: Z,
    PROP ()
    LOCAL (temp _scratch (gv _wifi_scratch); temp _saved saved; temp _prior prior; temp _vm vm; gvars gv;
           temp _m m; temp _image image)
    SEP (FRZL FRB; data_at Ews (tarray tuchar SC) (bytes_val S) (gv _wifi_scratch);
         data_at Ews (tarray tuchar SC) (bytes_val (sublist 0 i S) ++ Zrepeat Vundef (SC - i)) saved))%assert.
  { entailer!. }
  { forward; [ entailer!; pose proof (SB i ltac:(lia)); rewrite ?Int.unsigned_repr by rep_lia; rep_lia | ]. forward.
    rewrite zext8 by (apply SB; lia).
    rewrite (upd_sub_map (fun b => Vint (Int.repr b)) S i SC) by lia.
    entailer!. }
  assert (ESC: SC = SCRATCH) by (unfold SCRATCH; lia). clear HSC SB. revert LS. subst SC. intros LS.
  rewrite <- !scr_eq. thaw FRB.
  replace (SCRATCH - 262144) with 0 by (unfold SCRATCH; lia).
  rewrite Zrepeat_0, app_nil_r, sublist_same by (rewrite ?LS; unfold SCRATCH; lia).
  eapply semax_pre;
    [ | apply (sc_rest gv msh m lv ish image bs vm prior saved n0 b0 w0 P0 T0 rs ss sp0 pc0 st0 S); auto ].
  unfold vm_fields. entailer!.
Qed.
