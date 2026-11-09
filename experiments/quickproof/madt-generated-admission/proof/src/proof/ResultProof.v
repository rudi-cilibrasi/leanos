(* The body proof of madt_topology_admission_result (include/madt_generated_admission.h): the four result calls
   (the invariant `run ... = Some (result_collect args cur)`, the answer array holding cur), then the checks of
   result_check, each early return the model's result_end. *)
Require Import VST.floyd.proofauto.
Require Import LeanosMadtAdmission.madt_admission.code.
Require Import LeanosMadtAdmission.proof.Defs.
Require Import LeanosMadtAdmission.proof.MgaSpecs.
Require Import LeanosMadtAdmission.proof.InternalSpecs.
Require Import LeanosMadtAdmission.proof.BodyLemmas.
#[local] Existing Instance MgaSpecs.CS.
Local Open Scope Z_scope.

Lemma body_madt_topology_admission_result (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_madt_topology_admission_result (topology_result_spec Ora).
Proof.
  start_function.
  match goal with H: Zlength args = 10 |- _ => rename H into Largs end.
  match goal with H: Forall u64_ok args |- _ => rename H into Uargs end.
  match goal with H: run _ _ h = _ |- _ => rename H into Hrun end.
  change (Go (ExpectResult args nil)) with (result_collect args nil) in Hrun.
  rewrite (data_at__eq _ (tarray tulong 4) v_answer).
  change (default_val (tarray tulong 4)) with (Zrepeat Vundef 4).
  forward_for_simple_bound 4 (EX k: Z, EX hs: list answer, EX cur: list Z,
    PROP (run x (start x) (h ++ hs) = Some (result_collect args cur); Zlength cur = k; Forall u64_ok cur)
    LOCAL (temp _selected_kind (vl (Znth 0 args)); temp _selected_address (vl (Znth 1 args));
           temp _copied_root_address (vl (Znth 2 args)); temp _advertised_count (vl (Znth 3 args));
           temp _completed_copies (vl (Znth 4 args)); temp _madt_count (vl (Znth 5 args));
           temp _admission_status (vl (Znth 6 args)); temp _admission_detail (vl (Znth 7 args));
           temp _admitted_apic_id (vl (Znth 8 args)); temp _executing_apic_id (vl (Znth 9 args));
           temp _published_apic_id rp; lvar _answer (tarray tulong 4) v_answer; gvars gv)
    SEP (data_at Tsh (tarray tulong 4) (map vl cur ++ Zrepeat Vundef (4 - k)) v_answer;
         Ora gv x (h ++ hs); data_at rsh tuint rold rp))%assert.
  { Exists (@nil answer) (@nil Z). rewrite app_nil_r. entailer!. }
  { (* word k *)
    cbv beta. Intros.
    match goal with H: Zlength cur = ?k |- _ => subst k end.
    freeze FR := (data_at _ _ _ v_answer) (data_at _ _ _ rp).
    forward_call (gv, x, h ++ hs, args, Zlength cur).
    { apply (res_call x _ args cur); [ assumption | lia ]. }
    Intros v. thaw FR.
    forward.
    Exists (hs ++ [(ResultQuery args (Zlength cur), v)]) (cur ++ [v]).
    rewrite <- app_assoc.
    entailer!.
    { split; [ rewrite app_assoc; apply res_answer; [ assumption | lia ] |
        split; [ rewrite Zlength_app, Zlength_cons, Zlength_nil; lia |
                 apply Forall_app; split; [ assumption | constructor; auto ] ] ]. }
    apply derives_refl'. f_equal. apply upd_answers; lia. }
  Intros hs a.
  match goal with H: run _ _ (h ++ hs) = Some (result_collect args a) |- _ => rename H into Hr end.
  match goal with H: Zlength a = 4 |- _ => rename H into La end.
  match goal with H: Forall u64_ok a |- _ => rename H into Ua end.
  match goal with |- context [data_at Tsh (tarray tulong 4) ?X v_answer] =>
    replace X with (map vl a) by list_solve end.
  forward.
  forward_if.
  { (* word 0 *)
    z64. forward.
    Exists hs 18 0. entailer!.
    split; [ | unfold u32_ok; rep_lia ].
    rewrite Hr. f_equal. apply res_reject; [ assumption | unfold result_check; zrw; reflexivity | unfold S_OK; lia ]. }
  z64.
  forward.
  forward_if.
  { (* word 1 *)
    z64. forward.
    Exists hs 19 0. entailer!.
    split; [ | unfold u32_ok; rep_lia ].
    rewrite Hr. f_equal. apply res_reject; [ assumption | unfold result_check; zrw; reflexivity | unfold S_OK; lia ]. }
  z64.
  forward.
  forward_if.
  { (* word 2 *)
    z64. forward.
    Exists hs 20 0. entailer!.
    split; [ | unfold u32_ok; rep_lia ].
    rewrite Hr. f_equal. apply res_reject; [ assumption | unfold result_check; zrw; reflexivity | unfold S_OK; lia ]. }
  z64.
  forward.
  forward_if (temp _t'2 (Vint (Int.repr (b2z (res_c1 args a))))).
  { change (Int.unsigned (Int.repr (-1))) with 4294967295 in *. z64.
    forward. entailer!.
    unfold res_c1. rewrite (proj2 (Z.ltb_ge (Znth 3 a) (2 ^ 32))) by (change (2 ^ 32) with 4294967296; lia).
    reflexivity. }
  { change (Int.unsigned (Int.repr (-1))) with 4294967295 in *. z64.
    forward. forward. entailer!.
    unfold res_c1. rewrite (proj2 (Z.ltb_lt (Znth 3 a) (2 ^ 32))) by (change (2 ^ 32) with 4294967296; lia).
    bnorm. bclose. }
  forward_if (temp _t'3 (Vint (Int.repr (b2z (res_c2 args a))))).
  { bfix. forward. entailer!. unfold res_c2. zrw. reflexivity. }
  { bfix. forward. forward. entailer!. unfold res_c2. zrw. bnorm. bclose. }
  forward_if.
  { (* word 3 *)
    bfix. forward.
    Exists hs 21 0. entailer!.
    split; [ | unfold u32_ok; rep_lia ].
    unfold res_c2, res_c1 in *.
    rewrite Hr. f_equal. apply res_reject; [ assumption | unfold result_check; zrw; reflexivity | unfold S_OK; lia ]. }
  bfix.
  match goal with H: res_c2 _ _ = false |- _ => rename H into Hok; unfold res_c2, res_c1 in Hok end.
  assert (Id: u32_ok (Znth 3 a)).
  { pose proof Hok as Hb. apply orb_false_iff in Hb as [Hb _]. apply orb_false_iff in Hb as [Hb _].
    apply negb_false_iff, Z.ltb_lt in Hb.
    assert (U3: u64_ok (Znth 3 a)) by u64. unfold u64_ok, u32_ok in *. change (2 ^ 32) with 4294967296 in Hb. rep_lia. }
  forward. forward.
  assert (U3: u64_ok (Znth 3 a)) by u64.
  rewrite Int64.Z_mod_modulus_eq, Z.mod_small by (unfold u64_ok in U3; rep_lia).
  forward.
  Exists hs 0 (Znth 3 a). entailer!.
  rewrite Hr. f_equal. apply res_accept; [ assumption | unfold result_check; zrw; reflexivity ].
Qed.
