(* Law capabilities_adversarial: the body of the harness's device_read against the read protocol of Dev_adv. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosCaps.harness.capabilities_adversarial.code.
Require Import LeanosCaps.proof.Defs.
Require LeanosCaps.proof.CapsSpecs.
Require Import LeanosCaps.proof.AdvProg LeanosCaps.proof.AdvWalk LeanosCaps.proof.AdvSpecs.
Local Open Scope Z_scope.
#[local] Existing Instance AdvProg.LCS.

(* The log after one more answer. *)
Lemma log_at_snoc: forall h offs oks vals o ok v vals',
  Zlength h < 52 -> log_at h offs oks vals ->
  Zlength vals' = 52 ->
  (forall i, 0 <= i < Zlength h -> aok (Znth i h) = true -> Znth i vals' = Znth i vals) ->
  (ok = true -> Znth (Zlength h) vals' = Vint (Int.repr v)) ->
  log_at (h ++ [(o, ok, v)]) (upd_Znth (Zlength h) offs (Vint (Int.repr o)))
         (upd_Znth (Zlength h) oks (Vint (Int.repr (CapsSpecs.b2z ok)))) vals'.
Proof.
  intros h offs oks vals o ok v vals' L (L1 & L2 & L3 & F) L3' Kv Nv.
  pose proof (Zlength_nonneg h).
  split; [ rewrite upd_Znth_Zlength; lia | ]. split; [ rewrite upd_Znth_Zlength; lia | ]. split; [ exact L3' | ].
  intros i Hi. rewrite Zlength_app, Zlength_cons, Zlength_nil in Hi.
  destruct (Z.eq_dec i (Zlength h)) as [->|Hne].
  - rewrite !upd_Znth_same by lia. rewrite Znth_app2 by lia. rewrite Z.sub_diag, Znth_0_cons.
    unfold aoff, aok, aval; simpl. split; [ reflexivity | ]. split; [ reflexivity | ]. exact Nv.
  - rewrite !upd_Znth_diff by lia. rewrite Znth_app1 by lia.
    destruct (F i ltac:(lia)) as (F1 & F2 & F3). split; [ exact F1 | ]. split; [ exact F2 | ].
    intros E. rewrite Kv by (auto; lia). exact (F3 E).
Qed.

Lemma answers_ok_snoc: forall h o ok v, answers_ok h -> 0 <= o <= 252 -> CapsSpecs.u32_ok v ->
  answers_ok (h ++ [(o, ok, v)]).
Proof. intros. apply Forall_app. split; [ assumption | constructor; [ split; assumption | constructor ] ]. Qed.

Lemma data_at__tuint_cs: forall sh p, @data_at_ CapsSpecs.CS sh tuint p = @data_at_ LCS sh tuint p.
Proof.
  intros. apply (f_equal (fun f => f p)).
  apply (@data_at__change_composite CapsSpecs.CS LCS (CCE_any CapsSpecs.CS LCS)); reflexivity.
Qed.

Lemma data_at_tuint_cs: forall sh v p, @data_at CapsSpecs.CS sh tuint v p = @data_at LCS sh tuint v p.
Proof.
  intros. apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite CapsSpecs.CS LCS (CCE_any CapsSpecs.CS LCS)); [ apply JMeq_refl | reflexivity ].
Qed.

Lemma body_device_read: semax_body Vh Gh f_device_read device_read_spec.
Proof.
  start_function.
  unfold Dev_adv. Intros offs oks vals.
  destruct bdf as [[bus dev] fn]. unfold dev_val.
  unfold CapsSpecs.bus_of, CapsSpecs.dev_of, CapsSpecs.fn_of, CapsSpecs.u8_ok in *. simpl fst in *; simpl snd in *.
  rewrite data_at__tuint_cs.
  pose proof H7 as (L1 & L2 & L3 & _).
  forward. forward.
  forward_if (temp _t'1 (Vint Int.one)).
  { forward. forward. entailer!. }
  { contradiction. }
  forward_if (temp _t'2 (Vint Int.one)).
  { forward. forward. entailer!. }
  { discriminate. }
  forward_call (Int.one).
  forward_if (temp _t'3 (Vint Int.one)).
  { forward. entailer!. destruct (zlt 252 off); [ lia | reflexivity ]. }
  { exfalso. match goal with N: _ <> _ |- _ => apply N end. rewrite and_repr, H0. reflexivity. }
  forward_call (Int.one).
  forward.
  forward_call (Int.one).
  { entailer!. simpl. unfold Int.ltu. rewrite !Int.unsigned_repr by rep_lia.
    destruct (zlt _ _); [ reflexivity | lia ]. }
  pose proof (Zlength_nonneg h).
  forward. forward. forward; try solve [ entailer! ].
  rewrite add_repr. rewrite zero_ext_inrange by (rewrite Int.unsigned_repr by rep_lia; simpl; lia).
  forward_call. Intros b.
  forward_if.
  { forward; try solve [ entailer! ]. forward.
    Exists false 0. unfold Dev_adv.
    Exists (upd_Znth (Zlength h) offs (Vint (Int.repr off))) (upd_Znth (Zlength h) oks (Vint (Int.repr 0))) vals.
    change (if false then ?a else ?b) with b. rewrite data_at__tuint_cs.
    unfold dev_val, CapsSpecs.bus_of, CapsSpecs.dev_of, CapsSpecs.fn_of. simpl fst; simpl snd.
    replace (Zlength (h ++ [(off, false, 0)])) with (Zlength h + 1) by (rewrite Zlength_app; reflexivity).
    entailer!.
    split; [ apply answers_ok_snoc; auto; rep_lia | ].
    apply (log_at_snoc h offs oks vals); auto; discriminate. }
  { forward_call. Intros v. forward. forward; try solve [ entailer! ]. forward; try solve [ entailer! ].
    forward.
    Exists true v. unfold Dev_adv.
    Exists (upd_Znth (Zlength h) offs (Vint (Int.repr off))) (upd_Znth (Zlength h) oks (Vint (Int.repr 1)))
      (upd_Znth (Zlength h) vals (Vint (Int.repr v))).
    change (if true then ?a else ?b) with a. rewrite data_at_tuint_cs.
    change (Int.zero_ext 8 (Int.repr 1)) with (Int.repr 1).
    unfold dev_val, CapsSpecs.bus_of, CapsSpecs.dev_of, CapsSpecs.fn_of. simpl fst; simpl snd.
    replace (Zlength (h ++ [(off, true, v)])) with (Zlength h + 1) by (rewrite Zlength_app; reflexivity).
    entailer!.
    split; [ apply answers_ok_snoc; auto; rep_lia | ].
    apply (log_at_snoc h offs oks vals); auto.
    - rewrite upd_Znth_Zlength; lia.
    - intros i Hi _. rewrite upd_Znth_diff by lia. reflexivity.
    - intros _. rewrite upd_Znth_same by lia. reflexivity. }
Qed.
