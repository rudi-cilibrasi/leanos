(* The bodies of the admission functions of wifi-exec.h: wifi_policy_within (two loops with an early
   `return 0` against forallb, then the && chain of the scalar tests), wifi_service_admitted and
   wifi_source_admitted (|| chains with an early `return 0`, then a call or an && chain). *)
Require Import VST.floyd.proofauto.
Require Import LeanosDeviceProgramImage.device_program.code.
Require Import LeanosDeviceProgramImage.proof.Specs.
Require Import LeanosDeviceProgramImage.proof.BodyLookup.
Require Import LeanosDeviceProgramImage.proof.BodyPolicy.
#[local] Existing Instance Specs.CS.
Local Open Scope Z_scope.

Lemma forallb_prefix_step: forall {A} {d: Inhabitant A} (f: A -> bool) (l: list A) i,
  0 <= i < Zlength l ->
  forallb f (sublist 0 (i + 1) l) = (forallb f (sublist 0 i l) && f (Znth i l))%bool.
Proof.
  intros A d f l i I.
  rewrite (sublist_split 0 i (i + 1)) by lia. rewrite forallb_app.
  rewrite (sublist_one i (i + 1) l) by lia. cbn. rewrite andb_true_r. reflexivity.
Qed.

Lemma forallb_miss: forall {A} {d: Inhabitant A} (f: A -> bool) (l: list A) i n,
  0 <= i < n -> n <= Zlength l -> f (Znth i l) = false -> forallb f (sublist 0 n l) = false.
Proof.
  intros A d f l i n I N F. apply not_true_iff_false. intros T.
  rewrite forallb_forall in T.
  assert (In (Znth i l) (sublist 0 n l)).
  { replace (Znth i l) with (Znth i (sublist 0 n l)) by (rewrite Znth_sublist by lia; f_equal; lia).
    apply Znth_In. rewrite Zlength_sublist by lia. lia. }
  rewrite T in F by auto. discriminate.
Qed.

Lemma policy_val_eq: forall P, policy_val P =
  pol_tuple (Vint (Int.repr (pl_present P))) (Vint (Int.repr (pl_dma P))) (Vint (Int.repr (pl_window P)))
     (Vlong (Int64.repr (pl_cfg_read P))) (Vlong (Int64.repr (pl_cfg_write P)))
     (Vint (Int.repr (pl_cmd_clear P))) (Vint (Int.repr (pl_cmd_set P))) (Vint (Int.repr (pl_sink_count P)))
     (words_val (pl_sinks P)) (Vint (Int.repr (pl_desc_count P))) (map desc_val (pl_descs P)).
Proof. reflexivity. Qed.

Lemma policy_val_join: forall sh P i p,
  0 <= i < 16 -> Zlength (pl_descs P) = 16 -> field_compatible t_policy [] p ->
  (data_at sh t_desc (desc_val (Znth i (pl_descs P))) (offset_val (80 + 16 * i) p) *
   pol_hole sh (Vint (Int.repr (pl_present P))) (Vint (Int.repr (pl_dma P))) (Vint (Int.repr (pl_window P)))
     (Vlong (Int64.repr (pl_cfg_read P))) (Vlong (Int64.repr (pl_cfg_write P)))
     (Vint (Int.repr (pl_cmd_clear P))) (Vint (Int.repr (pl_cmd_set P))) (Vint (Int.repr (pl_sink_count P)))
     (words_val (pl_sinks P)) (Vint (Int.repr (pl_desc_count P)))
     (sublist 0 i (map desc_val (pl_descs P))) (sublist (i + 1) 16 (map desc_val (pl_descs P))) i p)%logic |--
  data_at sh t_policy (policy_val P) p.
Proof. intros. rewrite (policy_val_split sh P i p) by auto. apply derives_refl. Qed.

Lemma ule_val: forall x y, u32_ok x -> u32_ok y ->
  bool2val (negb (Int.ltu (Int.repr y) (Int.repr x))) = Vint (Int.repr (Z.b2z (x <=? y))).
Proof.
  intros x y X Y. unfold u32_ok in *. unfold Int.ltu. rewrite !Int.unsigned_repr by rep_lia.
  destruct (zlt y x), (Z.leb_spec x y); try lia; reflexivity.
Qed.

(* The joins of an && chain over unsigned comparisons and bit tests. *)
Ltac ujoin_le H c :=
  rewrite ?Int.unsigned_repr in H by rep_lia; unfold c;
  first [ rewrite (proj2 (Z.leb_le _ _)) by lia; cbn [andb] | rewrite (proj2 (Z.leb_gt _ _)) by lia ];
  try (rewrite ule_val by (unfold u32_ok; rep_lia));
  repeat match goal with |- context [zlt ?a ?b] => destruct (zlt a b) end;
  repeat match goal with |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b) end;
  try reflexivity; try lia.
Ltac bjoin_t H c := unfold c; rewrite H; cbn [andb];
  first [ unfold bits_in64; destruct (Int64.eq _ _); reflexivity
        | unfold bits_in32; destruct (Int.eq _ _); reflexivity ].
Ltac bjoin_f H c := unfold c; rewrite H; reflexivity.

Lemma body_wifi_policy_within : semax_body Vprog Gprog f_wifi_policy_within policy_within_spec.
Proof.
  start_function.
  rename H into PB, H0 into MB.
  pose proof PB as (PW & Psc & Pdc). pose proof MB as (MW & Msc & Mdc).
  pose proof MW as MW'. unfold policy_wf in MW'.
  destruct MW' as (_ & _ & _ & _ & _ & _ & _ & Usc & Lsk & Fsk & Udc & Lds & Fds).
  pose proof Usc as Usc'. pose proof Udc as Udc'. unfold u32_ok in Usc', Udc'.
  unfold MAX_SINKS, MAX_DESCS in *.
  assert_PROP (field_compatible t_policy [] mp) as FCm by entailer!.
  forward.
  forward_loop (EX k: Z,
      PROP (0 <= k <= pl_sink_count M; forallb (is_sink P) (sublist 0 k (pl_sinks M)) = true)
      LOCAL (temp _k (Vint (Int.repr k)); temp _p pp; temp _max mp)
      SEP (data_at psh t_policy (policy_val P) pp; data_at msh t_policy (policy_val M) mp))%assert
    break: (PROP (forallb (is_sink P) (declared_sinks M) = true)
      LOCAL (temp _p pp; temp _max mp)
      SEP (data_at psh t_policy (policy_val P) pp; data_at msh t_policy (policy_val M) mp)).
  { Exists 0. entailer!. }
  { Intros k. rename H into K, H0 into Fa.
    rewrite (policy_val_eq M). unfold pol_tuple.
    forward.
    forward_if; [ | forward; entailer!; unfold declared_sinks;
                    replace k with (pl_sink_count M) in Fa by lia; exact Fa ].
    rename H into Lt.
    forward.
    pose proof (Znth_u32 (pl_sinks M) k Fsk ltac:(lia)) as Uk.
    forward_call (psh, pp, P, Znth k (pl_sinks M)).
    forward_if.
    { apply b2z_false in H. forward. pu. entailer!.
      unfold within, declared_sinks. rewrite (forallb_miss _ _ k); [ reflexivity | lia | lia | exact H ]. }
    { apply b2z_true in H. forward. Exists (k + 1). pu. entailer!.
      rewrite forallb_prefix_step by lia. rewrite Fa, H. reflexivity. } }
  forward.
  forward_loop (EX k: Z,
      PROP (0 <= k <= pl_desc_count M; forallb (has_desc P) (sublist 0 k (pl_descs M)) = true)
      LOCAL (temp _k__1 (Vint (Int.repr k)); temp _p pp; temp _max mp)
      SEP (data_at psh t_policy (policy_val P) pp; data_at msh t_policy (policy_val M) mp))%assert
    break: (PROP (forallb (is_sink P) (declared_sinks M) = true;
                  forallb (has_desc P) (declared_descs M) = true)
      LOCAL (temp _p pp; temp _max mp)
      SEP (data_at psh t_policy (policy_val P) pp; data_at msh t_policy (policy_val M) mp)).
  { Exists 0. entailer!. }
  { Intros k. rename H0 into K, H1 into Fa.
    rewrite (policy_val_eq M). unfold pol_tuple.
    forward.
    forward_if; [ | forward; entailer!; unfold declared_descs;
                    replace k with (pl_desc_count M) in Fa by lia; exact Fa ].
    rename H0 into Lt.
    change (data_at msh t_policy _ mp) with (data_at msh t_policy (policy_val M) mp).
    rewrite (policy_val_split msh M k mp) by (auto; lia). Intros.
    assert (Wk: desc_wf (Znth k (pl_descs M))) by (apply (proj1 (Forall_Znth _ _) Fds k); lia).
    forward_call (psh, pp, P, msh, offset_val (80 + 16 * k) mp, Znth k (pl_descs M)).
    forward_if.
    { apply b2z_false in H0. sep_apply (policy_val_join msh M k mp ltac:(lia) Lds FCm). forward. pu. entailer!.
      unfold within, declared_descs. rewrite H.
      rewrite (forallb_miss _ _ k); [ reflexivity | lia | lia | exact H0 ]. }
    { apply b2z_true in H0. sep_apply (policy_val_join msh M k mp ltac:(lia) Lds FCm). forward.
      Exists (k + 1). pu. entailer!.
      rewrite forallb_prefix_step by lia. rewrite Fa, H0. reflexivity. } }
  Intros. rename H into Fs, H0 into Fd.
  pose proof PW as PW'. unfold policy_wf in PW'.
  destruct PW' as (Ppr & Pdm & Pwn & Pcr & Pcw & Pcc & Pcs & _).
  pose proof MW as MW'. unfold policy_wf in MW'.
  destruct MW' as (Mpr & Mdm & Mwn & Mcr & Mcw & Mcc & Mcs & _).
  unfold u32_ok, u64_ok in Ppr, Pdm, Pwn, Pcr, Pcw, Pcc, Pcs, Mpr, Mdm, Mwn, Mcr, Mcw, Mcc, Mcs.
  set (c1 := ((pl_window P <=? pl_window M) && (pl_dma P <=? pl_dma M))%bool).
  set (c2 := (c1 && bits_in64 (pl_cfg_read P) (pl_cfg_read M))%bool).
  set (c3 := (c2 && bits_in64 (pl_cfg_write P) (pl_cfg_write M))%bool).
  set (c4 := (c3 && bits_in32 (pl_cmd_clear P) (pl_cmd_clear M))%bool).
  set (c5 := (c4 && bits_in32 (pl_cmd_set P) (pl_cmd_set M))%bool).
  pu.
  forward. forward.
  forward_if (PROP () LOCAL (temp _t'3 (Vint (Int.repr (Z.b2z c1))); temp _p pp; temp _max mp)
              SEP (data_at psh t_policy (policy_val P) pp; data_at msh t_policy (policy_val M) mp)).
  { forward. forward. forward. pu. entailer!. ujoin_le H c1. }
  { forward. pu. entailer!. ujoin_le H c1. }
  pu.
  forward_if (PROP () LOCAL (temp _t'4 (Vint (Int.repr (Z.b2z c2))); temp _p pp; temp _max mp)
              SEP (data_at psh t_policy (policy_val P) pp; data_at msh t_policy (policy_val M) mp)).
  { forward. forward. forward. pu. entailer!. bjoin_t H c2. }
  { forward. pu. entailer!. bjoin_f H c2. }
  pu.
  forward_if (PROP () LOCAL (temp _t'5 (Vint (Int.repr (Z.b2z c3))); temp _p pp; temp _max mp)
              SEP (data_at psh t_policy (policy_val P) pp; data_at msh t_policy (policy_val M) mp)).
  { forward. forward. forward. pu. entailer!. bjoin_t H c3. }
  { forward. pu. entailer!. bjoin_f H c3. }
  pu.
  forward_if (PROP () LOCAL (temp _t'6 (Vint (Int.repr (Z.b2z c4))); temp _p pp; temp _max mp)
              SEP (data_at psh t_policy (policy_val P) pp; data_at msh t_policy (policy_val M) mp)).
  { forward. forward. forward. pu. entailer!. bjoin_t H c4. }
  { forward. pu. entailer!. bjoin_f H c4. }
  pu.
  forward_if (PROP () LOCAL (temp _t'7 (Vint (Int.repr (Z.b2z c5))); temp _p pp; temp _max mp)
              SEP (data_at psh t_policy (policy_val P) pp; data_at msh t_policy (policy_val M) mp)).
  { forward. forward. forward. pu. entailer!. bjoin_t H c5. }
  { forward. pu. entailer!. bjoin_f H c5. }
  forward.
  unfold within. rewrite Fs, Fd. cbn [andb]. entailer!.
Qed.
