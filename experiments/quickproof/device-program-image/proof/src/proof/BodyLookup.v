(* The bodies of the two lookups of wifi-exec.h: wifi_is_sink and wifi_has_desc, loops over the declared entries
   with an early `return 1`, against existsb over sublist 0 count. *)
Require Import VST.floyd.proofauto.
Require Import LeanosDeviceProgramImage.device_program.code.
Require Import LeanosDeviceProgramImage.proof.Specs.
#[local] Existing Instance Specs.CS.
Local Open Scope Z_scope.

(* existsb over a growing prefix. *)
Lemma existsb_prefix_step: forall {A} {d: Inhabitant A} (f: A -> bool) (l: list A) i,
  0 <= i < Zlength l ->
  existsb f (sublist 0 (i + 1) l) = (existsb f (sublist 0 i l) || f (Znth i l))%bool.
Proof.
  intros A d f l i I.
  rewrite (sublist_split 0 i (i + 1)) by lia. rewrite existsb_app.
  rewrite (sublist_one i (i + 1) l) by lia. cbn. rewrite orb_false_r. reflexivity.
Qed.

Lemma u32_eq: forall a b, u32_ok a -> u32_ok b -> (Int.eq (Int.repr a) (Int.repr b) = (a =? b)).
Proof.
  intros a b A B. unfold u32_ok in *.
  destruct (Z.eqb_spec a b) as [-> | N]; [ apply Int.eq_true | ].
  apply Int.eq_false. intros E. apply N. apply repr_inj_unsigned; auto; rep_lia.
Qed.

Lemma existsb_hit: forall {A} {d: Inhabitant A} (f: A -> bool) (l: list A) i n,
  0 <= i < n -> n <= Zlength l -> f (Znth i l) = true -> existsb f (sublist 0 n l) = true.
Proof.
  intros A d f l i n I N F. apply existsb_exists. exists (Znth i l). split; auto.
  replace (Znth i l) with (Znth i (sublist 0 n l)) by (rewrite Znth_sublist by lia; f_equal; lia).
  apply Znth_In. rewrite Zlength_sublist by lia. lia.
Qed.

Lemma Znth_u32: forall (l: list Z) i, Forall u32_ok l -> 0 <= i < Zlength l -> 0 <= Znth i l <= Int.max_unsigned.
Proof. intros l i F I. apply (proj1 (Forall_Znth l _) F i I). Qed.

Lemma body_wifi_is_sink : semax_body Vprog Gprog f_wifi_is_sink is_sink_spec.
Proof.
  start_function.
  rename H into PW, H0 into SC, H1 into UO.
  pose proof PW as PW'. unfold policy_wf in PW'.
  destruct PW' as (_ & _ & _ & _ & _ & _ & _ & Usc & Lsk & Fsk & _ & _ & _).
  pose proof UO as UO'. pose proof Usc as Usc'. unfold u32_ok in UO', Usc'.
  unfold MAX_SINKS in *.
  forward.
  forward_loop (EX i: Z,
      PROP (0 <= i <= pl_sink_count P; existsb (Z.eqb off) (sublist 0 i (pl_sinks P)) = false)
      LOCAL (temp _i (Vint (Int.repr i)); temp _p pp; temp _off (Vint (Int.repr off)))
      SEP (data_at psh t_policy (policy_val P) pp))%assert
    break: (PROP (existsb (Z.eqb off) (sublist 0 (pl_sink_count P) (pl_sinks P)) = false)
      LOCAL (temp _p pp; temp _off (Vint (Int.repr off)))
      SEP (data_at psh t_policy (policy_val P) pp)).
  { Exists 0. entailer!. }
  { Intros i. rename H into I, H0 into Ex.
    unfold policy_val, policy_rep.
    forward.
    forward_if; [ | forward; entailer!; replace i with (pl_sink_count P) in Ex by lia; exact Ex ].
    rename H into Lt.
    forward.
    pose proof (Znth_u32 (pl_sinks P) i Fsk ltac:(lia)) as Ui.
    forward_if.
    { rename H into E.
      forward. entailer!.
      unfold is_sink, declared_sinks. rewrite (existsb_hit _ _ i); [ reflexivity | lia | lia | ].
      apply Z.eqb_eq; congruence. }
    { rename H into N. forward. Exists (i + 1). entailer!.
      rewrite existsb_prefix_step by lia. rewrite Ex. cbn.
      apply Z.eqb_neq. intros E. apply N. rewrite E. reflexivity. } }

  forward.
  entailer!. unfold is_sink, declared_sinks. rewrite H. reflexivity.
Qed.

Lemma desc_eqb_sym_val: forall d e,
  desc_eqb d e = ((ds_trb e =? ds_trb d) && (ds_start e =? ds_start d) && (ds_count e =? ds_count d) &&
                  (ds_stride e =? ds_stride d))%bool.
Proof. intros. unfold desc_eqb. rewrite (Z.eqb_sym (ds_trb d)), (Z.eqb_sym (ds_start d)),
  (Z.eqb_sym (ds_count d)), (Z.eqb_sym (ds_stride d)). reflexivity. Qed.

Lemma b2z_and_eq: forall (b: bool) x y, u32_ok x -> u32_ok y ->
  Vint (if b then (if Int.eq (Int.repr x) (Int.repr y) then Int.one else Int.zero) else Int.zero) =
  Vint (Int.repr (Z.b2z (b && (x =? y))%bool)).
Proof.
  intros b x y X Y. rewrite u32_eq by auto. destruct b, (x =? y); reflexivity.
Qed.

(* Znth of a mapped list, whatever the default (VST's loads use the default of the type). *)
Lemma Znth_map_any: forall {A B} (da: Inhabitant A) (db: Inhabitant B) (f: A -> B) (l: list A) i,
  0 <= i < Zlength l -> @Znth B db i (map f l) = f (@Znth A da i l).
Proof.
  intros A B da db f l i I. unfold Znth. rewrite !if_false by lia.
  rewrite (nth_indep (map f l) db (f da)) by (rewrite length_map; rewrite Zlength_correct in I; lia).
  apply map_nth.
Qed.

Lemma bool2val_eq: forall x y, u32_ok x -> u32_ok y ->
  bool2val (Int.eq (Int.repr x) (Int.repr y)) = Vint (Int.repr (Z.b2z (x =? y))).
Proof. intros. rewrite u32_eq by auto. destruct (x =? y); reflexivity. Qed.

Lemma repr_u32_eq: forall x y, u32_ok x -> u32_ok y -> Int.repr x = Int.repr y -> (x =? y) = true.
Proof. intros x y X Y E. apply Z.eqb_eq. unfold u32_ok in *. apply repr_inj_unsigned; auto. Qed.

Lemma repr_u32_neq: forall x y, Int.repr x <> Int.repr y -> (x =? y) = false.
Proof. intros x y N. apply Z.eqb_neq. intros ->. apply N. reflexivity. Qed.

Lemma b2z_true: forall b: bool, Int.repr (Z.b2z b) <> Int.repr 0 -> b = true.
Proof. intros [ | ] N; [ reflexivity | contradiction N; reflexivity ]. Qed.

Lemma b2z_false: forall b: bool, Int.repr (Z.b2z b) = Int.repr 0 -> b = false.
Proof. intros [ | ] N; [ discriminate N | reflexivity ]. Qed.

Ltac pu := unfold policy_val, policy_rep.

(* A load of descs[i]'s field: the element as its record. *)
Ltac dload E := forward; [ entailer!; rewrite E; exact I | try rewrite E; cbn [desc_val] ].

(* The joins of the && chain: t = b && (x =? y) after a comparison, or 0. *)
Ltac jtrue H := pu; entailer!; rewrite H; cbn [andb]; symmetry; apply bool2val_eq; auto.
Ltac jfalse H := pu; entailer!; rewrite H; rewrite ?andb_false_r; reflexivity.

Lemma body_wifi_has_desc : semax_body Vprog Gprog f_wifi_has_desc has_desc_spec.
Proof.
  start_function.
  rename H into PW, H0 into DC, H1 into DW.
  pose proof PW as PW'. unfold policy_wf in PW'.
  destruct PW' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Udc & Lds & Fds).
  pose proof Udc as Udc'. unfold u32_ok in Udc'.
  pose proof DW as (Dt & Ds & Dc & Dd).
  unfold MAX_DESCS in *.
  forward.
  forward_loop (EX i: Z,
      PROP (0 <= i <= pl_desc_count P; existsb (desc_eqb d) (sublist 0 i (pl_descs P)) = false)
      LOCAL (temp _i (Vint (Int.repr i)); temp _p pp; temp _d dp)
      SEP (data_at psh t_policy (policy_val P) pp; data_at dsh t_desc (desc_val d) dp))%assert
    break: (PROP (existsb (desc_eqb d) (sublist 0 (pl_desc_count P) (pl_descs P)) = false)
      LOCAL (temp _p pp; temp _d dp)
      SEP (data_at psh t_policy (policy_val P) pp; data_at dsh t_desc (desc_val d) dp)).
  { Exists 0. entailer!. }
  { Intros i. rename H into I, H0 into Ex.
    pu.
    forward.
    forward_if; [ | forward; entailer!; replace i with (pl_desc_count P) in Ex by lia; exact Ex ].
    rename H into Lt.
    set (e := Znth i (pl_descs P)).
    assert (E: forall dd, @Znth (val * (val * (val * val))) dd i (map desc_val (pl_descs P)) = desc_val e)
      by (intros; unfold e; apply Znth_map_any; lia).
    assert (We: desc_wf e) by (apply (proj1 (Forall_Znth _ _) Fds i); lia).
    destruct We as (Et & Es & Ec & Ed).
    set (b1 := ((ds_trb e =? ds_trb d) && (ds_start e =? ds_start d))%bool).
    set (b2 := (b1 && (ds_count e =? ds_count d))%bool).
    set (b3 := (b2 && (ds_stride e =? ds_stride d))%bool).
    dload E. forward.
    forward_if (PROP () LOCAL (temp _t'1 (Vint (Int.repr (Z.b2z b1))); temp _i (Vint (Int.repr i)); temp _p pp;
                               temp _d dp)
                SEP (data_at psh t_policy (policy_val P) pp; data_at dsh t_desc (desc_val d) dp)).
    { apply repr_u32_eq in H; auto. dload E. forward. forward. unfold b1. jtrue H. }
    { apply repr_u32_neq in H. forward. unfold b1. jfalse H. }
    pu.
    forward_if (PROP () LOCAL (temp _t'2 (Vint (Int.repr (Z.b2z b2))); temp _i (Vint (Int.repr i)); temp _p pp;
                               temp _d dp)
                SEP (data_at psh t_policy (policy_val P) pp; data_at dsh t_desc (desc_val d) dp)).
    { try apply b2z_true in H. dload E. forward. forward. unfold b2. jtrue H. }
    { try apply b2z_false in H. forward. unfold b2. jfalse H. }
    pu.
    forward_if (PROP () LOCAL (temp _t'3 (Vint (Int.repr (Z.b2z b3))); temp _i (Vint (Int.repr i)); temp _p pp;
                               temp _d dp)
                SEP (data_at psh t_policy (policy_val P) pp; data_at dsh t_desc (desc_val d) dp)).
    { try apply b2z_true in H. dload E. forward. forward. unfold b3. jtrue H. }
    { try apply b2z_false in H. forward. unfold b3. jfalse H. }
    assert (B3: desc_eqb d e = b3) by (unfold b3, b2, b1; apply desc_eqb_sym_val).
    forward_if.
    { try apply b2z_true in H. forward. entailer!.
      unfold has_desc, declared_descs. rewrite (existsb_hit _ _ i); [ reflexivity | lia | lia | ].
      fold e. rewrite B3. exact H. }
    { try apply b2z_false in H. forward. Exists (i + 1). entailer!.
      rewrite existsb_prefix_step by lia. rewrite Ex. fold e. rewrite B3. exact H. } }
  forward.
  entailer!. unfold has_desc, declared_descs. rewrite H. reflexivity.
Qed.
