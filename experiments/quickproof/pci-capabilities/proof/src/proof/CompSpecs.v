(* Law capabilities_complete: the law's device and the specifications of the harness's functions, under the
   compspecs of the law's whole program (CompProg.LCS).

   The device of the law (Dev_comp ctx bdf h): the harness's struct space at ctx, with bus/device/function bdf
   and some 64 words W, and every answer of h the word of W at its offset, read successfully.  The device holds
   the share sh_dev of the struct; main keeps the other share, sh_main, through the call of the walker, so that
   the words the device holds afterwards are the words main planted (space_values_eq): the walker's
   specification, parametric in the device, cannot change them, and the share kept proves it. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosCaps.proof.Defs.
Require LeanosCaps.proof.CapsSpecs.
Require Import LeanosCaps.proof.CompPure.
Require Import LeanosCaps.proof.CompProg.
Require Import LeanosCaps.harness.capabilities_complete.code.
Local Open Scope Z_scope.

Notation LCS := LeanosCaps.proof.CompProg.LCS.
#[export] Existing Instance LeanosCaps.proof.CompProg.LCS.

Definition t_space := Tstruct _space noattr.
Definition vint (z: Z) : val := Vint (Int.repr z).

(* struct space: bus, device, function, words[64]. *)
Definition space_val (bdf: Z * Z * Z) (W: list Z) : reptype t_space :=
  (vint (CapsSpecs.bus_of bdf), (vint (CapsSpecs.dev_of bdf), (vint (CapsSpecs.fn_of bdf), map vint W))).

(* The device's share of the struct, and main's. *)
Definition sh_dev : share := fst (slice.cleave Tsh).
Definition sh_main : share := snd (slice.cleave Tsh).

Lemma sh_dev_readable: readable_share sh_dev.
Proof. apply slice.cleave_readable1. apply readable_share_top. Qed.

Lemma sh_main_readable: readable_share sh_main.
Proof. apply slice.cleave_readable2. apply readable_share_top. Qed.

#[export] Hint Resolve sh_dev_readable sh_main_readable : core share.

Lemma sh_join: sepalg.join sh_dev sh_main Tsh.
Proof. apply slice.cleave_join. Qed.

Definition Dev_comp (ctx: val) (bdf: Z * Z * Z) (h: list answer) : mpred :=
  EX W: list Z,
  !! (Zlength W = 64 /\ Forall CapsSpecs.u32_ok W /\ Forall (served W) h) &&
  data_at sh_dev t_space (space_val bdf W) ctx.

Definition space_read_spec : ident * funspec := (_space_read, CapsSpecs.read_spec Dev_comp).

Lemma uchar_defined: forall b, CapsSpecs.u8_ok b -> value_defined tuchar (vint b).
Proof.
  intros b Hb. unfold CapsSpecs.u8_ok in Hb. rewrite value_defined_eq. unfold value_defined_byvalue, vint.
  simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia.
Qed.

Lemma space_defined: forall bdf W,
  CapsSpecs.u8_ok (CapsSpecs.bus_of bdf) -> CapsSpecs.u8_ok (CapsSpecs.dev_of bdf) ->
  CapsSpecs.u8_ok (CapsSpecs.fn_of bdf) -> Zlength W = 64 ->
  value_defined t_space (space_val bdf W).
Proof.
  intros bdf W Hb Hd Hf LW.
  rewrite value_defined_eq. simpl.
  split; [ apply uchar_defined; exact Hb | ].
  split; [ apply uchar_defined; exact Hd | ].
  split; [ apply uchar_defined; exact Hf | ].
  apply value_defined_tarray; [ rewrite Zlength_map; exact LW | ].
  apply Forall_map. apply Forall_forall. intros x _. simpl. rewrite value_defined_eq.
  unfold value_defined_byvalue, vint. simpl. auto.
Qed.

Lemma map_vint_inj: forall W1 W2, Forall CapsSpecs.u32_ok W1 -> Forall CapsSpecs.u32_ok W2 ->
  map vint W1 = map vint W2 -> W1 = W2.
Proof.
  induction W1 as [|a W1 IH]; intros [|b W2] F1 F2 E; cbn [map] in E; try discriminate; auto.
  assert (Eab: vint a = vint b) by congruence.
  assert (Erest: map vint W1 = map vint W2) by congruence.
  assert (R: Int.repr a = Int.repr b) by (unfold vint in Eab; congruence).
  apply Forall_cons_iff in F1, F2. destruct F1 as [Fa F1], F2 as [Fb F2]. unfold CapsSpecs.u32_ok in Fa, Fb.
  f_equal; [ apply repr_inj_unsigned; auto | apply IH; auto ].
Qed.

(* Two readable shares of one space hold the same words. *)
Lemma space_values_eq: forall sh1 sh2 bdf W1 W2 p, readable_share sh1 -> readable_share sh2 ->
  CapsSpecs.u8_ok (CapsSpecs.bus_of bdf) -> CapsSpecs.u8_ok (CapsSpecs.dev_of bdf) ->
  CapsSpecs.u8_ok (CapsSpecs.fn_of bdf) -> Zlength W1 = 64 -> Zlength W2 = 64 ->
  Forall CapsSpecs.u32_ok W1 -> Forall CapsSpecs.u32_ok W2 ->
  data_at sh1 t_space (space_val bdf W1) p * data_at sh2 t_space (space_val bdf W2) p |-- !! (W1 = W2).
Proof.
  intros. eapply derives_trans.
  - apply data_at_values_cohere; auto; apply space_defined; auto.
  - apply prop_derives. intros E. unfold space_val in E. inversion E. apply map_vint_inj; auto.
Qed.

(* The unit's compspecs (of the specifications in CapsSpecs) and the law's agree on the types they share. *)
Lemma uint__cs: forall sh p, @data_at_ CapsSpecs.CS sh tuint p = @data_at_ LCS sh tuint p.
Proof. intros. apply equal_f. apply (@data_at__change_composite CapsSpecs.CS LCS LCR). reflexivity. Qed.

Lemma uint_cs: forall sh (v: val) p, @data_at CapsSpecs.CS sh tuint v p = @data_at LCS sh tuint v p.
Proof. intros. apply equal_f. apply (@data_at_change_composite CapsSpecs.CS LCS LCR); [ apply JMeq_refl | reflexivity ]. Qed.
