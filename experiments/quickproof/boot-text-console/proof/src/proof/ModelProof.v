(* The model unit patch/lean_export_model.c: leanos_boot_text_surface answers LeanOS.BootTextConsole.valid. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require LeanosConsole.units.Model.
Require Import LeanosConsole.model.code.
Require Import LeanosConsole.proof.Defs.

#[export] Instance CS : compspecs := LeanosConsole.units.Model.CS.
Definition Vprog : varspecs. mk_varspecs LeanosConsole.model.code.prog. Defined.

Definition surface_spec :=
  DECLARE _leanos_boot_text_surface
  WITH kind: Z, bits: Z, address: Z, pitch: Z, width: Z, height: Z
  PRE [ tulong, tulong, tulong, tulong, tulong, tulong ]
    PROP (0 <= kind <= Int64.max_unsigned; 0 <= bits <= Int64.max_unsigned;
          0 <= address <= Int64.max_unsigned; 0 <= pitch <= Int64.max_unsigned;
          0 <= width <= Int64.max_unsigned; 0 <= height <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr kind); Vlong (Int64.repr bits); Vlong (Int64.repr address);
            Vlong (Int64.repr pitch); Vlong (Int64.repr width); Vlong (Int64.repr height))
    SEP ()
  POST [ tulong ]
    PROP ()
    RETURN (Vlong (Int64.repr (if valid_geo kind bits address pitch width height then 1 else 0)))
    SEP ().

Definition Gprog : funspecs := [surface_spec].

Lemma valid_geo_iff: forall kind bits address pitch width height,
  valid_geo kind bits address pitch width height = true <->
  kind = 2 /\ bits = 16 /\ address = 753664 /\ 0 < width <= 160 /\ 0 < height <= 64 /\
  pitch mod 2 = 0 /\ 2 * width <= pitch /\ pitch <= 512.
Proof.
  split; [ apply valid_geo_bounds | ].
  intros (? & ? & ? & ? & ? & ? & ? & ?). unfold valid_geo.
  repeat rewrite andb_true_iff. rewrite !Z.eqb_eq, !Z.ltb_lt, !Z.leb_le. lia.
Qed.

(* Turn the hypotheses forward_if leaves into facts about Z. *)
Ltac to_z :=
  repeat match goal with
  | H: context [Int.unsigned (Int.repr ?n)] |- _ => rewrite (Int.unsigned_repr n) in H by rep_lia
  | H: Int64.eq (Int64.repr ?a) (Int64.repr ?b) = true |- _ =>
      apply Int64.same_if_eq in H; apply repr_inj_unsigned64 in H; [ | rep_lia | rep_lia ]
  | H: context [Int64.modu (Int64.repr ?a) (Int64.repr ?b)] |- _ =>
      unfold Int64.modu in H; rewrite (Int64.unsigned_repr a) in H by rep_lia;
      rewrite (Int64.unsigned_repr b) in H by rep_lia;
      assert (0 <= a mod b < b) by (apply Z.mod_pos_bound; lia)
  | H: context [Int64.mul (Int64.repr ?a) (Int64.repr ?b)] |- _ =>
      unfold Int64.mul in H; rewrite (Int64.unsigned_repr a) in H by rep_lia;
      rewrite (Int64.unsigned_repr b) in H by rep_lia
  | H: Int64.repr ?a = Int64.zero |- _ =>
      change Int64.zero with (Int64.repr 0) in H; apply repr_inj_unsigned64 in H; [ | rep_lia | rep_lia ]
  | H: Int64.repr ?a <> Int64.repr ?b |- _ =>
      let X := fresh "X" in
      assert (a <> b) by (intro X; rewrite X in H; contradiction); clear H
  | H: Int.repr (Z.b2z ?c) = Int.zero |- _ =>
      let E := fresh "E" in
      destruct c eqn:E; [ simpl in H; exfalso; apply Int.one_not_zero; exact H | clear H ]
  | H: Int.repr (Z.b2z ?c) <> Int.zero |- _ =>
      let E := fresh "E" in
      destruct c eqn:E; [ clear H | simpl in H; exfalso; apply H; reflexivity ]
  | H: negb ?c = true |- _ => apply negb_true_iff in H
  | H: negb ?c = false |- _ => apply negb_false_iff in H
  | H: Int64.ltu (Int64.repr ?a) (Int64.repr ?b) = true |- _ =>
      unfold Int64.ltu in H; rewrite !Int64.unsigned_repr in H by rep_lia;
      destruct (zlt a b); [ clear H | discriminate ]
  | H: Int64.ltu (Int64.repr ?a) (Int64.repr ?b) = false |- _ =>
      unfold Int64.ltu in H; rewrite !Int64.unsigned_repr in H by rep_lia;
      destruct (zlt a b); [ discriminate | clear H ]
  end.

(* A branch that returns 0: the selector's predicate is false there. *)
Ltac reject :=
  forward; entailer!; to_z;
  let V := fresh "V" in
  destruct (valid_geo _ _ _ _ _ _) eqn:V; [ exfalso; apply valid_geo_bounds in V; lia | reflexivity ].

Lemma body_surface: semax_body Vprog Gprog f_leanos_boot_text_surface surface_spec.
Proof.
  start_function.
  do 10 (forward_if; [ reject | ]).
  forward. entailer!. to_z.
  rewrite (proj2 (valid_geo_iff _ _ _ _ _ _)) by lia. reflexivity.
Qed.
