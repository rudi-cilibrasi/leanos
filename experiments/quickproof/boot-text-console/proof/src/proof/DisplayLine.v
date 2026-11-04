(* Body of boot_text_line. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import LeanosConsole.console.code.
Require Import LeanosConsole.proof.Defs.
Require Import LeanosConsole.proof.ConsoleSpecs.
Require Import LeanosConsole.proof.Easy.
Require Import LeanosConsole.proof.Display.
#[local] Existing Instance ConsoleSpecs.CS.

Lemma Znth_u16s: forall i cs, 0 <= i < Zlength cs -> Znth i (u16s cs) = Vint (Int.repr (Znth i cs)).
Proof. intros. unfold u16s. rewrite Znth_map by lia. reflexivity. Qed.

Lemma u16_of: forall cs i, u16_ok cs -> 0 <= i < Zlength cs -> 0 <= Znth i cs <= 65535.
Proof. intros cs i H Hi. exact (proj1 (Forall_Znth cs _) H i Hi). Qed.

Lemma body_boot_text_line: semax_body Vprog Gprog f_boot_text_line boot_text_line_spec.
Proof.
  start_function.
  destruct H as (Hw & Hs & Hh & Hr & Hc).
  assert (Hhs: height * stride <= 16384) by (apply (Z.le_trans _ (64 * 256)); [ apply Z.mul_le_mono_nonneg; lia | lia ]).
  unfold con_val.
  forward. forward. forward. forward. forward.
  forward_if.
  { forward. Exists cs. unfold con_val. rewrite (proj2 (Z.ltb_lt (row + 1) height)) by lia. entailer!. }
  assert (Hrow: row = height - 1) by lia. subst row.
  rewrite add_repr. replace (height - 1 + 1) with height by lia.
  forward.
  forward_loop
    (EX y: Z, EX cs1: list Z,
     PROP (1 <= y <= height; Zlength cs1 = (height * stride)%Z; u16_ok cs1)
     LOCAL (temp _y (Vint (Int.repr y)); temp _c c)
     SEP (data_at Tsh t_con (con_val w stride width height height 0 en bu) c;
          data_at sh (tarray tushort (height * stride)) (u16s cs1) w))
  break:
    (EX cs1: list Z,
     PROP (Zlength cs1 = (height * stride)%Z; u16_ok cs1)
     LOCAL (temp _c c)
     SEP (data_at Tsh t_con (con_val w stride width height height 0 en bu) c;
          data_at sh (tarray tushort (height * stride)) (u16s cs1) w)).
  { Exists 1 cs. unfold con_val. entailer!. }
  { Intros y cs1. unfold con_val. forward. forward_if.
    { forward.
      forward_loop
        (EX x: Z, EX cs2: list Z,
         PROP (0 <= x <= width; Zlength cs2 = (height * stride)%Z; u16_ok cs2)
         LOCAL (temp _x (Vint (Int.repr x)); temp _y (Vint (Int.repr y)); temp _c c)
         SEP (data_at Tsh t_con (con_val w stride width height height 0 en bu) c;
              data_at sh (tarray tushort (height * stride)) (u16s cs2) w))
      break:
        (EX cs2: list Z,
         PROP (Zlength cs2 = (height * stride)%Z; u16_ok cs2)
         LOCAL (temp _y (Vint (Int.repr y)); temp _c c)
         SEP (data_at Tsh t_con (con_val w stride width height height 0 en bu) c;
              data_at sh (tarray tushort (height * stride)) (u16s cs2) w)).
      { Exists 0 cs1. unfold con_val. entailer!. }
      { Intros x cs2. unfold con_val. forward. forward_if.
        { assert (Hsrc: 0 <= y * stride + x < height * stride).
          { split; [ nia | ]. assert (y + 1 <= height) by lia.
            assert ((y + 1) * stride <= height * stride) by (apply Z.mul_le_mono_nonneg_r; lia). nia. }
          assert (Hdst: 0 <= (y - 1) * stride + x < height * stride).
          { split; [ nia | ]. assert ((y - 1) * stride <= y * stride) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
          assert (Hv := u16_of cs2 (y * stride + x) ltac:(assumption) ltac:(lia)).
          forward. forward. forward. forward.
          forward.
          { entailer!. rewrite Znth_u16s by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
          rewrite Znth_u16s by lia.
          forward.
          rewrite ze16 by lia. rewrite u16s_upd by lia.
          forward.
          Exists (x + 1) (upd_Znth ((y - 1) * stride + x) cs2 (Znth (y * stride + x) cs2)).
          unfold con_val. entailer!.
          split; [ rewrite upd_Znth_Zlength; lia | apply Forall_upd_Znth; [ assumption | lia ] ]. }
        { forward. Exists cs2. unfold con_val. entailer!. }
      }
      { Intros cs2. forward. Exists (y + 1) cs2. unfold con_val. entailer!. }
    }
    { forward. Exists cs1. unfold con_val. entailer!. }
  }
  Intros cs1.
  unfold con_val.
  forward. forward. forward.
  rewrite sub_repr.
  forward_loop
    (EX x: Z, EX cs2: list Z,
     PROP (0 <= x <= width; Zlength cs2 = (height * stride)%Z; u16_ok cs2)
     LOCAL (temp _x__1 (Vint (Int.repr x)); temp _c c)
     SEP (data_at Tsh t_con (con_val w stride width height (height - 1) 0 en bu) c;
          data_at sh (tarray tushort (height * stride)) (u16s cs2) w))
  break:
    (EX cs2: list Z,
     PROP (Zlength cs2 = (height * stride)%Z; u16_ok cs2)
     LOCAL (temp _c c)
     SEP (data_at Tsh t_con (con_val w stride width height (height - 1) 0 en bu) c;
          data_at sh (tarray tushort (height * stride)) (u16s cs2) w)).
  { Exists 0 cs1. unfold con_val. entailer!. }
  { Intros x cs2. unfold con_val. forward. forward_if.
    { assert (Hidx: 0 <= (height - 1) * stride + x < height * stride).
      { split; [ nia | ]. assert ((height - 1 + 1) * stride <= height * stride) by (apply Z.mul_le_mono_nonneg_r; lia). nia. }
      forward. forward. forward. forward.
      rewrite ze16 by lia. rewrite u16s_upd by lia.
      forward.
      Exists (x + 1) (upd_Znth ((height - 1) * stride + x) cs2 1824).
      unfold con_val. entailer!.
      split; [ rewrite upd_Znth_Zlength; lia | apply Forall_upd_Znth; [ assumption | lia ] ]. }
    { forward. Exists cs2. unfold con_val. entailer!. }
  }
  Intros cs2. Exists cs2. unfold con_val.
  rewrite Z.ltb_irrefl.
  entailer!.
Qed.
