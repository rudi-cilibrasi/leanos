(* Body of boot_text_enable. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import LeanosConsole.console.code.
Require Import LeanosConsole.proof.Defs.
Require Import LeanosConsole.proof.ConsoleSpecs.
Require Import LeanosConsole.proof.Easy.
Require Import LeanosConsole.proof.Display.
Require LeanosConsole.proof.ModelProof.
#[local] Existing Instance ConsoleSpecs.CS.

Lemma divu2: forall p, 0 <= p <= Int.max_unsigned -> Int.divu (Int.repr p) (Int.repr 2) = Int.repr (p / 2).
Proof. intros. unfold Int.divu. rewrite !Int.unsigned_repr by rep_lia. reflexivity. Qed.

Lemma body_boot_text_enable: semax_body Vprog Gprog f_boot_text_enable boot_text_enable_spec.
Proof.
  start_function.
  destruct H as (Ha & Hp & Hwd & Hht & Hk & Hb).
  pose proof (geo_valid_con_ok g H0) as (Hok & Hp2 & Hsurf).
  destruct Hok as (Hw & Hs & Hh & _ & _).
  forward_call (c).
  unfold geo_val, con_disabled.
  forward; [ entailer!; simpl; rewrite ?Int.unsigned_repr by rep_lia; rep_lia | ].
  forward; [ entailer!; simpl; rewrite ?Int.unsigned_repr by rep_lia; rep_lia | ].
  forward. forward. forward. forward.
  forward_call (g_kind g, g_bits g, g_address g, g_pitch g, g_width g, g_height g).
  unfold geo_valid in H0. rewrite H0.
  forward_if; [ discriminate | ].
  forward. forward. forward. forward. forward. forward. forward. forward. forward. forward.
  rewrite divu2 by lia.
  set (st := g_pitch g / 2) in *. set (wd := g_width g) in *. set (ht := g_height g) in *.
  assert (Hhs: ht * st <= 16384) by (apply (Z.le_trans _ (64 * 256)); [ apply Z.mul_le_mono_nonneg; lia | lia ]).
  forward. forward.
  forward_loop
    (EX y: Z, EX cs1: list Z,
     PROP (0 <= y <= ht; Zlength cs1 = (ht * st)%Z; u16_ok cs1)
     LOCAL (temp _y (Vint (Int.repr y)); temp _c c; temp _g gp; temp _window w)
     SEP (data_at Tsh t_con (con_val w st wd ht 0 0 0 1) c; data_at Tsh t_geo (geo_val g) gp;
          data_at sh (tarray tushort (ht * st)) (u16s cs1) w))
  break:
    (EX cs1: list Z,
     PROP (Zlength cs1 = (ht * st)%Z; u16_ok cs1)
     LOCAL (temp _c c; temp _g gp; temp _window w)
     SEP (data_at Tsh t_con (con_val w st wd ht 0 0 0 1) c; data_at Tsh t_geo (geo_val g) gp;
          data_at sh (tarray tushort (ht * st)) (u16s cs1) w)).
  { Exists 0 cs. unfold con_val, geo_val. entailer!. }
  { Intros y cs1. unfold con_val. forward. forward_if.
    { forward.
      forward_loop
        (EX x: Z, EX cs2: list Z,
         PROP (0 <= x <= wd; Zlength cs2 = (ht * st)%Z; u16_ok cs2)
         LOCAL (temp _x (Vint (Int.repr x)); temp _y (Vint (Int.repr y)); temp _c c; temp _g gp;
                temp _window w)
         SEP (data_at Tsh t_con (con_val w st wd ht 0 0 0 1) c; data_at Tsh t_geo (geo_val g) gp;
              data_at sh (tarray tushort (ht * st)) (u16s cs2) w))
      break:
        (EX cs2: list Z,
         PROP (Zlength cs2 = (ht * st)%Z; u16_ok cs2)
         LOCAL (temp _y (Vint (Int.repr y)); temp _c c; temp _g gp; temp _window w)
         SEP (data_at Tsh t_con (con_val w st wd ht 0 0 0 1) c; data_at Tsh t_geo (geo_val g) gp;
              data_at sh (tarray tushort (ht * st)) (u16s cs2) w)).
      { Exists 0 cs1. unfold con_val. entailer!. }
      { Intros x cs2. unfold con_val. forward. forward_if.
        { assert (Hidx: 0 <= y * st + x < ht * st).
          { split; [ nia | ]. assert ((y + 1) * st <= ht * st) by (apply Z.mul_le_mono_nonneg_r; lia). nia. }
          forward. forward. forward.
          rewrite ?ze16 by lia. rewrite u16s_upd by lia.
          forward.
          Exists (x + 1) (upd_Znth (y * st + x) cs2 1824).
          unfold con_val. entailer!.
          split; [ rewrite upd_Znth_Zlength; lia | apply Forall_upd_Znth; [ assumption | lia ] ]. }
        { forward. Exists cs2. unfold con_val. entailer!. }
      }
      { Intros cs2. forward. Exists (y + 1) cs2. unfold con_val. entailer!. }
    }
    { forward. Exists cs1. unfold con_val. entailer!. }
  }
  Intros cs1. unfold con_val.
  forward. forward. forward.
  Exists cs1. unfold con_val, geo_val. entailer!.
Qed.
