(* Specifications of the functions of the unit patch/console_unit.c (include/boot_text_console.h and its three
   wrappers), under the unit's compspecs.  One specification per function serves both laws. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require LeanosConsole.units.Console.
Require Import LeanosConsole.console.code.
Require Import LeanosConsole.proof.Defs.
Require LeanosConsole.proof.ModelProof.

#[export] Instance CS : compspecs := LeanosConsole.units.Console.CS.
Definition Vprog : varspecs. mk_varspecs LeanosConsole.console.code.prog. Defined.

Definition t_geo := Tstruct _boot_text_geometry noattr.
Definition t_con := Tstruct _boot_text_console noattr.

Definition bytes (bs: list Z) : list val := map (fun b => Vint (Int.repr b)) bs.
Definition u16s (cs: list Z) : list val := map (fun v => Vint (Int.repr v)) cs.
Definition u16_ok (cs: list Z) : Prop := Forall (fun v => 0 <= v <= 65535) cs.
Definition bytes_ok (bs: list Z) : Prop := Forall (fun b => 0 <= b <= Byte.max_unsigned) bs.

(* struct boot_text_geometry: address, pitch, width, height, kind, bits *)
Definition geo_val (g: geo) : reptype t_geo :=
  (Vlong (Int64.repr (g_address g)), (Vint (Int.repr (g_pitch g)), (Vint (Int.repr (g_width g)),
   (Vint (Int.repr (g_height g)), (Vint (Int.repr (g_kind g)), Vint (Int.repr (g_bits g))))))).

(* struct boot_text_console: cells, stride, width, height, row, column, enabled, busy *)
Definition con_val (w: val) (stride width height row column en bu: Z) : reptype t_con :=
  (w, (Vint (Int.repr stride), (Vint (Int.repr width), (Vint (Int.repr height), (Vint (Int.repr row),
   (Vint (Int.repr column), (Vint (Int.repr en), Vint (Int.repr bu)))))))).

(* boot_text_disable's result on a console of unknown contents: only `enabled` is known. *)
Definition con_disabled : reptype t_con :=
  (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vint (Int.repr 0), Vundef))))))).

Definition boot_text_u32_spec :=
  DECLARE _boot_text_u32
  WITH sh: share, base: val, bs: list Z, k: Z
  PRE [ tptr tuchar ]
    PROP (readable_share sh; 0 <= k; k + 4 <= Zlength bs; bytes_ok bs)
    PARAMS (offset_val k base)
    SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes bs) base)
  POST [ tuint ]
    PROP ()
    RETURN (Vint (Int.repr (le32 bs k)))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes bs) base).

(* boot_text_parse on a buffer of exactly `available` bytes answers parse_model, and on acceptance writes
   exactly the accepted geometry. *)
Definition parse_pre_post (name: ident) :=
  DECLARE name
  WITH info: val, sh: share, bs: list Z, out: val
  PRE [ tptr tuchar, tuint, tptr t_geo ]
    PROP (readable_share sh; Zlength bs <= Int.max_unsigned; bytes_ok bs)
    PARAMS (info; Vint (Int.repr (Zlength bs)); out)
    SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes bs) info; data_at_ Tsh t_geo out)
  POST [ tint ]
    EX g: geo,
    PROP (geo_wf g; forall g', parse_model bs (Zlength bs) = Some g' -> g' = g)
    RETURN (Vint (Int.repr (parse_result bs (Zlength bs))))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes bs) info; data_at Tsh t_geo (geo_val g) out).

Definition boot_text_parse_spec := parse_pre_post _boot_text_parse.
Definition console_parse_spec := parse_pre_post _console_parse.

Definition boot_text_disable_spec :=
  DECLARE _boot_text_disable
  WITH c: val
  PRE [ tptr t_con ]
    PROP () PARAMS (c) SEP (data_at_ Tsh t_con c)
  POST [ tvoid ]
    PROP () RETURN () SEP (data_at Tsh t_con con_disabled c).

(* boot_text_enable on an accepted geometry and a window of exactly its surface: the console starts at the
   origin, enabled and not busy, with stride pitch / 2. *)
Definition enable_pre_post (name: ident) :=
  DECLARE name
  WITH c: val, gp: val, g: geo, w: val, sh: share, cs: list Z
  PRE [ tptr t_con, tptr t_geo, tptr tushort ]
    PROP (writable_share sh; geo_wf g; geo_valid g = true;
          Zlength cs = (g_height g * (g_pitch g / 2))%Z; u16_ok cs)
    PARAMS (c; gp; w)
    SEP (data_at_ Tsh t_con c; data_at Tsh t_geo (geo_val g) gp;
         data_at sh (tarray tushort ((g_height g * (g_pitch g / 2))%Z)) (u16s cs) w)
  POST [ tint ]
    EX cs': list Z,
    PROP (Zlength cs' = (g_height g * (g_pitch g / 2))%Z; u16_ok cs')
    RETURN (Vint (Int.repr 1))
    SEP (data_at Tsh t_con (con_val w (g_pitch g / 2) (g_width g) (g_height g) 0 0 1 0) c;
         data_at Tsh t_geo (geo_val g) gp;
         data_at sh (tarray tushort ((g_height g * (g_pitch g / 2))%Z)) (u16s cs') w).

Definition boot_text_enable_spec := enable_pre_post _boot_text_enable.
Definition console_enable_spec := enable_pre_post _console_enable.

(* boot_text_line: column 0 of the next row, scrolling on the last; enabled and busy unchanged. *)
Definition boot_text_line_spec :=
  DECLARE _boot_text_line
  WITH c: val, w: val, sh: share, stride: Z, width: Z, height: Z, row: Z, column: Z, en: Z, bu: Z, cs: list Z
  PRE [ tptr t_con ]
    PROP (writable_share sh; con_ok stride width height row column;
          0 <= en <= Byte.max_unsigned; 0 <= bu <= Byte.max_unsigned;
          Zlength cs = (height * stride)%Z; u16_ok cs)
    PARAMS (c)
    SEP (data_at Tsh t_con (con_val w stride width height row column en bu) c;
         data_at sh (tarray tushort ((height * stride)%Z)) (u16s cs) w)
  POST [ tvoid ]
    EX cs': list Z,
    PROP (Zlength cs' = (height * stride)%Z; u16_ok cs')
    RETURN ()
    SEP (data_at Tsh t_con
           (con_val w stride width height (if row + 1 <? height then row + 1 else height - 1) 0 en bu) c;
         data_at sh (tarray tushort ((height * stride)%Z)) (u16s cs') w).

(* boot_text_putc on an enabled console that is not busy: the cursor stays inside the surface; CR and LF move
   it; any other byte is displayed (as shown ch, attribute 7) in the cell just before the new cursor. *)
Definition putc_pre_post (name: ident) :=
  DECLARE name
  WITH c: val, w: val, sh: share, stride: Z, width: Z, height: Z, row: Z, column: Z, cs: list Z, ch: Z
  PRE [ tptr t_con, tuchar ]
    PROP (writable_share sh; con_ok stride width height row column;
          Zlength cs = (height * stride)%Z; u16_ok cs; 0 <= ch <= Byte.max_unsigned)
    PARAMS (c; Vint (Int.repr ch))
    SEP (data_at Tsh t_con (con_val w stride width height row column 1 0) c;
         data_at sh (tarray tushort ((height * stride)%Z)) (u16s cs) w)
  POST [ tvoid ]
    EX row': Z, EX column': Z, EX cs': list Z,
    PROP (con_ok stride width height row' column'; Zlength cs' = (height * stride)%Z; u16_ok cs';
          (ch = 13 -> row' = row /\ column' = 0)%Z;
          (ch = 10 -> row' = (if row + 1 <? height then row + 1 else height - 1) /\ column' = 0)%Z;
          (ch <> 13 -> ch <> 10 ->
            1 <= column' /\ Znth (row' * stride + column' - 1) cs' = 1792 + shown ch)%Z)
    RETURN ()
    SEP (data_at Tsh t_con (con_val w stride width height row' column' 1 0) c;
         data_at sh (tarray tushort ((height * stride)%Z)) (u16s cs') w).

Definition boot_text_putc_spec := putc_pre_post _boot_text_putc.
Definition console_putc_spec := putc_pre_post _console_putc.

Definition Gprog : funspecs :=
  [ModelProof.surface_spec; boot_text_u32_spec; boot_text_parse_spec; boot_text_disable_spec;
   boot_text_enable_spec; boot_text_line_spec; boot_text_putc_spec;
   console_parse_spec; console_enable_spec; console_putc_spec].
