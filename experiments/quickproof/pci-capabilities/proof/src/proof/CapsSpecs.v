(* Specifications of the functions of the unit patch/caps_unit.c (boot/pci-capabilities.h and its wrapper), under the
   unit's compspecs.  The read callback is specified by a protocol over an abstract device: `Dev ctx bdf h` is the
   device behind context ctx, serving bus/device/function bdf, after it has answered the reads h.  The protocol and
   the walker's specification are parameterized by Dev (a definition parameter: VST's WITH cannot range over mpred),
   and each law instantiates it with its own device. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require LeanosCaps.units.Caps.
Require Import LeanosCaps.caps.code.
Require Import LeanosCaps.proof.Defs.

#[export] Instance CS : compspecs := LeanosCaps.units.Caps.CS.
Definition Vprog : varspecs. mk_varspecs LeanosCaps.caps.code.prog. Defined.

Definition t_header := Tstruct _pci_enumeration_header noattr.
Definition t_cap := Tstruct _pci_capability_header noattr.
Definition t_snapshot := Tstruct _pci_capability_snapshot noattr.
Definition t_result := Tstruct _pci_capability_result noattr.
Definition t_read : type :=
  Tfunction ((tptr tvoid) :: tuchar :: tuchar :: tuchar :: tuchar :: (tptr tuint) :: nil) tint cc_default.

Definition u32_ok (x: Z) : Prop := 0 <= x <= Int.max_unsigned.
Definition u8_ok (x: Z) : Prop := 0 <= x <= Byte.max_unsigned.

(* struct pci_enumeration_header: bus, device, function, words[16]. *)
Definition header_val (bus dev fn: Z) (words: list Z) : reptype t_header :=
  (Vint (Int.repr bus), (Vint (Int.repr dev), (Vint (Int.repr fn), map (fun w => Vint (Int.repr w)) words))).

(* struct pci_capability_header: offset, raw. *)
Definition cap_val (c: Z * Z) : reptype t_cap := (Vint (Int.repr (fst c)), Vint (Int.repr (snd c))).

(* struct pci_capability_snapshot: count, headers[48]. *)
Definition snapshot_val (count: Z) (headers: list (reptype t_cap)) : reptype t_snapshot :=
  (Vint (Int.repr count), headers).

(* struct pci_capability_result: status, offset. *)
Definition result_val (st off: Z) : reptype t_result := (Vint (Int.repr st), Vint (Int.repr off)).

(* An object of type t at p, or nothing when p is NULL. *)
Definition maybe_at (sh: share) (t: type) (v: reptype t) (p: val) : mpred :=
  if Val.eq p nullval then emp else data_at sh t v p.

Definition bus_of (bdf: Z * Z * Z) : Z := fst (fst bdf).
Definition dev_of (bdf: Z * Z * Z) : Z := snd (fst bdf).
Definition fn_of (bdf: Z * Z * Z) : Z := snd bdf.

(* The read protocol of a device Dev: asked for a dword-aligned offset of conventional space of the function it
   serves, before its 53rd read, it answers success with any value, which it stores, or failure, which stores
   nothing, and records the answer. *)
Definition read_spec (Dev: val -> Z * Z * Z -> list answer -> mpred) : funspec :=
  WITH ctx: val, bdf: Z * Z * Z, h: list answer, off: Z, vp: val
  PRE [ tptr tvoid, tuchar, tuchar, tuchar, tuchar, tptr tuint ]
    PROP (0 <= off <= 252; Z.land off 3 = 0; u8_ok (bus_of bdf); u8_ok (dev_of bdf); u8_ok (fn_of bdf);
          Zlength h < 52)
    PARAMS (ctx; Vint (Int.repr (bus_of bdf)); Vint (Int.repr (dev_of bdf)); Vint (Int.repr (fn_of bdf));
            Vint (Int.repr off); vp)
    SEP (Dev ctx bdf h; data_at_ Tsh tuint vp)
  POST [ tint ]
    EX ok: bool, EX v: Z,
    PROP (u32_ok v)
    RETURN (Vint (Int.repr (if ok then 1 else 0)))
    SEP (Dev ctx bdf (h ++ [(off, ok, v)]);
         if ok then data_at Tsh tuint (Vint (Int.repr v)) vp else data_at_ Tsh tuint vp).

(* The callback argument: a function obeying the protocol, or NULL. *)
Definition maybe_read (Dev: val -> Z * Z * Z -> list answer -> mpred) (read: val) : mpred :=
  if Val.eq read nullval then emp else func_ptr' (read_spec Dev) read.

Definition b2z (b: bool) : Z := if b then 1 else 0.
Definition isnull (p: val) : bool := if Val.eq p nullval then true else false.

Definition finish_spec :=
  DECLARE _pci_capability_finish
  WITH result: val, rold: reptype t_result, st: Z, off: Z
  PRE [ tptr t_result, tint, tuchar ]
    PROP (0 <= st <= 6; u8_ok off; is_pointer_or_null result)
    PARAMS (result; Vint (Int.repr st); Vint (Int.repr off))
    SEP (maybe_at Tsh t_result rold result)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr st))
    SEP (maybe_at Tsh t_result (result_val st off) result).

(* pci_collect_capabilities.  The callback, the initial header, the snapshot and the result record may each be NULL;
   the snapshot and the result may hold anything.  It returns ARGUMENT, offset 0, without a read and with count 0
   when the callback, the header or the snapshot is NULL or args_ok fails; otherwise the device has answered exactly
   the reads h of a walk with outcome (st, off, caps): the status and offset are the outcome's, and the snapshot
   publishes count |caps| with caps first (and anything after them). *)
Definition collect_pre_post (Dev: val -> Z * Z * Z -> list answer -> mpred) (name: ident) :=
  DECLARE name
  WITH read: val, ctx: val, initial: val, ish: share, bus: Z, dev: Z, fn: Z, words: list Z,
       snapshot: val, sold: reptype t_snapshot, result: val, rold: reptype t_result
  PRE [ tptr t_read, tptr tvoid, tptr t_header, tptr t_snapshot, tptr t_result ]
    PROP (readable_share ish; u8_ok bus; u8_ok dev; u8_ok fn; Zlength words = 16; Forall u32_ok words;
          is_pointer_or_null read; is_pointer_or_null initial; is_pointer_or_null snapshot;
          is_pointer_or_null result)
    PARAMS (read; ctx; initial; snapshot; result)
    SEP (maybe_read Dev read; Dev ctx (bus, dev, fn) nil;
         maybe_at ish t_header (header_val bus dev fn words) initial;
         maybe_at Tsh t_snapshot sold snapshot; maybe_at Tsh t_result rold result)
  POST [ tint ]
    EX h: list answer, EX st: Z, EX off: Z, EX caps: list (Z * Z), EX rest: list (reptype t_cap),
    PROP ((Zlength caps + Zlength rest = 48)%Z;
          if (isnull read || isnull initial || isnull snapshot || negb (args_ok dev fn words))%bool
          then st = S_ARGUMENT /\ off = 0 /\ h = nil /\ caps = nil
          else walk words h = Some (st, off, caps))
    RETURN (Vint (Int.repr st))
    SEP (maybe_read Dev read; Dev ctx (bus, dev, fn) h;
         maybe_at ish t_header (header_val bus dev fn words) initial;
         maybe_at Tsh t_snapshot (snapshot_val (Zlength caps) (map cap_val caps ++ rest)) snapshot;
         maybe_at Tsh t_result (result_val st off) result).

Definition collect_spec Dev := collect_pre_post Dev _pci_collect_capabilities.
Definition caps_collect_spec Dev := collect_pre_post Dev _caps_collect.

Definition Gprog (Dev: val -> Z * Z * Z -> list answer -> mpred) : funspecs :=
  [finish_spec; collect_spec Dev; caps_collect_spec Dev].
