(* Specifications of the functions of the unit patch/enum_unit.c (boot/pci-enumeration.h and its wrapper), under the
   unit's compspecs.  The read callback is specified by a protocol over an abstract device: `Dev ctx h` is the device
   behind context ctx after it has answered the reads h.  The protocol and the scan's specification are
   parameterized by Dev (a definition parameter: VST's WITH cannot range over mpred), and the law instantiates it
   with its own device. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require LeanosEnum.units.Enum.
Require Import LeanosEnum.enum.code.
Require Import LeanosEnum.proof.Defs.

#[export] Instance CS : compspecs := LeanosEnum.units.Enum.CS.
Definition Vprog : varspecs. mk_varspecs LeanosEnum.enum.code.prog. Defined.

Definition t_header := Tstruct _pci_enumeration_header noattr.
Definition t_snapshot := Tstruct _pci_enumeration_snapshot noattr.
Definition t_result := Tstruct _pci_enumeration_result noattr.
Definition t_read : type :=
  Tfunction ((tptr tvoid) :: tuchar :: tuchar :: tuchar :: tuchar :: (tptr tuint) :: nil) tint cc_default.

Definition u32_ok (x: Z) : Prop := 0 <= x <= Int.max_unsigned.
Definition u8_ok (x: Z) : Prop := 0 <= x <= Byte.max_unsigned.

(* struct pci_enumeration_header: bus, device, function, words[16], of a header found (index, dwords). *)
Definition header_val (f: found) : reptype t_header :=
  (Vint (Int.repr (bus_of (fst f))), (Vint (Int.repr (dev_of (fst f))), (Vint (Int.repr (fn_of (fst f))),
   map (fun w => Vint (Int.repr w)) (snd f)))).

(* struct pci_enumeration_snapshot: count, headers[16]. *)
Definition snapshot_val (count: Z) (headers: list (reptype t_header)) : reptype t_snapshot :=
  (Vint (Int.repr count), headers).

(* struct pci_enumeration_result: status, bus, device, function, offset. *)
Definition result_val (st b d f off: Z) : reptype t_result :=
  (Vint (Int.repr st), (Vint (Int.repr b), (Vint (Int.repr d), (Vint (Int.repr f), Vint (Int.repr off))))).

(* The result naming the function of index i at offset off. *)
Definition result_at (st i off: Z) : reptype t_result := result_val st (bus_of i) (dev_of i) (fn_of i) off.

(* An object of type t at p, or nothing when p is NULL. *)
Definition maybe_at (sh: share) (t: type) (v: reptype t) (p: val) : mpred :=
  if Val.eq p nullval then emp else data_at sh t v p.

(* The read protocol of a device Dev: asked for the read the scan makes next after the answers h, it answers
   success with any value, which it stores, or failure, which stores nothing, and records the answer. *)
Definition read_spec (Dev: val -> list answer -> mpred) : funspec :=
  WITH ctx: val, h: list answer, i: Z, off: Z, vp: val
  PRE [ tptr tvoid, tuchar, tuchar, tuchar, tuchar, tptr tuint ]
    PROP (next_read h = Some (i, off))
    PARAMS (ctx; Vint (Int.repr (bus_of i)); Vint (Int.repr (dev_of i)); Vint (Int.repr (fn_of i));
            Vint (Int.repr off); vp)
    SEP (Dev ctx h; data_at_ Tsh tuint vp)
  POST [ tint ]
    EX ok: bool, EX v: Z,
    PROP (u32_ok v)
    RETURN (Vint (Int.repr (if ok then 1 else 0)))
    SEP (Dev ctx (h ++ [(i, off, ok, v)]);
         if ok then data_at Tsh tuint (Vint (Int.repr v)) vp else data_at_ Tsh tuint vp).

(* The callback argument: a function obeying the protocol, or NULL. *)
Definition maybe_read (Dev: val -> list answer -> mpred) (read: val) : mpred :=
  if Val.eq read nullval then emp else func_ptr' (read_spec Dev) read.

Definition isnull (p: val) : bool := if Val.eq p nullval then true else false.

Definition finish_spec :=
  DECLARE _pci_enumeration_finish
  WITH result: val, rold: reptype t_result, st: Z, b: Z, d: Z, f: Z, off: Z
  PRE [ tptr t_result, tint, tuchar, tuchar, tuchar, tuchar ]
    PROP (0 <= st <= 3; u8_ok b; u8_ok d; u8_ok f; u8_ok off; is_pointer_or_null result)
    PARAMS (result; Vint (Int.repr st); Vint (Int.repr b); Vint (Int.repr d); Vint (Int.repr f);
            Vint (Int.repr off))
    SEP (maybe_at Tsh t_result rold result)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr st))
    SEP (maybe_at Tsh t_result (result_val st b d f off) result).

(* pci_enumerate_segment.  The callback, the snapshot and the result record may each be NULL; the snapshot and the
   result may hold anything.  It returns INVALID_ARGUMENT, location 0, without a read and with count 0 when the
   callback or the snapshot is NULL; otherwise the device has answered exactly the reads h of a scan with outcome
   (st, i, off, pub): the status and location are the outcome's, and the snapshot publishes count |pub| with pub
   first (and anything after it). *)
Definition enum_pre_post (Dev: val -> list answer -> mpred) (name: ident) :=
  DECLARE name
  WITH read: val, ctx: val, snapshot: val, sold: reptype t_snapshot, result: val, rold: reptype t_result
  PRE [ tptr t_read, tptr tvoid, tptr t_snapshot, tptr t_result ]
    PROP (is_pointer_or_null read; is_pointer_or_null snapshot; is_pointer_or_null result)
    PARAMS (read; ctx; snapshot; result)
    SEP (maybe_read Dev read; Dev ctx nil; maybe_at Tsh t_snapshot sold snapshot; maybe_at Tsh t_result rold result)
  POST [ tint ]
    EX h: list answer, EX st: Z, EX i: Z, EX off: Z, EX pub: list found, EX rest: list (reptype t_header),
    PROP ((Zlength pub + Zlength rest = CAPACITY)%Z;
          if (isnull read || isnull snapshot)%bool
          then st = S_INVALID_ARGUMENT /\ i = 0 /\ off = 0 /\ h = nil /\ pub = nil
          else scan h = Some (st, i, off, pub))
    RETURN (Vint (Int.repr st))
    SEP (maybe_read Dev read; Dev ctx h;
         maybe_at Tsh t_snapshot (snapshot_val (Zlength pub) (map header_val pub ++ rest)) snapshot;
         maybe_at Tsh t_result (result_at st i off) result).

Definition enum_spec Dev := enum_pre_post Dev _pci_enumerate_segment.
Definition enum_scan_spec Dev := enum_pre_post Dev _enum_scan.

Definition Gprog (Dev: val -> list answer -> mpred) : funspecs :=
  [finish_spec; enum_spec Dev; enum_scan_spec Dev].
