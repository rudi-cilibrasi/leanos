(* Law capabilities_adversarial: the law's device (Dev_adv, the harness's struct device holding the log of the
   answered reads) and the specifications of the harness's functions, under the compspecs of the law's whole program
   (AdvProg.LCS). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosCaps.harness.capabilities_adversarial.code.
Require Import LeanosCaps.proof.Defs.
Require LeanosCaps.proof.CapsSpecs.
Require Import LeanosCaps.proof.AdvProg.
Require Import LeanosCaps.proof.AdvWalk LeanosCaps.proof.AdvFacts.
Local Open Scope Z_scope.

#[export] Existing Instance AdvProg.LCS.

Definition t_device := Tstruct _device noattr.
Definition t_header := Tstruct _pci_enumeration_header noattr.

(* The log h in the device's arrays: entry i of offsets and ok holds the i-th answer's offset and success, entry i
   of values its value when it succeeded.  Entries past the log, and the value slot of a failed read, hold
   anything. *)
Definition log_at (h: list answer) (offs oks vals: list val) : Prop :=
  Zlength offs = 52 /\ Zlength oks = 52 /\ Zlength vals = 52 /\
  forall i, 0 <= i < Zlength h ->
    Znth i offs = Vint (Int.repr (aoff (Znth i h))) /\
    Znth i oks = Vint (Int.repr (CapsSpecs.b2z (aok (Znth i h)))) /\
    (aok (Znth i h) = true -> Znth i vals = Vint (Int.repr (aval (Znth i h)))).

(* Every answer is at an offset of conventional space, with a 32-bit value. *)
Definition answers_ok (h: list answer) : Prop :=
  Forall (fun a => 0 <= aoff a <= 252 /\ CapsSpecs.u32_ok (aval a)) h.

(* struct device: bus, device, function, reads, offsets[52], ok[52], values[52]. *)
Definition dev_val (bdf: Z * Z * Z) (n: Z) (offs oks vals: list val) : reptype t_device :=
  (Vint (Int.repr (CapsSpecs.bus_of bdf)), (Vint (Int.repr (CapsSpecs.dev_of bdf)),
   (Vint (Int.repr (CapsSpecs.fn_of bdf)), (Vint (Int.repr n), (offs, (oks, vals)))))).

(* The law's device: the harness's struct device at ctx, serving bdf, whose log is h (reads = |h|). *)
Definition Dev_adv (ctx: val) (bdf: Z * Z * Z) (h: list answer) : mpred :=
  EX offs: list val, EX oks: list val, EX vals: list val,
    !! (Zlength h <= 52 /\ answers_ok h /\ log_at h offs oks vals) &&
    data_at Tsh t_device (dev_val bdf (Zlength h) offs oks vals) ctx.

(* struct pci_enumeration_header, under the law's compspecs (CapsSpecs.header_val). *)
Definition hdr_val (bus dev fn: Z) (words: list Z) : reptype t_header :=
  (Vint (Int.repr bus), (Vint (Int.repr dev), (Vint (Int.repr fn), map (fun w => Vint (Int.repr w)) words))).

(* named_pointer(d, initial): the list head after the four header reads, else the last read's next pointer. *)
Definition named_pointer_spec :=
  DECLARE _named_pointer
  WITH d: val, bdf: Z * Z * Z, h: list answer, ini: val, sh: share, bus: Z, dev: Z, fn: Z, words: list Z
  PRE [ tptr t_device, tptr t_header ]
    PROP (readable_share sh; 1 <= Zlength h; Zlength words = 16; Forall CapsSpecs.u32_ok words;
          Zlength h <> 4 -> aok (Znth (Zlength h - 1) h) = true)
    PARAMS (d; ini)
    SEP (Dev_adv d bdf h; data_at sh t_header (hdr_val bus dev fn words) ini)
  POST [ tuint ]
    PROP ()
    RETURN (Vint (Int.repr (named words h)))
    SEP (Dev_adv d bdf h; data_at sh t_header (hdr_val bus dev fn words) ini).

(* device_read obeys the read protocol of Dev_adv. *)
Definition device_read_spec : ident * funspec := (_device_read, CapsSpecs.read_spec Dev_adv).

Definition Vh : varspecs := nil.
(* The context of device_read and named_pointer: the environment functions device_read calls. *)
Definition Gh : funspecs := [gp_assert_spec; nondet_u8_spec; nondet_u32_spec].
