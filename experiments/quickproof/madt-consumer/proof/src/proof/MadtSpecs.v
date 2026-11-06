(* Specifications of the functions of the unit patch/madt_unit.c (include/qotom_bsp_consumer.h and its wrapper), and
   of the three Lean exports it calls, under the unit's compspecs.  The exports are specified by a protocol over an
   abstract oracle: `Ora gv x h` is the Lean behind the consumer's inputs x after it has answered the calls h, in the
   global environment gv (the exports take no context, so an implementation may keep its state in globals).  The
   protocol and the consumer's specification are parameterized by Ora (a definition parameter: VST's WITH cannot
   range over mpred), and the law instantiates it with its own oracle. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require LeanosMadt.units.Madt.
Require Import LeanosMadt.madt.code.
Require Import LeanosMadt.proof.Defs.

#[export] Instance CS : compspecs := LeanosMadt.units.Madt.CS.
Definition Vprog : varspecs. mk_varspecs LeanosMadt.madt.code.prog. Defined.

Definition t_obs := Tstruct _qotom_bsp_observation noattr.
Definition t_result := Tstruct _qotom_bsp_result noattr.

Definition u64_ok (x: Z) : Prop := 0 <= x <= Int64.max_unsigned.
Definition byte_ok (x: Z) : Prop := 0 <= x <= Byte.max_unsigned.
Definition obs_ok (ob: observation) : Prop :=
  u64_ok (o_executing ob) /\ u64_ok (o_cpuid_edx ob) /\ u64_ok (o_available ob) /\ u64_ok (o_apic_base ob) /\
  u64_ok (o_sample_id ob) /\ u64_ok (o_routing ob).

Definition vl (x: Z) : val := Vlong (Int64.repr x).

(* struct qotom_bsp_observation *)
Definition obs_val (ob: observation) : reptype t_obs :=
  (vl (o_executing ob), (vl (o_cpuid_edx ob), (vl (o_available ob), (vl (o_apic_base ob),
   (vl (o_sample_id ob), vl (o_routing ob)))))).

(* struct qotom_bsp_result: status, detail, offset, apic_id, processor_count, apic_base *)
Definition result_val (o: outcome) : reptype t_result :=
  let '(st, d, off, a, c, b) := o in (vl st, (vl d, (vl off, (vl a, (vl c, vl b))))).

Definition status_of (o: outcome) : Z := let '(st, _, _, _, _, _) := o in st.

(* The span: bytes as unsigned chars. *)
Definition bytes_val (bytes: list Z) : list val := map (fun b => Vint (Int.repr b)) bytes.

(* An object of type t at p, or nothing when p is NULL. *)
Definition maybe_at (sh: share) (t: type) (v: reptype t) (p: val) : mpred :=
  if Val.eq p nullval then emp else data_at sh t v p.

Definition isnull (p: val) : bool := if Val.eq p nullval then true else false.

Definition ORA : Type := globals -> inputs -> list answer -> mpred.

(* The stream step: asked for the consumer's next call after the answers h, it answers any 64-bit value and records
   the answer. *)
Definition step_spec (Ora: ORA) :=
  DECLARE _leanos_qotom_madt_stream_byte_step_query
  WITH gv: globals, x: inputs, h: list answer, state: list Z, tl: Z, ex: Z, off: Z, byte: Z, word: Z
  PRE [ tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong,
        tulong, tulong, tulong, tulong, tulong ]
    PROP (next_call x h = Some (Step state tl ex off byte word))
    PARAMS (vl (Znth 0 state); vl (Znth 1 state); vl (Znth 2 state); vl (Znth 3 state); vl (Znth 4 state);
            vl (Znth 5 state); vl (Znth 6 state); vl (Znth 7 state); vl (Znth 8 state); vl (Znth 9 state);
            vl (Znth 10 state); vl (Znth 11 state); vl tl; vl ex; vl off; vl byte; vl word)
    GLOBALS (gv)
    SEP (Ora gv x h)
  POST [ tulong ]
    EX v: Z,
    PROP (u64_ok v)
    RETURN (vl v)
    SEP (Ora gv x (h ++ [(Step state tl ex off byte word, v)])).

(* The NMI policy, likewise. *)
Definition nmi_spec (Ora: ORA) :=
  DECLARE _leanos_qotom_madt_nmi_policy_query
  WITH gv: globals, x: inputs, h: list answer, count: Z, nmi: list Z, routing: Z, word: Z
  PRE [ tulong, tulong, tulong, tulong, tulong, tulong, tulong ]
    PROP (next_call x h = Some (Nmi count nmi routing word))
    PARAMS (vl count; vl (Znth 0 nmi); vl (Znth 1 nmi); vl (Znth 2 nmi); vl (Znth 3 nmi); vl routing; vl word)
    GLOBALS (gv)
    SEP (Ora gv x h)
  POST [ tulong ]
    EX v: Z,
    PROP (u64_ok v)
    RETURN (vl v)
    SEP (Ora gv x (h ++ [(Nmi count nmi routing word, v)])).

(* The finish, likewise. *)
Definition finish_spec (Ora: ORA) :=
  DECLARE _leanos_qotom_madt_stream_finish_query
  WITH gv: globals, x: inputs, h: list answer, st: Z, er: Z, state: list Z, tl: Z, ex: Z, edx: Z, av: Z, ab: Z,
       sid: Z, word: Z
  PRE [ tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong,
        tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong ]
    PROP (next_call x h = Some (Finish st er state tl ex edx av ab sid word))
    PARAMS (vl st; vl er; vl (Znth 0 state); vl (Znth 1 state); vl (Znth 2 state); vl (Znth 3 state);
            vl (Znth 4 state); vl (Znth 5 state); vl (Znth 6 state); vl (Znth 7 state); vl (Znth 8 state);
            vl (Znth 9 state); vl (Znth 10 state); vl (Znth 11 state); vl tl; vl ex; vl edx; vl av; vl ab;
            vl sid; vl word)
    GLOBALS (gv)
    SEP (Ora gv x h)
  POST [ tulong ]
    EX v: Z,
    PROP (u64_ok v)
    RETURN (vl v)
    SEP (Ora gv x (h ++ [(Finish st er state tl ex edx av ab sid word, v)])).

Definition publish_spec :=
  DECLARE _qotom_bsp_publish
  WITH out: val, rold: reptype t_result, o: outcome
  PRE [ tptr t_result, tulong, tulong, tulong, tulong, tulong, tulong ]
    PROP (let '(st, d, off, a, c, b) := o in
          u64_ok st /\ u64_ok d /\ u64_ok off /\ u64_ok a /\ u64_ok c /\ u64_ok b)
    PARAMS (out; vl (let '(st, _, _, _, _, _) := o in st); vl (let '(_, d, _, _, _, _) := o in d);
            vl (let '(_, _, off, _, _, _) := o in off); vl (let '(_, _, _, a, _, _) := o in a);
            vl (let '(_, _, _, _, c, _) := o in c); vl (let '(_, _, _, _, _, b) := o in b))
    SEP (data_at Tsh t_result rold out)
  POST [ tulong ]
    PROP ()
    RETURN (vl (status_of o))
    SEP (data_at Tsh t_result (result_val o) out).

(* qotom_bind_validated_madt_entries.  The span, the observation and the result record may each be NULL; the result
   may hold anything.  The span is `bytes` (at least one byte, so that its pointer is valid), exactly `length` bytes
   long when the consumer accepts the length.  With no result record it returns 1, writing nothing; with an absent
   span or observation or a length outside 1..65536-44 it publishes the input-bounds rejection, calling nothing,
   and is not handed the oracle; otherwise the Lean has answered exactly the calls h of a run with outcome o, which
   it publishes and whose status it returns. *)
Definition invalid_call (entries observation out: val) (length: Z) : bool :=
  (isnull out || isnull entries || isnull observation || negb (length_ok length))%bool.

Definition bind_pre_post (Ora: ORA) (name: ident) :=
  DECLARE name
  WITH gv: globals, entries: val, esh: share, bytes: list Z, length: Z, observation: val, osh: share,
       ob: observation, out: val, rold: reptype t_result
  PRE [ tptr tuchar, tulong, tptr t_obs, tptr t_result ]
    PROP (readable_share esh; readable_share osh; u64_ok length; 0 < Zlength bytes;
          length_ok length = true -> Zlength bytes = length; Forall byte_ok bytes; obs_ok ob;
          is_pointer_or_null entries; is_pointer_or_null observation; is_pointer_or_null out)
    PARAMS (entries; vl length; observation; out)
    GLOBALS (gv)
    SEP (if invalid_call entries observation out length then emp else Ora gv (bytes, ob) nil;
         maybe_at esh (tarray tuchar (Zlength bytes)) (bytes_val bytes) entries;
         maybe_at osh t_obs (obs_val ob) observation;
         maybe_at Tsh t_result rold out)
  POST [ tulong ]
    EX h: list answer, EX o: outcome,
    PROP (if invalid_call entries observation out length
          then h = nil /\ o = reject 1 0 44
          else consume (bytes, ob) h = Some o)
    RETURN (vl (status_of o))
    SEP (if invalid_call entries observation out length then emp else Ora gv (bytes, ob) h;
         maybe_at esh (tarray tuchar (Zlength bytes)) (bytes_val bytes) entries;
         maybe_at osh t_obs (obs_val ob) observation;
         maybe_at Tsh t_result (result_val o) out).

Definition bind_spec Ora := bind_pre_post Ora _qotom_bind_validated_madt_entries.
Definition madt_bind_spec Ora := bind_pre_post Ora _madt_bind.

Definition Gprog (Ora: ORA) : funspecs :=
  [step_spec Ora; nmi_spec Ora; finish_spec Ora; publish_spec; bind_spec Ora; madt_bind_spec Ora].
