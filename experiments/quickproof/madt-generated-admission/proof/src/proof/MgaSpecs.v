(* Specifications of the four functions main calls (patch/madt_admission_unit.c: madt_envelope, madt_entries,
   madt_result, madt_admission) and of the three Lean exports they call, under the unit's compspecs.

   The exports are specified by a protocol over an abstract oracle: `Ora gv x h` is the Lean behind main's
   inputs x after it has answered the calls h, in the global environment gv (the exports take no context, so an
   implementation may keep its state in globals, as the law's does in `law`).  Each export is asked only for the
   function's next call (Defs.next_call) and records its answer.  The protocol and the specifications are
   parameterized by Ora (a definition parameter: VST's WITH cannot range over mpred), and the law instantiates
   it with its own oracle.

   This file is the interface the law depends on.  The specifications of the header's four functions, which
   the wrappers forward to, and Gprog are in InternalSpecs.v, which the body proofs may revise without touching
   this file. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require LeanosMadtAdmission.units.MadtAdmission.
Require Import LeanosMadtAdmission.madt_admission.code.
Require Import LeanosMadtAdmission.proof.Defs.

#[export] Instance CS : compspecs := LeanosMadtAdmission.units.MadtAdmission.CS.
Definition Vprog : varspecs. mk_varspecs LeanosMadtAdmission.madt_admission.code.prog. Defined.

Definition u64_ok (v: Z) : Prop := 0 <= v <= Int64.max_unsigned.
Definition u32_ok (v: Z) : Prop := 0 <= v <= Int.max_unsigned.
Definition byte_ok (v: Z) : Prop := 0 <= v <= Byte.max_unsigned.

Definition vl (v: Z) : val := Vlong (Int64.repr v).
Definition vi (v: Z) : val := Vint (Int.repr v).

(* The copy: bytes as unsigned chars (as nondet_bytes leaves them). *)
Definition bytes_val (bs: list Z) : list val := map (fun b => Vint (Int.repr b)) bs.

(* The inputs main may choose: a copy of exactly its 32-bit length holding bytes, a 32-bit executing ID, ten
   64-bit result arguments, a 32-bit prior APIC ID. *)
Definition inputs_ok (x: inputs) : Prop :=
  u32_ok (i_length x) /\ Zlength (i_bytes x) = i_length x /\ Forall byte_ok (i_bytes x) /\
  u32_ok (i_executing x) /\ Zlength (i_args x) = 10 /\ Forall u64_ok (i_args x) /\ u32_ok (i_prior x).

(* ---------------------------------------------------------------------- *)
(* The oracle and the protocols of the three exports.                    *)
(* ---------------------------------------------------------------------- *)

Definition ORA : Type := globals -> inputs -> list answer -> mpred.

(* The envelope step: asked for the function's next call after the answers h, it answers any 64-bit value and
   records the answer. *)
Definition envelope_step_spec (Ora: ORA) :=
  DECLARE _leanos_boot_machine_madt_envelope_byte_step_query
  WITH gv: globals, x: inputs, h: list answer, st: list Z, len: Z, off: Z, byte: Z, term: Z, word: Z
  PRE [ tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong ]
    PROP (next_call x h = Some (EnvelopeStep st len off byte term word))
    PARAMS (vl (Znth 0 st); vl (Znth 1 st); vl (Znth 2 st); vl len; vl off; vl byte; vl term; vl word)
    GLOBALS (gv)
    SEP (Ora gv x h)
  POST [ tulong ]
    EX v: Z,
    PROP (u64_ok v)
    RETURN (vl v)
    SEP (Ora gv x (h ++ [(EnvelopeStep st len off byte term word, v)])).

(* The entry-stream step, likewise. *)
Definition entry_step_spec (Ora: ORA) :=
  DECLARE _leanos_boot_machine_madt_entry_stream_byte_step_query
  WITH gv: globals, x: inputs, h: list answer, st: list Z, len: Z, ex: Z, off: Z, byte: Z, word: Z
  PRE [ tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong,
        tulong, tulong, tulong, tulong, tulong ]
    PROP (next_call x h = Some (EntryStep st len ex off byte word))
    PARAMS (vl (Znth 0 st); vl (Znth 1 st); vl (Znth 2 st); vl (Znth 3 st); vl (Znth 4 st);
            vl (Znth 5 st); vl (Znth 6 st); vl (Znth 7 st); vl (Znth 8 st); vl (Znth 9 st);
            vl (Znth 10 st); vl (Znth 11 st); vl len; vl ex; vl off; vl byte; vl word)
    GLOBALS (gv)
    SEP (Ora gv x h)
  POST [ tulong ]
    EX v: Z,
    PROP (u64_ok v)
    RETURN (vl v)
    SEP (Ora gv x (h ++ [(EntryStep st len ex off byte word, v)])).

(* The admission result, likewise. *)
Definition result_query_spec (Ora: ORA) :=
  DECLARE _leanos_boot_machine_topology_admission_result_query
  WITH gv: globals, x: inputs, h: list answer, args: list Z, word: Z
  PRE [ tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong ]
    PROP (next_call x h = Some (ResultQuery args word))
    PARAMS (vl (Znth 0 args); vl (Znth 1 args); vl (Znth 2 args); vl (Znth 3 args); vl (Znth 4 args);
            vl (Znth 5 args); vl (Znth 6 args); vl (Znth 7 args); vl (Znth 8 args); vl (Znth 9 args);
            vl word)
    GLOBALS (gv)
    SEP (Ora gv x h)
  POST [ tulong ]
    EX v: Z,
    PROP (u64_ok v)
    RETURN (vl v)
    SEP (Ora gv x (h ++ [(ResultQuery args word, v)])).

(* ---------------------------------------------------------------------- *)
(* The four functions main calls.                                        *)
(* ---------------------------------------------------------------------- *)

(* Common to the four: main's inputs x, with i_call x the function; the oracle before any call; the copy
   (readable, any share) of exactly i_length x bytes at bp; the APIC ID record (writable) at rp, holding the
   prior ID, separate from the copy.  Each returns after the Lean answered exactly the calls h of a run whose
   outcome is (st, w): it returns st and leaves the copy as it was; except for the envelope, which has no
   record, w is Some id exactly on OK, id is 32-bit, and the record then holds id, else the prior ID. *)

(* madt_envelope(bytes, length). *)
Definition envelope_spec (Ora: ORA) :=
  DECLARE _madt_envelope
  WITH gv: globals, x: inputs, bp: val, sh: share
  PRE [ tptr tuchar, tuint ]
    PROP (i_call x = FEnvelope; inputs_ok x; readable_share sh)
    PARAMS (bp; vi (i_length x))
    GLOBALS (gv)
    SEP (Ora gv x nil; data_at sh (tarray tuchar (i_length x)) (bytes_val (i_bytes x)) bp)
  POST [ tint ]
    EX h: list answer, EX st: Z,
    PROP (returns x h = Some (st, None))
    RETURN (vi st)
    SEP (Ora gv x h; data_at sh (tarray tuchar (i_length x)) (bytes_val (i_bytes x)) bp).

(* madt_entries(bytes, length, executing_apic_id, admitted_apic_id). *)
Definition entries_spec (Ora: ORA) :=
  DECLARE _madt_entries
  WITH gv: globals, x: inputs, bp: val, sh: share, rp: val, rsh: share
  PRE [ tptr tuchar, tuint, tuint, tptr tuint ]
    PROP (i_call x = FEntries; inputs_ok x; readable_share sh; writable_share rsh)
    PARAMS (bp; vi (i_length x); vi (i_executing x); rp)
    GLOBALS (gv)
    SEP (Ora gv x nil; data_at sh (tarray tuchar (i_length x)) (bytes_val (i_bytes x)) bp;
         data_at rsh tuint (vi (i_prior x)) rp)
  POST [ tint ]
    EX h: list answer, EX st: Z, EX id: Z,
    PROP (returns x h = Some (st, if st =? S_OK then Some id else None); u32_ok id)
    RETURN (vi st)
    SEP (Ora gv x h; data_at sh (tarray tuchar (i_length x)) (bytes_val (i_bytes x)) bp;
         data_at rsh tuint (vi (if st =? S_OK then id else i_prior x)) rp).

(* madt_result(a0, ..., a9, published_apic_id): the arguments are i_args x; no copy. *)
Definition result_spec (Ora: ORA) :=
  DECLARE _madt_result
  WITH gv: globals, x: inputs, rp: val, rsh: share
  PRE [ tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tptr tuint ]
    PROP (i_call x = FResult; inputs_ok x; writable_share rsh)
    PARAMS (vl (Znth 0 (i_args x)); vl (Znth 1 (i_args x)); vl (Znth 2 (i_args x)); vl (Znth 3 (i_args x));
            vl (Znth 4 (i_args x)); vl (Znth 5 (i_args x)); vl (Znth 6 (i_args x)); vl (Znth 7 (i_args x));
            vl (Znth 8 (i_args x)); vl (Znth 9 (i_args x)); rp)
    GLOBALS (gv)
    SEP (Ora gv x nil; data_at rsh tuint (vi (i_prior x)) rp)
  POST [ tint ]
    EX h: list answer, EX st: Z, EX id: Z,
    PROP (returns x h = Some (st, if st =? S_OK then Some id else None); u32_ok id)
    RETURN (vi st)
    SEP (Ora gv x h; data_at rsh tuint (vi (if st =? S_OK then id else i_prior x)) rp).

(* madt_admission(bytes, length, executing_apic_id, a0, ..., a4, published_apic_id), and the header's
   madt_generated_admission (InternalSpecs.v), which it forwards to. *)
Definition admission_pre_post (Ora: ORA) (name: ident) :=
  DECLARE name
  WITH gv: globals, x: inputs, bp: val, sh: share, rp: val, rsh: share
  PRE [ tptr tuchar, tuint, tuint, tulong, tulong, tulong, tulong, tulong, tptr tuint ]
    PROP (i_call x = FAdmission; inputs_ok x; readable_share sh; writable_share rsh)
    PARAMS (bp; vi (i_length x); vi (i_executing x); vl (Znth 0 (i_args x)); vl (Znth 1 (i_args x));
            vl (Znth 2 (i_args x)); vl (Znth 3 (i_args x)); vl (Znth 4 (i_args x)); rp)
    GLOBALS (gv)
    SEP (Ora gv x nil; data_at sh (tarray tuchar (i_length x)) (bytes_val (i_bytes x)) bp;
         data_at rsh tuint (vi (i_prior x)) rp)
  POST [ tint ]
    EX h: list answer, EX st: Z, EX id: Z,
    PROP (returns x h = Some (st, if st =? S_OK then Some id else None); u32_ok id)
    RETURN (vi st)
    SEP (Ora gv x h; data_at sh (tarray tuchar (i_length x)) (bytes_val (i_bytes x)) bp;
         data_at rsh tuint (vi (if st =? S_OK then id else i_prior x)) rp).

Definition admission_spec Ora := admission_pre_post Ora _madt_admission.
