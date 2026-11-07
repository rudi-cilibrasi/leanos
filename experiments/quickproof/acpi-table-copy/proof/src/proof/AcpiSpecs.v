(* Specifications of the functions of the unit patch/acpi_unit.c (include/acpi_table_copy.h and its wrapper), of
   the two Lean exports it calls and of the physical copy callback it is given, under the unit's compspecs.

   The callees are specified by a protocol over an abstract oracle: `Ora gv ctx pl x h` is the firmware and the
   Lean behind the pipeline's inputs x after they have answered the calls h, for the copy's context ctx and the
   storage's byte objects pl, in the global environment gv (the exports take no context, so an implementation
   may keep its state in globals).  Each callee is asked only for the pipeline's next call (Defs.next_call) and
   records its answer.  The protocol and the specifications are parameterized by Ora (a definition parameter:
   VST's WITH cannot range over mpred), and the law instantiates it with its own oracle.

   This file is the interface the law depends on: the oracle, the three callee specifications (copy_spec,
   stream_spec, sequence_spec) and pipeline_spec.  The specifications of the internal functions and Gprog are in
   InternalSpecs.v, which the body proofs may revise without touching this file. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require LeanosAcpi.units.Acpi.
Require Import LeanosAcpi.acpi.code.
Require Import LeanosAcpi.proof.Defs.

#[export] Instance CS : compspecs := LeanosAcpi.units.Acpi.CS.
Definition Vprog : varspecs. mk_varspecs LeanosAcpi.acpi.code.prog. Defined.

Definition t_sdt := Tstruct _copied_acpi_sdt noattr.
Definition t_entries := Tstruct _acpi_root_entries noattr.
Definition t_storage := Tstruct _acpi_table_copy_storage noattr.
Definition t_result := Tstruct _acpi_table_copy_result noattr.
(* acpi_physical_copy *)
Definition t_copy : type :=
  Tfunction ((tptr tvoid) :: tulong :: (tptr tuchar) :: tuint :: nil) tint cc_default.

(* The values of struct copied_acpi_sdt (physical_address, bytes, length, next_copy_offset) and of struct
   acpi_root_entries (bytes, count, width): their reptypes, written out.  The specifications use these types,
   not reptype t_sdt: Coq's unifier takes about 25 s to accept a list (reptype t_sdt) where data_at expects a
   reptype (tarray t_sdt n), and no time for a list sdt_rep. *)
Notation sdt_rep := (val * (val * (val * val)))%type.
Notation entries_rep := (val * (val * val))%type.

(* sizeof(struct copied_acpi_sdt): &copies[i] is copies + 24 i. *)
Definition SDT_BYTES : Z := 24.
Lemma sizeof_t_sdt: sizeof t_sdt = SDT_BYTES.
Proof. reflexivity. Qed.

Definition u64_ok (v: Z) : Prop := 0 <= v <= Int64.max_unsigned.
Definition u32_ok (v: Z) : Prop := 0 <= v <= Int.max_unsigned.
Definition byte_ok (v: Z) : Prop := 0 <= v <= Byte.max_unsigned.

Definition vl (v: Z) : val := Vlong (Int64.repr v).
Definition vi (v: Z) : val := Vint (Int.repr v).

(* Bytes as unsigned chars (as nondet_bytes leaves them). *)
Definition bytes_val (bs: list Z) : list val := map (fun b => Vint (Int.repr b)) bs.

(* A string literal of four characters and its NUL, as clightgen makes it a global (__stringlit_acpi_1 "APIC",
   __stringlit_acpi_2 "XSDT", __stringlit_acpi_3 "RSDT") and main's precondition holds it (expand_main_pre:
   data_at Ers, the characters as signed chars, all below 128 here). *)
Definition lit_val (s: list Z) : list val := map (fun c => Vint (Int.repr c)) (s ++ [0]).
Definition literal (s: list Z) (p: val) : mpred := data_at Ers (tarray tschar 5) (lit_val s) p.

(* The inputs a call of the pipeline may have: a 64-bit selection, a 36-byte header scratch, arenas whose
   capacities are 32-bit, all holding bytes. *)
Definition inputs_ok (x: inputs) : Prop :=
  u64_ok (i_kind x) /\ u64_ok (i_address x) /\ Zlength (i_header x) = HEADER_BYTES /\
  root_capacity x <= Int.max_unsigned /\ table_capacity x <= Int.max_unsigned /\
  Forall byte_ok (i_header x) /\ Forall byte_ok (i_root x) /\ Forall byte_ok (i_tables x).

(* The storage's three byte objects: the header scratch, the root arena, the table arena. *)
Record place : Type := mk_place { p_header: val; p_root: val; p_tables: val }.

(* Where a copy to d writes. *)
Definition dest_ptr (pl: place) (d: dest) : val :=
  match d with
  | DHeader => p_header pl
  | DRoot => p_root pl
  | DTables off => offset_val off (p_tables pl)
  end.

(* ---------------------------------------------------------------------- *)
(* The oracle and the protocols of the three callees.                    *)
(* ---------------------------------------------------------------------- *)

Definition ORA : Type := globals -> val -> place -> inputs -> list answer -> mpred.

(* The physical copy callback: asked for the pipeline's next copy after the answers h, of len bytes to d, whose
   bytes it is given as the model says they are, it returns any int and leaves any len bytes there (it may write
   before it fails), and records both. *)
Definition copy_spec (Ora: ORA) : funspec :=
  WITH gv: globals, ctx: val, pl: place, sh: share, x: inputs, h: list answer, a: Z, d: dest, len: Z
  PRE [ tptr tvoid, tulong, tptr tuchar, tuint ]
    PROP (writable_share sh; next_call x h = Some (Copy a d len))
    PARAMS (ctx; vl a; dest_ptr pl d; vi len)
    GLOBALS (gv)
    SEP (Ora gv ctx pl x h; data_at sh (tarray tuchar len) (bytes_val (holds x h d len)) (dest_ptr pl d))
  POST [ tint ]
    EX ret: Z, EX bs: list Z,
    PROP (Int.min_signed <= ret <= Int.max_signed; Zlength bs = len; Forall byte_ok bs)
    RETURN (Vint (Int.repr ret))
    SEP (Ora gv ctx pl x (h ++ [(Copy a d len, Copied ret bs)]);
         data_at sh (tarray tuchar len) (bytes_val bs) (dest_ptr pl d)).

(* The copy stream: asked for the pipeline's next call after the answers h, it answers any 64-bit value and
   records the answer. *)
Definition stream_spec (Ora: ORA) :=
  DECLARE _leanos_boot_machine_acpi_copy_stream_step_query
  WITH gv: globals, ctx: val, pl: place, x: inputs, h: list answer,
       a1: Z, a2: Z, a3: Z, a4: Z, a5: Z, a6: Z, a7: Z, a8: Z, a9: Z
  PRE [ tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong, tulong ]
    PROP (next_call x h = Some (Stream a1 a2 a3 a4 a5 a6 a7 a8 a9))
    PARAMS (vl a1; vl a2; vl a3; vl a4; vl a5; vl a6; vl a7; vl a8; vl a9)
    GLOBALS (gv)
    SEP (Ora gv ctx pl x h)
  POST [ tulong ]
    EX v: Z,
    PROP (u64_ok v)
    RETURN (vl v)
    SEP (Ora gv ctx pl x (h ++ [(Stream a1 a2 a3 a4 a5 a6 a7 a8 a9, Word v)])).

(* The copy sequence, likewise. *)
Definition sequence_spec (Ora: ORA) :=
  DECLARE _leanos_boot_machine_acpi_copy_sequence_step_query
  WITH gv: globals, ctx: val, pl: place, x: inputs, h: list answer, a1: Z, a2: Z, a3: Z, a4: Z, a5: Z, a6: Z
  PRE [ tulong, tulong, tulong, tulong, tulong, tulong ]
    PROP (next_call x h = Some (Sequence a1 a2 a3 a4 a5 a6))
    PARAMS (vl a1; vl a2; vl a3; vl a4; vl a5; vl a6)
    GLOBALS (gv)
    SEP (Ora gv ctx pl x h)
  POST [ tulong ]
    EX v: Z,
    PROP (u64_ok v)
    RETURN (vl v)
    SEP (Ora gv ctx pl x (h ++ [(Sequence a1 a2 a3 a4 a5 a6, Word v)])).

(* ---------------------------------------------------------------------- *)
(* The storage and the result.                                           *)
(* ---------------------------------------------------------------------- *)

(* struct acpi_table_copy_storage: header, root, root_capacity, tables, table_capacity, copies. *)
Definition storage_val (pl: place) (x: inputs) (copies: val) : reptype t_storage :=
  (p_header pl, (p_root pl, (vi (root_capacity x), (p_tables pl, (vi (table_capacity x), copies))))).

(* struct copied_acpi_sdt: physical_address, bytes (base + offset), length, next_copy_offset. *)
Definition sdt_val (base: val) (s: sdt) : sdt_rep :=
  (vl (s_address s), (offset_val (s_offset s) base, (vi (s_length s), vi (s_next s)))).

(* struct acpi_root_entries: bytes, count, width. *)
Definition entries_val (base: val) (count width: Z) : entries_rep :=
  (offset_val HEADER_BYTES base, (vi count, vi width)).

(* The 256 slots: those the pipeline wrote, then the rest as they were (sold). *)
Definition slots_val (pl: place) (m: mem) (sold: list sdt_rep) : list sdt_rep :=
  map (sdt_val (p_tables pl)) (m_slots m) ++ sublist (Zlength (m_slots m)) MAX_ENTRIES sold.

(* struct acpi_table_copy_result: root, entries, table_count, madt; each field written, or as it was. *)
Definition result_val (pl: place) (copies: val) (m: mem) (pub: option (Z * Z))
    (rroot: sdt_rep) (rentries: entries_rep) (rcount rmadt: val) : sdt_rep * (entries_rep * (val * val)) :=
  (match m_root_copy m with Some s => sdt_val (p_root pl) s | None => rroot end,
   (match m_entries m with Some (count, w) => entries_val (p_root pl) count w | None => rentries end,
    (match pub with Some (count, _) => vi count | None => rcount end,
     match pub with Some (_, i) => offset_val (SDT_BYTES * i) copies | None => rmadt end))).

(* ---------------------------------------------------------------------- *)
(* The pipeline.                                                          *)
(* ---------------------------------------------------------------------- *)

(* acpi_copy_root_and_tables and acpi_pipeline.  Any selection, any callback obeying the copy protocol, any
   context; the storage record (readable) naming a header scratch of 36 bytes, root and table arenas of exactly
   their capacities and 256 copy slots, and a result record, each holding anything (the byte objects bytes), none
   aliasing another (separate conjuncts); the three string literals.  It returns after the callees answered
   exactly the calls h of a run of the model with outcome (st, pub, m): it returns st, the byte objects hold
   m's bytes, the slots the m_slots written and their old values after them, and the result the fields written
   (the table count and the MADT only on OK) and its old fields elsewhere. *)
Definition pipeline_pre_post (Ora: ORA) (name: ident) :=
  DECLARE name
  WITH gv: globals, copy: val, ctx: val, x: inputs, pl: place, sh: share, sp: val, ssh: share,
       copies: val, osh: share, sold: list sdt_rep,
       res: val, rroot: sdt_rep, rentries: entries_rep, rcount: val, rmadt: val
  PRE [ tptr t_copy, tptr tvoid, tulong, tulong, tptr t_storage, tptr t_result ]
    PROP (writable_share sh; readable_share ssh; writable_share osh; inputs_ok x; Zlength sold = MAX_ENTRIES)
    PARAMS (copy; ctx; vl (i_kind x); vl (i_address x); sp; res)
    GLOBALS (gv)
    SEP (func_ptr' (copy_spec Ora) copy; Ora gv ctx pl x nil;
         literal APIC (gv ___stringlit_acpi_1); literal XSDT (gv ___stringlit_acpi_2);
         literal RSDT (gv ___stringlit_acpi_3);
         data_at ssh t_storage (storage_val pl x copies) sp;
         data_at sh (tarray tuchar HEADER_BYTES) (bytes_val (i_header x)) (p_header pl);
         data_at sh (tarray tuchar (root_capacity x)) (bytes_val (i_root x)) (p_root pl);
         data_at sh (tarray tuchar (table_capacity x)) (bytes_val (i_tables x)) (p_tables pl);
         data_at osh (tarray t_sdt MAX_ENTRIES) sold copies;
         data_at osh t_result (rroot, (rentries, (rcount, rmadt))) res)
  POST [ tint ]
    EX h: list answer, EX st: Z, EX pub: option (Z * Z), EX m: mem,
    PROP (pipeline x h = Some (st, pub, m))
    RETURN (Vint (Int.repr st))
    SEP (func_ptr' (copy_spec Ora) copy; Ora gv ctx pl x h;
         literal APIC (gv ___stringlit_acpi_1); literal XSDT (gv ___stringlit_acpi_2);
         literal RSDT (gv ___stringlit_acpi_3);
         data_at ssh t_storage (storage_val pl x copies) sp;
         data_at sh (tarray tuchar HEADER_BYTES) (bytes_val (m_header m)) (p_header pl);
         data_at sh (tarray tuchar (root_capacity x)) (bytes_val (m_root m)) (p_root pl);
         data_at sh (tarray tuchar (table_capacity x)) (bytes_val (m_tables m)) (p_tables pl);
         data_at osh (tarray t_sdt MAX_ENTRIES) (slots_val pl m sold) copies;
         data_at osh t_result (result_val pl copies m pub rroot rentries rcount rmadt) res).

Definition copy_root_and_tables_spec Ora := pipeline_pre_post Ora _acpi_copy_root_and_tables.
Definition pipeline_spec Ora := pipeline_pre_post Ora _acpi_pipeline.
