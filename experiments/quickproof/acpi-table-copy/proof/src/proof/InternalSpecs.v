(* Specifications of the internal functions of the unit patch/acpi_unit.c (include/acpi_table_copy.h), and Gprog,
   the specifications the body proofs are stated against.  A starting point for the body proofs, which may revise
   them; the interface the law depends on (the oracle, the callees and the pipeline) is AcpiSpecs.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import LeanosAcpi.acpi.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
#[local] Existing Instance AcpiSpecs.CS.

(* ---------------------------------------------------------------------- *)
(* The internal functions: a starting point for their body proofs.        *)
(* ---------------------------------------------------------------------- *)

(* acpi_signature_matches(table, signature): the table's record (its length len and bytes bp, whose bytes start
   with bs), a literal of four characters. *)
Definition signature_matches_spec :=
  DECLARE _acpi_signature_matches
  WITH tsh: share, tp: val, ta: val, len: Z, tn: val, bp: val, bsh: share, bs: list Z, sp: val, sig: list Z
  PRE [ tptr t_sdt, tptr tschar ]
    PROP (readable_share tsh; readable_share bsh; u32_ok len; HEADER_BYTES <= len -> 4 <= Zlength bs;
          Forall byte_ok bs; Zlength sig = 4; Forall (fun c => 0 <= c < 128) sig)
    PARAMS (tp; sp)
    SEP (data_at tsh t_sdt (ta, (bp, (vi len, tn))) tp; data_at bsh (tarray tuchar (Zlength bs)) (bytes_val bs) bp;
         literal sig sp)
  POST [ tint ]
    PROP ()
    RETURN (Vint (if signature_matches len bs sig then Int.one else Int.zero))
    SEP (data_at tsh t_sdt (ta, (bp, (vi len, tn))) tp; data_at bsh (tarray tuchar (Zlength bs)) (bytes_val bs) bp;
         literal sig sp).

(* acpi_validate_copied_sdt(table, signature): signature NULL (None) or a literal. *)
Definition validate_spec :=
  DECLARE _acpi_validate_copied_sdt
  WITH tsh: share, tp: val, ta: val, len: Z, tn: val, bp: val, bsh: share, bs: list Z, sp: val,
       sig: option (list Z)
  PRE [ tptr t_sdt, tptr tschar ]
    PROP (readable_share tsh; readable_share bsh; u32_ok len; 0 < Zlength bs;
          HEADER_BYTES <= len -> len <= Zlength bs; Forall byte_ok bs;
          match sig with
          | None => sp = nullval
          | Some s => Zlength s = 4 /\ Forall (fun c => 0 <= c < 128) s
          end)
    PARAMS (tp; sp)
    SEP (data_at tsh t_sdt (ta, (bp, (vi len, tn))) tp; data_at bsh (tarray tuchar (Zlength bs)) (bytes_val bs) bp;
         match sig with Some s => literal s sp | None => emp end)
  POST [ tint ]
    PROP ()
    RETURN (vi (validate len bs sig))
    SEP (data_at tsh t_sdt (ta, (bp, (vi len, tn))) tp; data_at bsh (tarray tuchar (Zlength bs)) (bytes_val bs) bp;
         match sig with Some s => literal s sp | None => emp end).

(* The status of a model function that returns a status (inl) or a value on OK (inr). *)
Definition status_of {A: Type} (r: Z + A) : Z := match r with inl st => st | inr _ => S_OK end.

(* A slot written by the pipeline, within the table arena T. *)
Definition slot_ok (T: list Z) (s: sdt) : Prop :=
  u64_ok (s_address s) /\ HEADER_BYTES <= s_length s /\ 0 <= s_offset s /\
  s_offset s + s_length s <= Zlength T /\ u32_ok (s_length s) /\ u32_ok (s_next s).


(* acpi_select_unique_madt(copies, copied_count, madt): the first |ss| slots are ss, in the table arena T. *)
Definition select_unique_madt_spec :=
  DECLARE _acpi_select_unique_madt
  WITH gv: globals, copies: val, osh: share, ss: list sdt, rest: list sdt_rep, tp: val, sh: share,
       T: list Z, mp: val, msh: share, mold: val
  PRE [ tptr t_sdt, tuint, tptr (tptr t_sdt) ]
    PROP (readable_share osh; readable_share sh; writable_share msh; (Zlength ss + Zlength rest = MAX_ENTRIES)%Z;
          Forall byte_ok T; Forall (slot_ok T) ss)
    PARAMS (copies; vi (Zlength ss); mp)
    GLOBALS (gv)
    SEP (data_at osh (tarray t_sdt MAX_ENTRIES) (map (sdt_val tp) ss ++ rest) copies;
         data_at sh (tarray tuchar (Zlength T)) (bytes_val T) tp; literal APIC (gv ___stringlit_acpi_1);
         data_at msh (tptr t_sdt) mold mp)
  POST [ tint ]
    PROP ()
    RETURN (vi (status_of (select_from T ss 0 None)))
    SEP (data_at osh (tarray t_sdt MAX_ENTRIES) (map (sdt_val tp) ss ++ rest) copies;
         data_at sh (tarray tuchar (Zlength T)) (bytes_val T) tp; literal APIC (gv ___stringlit_acpi_1);
         data_at msh (tptr t_sdt)
           (match select_from T ss 0 None with inl _ => mold | inr i => offset_val (SDT_BYTES * i) copies end) mp).

(* acpi_decode_root_entries(root, selected_kind, entries): the root's record, its bytes at base. *)
Definition decode_root_entries_spec :=
  DECLARE _acpi_decode_root_entries
  WITH rsh: share, rp: val, ra: val, base: val, len: Z, rn: val, kind: Z, esh: share, ep: val,
       eold: entries_rep
  PRE [ tptr t_sdt, tulong, tptr t_entries ]
    PROP (readable_share rsh; writable_share esh; u32_ok len; u64_ok kind; isptr base)
    PARAMS (rp; vl kind; ep)
    SEP (data_at rsh t_sdt (ra, (base, (vi len, rn))) rp; data_at esh t_entries eold ep)
  POST [ tint ]
    PROP ()
    RETURN (vi (status_of (decode_entries kind len)))
    SEP (data_at rsh t_sdt (ra, (base, (vi len, rn))) rp;
         data_at esh t_entries
           (match decode_entries kind len with inl _ => eold | inr (count, w) => entries_val base count w end) ep).

(* acpi_decode_root_entry(entries, index, address): the entry vector vec at eb (the root's bytes from 36 on). *)
Definition decode_root_entry_spec :=
  DECLARE _acpi_decode_root_entry
  WITH esh: share, ep: val, eb: val, count: Z, w: Z, bsh: share, vec: list Z, index: Z, ash: share, ap: val,
       aold: val
  PRE [ tptr t_entries, tuint, tptr tulong ]
    PROP (readable_share esh; readable_share bsh; writable_share ash; u32_ok count; u32_ok w; u32_ok index;
          index < count -> (w = 4 \/ w = 8) -> index * w + w <= Zlength vec; Zlength vec <= Int.max_unsigned;
          Forall byte_ok vec; isptr eb)
    PARAMS (ep; vi index; ap)
    SEP (data_at esh t_entries (eb, (vi count, vi w)) ep;
         data_at bsh (tarray tuchar (Zlength vec)) (bytes_val vec) eb; data_at ash tulong aold ap)
  POST [ tint ]
    PROP ()
    RETURN (vi (status_of (decode_entry vec count w index)))
    SEP (data_at esh t_entries (eb, (vi count, vi w)) ep;
         data_at bsh (tarray tuchar (Zlength vec)) (bytes_val vec) eb;
         data_at ash tulong (match decode_entry vec count w index with inl _ => aold | inr a => vl a end) ap).

(* acpi_decode_root_addresses(entries, addresses): on OK the first count addresses are the decoded ones. *)
Definition decode_root_addresses_spec :=
  DECLARE _acpi_decode_root_addresses
  WITH esh: share, ep: val, eb: val, count: Z, w: Z, bsh: share, vec: list Z, ash: share, ap: val,
       aold: list val
  PRE [ tptr t_entries, tptr tulong ]
    PROP (readable_share esh; readable_share bsh; writable_share ash; 0 <= count <= MAX_ENTRIES; w = 4 \/ w = 8;
          count * w <= Zlength vec; Zlength vec <= Int.max_unsigned; Forall byte_ok vec; Zlength aold = MAX_ENTRIES;
          isptr eb)
    PARAMS (ep; ap)
    SEP (data_at esh t_entries (eb, (vi count, vi w)) ep;
         data_at bsh (tarray tuchar (Zlength vec)) (bytes_val vec) eb;
         data_at ash (tarray tulong MAX_ENTRIES) aold ap)
  POST [ tint ]
    EX aout: list val,
    PROP (Zlength aout = MAX_ENTRIES;
          match decode_addresses vec w count with
          | inr addresses => aout = map vl addresses ++ sublist count MAX_ENTRIES aold
          | inl _ => True
          end)
    RETURN (vi (status_of (decode_addresses vec w count)))
    SEP (data_at esh t_entries (eb, (vi count, vi w)) ep;
         data_at bsh (tarray tuchar (Zlength vec)) (bytes_val vec) eb;
         data_at ash (tarray tulong MAX_ENTRIES) aout ap).

(* A status of enum acpi_table_copy_status (so that a caller may compare it with OK as an int). *)
Definition status_ok (st: Z) : Prop := andb (Z.leb 0 st) (Z.leb st S_MADT_SELECTION) = true.

(* The arena an SDT g is copied into, and its offset there. *)
Definition base_of (pl: place) (g: target) : val :=
  match g with TRoot => p_root pl | TTable _ => p_tables pl end.
Definition offset_of (g: target) : Z :=
  match g with TRoot => 0 | TTable l => l_offset l end.

(* What acpi_copy_sdt on g may change of the model's mem: the header scratch and g's destination (from its
   offset on), nothing else. *)
Definition copy_frame (g: target) (m m': mem) : Prop :=
  Zlength (m_header m') = Zlength (m_header m) /\
  Zlength (m_root m') = Zlength (m_root m) /\ Zlength (m_tables m') = Zlength (m_tables m) /\
  m_root_copy m' = m_root_copy m /\ m_entries m' = m_entries m /\ m_slots m' = m_slots m /\
  match g with
  | TRoot => m_tables m' = m_tables m
  | TTable l => m_root m' = m_root m /\ sublist 0 (l_offset l) (m_tables m') = sublist 0 (l_offset l) (m_tables m)
  end.

(* The mem m of a run of the model on x: its byte objects as long as x's. *)
Definition mem_ok (x: inputs) (m: mem) : Prop :=
  Zlength (m_header m) = HEADER_BYTES /\ Zlength (m_root m) = root_capacity x /\
  Zlength (m_tables m) = table_capacity x /\
  Forall byte_ok (m_header m) /\ Forall byte_ok (m_root m) /\ Forall byte_ok (m_tables m).

(* acpi_copy_sdt on the SDT g, where the model, after the answers h, begins it (begin_sdt) with mem m.  It returns
   after the further answers hs, with the model either at g's stream end (sdt_copied, on OK, when it wrote
   *copied) or returned with its status; m' is the mem then. *)
Definition copy_sdt_spec (Ora: ORA) :=
  DECLARE _acpi_copy_sdt
  WITH gv: globals, copy: val, ctx: val, pl: place, sh: share, x: inputs, h: list answer, g: target, m: mem,
       csh: share, cp: val, cold: sdt_rep
  PRE [ tptr t_copy, tptr tvoid, tulong, tptr tuchar, tptr tuchar, tuint, tuint, tptr t_sdt ]
    PROP (writable_share sh; writable_share csh; inputs_ok x; mem_ok x m;
          run x (start x) h = Some (begin_sdt x g m); u64_ok (address_of x g);
          match g with TRoot => True | TTable l => 0 <= l_offset l < table_capacity x end)
    PARAMS (copy; ctx; vl (address_of x g); p_header pl; dest_ptr pl (dest_of g); vi (capacity_of x g);
            vi (cursor_of g); cp)
    GLOBALS (gv)
    SEP (func_ptr' (copy_spec Ora) copy; Ora gv ctx pl x h;
         data_at sh (tarray tuchar HEADER_BYTES) (bytes_val (m_header m)) (p_header pl);
         data_at sh (tarray tuchar (capacity_of x g)) (bytes_val (region m (dest_of g) (capacity_of x g)))
           (dest_ptr pl (dest_of g));
         data_at csh t_sdt cold cp)
  POST [ tint ]
    EX hs: list answer, EX st: Z, EX m': mem, EX len: Z, EX cursor: Z,
    PROP (run x (begin_sdt x g m) hs =
            Some (if st =? S_OK then sdt_copied x g len cursor m' else Return st None m');
          mem_ok x m'; copy_frame g m m'; status_ok st;
          st = S_OK -> HEADER_BYTES <= len <= MAX_SDT_BYTES /\ len <= capacity_of x g /\ u64_ok cursor)
    RETURN (vi st)
    SEP (func_ptr' (copy_spec Ora) copy; Ora gv ctx pl x (h ++ hs);
         data_at sh (tarray tuchar HEADER_BYTES) (bytes_val (m_header m')) (p_header pl);
         data_at sh (tarray tuchar (capacity_of x g)) (bytes_val (region m' (dest_of g) (capacity_of x g)))
           (dest_ptr pl (dest_of g));
         data_at csh t_sdt
           (if st =? S_OK
            then sdt_val (base_of pl g) (mk_sdt (address_of x g) (offset_of g) len (cursor mod 2 ^ 32))
            else cold) cp).

(* acpi_copy_root_tables, where the model, after the answers h, starts the tables (tables_start) on the root's
   addresses with mem m and no slot written.  On OK the model is at the MADT selection (tables_done); otherwise it
   returned with the status.  m' is the mem then. *)
Definition copy_root_tables_spec (Ora: ORA) :=
  DECLARE _acpi_copy_root_tables
  WITH gv: globals, copy: val, ctx: val, pl: place, sh: share, x: inputs, h: list answer, addresses: list Z,
       m: mem, esh: share, ep: val, eb: val, w: val, ash: share, ap: val, arest: list val, csh: share, cp: val,
       sold: list sdt_rep, nsh: share, np: val, nold: val
  PRE [ tptr t_copy, tptr tvoid, tptr t_entries, tptr tulong, tptr tuchar, tptr tuchar, tuint, tptr t_sdt,
        tptr tuint ]
    PROP (writable_share sh; readable_share esh; readable_share ash; writable_share csh; writable_share nsh;
          inputs_ok x; mem_ok x m; m_slots m = nil; run x (start x) h = Some (tables_start x addresses m);
          Zlength addresses <= MAX_ENTRIES; Zlength (map vl addresses ++ arest) = MAX_ENTRIES;
          Forall (fun a => 0 < a <= MAX_U32) addresses; Zlength sold = MAX_ENTRIES)
    PARAMS (copy; ctx; ep; ap; p_header pl; p_tables pl; vi (table_capacity x); cp; np)
    GLOBALS (gv)
    SEP (func_ptr' (copy_spec Ora) copy; Ora gv ctx pl x h;
         data_at esh t_entries (eb, (vi (Zlength addresses), w)) ep;
         data_at ash (tarray tulong MAX_ENTRIES) (map vl addresses ++ arest) ap;
         data_at sh (tarray tuchar HEADER_BYTES) (bytes_val (m_header m)) (p_header pl);
         data_at sh (tarray tuchar (table_capacity x)) (bytes_val (m_tables m)) (p_tables pl);
         data_at csh (tarray t_sdt MAX_ENTRIES) sold cp; data_at nsh tuint nold np)
  POST [ tint ]
    EX hs: list answer, EX st: Z, EX m': mem,
    PROP (run x (tables_start x addresses m) hs =
            Some (if st =? S_OK then tables_done (Zlength addresses) m' else Return st None m');
          mem_ok x m'; m_root m' = m_root m; m_root_copy m' = m_root_copy m; m_entries m' = m_entries m;
          Forall (slot_ok (m_tables m')) (m_slots m'); status_ok st;
          st = S_OK -> Zlength (m_slots m') = Zlength addresses)
    RETURN (vi st)
    SEP (func_ptr' (copy_spec Ora) copy; Ora gv ctx pl x (h ++ hs);
         data_at esh t_entries (eb, (vi (Zlength addresses), w)) ep;
         data_at ash (tarray tulong MAX_ENTRIES) (map vl addresses ++ arest) ap;
         data_at sh (tarray tuchar HEADER_BYTES) (bytes_val (m_header m')) (p_header pl);
         data_at sh (tarray tuchar (table_capacity x)) (bytes_val (m_tables m')) (p_tables pl);
         data_at csh (tarray t_sdt MAX_ENTRIES) (slots_val pl m' sold) cp;
         data_at nsh tuint (if st =? S_OK then vi (Zlength addresses) else nold) np).

Definition Gprog (Ora: ORA) : funspecs :=
  [stream_spec Ora; sequence_spec Ora;
   signature_matches_spec; copy_sdt_spec Ora; validate_spec; select_unique_madt_spec; decode_root_entries_spec;
   decode_root_entry_spec; decode_root_addresses_spec; copy_root_tables_spec Ora;
   copy_root_and_tables_spec Ora; pipeline_spec Ora].
