(* Pure definitions shared by every proof of leanos_acpi (include/acpi_table_copy.h): the pipeline
   acpi_copy_root_and_tables as a state machine over the answers of its three callees, the physical copy callback
   and the two Lean exports.  No program here.  Words are Z values in their C type's range (uint64_t, uint32_t,
   bytes 0..255); every definition follows the C it names.

   Every byte the pipeline reads was written by the firmware first: a header before its length is decoded, a body
   before its stream, its validation and its entries.  So the calls the pipeline makes, and its status, depend only
   on the answers, the selection and the two capacities, never on what the storage held before.  The prior bytes
   only show in what the pipeline leaves behind, which the model computes as well (`mem`): the header scratch, the
   two arenas, the result record and the 256 copy slots.

   Checks of the C that cannot fail, because they test what the pipeline itself just computed, are not in the
   model; the body proofs show they pass:
   - acpi_copy_root_and_tables: ROOT_COPY (the root's record is what acpi_copy_sdt wrote, its length >= 36),
     ROOT_VECTOR (what acpi_decode_root_entries wrote), INCOMPLETE (copied_count is entries->count) and
     MADT_SELECTION (the selected copy's signature matched APIC);
   - acpi_copy_root_tables: BINDING (the slot is what acpi_copy_sdt wrote), BUDGET on `padded_length < length`
     (a length is at most 65536) and SEQUENCE after the loop (the carried ordinal is entry + 1 = count);
   - acpi_decode_root_entry, from acpi_decode_root_addresses: ROOT_ENTRY_INDEX (entry < count, width 4 or 8),
     though `decode_entry`, its own model, has it.
   Checks that cannot fail but belong to a function the model follows as a whole stay in it: SDT_ADDRESS_WIDTH in
   `begin_sdt` for a table too (every entry was checked to be below 2^32), and the checks of `validate`,
   `signature_matches` and `decode_entries` on their arguments (a length below 36, a kind other than 1 and 2),
   which pass on every copy the pipeline makes. *)
Require Import VST.floyd.proofauto.
Local Open Scope Z_scope.
Local Open Scope bool_scope.   (* && and || are andb and orb here, not VST's andp and orp *)

(* enum acpi_table_copy_status *)
Definition S_OK : Z := 0.
Definition S_ROOT_SELECTION : Z := 1.
Definition S_SDT_ADDRESS_WIDTH : Z := 2.
Definition S_PHYSICAL : Z := 3.
Definition S_SDT_LENGTH : Z := 4.
Definition S_BUDGET : Z := 5.
Definition S_LENGTH : Z := 6.
Definition S_ADDRESS : Z := 7.
Definition S_OFFSET : Z := 8.
Definition S_TERMINAL : Z := 9.
Definition S_ERROR : Z := 10.
Definition S_STATUS : Z := 11.
Definition S_NEXT_BYTE : Z := 12.
Definition S_EXPOSED : Z := 13.
Definition S_PARTIAL_CURSOR : Z := 14.
Definition S_FINAL_CURSOR : Z := 15.
Definition S_ROOT_COPY : Z := 16.
Definition S_SDT_ENVELOPE : Z := 17.
Definition S_SDT_CHECKSUM : Z := 18.
Definition S_ROOT_KIND : Z := 19.
Definition S_ROOT_HEADER : Z := 20.
Definition S_ROOT_WIDTH : Z := 21.
Definition S_ROOT_ENTRIES : Z := 22.
Definition S_ROOT_VECTOR : Z := 23.
Definition S_ROOT_ENTRY_INDEX : Z := 24.
Definition S_ROOT_ENTRY_ADDRESS : Z := 25.
Definition S_ROOT_ENTRY_DUPLICATE : Z := 26.
Definition S_SEQUENCE : Z := 27.
Definition S_BINDING : Z := 28.
Definition S_STREAM : Z := 29.
Definition S_INCOMPLETE : Z := 30.
Definition S_MADT_DUPLICATE : Z := 31.
Definition S_MADT_MISSING : Z := 32.
Definition S_MADT_SELECTION : Z := 33.

Definition HEADER_BYTES : Z := 36.        (* ACPI_SDT_HEADER_BYTES *)
Definition MAX_SDT_BYTES : Z := 65536.    (* MAX_COPIED_ACPI_SDT_BYTES *)
Definition MAX_ENTRIES : Z := 256.        (* MAX_ACPI_ROOT_ENTRIES *)
Definition MAX_U32 : Z := 4294967295.     (* UINT64_C(0xffffffff) *)

(* The string literals "RSDT", "XSDT", "APIC", without their NUL. *)
Definition RSDT : list Z := [82; 83; 68; 84].
Definition XSDT : list Z := [88; 83; 68; 84].
Definition APIC : list Z := [65; 80; 73; 67].

(* 0, 1, .., n - 1 *)
Definition range (n: Z) : list Z := map Z.of_nat (seq 0 (Z.to_nat n)).

(* bs little-endian, as the C composes it: byte i or-ed in at bit 8 i (the header's length, a chunk, an entry). *)
Definition little (bs: list Z) : Z :=
  fold_left (fun v i => Z.lor v (Z.shiftl (Znth i bs) (8 * i))) (range (Zlength bs)) 0.

(* acpi_validate_copied_sdt's checksum: the uint8_t sum of bs. *)
Definition checksum (bs: list Z) : Z := fold_left (fun c b => (c + b) mod 256) bs 0.

(* acpi_signature_matches(table, signature), for a table of length len whose bytes start with bs. *)
Definition signature_matches (len: Z) (bs sig: list Z) : bool :=
  (HEADER_BYTES <=? len) && (Znth 0 bs =? Znth 0 sig) && (Znth 1 bs =? Znth 1 sig) &&
  (Znth 2 bs =? Znth 2 sig) && (Znth 3 bs =? Znth 3 sig).

(* acpi_validate_copied_sdt(table, signature) for a table of length len whose bytes start with bs (non-NULL), the
   signature NULL (None) or a literal: SDT_ENVELOPE, SDT_CHECKSUM or OK. *)
Definition validate (len: Z) (bs: list Z) (sig: option (list Z)) : Z :=
  if (len <? HEADER_BYTES) || negb (little (sublist 4 8 bs) =? len) ||
     (match sig with Some s => negb (signature_matches len bs s) | None => false end)
  then S_SDT_ENVELOPE
  else if negb (checksum (sublist 0 len bs) =? 0) then S_SDT_CHECKSUM
  else S_OK.

(* acpi_decode_root_entries(root, kind, entries) for a root of length len: a status, or the entry count and
   width it writes to `entries`. *)
Definition decode_entries (kind len: Z) : Z + (Z * Z) :=
  let width := if kind =? 1 then 4 else if kind =? 2 then 8 else 0 in
  if width =? 0 then inl S_ROOT_KIND
  else if len <? HEADER_BYTES then inl S_ROOT_HEADER
  else if negb ((len - HEADER_BYTES) mod width =? 0) then inl S_ROOT_WIDTH
  else if MAX_ENTRIES <? (len - HEADER_BYTES) / width then inl S_ROOT_ENTRIES
  else inr ((len - HEADER_BYTES) / width, width).

(* Entry e of the entry vector vec (the root's bytes from 36 on), w bytes wide. *)
Definition entry_at (vec: list Z) (w e: Z) : Z := little (sublist (e * w) (e * w + w) vec).

(* acpi_decode_root_entry(entries, index, address) on the vector vec of count entries of width w: a status, or
   the address it writes. *)
Definition decode_entry (vec: list Z) (count w index: Z) : Z + Z :=
  if (count <=? index) || negb ((w =? 4) || (w =? 8)) then inl S_ROOT_ENTRY_INDEX
  else let a := entry_at vec w index in
  if (a =? 0) || (MAX_U32 <? a) then inl S_ROOT_ENTRY_ADDRESS else inr a.

(* acpi_decode_root_addresses: the entries es in order, each checked as an address, then against the earlier
   ones; a status, or every address. *)
Fixpoint decode_from (vec: list Z) (w: Z) (es: list Z) (prior: list Z) : Z + list Z :=
  match es with
  | nil => inr prior
  | e :: rest =>
    let a := entry_at vec w e in
    if (a =? 0) || (MAX_U32 <? a) then inl S_ROOT_ENTRY_ADDRESS
    else if existsb (Z.eqb a) prior then inl S_ROOT_ENTRY_DUPLICATE
    else decode_from vec w rest (prior ++ [a])
  end.

Definition decode_addresses (vec: list Z) (w count: Z) : Z + list Z := decode_from vec w (range count) nil.

(* (length + 7u) & ~7u *)
Definition padded (len: Z) : Z := (len + 7) / 8 * 8.

(* ---------------------------------------------------------------------- *)
(* The calls and their answers.                                           *)
(* ---------------------------------------------------------------------- *)

(* The destination of a physical copy: the header scratch, the root arena, or the table arena from byte off. *)
Inductive dest : Type :=
  | DHeader
  | DRoot
  | DTables (off: Z).

Inductive call : Type :=
  (* copy(context, address, destination, length) *)
  | Copy (address: Z) (d: dest) (length: Z)
  (* leanos_boot_machine_acpi_copy_stream_step_query(current_copy_offset, current_table_address,
     current_byte_offset, table_address, table_length, byte_offset, chunk, terminal, word) *)
  | Stream (cursor current_address current_byte address length byte chunk terminal word: Z)
  (* leanos_boot_machine_acpi_copy_sequence_step_query(current_ordinal, advertised_count, table_ordinal,
     table_complete, final_table, word) *)
  | Sequence (ordinal count table complete final word: Z).

(* An answer: of the copy, its return value and the bytes the destination holds afterwards (as many as it was
   asked for; on failure too, since a callback may write before it fails); of an export, the value. *)
Inductive reply : Type :=
  | Copied (ret: Z) (bytes: list Z)
  | Word (v: Z).

Definition reply_value (r: reply) : Z := match r with Copied v _ => v | Word v => v end.
Definition reply_bytes (r: reply) : list Z := match r with Copied _ bs => bs | Word _ => nil end.

(* One answered call. *)
Definition answer : Type := (call * reply)%type.

(* Whether r answers c: a copy with exactly its length's bytes, an export with a value. *)
Definition fits (c: call) (r: reply) : bool :=
  match c, r with
  | Copy _ _ len, Copied _ bs => Zlength bs =? len
  | Stream _ _ _ _ _ _ _ _ _, Word _ => true
  | Sequence _ _ _ _ _ _, Word _ => true
  | _, _ => false
  end.

(* ---------------------------------------------------------------------- *)
(* The inputs and what the pipeline leaves behind.                       *)
(* ---------------------------------------------------------------------- *)

(* The pipeline's inputs: the selection (selected_kind, selected_address) and the prior bytes of the header
   scratch (36) and of the root and table arenas, whose capacities are their lengths. *)
Record inputs : Type := mk_inputs {
  i_kind: Z; i_address: Z;
  i_header: list Z; i_root: list Z; i_tables: list Z }.

Definition root_capacity (x: inputs) : Z := Zlength (i_root x).
Definition table_capacity (x: inputs) : Z := Zlength (i_tables x).

(* A struct copied_acpi_sdt the pipeline wrote: physical_address, bytes (its arena + offset), length,
   next_copy_offset (the final cursor truncated to 32 bits). *)
Record sdt : Type := mk_sdt { s_address: Z; s_offset: Z; s_length: Z; s_next: Z }.

(* What the storage and the result hold: the header scratch, the root arena, the table arena; the result's root
   once written (its bytes the root arena), its entries once written (count and width; its bytes the root arena +
   36); the copy slots written, copies[0 .. |m_slots|) (each one's bytes the table arena + its offset). *)
Record mem : Type := mk_mem {
  m_header: list Z; m_root: list Z; m_tables: list Z;
  m_root_copy: option sdt; m_entries: option (Z * Z); m_slots: list sdt }.

Definition initial (x: inputs) : mem := mk_mem (i_header x) (i_root x) (i_tables x) None None nil.

(* bs written into l from off on. *)
Definition overlay (off: Z) (bs l: list Z) : list Z :=
  sublist 0 off l ++ bs ++ sublist (off + Zlength bs) (Zlength l) l.

(* What the copy to d leaves: the 36 header bytes, or bs over the arena. *)
Definition write (m: mem) (d: dest) (bs: list Z) : mem :=
  match d with
  | DHeader => mk_mem bs (m_root m) (m_tables m) (m_root_copy m) (m_entries m) (m_slots m)
  | DRoot => mk_mem (m_header m) (overlay 0 bs (m_root m)) (m_tables m) (m_root_copy m) (m_entries m) (m_slots m)
  | DTables off =>
      mk_mem (m_header m) (m_root m) (overlay off bs (m_tables m)) (m_root_copy m) (m_entries m) (m_slots m)
  end.

(* The len bytes of d. *)
Definition region (m: mem) (d: dest) (len: Z) : list Z :=
  match d with
  | DHeader => sublist 0 len (m_header m)
  | DRoot => sublist 0 len (m_root m)
  | DTables off => sublist off (off + len) (m_tables m)
  end.

Definition set_root_copy (m: mem) (s: sdt) : mem :=
  mk_mem (m_header m) (m_root m) (m_tables m) (Some s) (m_entries m) (m_slots m).
Definition set_entries (m: mem) (count width: Z) : mem :=
  mk_mem (m_header m) (m_root m) (m_tables m) (m_root_copy m) (Some (count, width)) (m_slots m).
Definition add_slot (m: mem) (s: sdt) : mem :=
  mk_mem (m_header m) (m_root m) (m_tables m) (m_root_copy m) (m_entries m) (m_slots m ++ [s]).

(* ---------------------------------------------------------------------- *)
(* The state machine.                                                     *)
(* ---------------------------------------------------------------------- *)

(* acpi_copy_root_tables' variables: the root's entry addresses (entries->count of them), the entry being copied,
   the arena cursor arena_offset, the carried copied_ordinal. *)
Record tloop : Type := mk_tloop { l_addresses: list Z; l_entry: Z; l_offset: Z; l_ordinal: Z }.

Definition set_offset (l: tloop) (off: Z) : tloop := mk_tloop (l_addresses l) (l_entry l) off (l_ordinal l).
Definition set_ordinal (l: tloop) (o: Z) : tloop := mk_tloop (l_addresses l) (l_entry l) (l_offset l) o.
Definition next_entry (l: tloop) : tloop := mk_tloop (l_addresses l) (l_entry l + 1) (l_offset l) (l_ordinal l).

(* The SDT acpi_copy_sdt copies: the root, or table l_entry of the loop l. *)
Inductive target : Type :=
  | TRoot
  | TTable (l: tloop).

(* Its acpi_copy_sdt arguments: physical_address, destination, destination_capacity, current_copy_offset. *)
Definition address_of (x: inputs) (g: target) : Z :=
  match g with TRoot => i_address x | TTable l => Znth (l_entry l) (l_addresses l) end.
Definition dest_of (g: target) : dest :=
  match g with TRoot => DRoot | TTable l => DTables (l_offset l) end.
Definition capacity_of (x: inputs) (g: target) : Z :=
  match g with TRoot => root_capacity x | TTable l => table_capacity x - l_offset l end.
Definition cursor_of (g: target) : Z :=
  match g with TRoot => 0 | TTable l => l_offset l end.

(* Inside acpi_copy_sdt, at its next call: the header copy; the body copy of the declared length len; the stream
   transition of the chunk at `byte`, with the carried cursor, the copy's bytes and the answers cur of words
   1, 2, 4, 5, 6 so far. *)
Inductive cstage : Type :=
  | CHeader
  | CBody (len: Z)
  | CChunk (len: Z) (bytes: list Z) (cursor byte: Z) (cur: list Z).

(* Where the pipeline is between calls: copying an SDT, or at the copy sequence step of the table l_entry l (its
   arena cursor already advanced), with the answers cur of words 1, 2, 3 so far. *)
Inductive stage : Type :=
  | Copying (g: target) (c: cstage)
  | Sequencing (l: tloop) (cur: list Z).

(* Calling again, or returned with a status, (table_count, the MADT's slot) on OK, and what it leaves. *)
Inductive progress : Type :=
  | Go (s: stage) (m: mem)
  | Return (status: Z) (published: option (Z * Z)) (m: mem).

(* The chunk at byte of a copy of length len: chunk_bytes, and whether it is the last. *)
Definition chunk_bytes (len byte: Z) : Z := Z.min 8 (len - byte).
Definition terminal (len byte: Z) : Z := if byte + chunk_bytes len byte =? len then 1 else 0.

(* The stream words 1, 2, 4, 5, 6, by the number of answers so far. *)
Definition stream_word (k: Z) : Z := if k <? 2 then k + 1 else k + 2.

(* The call the pipeline makes in stage s. *)
Definition expected (x: inputs) (s: stage) : call :=
  match s with
  | Copying g CHeader => Copy (address_of x g) DHeader HEADER_BYTES
  | Copying g (CBody len) => Copy (address_of x g) (dest_of g) len
  | Copying g (CChunk len bs cursor byte cur) =>
      let a := address_of x g in
      Stream cursor a byte a len byte (little (sublist byte (byte + chunk_bytes len byte) bs)) (terminal len byte)
             (stream_word (Zlength cur))
  | Sequencing l cur =>
      let count := Zlength (l_addresses l) in
      Sequence (l_ordinal l) count (l_entry l) 1 (if l_entry l + 1 =? count then 1 else 0) (Zlength cur + 1)
  end.

(* acpi_copy_sdt from its start: the address check, then the header copy. *)
Definition begin_sdt (x: inputs) (g: target) (m: mem) : progress :=
  if MAX_U32 <? address_of x g then Return S_SDT_ADDRESS_WIDTH None m else Go (Copying g CHeader) m.

(* An iteration of acpi_copy_root_tables' loop from its start: the budget check, then acpi_copy_sdt. *)
Definition begin_table (x: inputs) (l: tloop) (m: mem) : progress :=
  if table_capacity x <=? l_offset l then Return S_BUDGET None m else begin_sdt x (TTable l) m.

(* acpi_copy_root_tables from its start, on the root's addresses. *)
Definition tables_start (x: inputs) (addresses: list Z) (m: mem) : progress :=
  if Zlength addresses =? 0 then Return S_SEQUENCE None m else begin_table x (mk_tloop addresses 0 0 0) m.

(* acpi_select_unique_madt over the slots ss from index on (selected: the MADT found so far): a status, or the
   MADT's index.  A slot's bytes are the table arena from its offset on. *)
Fixpoint select_from (tables: list Z) (ss: list sdt) (index: Z) (selected: option Z) : Z + Z :=
  match ss with
  | nil => match selected with None => inl S_MADT_MISSING | Some i => inr i end
  | s :: rest =>
    let bs := sublist (s_offset s) (Zlength tables) tables in
    let st := validate (s_length s) bs None in
    if negb (st =? S_OK) then inl st
    else if signature_matches (s_length s) bs APIC then
      match selected with
      | Some _ => inl S_MADT_DUPLICATE
      | None => select_from tables rest (index + 1) (Some index)
      end
    else select_from tables rest (index + 1) selected
  end.

Definition select_madt (m: mem) : Z + Z := select_from (m_tables m) (m_slots m) 0 None.

(* After the last table: the MADT selection, then the result's table count and MADT. *)
Definition tables_done (count: Z) (m: mem) : progress :=
  match select_madt m with
  | inl st => Return st None m
  | inr i => Return S_OK (Some (count, i)) m
  end.

(* The root's stream ended (acpi_copy_sdt wrote result->root): its validation, entries and addresses.  As in the
   C, a pointer into an arena sees the arena from there on: the root's bytes are the root arena, its entry vector
   the root arena from 36 on (only their first len and count * width bytes are read). *)
Definition root_copied (x: inputs) (len cursor: Z) (m: mem) : progress :=
  let m := set_root_copy m (mk_sdt (i_address x) 0 len (cursor mod 2 ^ 32)) in
  let bs := m_root m in
  let st := validate len bs (Some (if i_kind x =? 1 then RSDT else XSDT)) in
  if negb (st =? S_OK) then Return st None m
  else match decode_entries (i_kind x) len with
  | inl st => Return st None m
  | inr (count, w) =>
    let m := set_entries m count w in
    match decode_addresses (sublist HEADER_BYTES (Zlength bs) bs) w count with
    | inl st => Return st None m
    | inr addresses => tables_start x addresses m
    end
  end.

(* Table l_entry l's stream ended (acpi_copy_sdt wrote its slot): its placement and its cursor. *)
Definition table_copied (x: inputs) (l: tloop) (len cursor: Z) (m: mem) : progress :=
  let next := cursor mod 2 ^ 32 in
  let m := add_slot m (mk_sdt (Znth (l_entry l) (l_addresses l)) (l_offset l) len next) in
  if table_capacity x - l_offset l <? padded len then Return S_BUDGET None m
  else if negb (next =? l_offset l + padded len) then Return S_STREAM None m
  else Go (Sequencing (set_offset l (l_offset l + padded len)) nil) m.

Definition sdt_copied (x: inputs) (g: target) (len cursor: Z) (m: mem) : progress :=
  match g with
  | TRoot => root_copied x len cursor m
  | TTable l => table_copied x l len cursor m
  end.

(* The verdict of the five stream answers a on the chunk at byte, of n bytes, with the carried cursor: a status,
   or OK. *)
Definition transition (a: list Z) (chunk cursor byte n last: Z) : Z :=
  let status := Znth 0 a in let error := Znth 1 a in let next := Znth 2 a in
  let emitted := Znth 3 a in let exposed := Znth 4 a in
  if error =? 43 then S_BUDGET
  else if error =? 44 then S_LENGTH
  else if error =? 45 then S_ADDRESS
  else if error =? 46 then S_OFFSET
  else if error =? 47 then S_TERMINAL
  else if negb (error =? 0) then S_ERROR
  else if negb (status =? 1) then S_STATUS
  else if negb (next =? byte + n) then S_NEXT_BYTE
  else if negb (exposed =? chunk) then S_EXPOSED
  else if (last =? 0) && negb (emitted =? cursor) then S_PARTIAL_CURSOR
  else if negb (last =? 0) && (emitted <=? cursor) then S_FINAL_CURSOR
  else S_OK.

(* One answer r in stage s, with mem m. *)
Definition step (x: inputs) (s: stage) (m: mem) (r: reply) : progress :=
  match s with
  | Copying g CHeader =>
    let bs := reply_bytes r in
    let m := write m DHeader bs in
    if reply_value r =? 0 then Return S_PHYSICAL None m
    else
      let len := little (sublist 4 8 bs) in
      if (len <? HEADER_BYTES) || (MAX_SDT_BYTES <? len) || (capacity_of x g <? len)
      then Return S_SDT_LENGTH None m
      else Go (Copying g (CBody len)) m
  | Copying g (CBody len) =>
    let bs := reply_bytes r in
    let m := write m (dest_of g) bs in
    if reply_value r =? 0 then Return S_PHYSICAL None m
    else Go (Copying g (CChunk len bs (cursor_of g) 0 nil)) m
  | Copying g (CChunk len bs cursor byte cur) =>
    let a := cur ++ [reply_value r] in
    if Zlength a <? 5 then Go (Copying g (CChunk len bs cursor byte a)) m
    else
      let n := chunk_bytes len byte in
      let last := terminal len byte in
      let st := transition a (little (sublist byte (byte + n) bs)) cursor byte n last in
      if negb (st =? S_OK) then Return st None m
      else
        let cursor' := if last =? 0 then cursor else Znth 3 a in
        if Znth 2 a <? len then Go (Copying g (CChunk len bs cursor' (Znth 2 a) nil)) m
        else sdt_copied x g len cursor' m
  | Sequencing l cur =>
    let a := cur ++ [reply_value r] in
    if Zlength a <? 3 then Go (Sequencing l a) m
    else if negb (Znth 0 a =? 1) || negb (Znth 1 a =? 0) || negb (Znth 2 a =? l_entry l + 1)
    then Return S_SEQUENCE None m
    else
      let l := set_ordinal l (Znth 2 a) in
      if l_entry l + 1 <? Zlength (l_addresses l) then begin_table x (next_entry l) m
      else tables_done (Zlength (l_addresses l)) m
  end.

(* The pipeline before its first call: the selection check, then the root's acpi_copy_sdt. *)
Definition start (x: inputs) : progress :=
  if negb ((i_kind x =? 1) || (i_kind x =? 2)) || (i_address x =? 0)
  then Return S_ROOT_SELECTION None (initial x)
  else begin_sdt x TRoot (initial x).

(* Decidable equality of calls, argument by argument. *)
Definition dest_eqb (a b: dest) : bool :=
  match a, b with
  | DHeader, DHeader => true
  | DRoot, DRoot => true
  | DTables o, DTables o' => o =? o'
  | _, _ => false
  end.

Definition call_eqb (a b: call) : bool :=
  match a, b with
  | Copy ad d n, Copy ad' d' n' => (ad =? ad') && dest_eqb d d' && (n =? n')
  | Stream a1 a2 a3 a4 a5 a6 a7 a8 a9, Stream b1 b2 b3 b4 b5 b6 b7 b8 b9 =>
      (a1 =? b1) && (a2 =? b2) && (a3 =? b3) && (a4 =? b4) && (a5 =? b5) && (a6 =? b6) && (a7 =? b7) &&
      (a8 =? b8) && (a9 =? b9)
  | Sequence a1 a2 a3 a4 a5 a6, Sequence b1 b2 b3 b4 b5 b6 =>
      (a1 =? b1) && (a2 =? b2) && (a3 =? b3) && (a4 =? b4) && (a5 =? b5) && (a6 =? b6)
  | _, _ => false
  end.

(* The pipeline after the answers h from progress p: Some (Go s m) while it would call again, Some (Return ..)
   when it returned after the last answer (or before any), None when h is not its sequence of calls. *)
Fixpoint run (x: inputs) (p: progress) (h: list answer) : option progress :=
  match h with
  | nil => Some p
  | (c, r) :: rest =>
    match p with
    | Go s m => if call_eqb c (expected x s) && fits c r then run x (step x s m r) rest else None
    | Return _ _ _ => None
    end
  end.

(* The call the pipeline makes after the answers h, if it calls again. *)
Definition next_call (x: inputs) (h: list answer) : option call :=
  match run x (start x) h with Some (Go s _) => Some (expected x s) | _ => None end.

(* The len bytes destination d holds after the answers h, when the pipeline calls again. *)
Definition holds (x: inputs) (h: list answer) (d: dest) (len: Z) : list Z :=
  match run x (start x) h with Some (Go _ m) => region m d len | _ => nil end.

(* The pipeline's outcome when it returns after the answers h: its status, (table_count, the MADT's slot) on OK,
   and what it leaves in the storage and the result. *)
Definition outcome : Type := (Z * option (Z * Z) * mem)%type.

Definition pipeline (x: inputs) (h: list answer) : option outcome :=
  match run x (start x) h with Some (Return st pub m) => Some (st, pub, m) | _ => None end.

(* ---------------------------------------------------------------------- *)
(* Facts about the machine itself.                                        *)
(* ---------------------------------------------------------------------- *)

Lemma dest_eqb_refl: forall d, dest_eqb d d = true.
Proof. destruct d; simpl; auto using Z.eqb_refl. Qed.

Lemma dest_eqb_true: forall a b, dest_eqb a b = true -> a = b.
Proof. destruct a, b; simpl; intros H; try discriminate; auto. apply Z.eqb_eq in H; subst; auto. Qed.

Lemma call_eqb_refl: forall c, call_eqb c c = true.
Proof. destruct c; simpl; rewrite ?dest_eqb_refl, ?Z.eqb_refl; reflexivity. Qed.

Lemma call_eqb_true: forall a b, call_eqb a b = true -> a = b.
Proof.
  destruct a, b; simpl; intros H; try discriminate;
    repeat match goal with H: (_ && _) = true |- _ => apply andb_prop in H; destruct H end;
    repeat match goal with H: (_ =? _) = true |- _ => apply Z.eqb_eq in H; subst end;
    repeat match goal with H: dest_eqb _ _ = true |- _ => apply dest_eqb_true in H; subst end;
    reflexivity.
Qed.

Lemma run_app: forall x h1 h2 p,
  run x p (h1 ++ h2) = match run x p h1 with Some p' => run x p' h2 | None => None end.
Proof.
  induction h1 as [ | [c r] h1 IH]; intros h2 p; simpl; [ reflexivity | ].
  destruct p as [s m | st pub m]; [ | reflexivity ].
  destruct (call_eqb c (expected x s) && fits c r); [ apply IH | reflexivity ].
Qed.

(* The pipeline making the call c = expected x s and getting the answer r. *)
Lemma run_snoc: forall x h s m c r,
  run x (start x) h = Some (Go s m) -> c = expected x s -> fits c r = true ->
  run x (start x) (h ++ [(c, r)]) = Some (step x s m r).
Proof.
  intros x h s m c r H E F. rewrite run_app, H. simpl. subst c. rewrite call_eqb_refl, F. reflexivity.
Qed.

Lemma next_call_run: forall x h c,
  next_call x h = Some c -> exists s m, run x (start x) h = Some (Go s m) /\ c = expected x s.
Proof.
  unfold next_call. intros x h c H.
  destruct (run x (start x) h) as [[s m | st pub m] | ]; inversion H; eauto.
Qed.

Lemma holds_run: forall x h s m d len,
  run x (start x) h = Some (Go s m) -> holds x h d len = region m d len.
Proof. unfold holds. intros x h s m d len H. rewrite H. reflexivity. Qed.

(* Every return of the model publishes (table_count, MADT) exactly when its status is OK. *)
Definition publishes_iff_ok (p: progress) : Prop :=
  match p with Return st pub _ => (st = S_OK <-> pub <> None) | Go _ _ => True end.

Lemma ret_none_pub: forall st m, st <> S_OK -> publishes_iff_ok (Return st None m).
Proof. intros. simpl. split; [ congruence | tauto ]. Qed.

Lemma decode_entries_inl: forall k l st, decode_entries k l = inl st -> st <> S_OK.
Proof.
  unfold decode_entries. intros k l st H.
  repeat match type of H with context [if ?b then _ else _] => destruct b end;
    inversion H; subst; unfold S_OK; discriminate.
Qed.

Lemma decode_from_inl: forall vec w es prior st, decode_from vec w es prior = inl st -> st <> S_OK.
Proof.
  induction es as [ | e es IH]; simpl; intros prior st H; [ discriminate | ].
  repeat match type of H with context [if ?b then _ else _] => destruct b end;
    try (inversion H; subst; unfold S_OK; discriminate); eauto.
Qed.

Lemma validate_ok_or: forall len bs sig, validate len bs sig = S_OK \/ validate len bs sig <> S_OK.
Proof. intros. destruct (Z.eq_dec (validate len bs sig) S_OK); auto. Qed.

Lemma select_from_inl: forall T ss i sel st, select_from T ss i sel = inl st -> st <> S_OK.
Proof.
  induction ss as [ | s ss IH]; simpl; intros i sel st H.
  - destruct sel; inversion H; subst; unfold S_OK; discriminate.
  - destruct (negb (validate (s_length s) (sublist (s_offset s) (Zlength T) T) None =? S_OK)) eqn:E.
    + inversion H; subst. intro C. rewrite C in E. discriminate.
    + destruct (signature_matches _ _ _); [ destruct sel; [ inversion H; subst; unfold S_OK; discriminate | ] | ];
        eauto.
Qed.

Lemma begin_sdt_pub: forall x g m, publishes_iff_ok (begin_sdt x g m).
Proof. intros. unfold begin_sdt. destruct (_ <? _); [ apply ret_none_pub; unfold S_OK; discriminate | exact I ]. Qed.

Lemma begin_table_pub: forall x l m, publishes_iff_ok (begin_table x l m).
Proof. intros. unfold begin_table. destruct (_ <=? _); [ apply ret_none_pub; unfold S_OK; discriminate | apply begin_sdt_pub ]. Qed.

Lemma tables_done_pub: forall c m, publishes_iff_ok (tables_done c m).
Proof.
  intros. unfold tables_done, select_madt. destruct (select_from _ _ _ _) eqn:E.
  - apply ret_none_pub. eapply select_from_inl; eauto.
  - simpl. split; [ intros _; discriminate | auto ].
Qed.

Lemma sdt_copied_pub: forall x g len cursor m, publishes_iff_ok (sdt_copied x g len cursor m).
Proof.
  intros. destruct g as [ | l]; simpl.
  - unfold root_copied. cbv zeta.
    destruct (negb (validate _ _ _ =? S_OK)) eqn:E.
    + apply ret_none_pub. intro C. rewrite C in E. discriminate.
    + destruct (decode_entries _ _) as [st | [count w]] eqn:D.
      * apply ret_none_pub. eapply decode_entries_inl; eauto.
      * destruct (decode_addresses _ _ _) as [st | a] eqn:A.
        -- apply ret_none_pub. eapply decode_from_inl; eauto.
        -- unfold tables_start. destruct (_ =? 0); [ apply ret_none_pub; unfold S_OK; discriminate | apply begin_table_pub ].
  - unfold table_copied. cbv zeta.
    destruct (_ <? _); [ apply ret_none_pub; unfold S_OK; discriminate | ].
    destruct (negb _); [ apply ret_none_pub; unfold S_OK; discriminate | exact I ].
Qed.

Lemma step_pub: forall x s m r, publishes_iff_ok (step x s m r).
Proof.
  intros. destruct s as [g c | l cur]; [ destruct c | ]; unfold step; cbv zeta.
  - destruct (reply_value r =? 0); [ apply ret_none_pub; unfold S_OK; discriminate | ].
    destruct (_ || _); [ apply ret_none_pub; unfold S_OK; discriminate | exact I ].
  - destruct (reply_value r =? 0); [ apply ret_none_pub; unfold S_OK; discriminate | exact I ].
  - destruct (_ <? 5); [ exact I | ].
    destruct (negb (transition _ _ _ _ _ _ =? S_OK)) eqn:E.
    + apply ret_none_pub. intro C. rewrite C in E. discriminate.
    + destruct (_ <? len); [ exact I | apply sdt_copied_pub ].
  - destruct (_ <? 3); [ exact I | ].
    destruct (_ || _); [ apply ret_none_pub; unfold S_OK; discriminate | ].
    destruct (_ <? _); [ apply begin_table_pub | apply tables_done_pub ].
Qed.

Lemma run_pub: forall x h p q, publishes_iff_ok p -> run x p h = Some q -> publishes_iff_ok q.
Proof.
  induction h as [ | [c r] h IH]; simpl; intros p q P H.
  - inversion H; subst; auto.
  - destruct p as [s m | st pub m]; [ | discriminate ].
    destruct (_ && _); [ | discriminate ]. eapply IH; [ apply step_pub | eauto ].
Qed.

Lemma start_pub: forall x, publishes_iff_ok (start x).
Proof.
  intros. unfold start. destruct (_ || _); [ apply ret_none_pub; unfold S_OK; discriminate | apply begin_sdt_pub ].
Qed.

(* The result names a table count and a MADT exactly on OK. *)
Lemma pipeline_published: forall x h st pub m,
  pipeline x h = Some (st, pub, m) -> (st = S_OK <-> pub <> None).
Proof.
  unfold pipeline. intros x h st pub m H.
  destruct (run x (start x) h) as [[s m' | st' pub' m'] | ] eqn:R; inversion H; subst.
  apply (run_pub x h (start x) (Return st pub m) (start_pub x) R).
Qed.
