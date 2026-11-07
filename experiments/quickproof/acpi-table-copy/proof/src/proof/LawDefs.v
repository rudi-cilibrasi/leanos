(* Law table_copy_exact: the law's oracle Ora_law (the harness's global `law` as its fields, and the two
   expectation arenas root_expect and tables_expect), as the oracle predicate of the protocol of AcpiSpecs, and the
   specifications of the harness's helpers.

   The law's state is the record lst (its fields that change while the pipeline runs); the fields that are the
   pipeline's arguments (kind, address, the storage's three pointers and two capacities) are functions of the
   inputs and the place, and header_expect and the two expectation arenas hold what the model's mem says the
   header scratch and the two arenas hold.  The record is a function of the run of the model (J): while the
   pipeline calls (Go) it is the stage's (go_inv), and once the pipeline returned (Return) it is what main's checks
   need of it (ret_inv).  In both, mem_rel ties the law's root, entries and copy records to the model's. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosAcpi.harness.table_copy_exact.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.LawProg.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[export] Existing Instance LawProg.LCS.

Definition t_law := Tstruct _law__1 noattr.

(* EXPECT_* and VERDICT_TABLES of harness/table_copy_exact.h *)
Definition E_HEADER : Z := 0.
Definition E_BODY : Z := 1.
Definition E_STREAM : Z := 2.
Definition E_SEQUENCE : Z := 3.
Definition E_NOTHING : Z := 4.
Definition VERDICT_TABLES : Z := 255.

(* The mutable fields of struct law, in its order (header_expect apart). *)
Record lst : Type := mk_lst {
  w_expect: Z; w_verdict: Z; w_is_root: Z; w_table: Z; w_sdt_address: Z;
  w_dest: val; w_dexp: val; w_capacity: Z; w_length: Z; w_cursor: Z; w_byte: Z; w_word: Z;
  w_answer: list Z;
  w_root_done: Z; w_root_length: Z; w_entries_done: Z; w_width: Z; w_count: Z; w_root_cursor: Z;
  w_addresses: list Z; w_arena: Z; w_ended: Z; w_offsets: list Z; w_lengths: list Z; w_finals: list Z;
  w_ordinal: Z }.

Definition set_expect (s: lst) (v: Z) : lst :=
  mk_lst v (w_verdict s) (w_is_root s) (w_table s) (w_sdt_address s) (w_dest s) (w_dexp s) (w_capacity s) (w_length s) (w_cursor s) (w_byte s) (w_word s) (w_answer s) (w_root_done s) (w_root_length s) (w_entries_done s) (w_width s) (w_count s) (w_root_cursor s) (w_addresses s) (w_arena s) (w_ended s) (w_offsets s) (w_lengths s) (w_finals s) (w_ordinal s).
Definition set_verdict (s: lst) (v: Z) : lst :=
  mk_lst (w_expect s) v (w_is_root s) (w_table s) (w_sdt_address s) (w_dest s) (w_dexp s) (w_capacity s) (w_length s) (w_cursor s) (w_byte s) (w_word s) (w_answer s) (w_root_done s) (w_root_length s) (w_entries_done s) (w_width s) (w_count s) (w_root_cursor s) (w_addresses s) (w_arena s) (w_ended s) (w_offsets s) (w_lengths s) (w_finals s) (w_ordinal s).
Definition set_is_root (s: lst) (v: Z) : lst :=
  mk_lst (w_expect s) (w_verdict s) v (w_table s) (w_sdt_address s) (w_dest s) (w_dexp s) (w_capacity s) (w_length s) (w_cursor s) (w_byte s) (w_word s) (w_answer s) (w_root_done s) (w_root_length s) (w_entries_done s) (w_width s) (w_count s) (w_root_cursor s) (w_addresses s) (w_arena s) (w_ended s) (w_offsets s) (w_lengths s) (w_finals s) (w_ordinal s).
Definition set_table (s: lst) (v: Z) : lst :=
  mk_lst (w_expect s) (w_verdict s) (w_is_root s) v (w_sdt_address s) (w_dest s) (w_dexp s) (w_capacity s) (w_length s) (w_cursor s) (w_byte s) (w_word s) (w_answer s) (w_root_done s) (w_root_length s) (w_entries_done s) (w_width s) (w_count s) (w_root_cursor s) (w_addresses s) (w_arena s) (w_ended s) (w_offsets s) (w_lengths s) (w_finals s) (w_ordinal s).
Definition set_sdt_address (s: lst) (v: Z) : lst :=
  mk_lst (w_expect s) (w_verdict s) (w_is_root s) (w_table s) v (w_dest s) (w_dexp s) (w_capacity s) (w_length s) (w_cursor s) (w_byte s) (w_word s) (w_answer s) (w_root_done s) (w_root_length s) (w_entries_done s) (w_width s) (w_count s) (w_root_cursor s) (w_addresses s) (w_arena s) (w_ended s) (w_offsets s) (w_lengths s) (w_finals s) (w_ordinal s).
Definition set_dest (s: lst) (v: val) : lst :=
  mk_lst (w_expect s) (w_verdict s) (w_is_root s) (w_table s) (w_sdt_address s) v (w_dexp s) (w_capacity s) (w_length s) (w_cursor s) (w_byte s) (w_word s) (w_answer s) (w_root_done s) (w_root_length s) (w_entries_done s) (w_width s) (w_count s) (w_root_cursor s) (w_addresses s) (w_arena s) (w_ended s) (w_offsets s) (w_lengths s) (w_finals s) (w_ordinal s).
Definition set_dexp (s: lst) (v: val) : lst :=
  mk_lst (w_expect s) (w_verdict s) (w_is_root s) (w_table s) (w_sdt_address s) (w_dest s) v (w_capacity s) (w_length s) (w_cursor s) (w_byte s) (w_word s) (w_answer s) (w_root_done s) (w_root_length s) (w_entries_done s) (w_width s) (w_count s) (w_root_cursor s) (w_addresses s) (w_arena s) (w_ended s) (w_offsets s) (w_lengths s) (w_finals s) (w_ordinal s).
Definition set_capacity (s: lst) (v: Z) : lst :=
  mk_lst (w_expect s) (w_verdict s) (w_is_root s) (w_table s) (w_sdt_address s) (w_dest s) (w_dexp s) v (w_length s) (w_cursor s) (w_byte s) (w_word s) (w_answer s) (w_root_done s) (w_root_length s) (w_entries_done s) (w_width s) (w_count s) (w_root_cursor s) (w_addresses s) (w_arena s) (w_ended s) (w_offsets s) (w_lengths s) (w_finals s) (w_ordinal s).
Definition set_length (s: lst) (v: Z) : lst :=
  mk_lst (w_expect s) (w_verdict s) (w_is_root s) (w_table s) (w_sdt_address s) (w_dest s) (w_dexp s) (w_capacity s) v (w_cursor s) (w_byte s) (w_word s) (w_answer s) (w_root_done s) (w_root_length s) (w_entries_done s) (w_width s) (w_count s) (w_root_cursor s) (w_addresses s) (w_arena s) (w_ended s) (w_offsets s) (w_lengths s) (w_finals s) (w_ordinal s).
Definition set_cursor (s: lst) (v: Z) : lst :=
  mk_lst (w_expect s) (w_verdict s) (w_is_root s) (w_table s) (w_sdt_address s) (w_dest s) (w_dexp s) (w_capacity s) (w_length s) v (w_byte s) (w_word s) (w_answer s) (w_root_done s) (w_root_length s) (w_entries_done s) (w_width s) (w_count s) (w_root_cursor s) (w_addresses s) (w_arena s) (w_ended s) (w_offsets s) (w_lengths s) (w_finals s) (w_ordinal s).
Definition set_byte (s: lst) (v: Z) : lst :=
  mk_lst (w_expect s) (w_verdict s) (w_is_root s) (w_table s) (w_sdt_address s) (w_dest s) (w_dexp s) (w_capacity s) (w_length s) (w_cursor s) v (w_word s) (w_answer s) (w_root_done s) (w_root_length s) (w_entries_done s) (w_width s) (w_count s) (w_root_cursor s) (w_addresses s) (w_arena s) (w_ended s) (w_offsets s) (w_lengths s) (w_finals s) (w_ordinal s).
Definition set_word (s: lst) (v: Z) : lst :=
  mk_lst (w_expect s) (w_verdict s) (w_is_root s) (w_table s) (w_sdt_address s) (w_dest s) (w_dexp s) (w_capacity s) (w_length s) (w_cursor s) (w_byte s) v (w_answer s) (w_root_done s) (w_root_length s) (w_entries_done s) (w_width s) (w_count s) (w_root_cursor s) (w_addresses s) (w_arena s) (w_ended s) (w_offsets s) (w_lengths s) (w_finals s) (w_ordinal s).
Definition set_answer (s: lst) (v: list Z) : lst :=
  mk_lst (w_expect s) (w_verdict s) (w_is_root s) (w_table s) (w_sdt_address s) (w_dest s) (w_dexp s) (w_capacity s) (w_length s) (w_cursor s) (w_byte s) (w_word s) v (w_root_done s) (w_root_length s) (w_entries_done s) (w_width s) (w_count s) (w_root_cursor s) (w_addresses s) (w_arena s) (w_ended s) (w_offsets s) (w_lengths s) (w_finals s) (w_ordinal s).
Definition set_root_done (s: lst) (v: Z) : lst :=
  mk_lst (w_expect s) (w_verdict s) (w_is_root s) (w_table s) (w_sdt_address s) (w_dest s) (w_dexp s) (w_capacity s) (w_length s) (w_cursor s) (w_byte s) (w_word s) (w_answer s) v (w_root_length s) (w_entries_done s) (w_width s) (w_count s) (w_root_cursor s) (w_addresses s) (w_arena s) (w_ended s) (w_offsets s) (w_lengths s) (w_finals s) (w_ordinal s).
Definition set_root_length (s: lst) (v: Z) : lst :=
  mk_lst (w_expect s) (w_verdict s) (w_is_root s) (w_table s) (w_sdt_address s) (w_dest s) (w_dexp s) (w_capacity s) (w_length s) (w_cursor s) (w_byte s) (w_word s) (w_answer s) (w_root_done s) v (w_entries_done s) (w_width s) (w_count s) (w_root_cursor s) (w_addresses s) (w_arena s) (w_ended s) (w_offsets s) (w_lengths s) (w_finals s) (w_ordinal s).
Definition set_entries_done (s: lst) (v: Z) : lst :=
  mk_lst (w_expect s) (w_verdict s) (w_is_root s) (w_table s) (w_sdt_address s) (w_dest s) (w_dexp s) (w_capacity s) (w_length s) (w_cursor s) (w_byte s) (w_word s) (w_answer s) (w_root_done s) (w_root_length s) v (w_width s) (w_count s) (w_root_cursor s) (w_addresses s) (w_arena s) (w_ended s) (w_offsets s) (w_lengths s) (w_finals s) (w_ordinal s).
Definition set_width (s: lst) (v: Z) : lst :=
  mk_lst (w_expect s) (w_verdict s) (w_is_root s) (w_table s) (w_sdt_address s) (w_dest s) (w_dexp s) (w_capacity s) (w_length s) (w_cursor s) (w_byte s) (w_word s) (w_answer s) (w_root_done s) (w_root_length s) (w_entries_done s) v (w_count s) (w_root_cursor s) (w_addresses s) (w_arena s) (w_ended s) (w_offsets s) (w_lengths s) (w_finals s) (w_ordinal s).
Definition set_count (s: lst) (v: Z) : lst :=
  mk_lst (w_expect s) (w_verdict s) (w_is_root s) (w_table s) (w_sdt_address s) (w_dest s) (w_dexp s) (w_capacity s) (w_length s) (w_cursor s) (w_byte s) (w_word s) (w_answer s) (w_root_done s) (w_root_length s) (w_entries_done s) (w_width s) v (w_root_cursor s) (w_addresses s) (w_arena s) (w_ended s) (w_offsets s) (w_lengths s) (w_finals s) (w_ordinal s).
Definition set_root_cursor (s: lst) (v: Z) : lst :=
  mk_lst (w_expect s) (w_verdict s) (w_is_root s) (w_table s) (w_sdt_address s) (w_dest s) (w_dexp s) (w_capacity s) (w_length s) (w_cursor s) (w_byte s) (w_word s) (w_answer s) (w_root_done s) (w_root_length s) (w_entries_done s) (w_width s) (w_count s) v (w_addresses s) (w_arena s) (w_ended s) (w_offsets s) (w_lengths s) (w_finals s) (w_ordinal s).
Definition set_addresses (s: lst) (v: list Z) : lst :=
  mk_lst (w_expect s) (w_verdict s) (w_is_root s) (w_table s) (w_sdt_address s) (w_dest s) (w_dexp s) (w_capacity s) (w_length s) (w_cursor s) (w_byte s) (w_word s) (w_answer s) (w_root_done s) (w_root_length s) (w_entries_done s) (w_width s) (w_count s) (w_root_cursor s) v (w_arena s) (w_ended s) (w_offsets s) (w_lengths s) (w_finals s) (w_ordinal s).
Definition set_arena (s: lst) (v: Z) : lst :=
  mk_lst (w_expect s) (w_verdict s) (w_is_root s) (w_table s) (w_sdt_address s) (w_dest s) (w_dexp s) (w_capacity s) (w_length s) (w_cursor s) (w_byte s) (w_word s) (w_answer s) (w_root_done s) (w_root_length s) (w_entries_done s) (w_width s) (w_count s) (w_root_cursor s) (w_addresses s) v (w_ended s) (w_offsets s) (w_lengths s) (w_finals s) (w_ordinal s).
Definition set_ended (s: lst) (v: Z) : lst :=
  mk_lst (w_expect s) (w_verdict s) (w_is_root s) (w_table s) (w_sdt_address s) (w_dest s) (w_dexp s) (w_capacity s) (w_length s) (w_cursor s) (w_byte s) (w_word s) (w_answer s) (w_root_done s) (w_root_length s) (w_entries_done s) (w_width s) (w_count s) (w_root_cursor s) (w_addresses s) (w_arena s) v (w_offsets s) (w_lengths s) (w_finals s) (w_ordinal s).
Definition set_offsets (s: lst) (v: list Z) : lst :=
  mk_lst (w_expect s) (w_verdict s) (w_is_root s) (w_table s) (w_sdt_address s) (w_dest s) (w_dexp s) (w_capacity s) (w_length s) (w_cursor s) (w_byte s) (w_word s) (w_answer s) (w_root_done s) (w_root_length s) (w_entries_done s) (w_width s) (w_count s) (w_root_cursor s) (w_addresses s) (w_arena s) (w_ended s) v (w_lengths s) (w_finals s) (w_ordinal s).
Definition set_lengths (s: lst) (v: list Z) : lst :=
  mk_lst (w_expect s) (w_verdict s) (w_is_root s) (w_table s) (w_sdt_address s) (w_dest s) (w_dexp s) (w_capacity s) (w_length s) (w_cursor s) (w_byte s) (w_word s) (w_answer s) (w_root_done s) (w_root_length s) (w_entries_done s) (w_width s) (w_count s) (w_root_cursor s) (w_addresses s) (w_arena s) (w_ended s) (w_offsets s) v (w_finals s) (w_ordinal s).
Definition set_finals (s: lst) (v: list Z) : lst :=
  mk_lst (w_expect s) (w_verdict s) (w_is_root s) (w_table s) (w_sdt_address s) (w_dest s) (w_dexp s) (w_capacity s) (w_length s) (w_cursor s) (w_byte s) (w_word s) (w_answer s) (w_root_done s) (w_root_length s) (w_entries_done s) (w_width s) (w_count s) (w_root_cursor s) (w_addresses s) (w_arena s) (w_ended s) (w_offsets s) (w_lengths s) v (w_ordinal s).
Definition set_word_ordinal (s: lst) (v: Z) : lst :=
  mk_lst (w_expect s) (w_verdict s) (w_is_root s) (w_table s) (w_sdt_address s) (w_dest s) (w_dexp s) (w_capacity s) (w_length s) (w_cursor s) (w_byte s) (w_word s) (w_answer s) (w_root_done s) (w_root_length s) (w_entries_done s) (w_width s) (w_count s) (w_root_cursor s) (w_addresses s) (w_arena s) (w_ended s) (w_offsets s) (w_lengths s) (w_finals s) v.


Ltac lst_cbn := cbn [w_expect w_verdict w_is_root w_table w_sdt_address w_dest w_dexp w_capacity w_length w_cursor
  w_byte w_word w_answer w_root_done w_root_length w_entries_done w_width w_count w_root_cursor w_addresses w_arena
  w_ended w_offsets w_lengths w_finals w_ordinal
  set_expect set_verdict set_is_root set_table set_sdt_address set_dest set_dexp set_capacity set_length set_cursor
  set_byte set_word set_answer set_root_done set_root_length set_entries_done set_width set_count set_root_cursor
  set_addresses set_arena set_ended set_offsets set_lengths set_finals set_word_ordinal].

(* struct law, field by field: the arguments (x, pl), header_expect (hx), the expectation arenas' pointers (re, te)
   and the record s. *)
Definition lfields (q: val) (x: inputs) (pl: place) (re te: val) (hx: list Z) (s: lst) : mpred :=
 (field_at Ews t_law (DOT _kind) (vl (i_kind x)) q *
  field_at Ews t_law (DOT _address) (vl (i_address x)) q *
  field_at Ews t_law (DOT _header) (p_header pl) q *
  field_at Ews t_law (DOT _root) (p_root pl) q *
  field_at Ews t_law (DOT _tables) (p_tables pl) q *
  field_at Ews t_law (DOT _root_capacity) (vi (root_capacity x)) q *
  field_at Ews t_law (DOT _table_capacity) (vi (table_capacity x)) q *
  field_at Ews t_law (DOT _header_expect) (bytes_val hx) q *
  field_at Ews t_law (DOT _root_expect) re q *
  field_at Ews t_law (DOT _tables_expect) te q *
  field_at Ews t_law (DOT _expect) (vi (w_expect s)) q *
  field_at Ews t_law (DOT _verdict) (vi (w_verdict s)) q *
  field_at Ews t_law (DOT _is_root) (vi (w_is_root s)) q *
  field_at Ews t_law (DOT _table) (vi (w_table s)) q *
  field_at Ews t_law (DOT _sdt_address) (vl (w_sdt_address s)) q *
  field_at Ews t_law (DOT _destination) (w_dest s) q *
  field_at Ews t_law (DOT _destination_expect) (w_dexp s) q *
  field_at Ews t_law (DOT _capacity) (vi (w_capacity s)) q *
  field_at Ews t_law (DOT _length) (vi (w_length s)) q *
  field_at Ews t_law (DOT _cursor) (vl (w_cursor s)) q *
  field_at Ews t_law (DOT _byte) (vl (w_byte s)) q *
  field_at Ews t_law (DOT _word) (vi (w_word s)) q *
  field_at Ews t_law (DOT _answer) (map vl (w_answer s)) q *
  field_at Ews t_law (DOT _root_done) (vi (w_root_done s)) q *
  field_at Ews t_law (DOT _root_length) (vi (w_root_length s)) q *
  field_at Ews t_law (DOT _entries_done) (vi (w_entries_done s)) q *
  field_at Ews t_law (DOT _width) (vi (w_width s)) q *
  field_at Ews t_law (DOT _count) (vi (w_count s)) q *
  field_at Ews t_law (DOT _root_cursor) (vl (w_root_cursor s)) q *
  field_at Ews t_law (DOT _addresses) (map vl (w_addresses s)) q *
  field_at Ews t_law (DOT _arena) (vi (w_arena s)) q *
  field_at Ews t_law (DOT _ended) (vi (w_ended s)) q *
  field_at Ews t_law (DOT _offsets) (map vi (w_offsets s)) q *
  field_at Ews t_law (DOT _lengths) (map vi (w_lengths s)) q *
  field_at Ews t_law (DOT _finals) (map vl (w_finals s)) q *
  field_at Ews t_law (DOT _ordinal) (vl (w_ordinal s)) q)%logic.

(* The same as the struct's value (LawSplit proves the two equal). *)
Definition law_val (x: inputs) (pl: place) (re te: val) (hx: list Z) (s: lst) : reptype t_law :=
  (vl (i_kind x), (vl (i_address x), (p_header pl, (p_root pl, (p_tables pl, (vi (root_capacity x),
   (vi (table_capacity x), (bytes_val hx, (re, (te, (vi (w_expect s), (vi (w_verdict s), (vi (w_is_root s),
   (vi (w_table s), (vl (w_sdt_address s), (w_dest s, (w_dexp s, (vi (w_capacity s), (vi (w_length s),
   (vl (w_cursor s), (vl (w_byte s), (vi (w_word s), (map vl (w_answer s), (vi (w_root_done s),
   (vi (w_root_length s), (vi (w_entries_done s), (vi (w_width s), (vi (w_count s), (vl (w_root_cursor s),
   (map vl (w_addresses s), (vi (w_arena s), (vi (w_ended s), (map vi (w_offsets s), (map vi (w_lengths s),
   (map vl (w_finals s), vl (w_ordinal s)))))))))))))))))))))))))))))))))))).

(* ---------------------------------------------------------------------- *)
(* The invariant                                                          *)
(* ---------------------------------------------------------------------- *)

(* Every field in its C type's range. *)
Definition lst_ok (s: lst) : Prop :=
  u32_ok (w_expect s) /\ u32_ok (w_verdict s) /\ u32_ok (w_is_root s) /\ u32_ok (w_table s) /\
  u64_ok (w_sdt_address s) /\ u32_ok (w_capacity s) /\ u32_ok (w_length s) /\ u64_ok (w_cursor s) /\
  u64_ok (w_byte s) /\ u32_ok (w_word s) /\ Zlength (w_answer s) = 5 /\ Forall u64_ok (w_answer s) /\
  u32_ok (w_root_done s) /\ u32_ok (w_root_length s) /\ u32_ok (w_entries_done s) /\ u32_ok (w_width s) /\
  u32_ok (w_count s) /\ u64_ok (w_root_cursor s) /\
  Zlength (w_addresses s) = MAX_ENTRIES /\ Forall u64_ok (w_addresses s) /\
  u32_ok (w_arena s) /\ u32_ok (w_ended s) /\
  Zlength (w_offsets s) = MAX_ENTRIES /\ Forall u32_ok (w_offsets s) /\
  Zlength (w_lengths s) = MAX_ENTRIES /\ Forall u32_ok (w_lengths s) /\
  Zlength (w_finals s) = MAX_ENTRIES /\ Forall u64_ok (w_finals s) /\ u64_ok (w_ordinal s).

(* The model's mem: its byte objects as long as the inputs', holding bytes. *)
Definition mem_fit (x: inputs) (m: mem) : Prop :=
  Zlength (m_header m) = HEADER_BYTES /\ Zlength (m_root m) = root_capacity x /\
  Zlength (m_tables m) = table_capacity x /\
  Forall byte_ok (m_header m) /\ Forall byte_ok (m_root m) /\ Forall byte_ok (m_tables m).

#[export] Instance Inhabitant_sdt : Inhabitant sdt := mk_sdt 0 0 0 0.

(* Copy record t as the law keeps it. *)
Definition slot_of (s: lst) (t: Z) : sdt :=
  mk_sdt (Znth t (w_addresses s)) (Znth t (w_offsets s)) (Znth t (w_lengths s)) (Znth t (w_finals s) mod 2 ^ 32).

(* The law's record of what the pipeline wrote: the result's root, its entries, the copy records. *)
Definition mem_rel (x: inputs) (s: lst) (m: mem) : Prop :=
  match m_root_copy m with
  | None => w_root_done s = 0
  | Some sd => w_root_done s = 1 /\ sd = mk_sdt (i_address x) 0 (w_root_length s) (w_root_cursor s mod 2 ^ 32)
  end /\
  match m_entries m with
  | None => w_entries_done s = 0
  | Some (c, w) => w_entries_done s = 1 /\ c = w_count s /\ w = w_width s
  end /\
  w_ended s = Zlength (m_slots m) /\
  (forall t, 0 <= t < Zlength (m_slots m) -> Znth t (m_slots m) = slot_of s t) /\
  Forall (fun sd => HEADER_BYTES <= s_length sd <= MAX_SDT_BYTES) (m_slots m).

(* The copy records ss tile the table arena from off on, in order, each padded to 8, up to e; each one's cursor
   (truncated) is its end. *)
Fixpoint tiles_from (off: Z) (ss: list sdt) (e: Z) : Prop :=
  match ss with
  | nil => e = off
  | sd :: rest =>
      s_offset sd = off /\ s_next sd = off + padded (s_length sd) /\ tiles_from (off + padded (s_length sd)) rest e
  end.
Definition tiled (ss: list sdt) (e: Z) : Prop := tiles_from 0 ss e.

(* The expectation arena of the SDT g, and its destination there. *)
Definition base_exp (re te: val) (g: target) : val := match g with TRoot => re | TTable _ => te end.
Definition dexp_of (re te: val) (g: target) : val :=
  match g with TRoot => re | TTable l => offset_val (l_offset l) te end.

(* A length its header declared that the pipeline copies. *)
Definition len_ok (x: inputs) (g: target) (len: Z) : Prop :=
  HEADER_BYTES <= len <= MAX_SDT_BYTES /\ len <= capacity_of x g.

(* begin_sdt's fields for the SDT g. *)
Definition sdt_inv (x: inputs) (pl: place) (re te: val) (g: target) (s: lst) : Prop :=
  w_is_root s = (match g with TRoot => 1 | TTable _ => 0 end) /\ w_sdt_address s = address_of x g /\
  w_dest s = dest_ptr pl (dest_of g) /\ w_dexp s = dexp_of re te g /\ w_capacity s = capacity_of x g.

(* The tables loop l: the root's entries and addresses, the table, the arena cursor, the ordinal, the copy records
   so far. *)
Definition tab_inv (x: inputs) (l: tloop) (m: mem) (s: lst) : Prop :=
  let n := Zlength (l_addresses l) in
  w_count s = n /\ 1 <= n <= MAX_ENTRIES /\ sublist 0 n (w_addresses s) = l_addresses l /\
  Forall (fun a => 0 < a <= MAX_U32) (l_addresses l) /\ w_table s = l_entry l /\ 0 <= l_entry l < n /\
  w_arena s = l_offset l /\ 0 <= l_offset l /\ w_ordinal s = l_ordinal l /\ tiled (m_slots m) (l_offset l).

(* Copying the SDT g: the root before anything else, or table l_entry l. *)
Definition tgt_inv (x: inputs) (g: target) (m: mem) (s: lst) : Prop :=
  match g with
  | TRoot =>
      (i_kind x = 1 \/ i_kind x = 2) /\ 0 < i_address x <= MAX_U32 /\
      m_root_copy m = None /\ m_entries m = None /\ m_slots m = nil /\ w_arena s = 0 /\ w_ordinal s = 0
  | TTable l =>
      tab_inv x l m s /\ Zlength (m_slots m) = l_entry l /\ Znth (l_entry l) (w_offsets s) = l_offset l /\
      l_offset l < table_capacity x
  end.

(* Inside acpi_copy_sdt on g. *)
Definition cst_inv (x: inputs) (g: target) (m: mem) (c: cstage) (s: lst) : Prop :=
  match c with
  | CHeader => w_expect s = E_HEADER /\ w_cursor s = cursor_of g
  | CBody len => w_expect s = E_BODY /\ w_length s = len /\ w_cursor s = cursor_of g /\ len_ok x g len
  | CChunk len bs cursor byte cur =>
      w_expect s = E_STREAM /\ w_length s = len /\ w_cursor s = cursor /\ w_byte s = byte /\
      w_word s = Zlength cur /\ sublist 0 (Zlength cur) (w_answer s) = cur /\ Zlength cur < 5 /\
      0 <= byte < len /\ region m (dest_of g) len = bs /\ len_ok x g len
  end.

(* At the sequence step of table l_entry l. *)
Definition seq_inv (x: inputs) (l: tloop) (m: mem) (cur: list Z) (s: lst) : Prop :=
  tab_inv x l m s /\ w_expect s = E_SEQUENCE /\ w_word s = Zlength cur /\
  sublist 0 (Zlength cur) (w_answer s) = cur /\ Zlength cur < 3 /\ Zlength (m_slots m) = l_entry l + 1 /\
  l_offset l <= table_capacity x.

Definition go_inv (x: inputs) (pl: place) (re te: val) (st: stage) (m: mem) (s: lst) : Prop :=
  match st with
  | Copying g c => sdt_inv x pl re te g s /\ tgt_inv x g m s /\ cst_inv x g m c s
  | Sequencing l cur => seq_inv x l m cur s
  end.

(* A model function's status. *)
Definition stat {A: Type} (r: Z + A) : Z := match r with inl st => st | inr _ => S_OK end.

(* Returned with st (pub on OK): no call expected; the verdict is st, or VERDICT_TABLES when every table was
   copied and the MADT selection on the final mem decides. *)
Definition ret_inv (x: inputs) (st: Z) (pub: option (Z * Z)) (m: mem) (s: lst) : Prop :=
  w_expect s = E_NOTHING /\
  (w_verdict s = VERDICT_TABLES ->
     w_count s = Zlength (m_slots m) /\ 1 <= w_count s <= MAX_ENTRIES /\ tiled (m_slots m) (w_arena s) /\
     w_arena s <= table_capacity x /\ st = stat (select_madt m) /\
     pub = match select_madt m with inl _ => None | inr i => Some (w_count s, i) end) /\
  (w_verdict s <> VERDICT_TABLES -> st = w_verdict s /\ st <> S_OK /\ pub = None).

Definition mem_of (p: progress) : mem := match p with Go _ m => m | Return _ _ m => m end.

Definition J (x: inputs) (pl: place) (re te: val) (p: progress) (s: lst) : Prop :=
  lst_ok s /\ mem_fit x (mem_of p) /\ mem_rel x s (mem_of p) /\
  match p with
  | Go st m => go_inv x pl re te st m s
  | Return st pub m => ret_inv x st pub m s
  end.

(* The law's oracle: the global `law` (the copy's context) and the two expectation arenas. *)
Definition Ora_law : ORA := fun gv ctx pl x h =>
  EX p: progress, EX s: lst, EX re: val, EX te: val,
    !! (ctx = gv _law /\ inputs_ok x /\ run x (start x) h = Some p /\ J x pl re te p s /\
        isptr (p_header pl) /\ isptr (p_root pl) /\ isptr (p_tables pl) /\ isptr re /\ isptr te) &&
    (lfields (gv _law) x pl re te (m_header (mem_of p)) s *
     data_at Ews (tarray tuchar (root_capacity x)) (bytes_val (m_root (mem_of p))) re *
     data_at Ews (tarray tuchar (table_capacity x)) (bytes_val (m_tables (mem_of p))) te)%logic.

(* ---------------------------------------------------------------------- *)
(* The harness's helpers                                                   *)
(* ---------------------------------------------------------------------- *)

Definition any_u64_spec :=
  DECLARE _any_u64
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tulong ] EX v: Z, PROP (u64_ok v) RETURN (vl v) SEP ().

(* little(p, n), p at byte k of the bytes bs at b. *)
Definition little_spec :=
  DECLARE _little
  WITH sh: share, p: val, b: val, bs: list Z, N: Z, k: Z, n: Z
  PRE [ tptr tuchar, tuint ]
    PROP (readable_share sh; Zlength bs = N; Forall byte_ok bs; 0 <= k; 0 <= n <= 8; k + n <= N;
          p = offset_val k b)
    PARAMS (p; vi n)
    SEP (data_at sh (tarray tuchar N) (bytes_val bs) b)
  POST [ tulong ]
    PROP () RETURN (vl (little (sublist k (k + n) bs)))
    SEP (data_at sh (tarray tuchar N) (bytes_val bs) b).

Definition byte_sum_spec :=
  DECLARE _byte_sum
  WITH sh: share, p: val, b: val, bs: list Z, N: Z, k: Z, n: Z
  PRE [ tptr tuchar, tuint ]
    PROP (readable_share sh; Zlength bs = N; Forall byte_ok bs; 0 <= k; 0 <= n <= Int.max_unsigned; k + n <= N;
          p = offset_val k b)
    PARAMS (p; vi n)
    SEP (data_at sh (tarray tuchar N) (bytes_val bs) b)
  POST [ tuint ]
    PROP () RETURN (vi (fold_left Z.add (sublist k (k + n) bs) 0))
    SEP (data_at sh (tarray tuchar N) (bytes_val bs) b).

Definition padded_spec :=
  DECLARE _padded
  WITH n: Z
  PRE [ tuint ] PROP (0 <= n <= MAX_SDT_BYTES) PARAMS (vi n) SEP ()
  POST [ tuint ] PROP () RETURN (vi (padded n)) SEP ().

(* The four bytes of bs from k are sg. *)
Definition sig_at (bs: list Z) (k: Z) (sg: list Z) : bool :=
  (Znth k bs =? Znth 0 sg) && (Znth (k + 1) bs =? Znth 1 sg) && (Znth (k + 2) bs =? Znth 2 sg) &&
  (Znth (k + 3) bs =? Znth 3 sg).

Definition signature_spec :=
  DECLARE _signature
  WITH sh: share, p: val, b: val, bs: list Z, N: Z, k: Z, c0: Z, c1: Z, c2: Z, c3: Z
  PRE [ tptr tuchar, tuchar, tuchar, tuchar, tuchar ]
    PROP (readable_share sh; Zlength bs = N; Forall byte_ok bs; 0 <= k; k + 4 <= N; p = offset_val k b;
          byte_ok c0; byte_ok c1; byte_ok c2; byte_ok c3)
    PARAMS (p; vi c0; vi c1; vi c2; vi c3)
    SEP (data_at sh (tarray tuchar N) (bytes_val bs) b)
  POST [ tint ]
    PROP () RETURN (vi (if sig_at bs k [c0; c1; c2; c3] then 1 else 0))
    SEP (data_at sh (tarray tuchar N) (bytes_val bs) b).

Definition stop_spec :=
  DECLARE _stop
  WITH q: val, e0: val, v0: val, v: Z
  PRE [ tptr t_law, tuint ]
    PROP (u32_ok v) PARAMS (q; vi v)
    SEP (field_at Ews t_law (DOT _expect) e0 q; field_at Ews t_law (DOT _verdict) v0 q)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (field_at Ews t_law (DOT _expect) (vi E_NOTHING) q; field_at Ews t_law (DOT _verdict) (vi v) q).

Definition begin_sdt_spec :=
  DECLARE _begin_sdt
  WITH q: val, a: Z, d: val, de: val, c: Z, cur: Z, sa0: val, d0: val, de0: val, c0: val, cu0: val, b0: val,
       w0: val, e0: val
  PRE [ tptr t_law, tulong, tptr tuchar, tptr tuchar, tuint, tulong ]
    PROP (u64_ok a; u32_ok c; u64_ok cur; is_pointer_or_null d; is_pointer_or_null de)
    PARAMS (q; vl a; d; de; vi c; vl cur)
    SEP (field_at Ews t_law (DOT _sdt_address) sa0 q; field_at Ews t_law (DOT _destination) d0 q;
         field_at Ews t_law (DOT _destination_expect) de0 q; field_at Ews t_law (DOT _capacity) c0 q;
         field_at Ews t_law (DOT _cursor) cu0 q; field_at Ews t_law (DOT _byte) b0 q;
         field_at Ews t_law (DOT _word) w0 q; field_at Ews t_law (DOT _expect) e0 q)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (field_at Ews t_law (DOT _sdt_address) (vl a) q; field_at Ews t_law (DOT _destination) d q;
         field_at Ews t_law (DOT _destination_expect) de q; field_at Ews t_law (DOT _capacity) (vi c) q;
         field_at Ews t_law (DOT _cursor) (vl cur) q; field_at Ews t_law (DOT _byte) (vl 0) q;
         field_at Ews t_law (DOT _word) (vi 0) q; field_at Ews t_law (DOT _expect) (vi E_HEADER) q).

(* begin_table(m, t): BUDGET when the arena cursor reached the capacity (b), else table t from the arena cursor. *)
Definition begin_table_spec :=
  DECLARE _begin_table
  WITH q: val, t: Z, arena: Z, cap: Z, tb: val, te: val, addrs: list Z, offs: list Z,
       ir0: val, tb0: val, sa0: val, d0: val, de0: val, c0: val, cu0: val, by0: val, w0: val, e0: val, v0: val
  PRE [ tptr t_law, tuint ]
    PROP (0 <= t < MAX_ENTRIES; Zlength addrs = MAX_ENTRIES; Forall u64_ok addrs; Zlength offs = MAX_ENTRIES;
          u32_ok arena; u32_ok cap; isptr tb; isptr te)
    PARAMS (q; vi t)
    SEP (field_at Ews t_law (DOT _arena) (vi arena) q; field_at Ews t_law (DOT _table_capacity) (vi cap) q;
         field_at Ews t_law (DOT _tables) tb q; field_at Ews t_law (DOT _tables_expect) te q;
         field_at Ews t_law (DOT _addresses) (map vl addrs) q; field_at Ews t_law (DOT _offsets) (map vi offs) q;
         field_at Ews t_law (DOT _is_root) ir0 q; field_at Ews t_law (DOT _table) tb0 q;
         field_at Ews t_law (DOT _sdt_address) sa0 q; field_at Ews t_law (DOT _destination) d0 q;
         field_at Ews t_law (DOT _destination_expect) de0 q; field_at Ews t_law (DOT _capacity) c0 q;
         field_at Ews t_law (DOT _cursor) cu0 q; field_at Ews t_law (DOT _byte) by0 q;
         field_at Ews t_law (DOT _word) w0 q; field_at Ews t_law (DOT _expect) e0 q;
         field_at Ews t_law (DOT _verdict) v0 q)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (field_at Ews t_law (DOT _arena) (vi arena) q; field_at Ews t_law (DOT _table_capacity) (vi cap) q;
         field_at Ews t_law (DOT _tables) tb q; field_at Ews t_law (DOT _tables_expect) te q;
         field_at Ews t_law (DOT _addresses) (map vl addrs) q;
         field_at Ews t_law (DOT _offsets) (map vi (if cap <=? arena then offs else upd_Znth t offs arena)) q;
         field_at Ews t_law (DOT _is_root) (if cap <=? arena then ir0 else vi 0) q;
         field_at Ews t_law (DOT _table) (if cap <=? arena then tb0 else vi t) q;
         field_at Ews t_law (DOT _sdt_address) (if cap <=? arena then sa0 else vl (Znth t addrs)) q;
         field_at Ews t_law (DOT _destination) (if cap <=? arena then d0 else offset_val arena tb) q;
         field_at Ews t_law (DOT _destination_expect) (if cap <=? arena then de0 else offset_val arena te) q;
         field_at Ews t_law (DOT _capacity) (if cap <=? arena then c0 else vi (cap - arena)) q;
         field_at Ews t_law (DOT _cursor) (if cap <=? arena then cu0 else vl arena) q;
         field_at Ews t_law (DOT _byte) (if cap <=? arena then by0 else vl 0) q;
         field_at Ews t_law (DOT _word) (if cap <=? arena then w0 else vi 0) q;
         field_at Ews t_law (DOT _expect) (vi (if cap <=? arena then E_NOTHING else E_HEADER)) q;
         field_at Ews t_law (DOT _verdict) (if cap <=? arena then vi S_BUDGET else v0) q).

(* transition(m, chunk, end, last): the C's verdict on the five answers. *)
Definition law_transition (a: list Z) (chunk e last cursor: Z) : Z :=
  let status := Znth 0 a in let error := Znth 1 a in let next := Znth 2 a in
  let emitted := Znth 3 a in let exposed := Znth 4 a in
  if error =? 43 then S_BUDGET
  else if error =? 44 then S_LENGTH
  else if error =? 45 then S_ADDRESS
  else if error =? 46 then S_OFFSET
  else if error =? 47 then S_TERMINAL
  else if negb (error =? 0) then S_ERROR
  else if negb (status =? 1) then S_STATUS
  else if negb (next =? e) then S_NEXT_BYTE
  else if negb (exposed =? chunk) then S_EXPOSED
  else if (last =? 0) && negb (emitted =? cursor) then S_PARTIAL_CURSOR
  else if negb (last =? 0) && (emitted <=? cursor) then S_FINAL_CURSOR
  else S_OK.

Definition transition_spec :=
  DECLARE _transition
  WITH q: val, a: list Z, cursor: Z, chunk: Z, e: Z, last: Z
  PRE [ tptr t_law, tulong, tulong, tulong ]
    PROP (Zlength a = 5; Forall u64_ok a; u64_ok cursor; u64_ok chunk; u64_ok e; u64_ok last)
    PARAMS (q; vl chunk; vl e; vl last)
    SEP (field_at Ews t_law (DOT _answer) (map vl a) q; field_at Ews t_law (DOT _cursor) (vl cursor) q)
  POST [ tuint ]
    PROP () RETURN (vi (law_transition a chunk e last cursor))
    SEP (field_at Ews t_law (DOT _answer) (map vl a) q; field_at Ews t_law (DOT _cursor) (vl cursor) q).

(* madt_verdict(m, &madt) on the copy records ss, the table arena T. *)
Definition madt_verdict_spec :=
  DECLARE _madt_verdict
  WITH q: val, te: val, T: list Z, N: Z, ss: list sdt, offs: list Z, lens: list Z, mp: val, mold: val
  PRE [ tptr t_law, tptr tuint ]
    PROP (Zlength T = N; Forall byte_ok T; Zlength offs = MAX_ENTRIES; Zlength lens = MAX_ENTRIES;
          Zlength ss <= MAX_ENTRIES;
          forall t, 0 <= t < Zlength ss -> s_offset (Znth t ss) = Znth t offs /\ s_length (Znth t ss) = Znth t lens /\
            HEADER_BYTES <= Znth t lens <= MAX_SDT_BYTES /\ 0 <= Znth t offs /\ Znth t offs + Znth t lens <= N)
    PARAMS (q; mp)
    SEP (field_at Ews t_law (DOT _count) (vi (Zlength ss)) q; field_at Ews t_law (DOT _tables_expect) te q;
         field_at Ews t_law (DOT _offsets) (map vi offs) q; field_at Ews t_law (DOT _lengths) (map vi lens) q;
         data_at Ews (tarray tuchar N) (bytes_val T) te; data_at Tsh tuint mold mp)
  POST [ tuint ]
    EX mv: val,
    PROP (match select_from T ss 0 None with inr i => mv = vi i | inl _ => True end)
    RETURN (vi (stat (select_from T ss 0 None)))
    SEP (field_at Ews t_law (DOT _count) (vi (Zlength ss)) q; field_at Ews t_law (DOT _tables_expect) te q;
         field_at Ews t_law (DOT _offsets) (map vi offs) q; field_at Ews t_law (DOT _lengths) (map vi lens) q;
         data_at Ews (tarray tuchar N) (bytes_val T) te; data_at Tsh tuint mv mp).

(* root_copied(m), at the end of the root's stream (the model at sdt_copied x TRoot len cursor m). *)
Definition rc_pre (x: inputs) (pl: place) (re te: val) (s: lst) (m: mem) (len cursor: Z) : Prop :=
  lst_ok s /\ mem_fit x m /\ mem_rel x s m /\ sdt_inv x pl re te TRoot s /\ tgt_inv x TRoot m s /\
  w_length s = len /\ w_cursor s = cursor /\ len_ok x TRoot len /\ inputs_ok x /\
  isptr re /\ isptr te /\ isptr (p_tables pl).

Definition root_copied_spec :=
  DECLARE _root_copied
  WITH q: val, x: inputs, pl: place, re: val, te: val, s: lst, m: mem, len: Z, cursor: Z
  PRE [ tptr t_law ]
    PROP (rc_pre x pl re te s m len cursor)
    PARAMS (q)
    SEP (lfields q x pl re te (m_header m) s;
         data_at Ews (tarray tuchar (root_capacity x)) (bytes_val (m_root m)) re)
  POST [ tvoid ]
    EX s': lst,
    PROP (J x pl re te (root_copied x len cursor m) s')
    RETURN ()
    SEP (lfields q x pl re te (m_header m) s';
         data_at Ews (tarray tuchar (root_capacity x)) (bytes_val (m_root m)) re).

(* table_copied(m), at the end of table l_entry l's stream (the model at sdt_copied x (TTable l) len cursor m). *)
Definition tc_pre (x: inputs) (pl: place) (re te: val) (l: tloop) (s: lst) (m: mem) (len cursor: Z) : Prop :=
  lst_ok s /\ mem_fit x m /\ mem_rel x s m /\ sdt_inv x pl re te (TTable l) s /\ tgt_inv x (TTable l) m s /\
  w_length s = len /\ w_cursor s = cursor /\ len_ok x (TTable l) len /\ inputs_ok x.

Definition table_copied_spec :=
  DECLARE _table_copied
  WITH q: val, x: inputs, pl: place, re: val, te: val, hx: list Z, l: tloop, s: lst, m: mem, len: Z, cursor: Z
  PRE [ tptr t_law ]
    PROP (tc_pre x pl re te l s m len cursor)
    PARAMS (q)
    SEP (lfields q x pl re te hx s)
  POST [ tvoid ]
    EX s': lst,
    PROP (J x pl re te (table_copied x l len cursor m) s')
    RETURN ()
    SEP (lfields q x pl re te hx s').

(* The global variable of the harness, for the functions that use it. *)
Definition Vlaw : varspecs := [(_law, t_law)].
