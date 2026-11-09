(* Pure definitions shared by every proof of leanos_madt_admission (include/madt_generated_admission.h, through
   the wrapper unit patch/madt_admission_unit.c): the four functions main may call, as one state machine over the
   answers of the three Lean exports they call.  No program here.

   The model follows the first comment of harness/admission_exact.c (the law's claim) clause by clause, and its
   stages are those of the law's struct law (harness/admission_exact.h): ExpectEnvelope, ExpectEntries and
   ExpectResult are EXPECT_ENVELOPE, EXPECT_ENTRIES and EXPECT_RESULT with `at`, `state`, the answers so far
   (answer[0 .. word-1]) and `args`; Return is EXPECT_NOTHING with `verdict` and `id`.  Words are Z values in
   their C type's range (uint64_t; bytes 0..255; the length, the executing ID and the prior ID 32-bit); the
   specifications (MgaSpecs.inputs_ok) state those ranges. *)
Require Import VST.floyd.proofauto.
Local Open Scope Z_scope.
Local Open Scope bool_scope.   (* && and || are andb and orb here, not VST's andp and orp *)

(* ---------------------------------------------------------------------- *)
(* The statuses (enum madt_generated_status, in order).                  *)
(* ---------------------------------------------------------------------- *)

Definition S_OK : Z := 0.
Definition S_ENVELOPE_ABI : Z := 1.
Definition S_ENVELOPE_STATUS : Z := 2.
Definition S_ENVELOPE_ERROR : Z := 3.
Definition S_ENVELOPE_NEXT_BYTE : Z := 4.
Definition S_ENVELOPE_EXPOSED : Z := 5.
Definition S_ENVELOPE_LENGTH : Z := 6.
Definition S_ENVELOPE_CHECKSUM : Z := 7.
Definition S_ENTRIES_BOUNDS : Z := 8.
Definition S_ENTRIES_ABI : Z := 9.
Definition S_ENTRIES_STATUS : Z := 10.
Definition S_ENTRIES_ERROR : Z := 11.
Definition S_ENTRIES_NEXT_OFFSET : Z := 12.
Definition S_ENTRIES_EXPOSED : Z := 13.
Definition S_ENTRIES_RECORD : Z := 14.
Definition S_ENTRIES_ENABLED : Z := 15.
Definition S_ENTRIES_APIC_ID : Z := 16.
Definition S_ENTRIES_SEEN : Z := 17.
Definition S_RESULT_ABI : Z := 18.
Definition S_RESULT_STATUS : Z := 19.
Definition S_RESULT_ERROR : Z := 20.
Definition S_RESULT_APIC_ID : Z := 21.

(* ---------------------------------------------------------------------- *)
(* The inputs.                                                            *)
(* ---------------------------------------------------------------------- *)

(* The function main calls (CALL_ENVELOPE .. CALL_ADMISSION): madt_envelope, madt_entries, madt_result, madt_admission. *)
Inductive func : Type := FEnvelope | FEntries | FResult | FAdmission.

(* Everything main chooses: the function, the copy's bytes and its length (the specifications require
   Zlength i_bytes = i_length), the executing APIC ID, the result's ten arguments a0..a9 (the admission uses
   a0..a4) and the prior value of the APIC ID record. *)
Record inputs : Type := mk_inputs {
  i_call: func;
  i_bytes: list Z;
  i_length: Z;
  i_executing: Z;
  i_args: list Z;
  i_prior: Z }.

(* The envelope's initial state (offset, declared length, checksum) and the entry stream's. *)
Definition initial_envelope : list Z := [0; 0; 0].
Definition initial_entries : list Z := [44; 0; 0; 0; 0; 0; 0; 256; 0; 0; 0; 0].

(* The terminal marker of byte i: 1 at the last byte, 0 before. *)
Definition terminal (x: inputs) (i: Z) : Z := if i + 1 =? i_length x then 1 else 0.

(* The admission result's arguments in an admission, after the entries admitted id: a0..a4, one MADT, the
   accepted admission (status 1, detail 0), id and the executing ID. *)
Definition admission_args (x: inputs) (id: Z) : list Z :=
  [Znth 0 (i_args x); Znth 1 (i_args x); Znth 2 (i_args x); Znth 3 (i_args x); Znth 4 (i_args x);
   1; 1; 0; id; i_executing x].

(* ---------------------------------------------------------------------- *)
(* Calls, answers, stages.                                                *)
(* ---------------------------------------------------------------------- *)

(* A call to one of the three exports, with its arguments. *)
Inductive call : Type :=
  (* leanos_boot_machine_madt_envelope_byte_step_query(state[0..2], table_length, byte_offset, byte_value,
     terminal, word) *)
  | EnvelopeStep (state: list Z) (table_length offset byte term word: Z)
  (* leanos_boot_machine_madt_entry_stream_byte_step_query(state[0..11], table_length, executing_apic_id,
     byte_offset, byte_value, word) *)
  | EntryStep (state: list Z) (table_length executing offset byte word: Z)
  (* leanos_boot_machine_topology_admission_result_query(args[0..9], word) *)
  | ResultQuery (args: list Z) (word: Z).

(* One answered call: the call and the value the export returned. *)
Definition answer : Type := (call * Z)%type.

(* Where the function is between calls; cur holds the answers to the current transition so far. *)
Inductive stage : Type :=
  (* the envelope step of byte i, from the old state (offset, declared length, checksum) *)
  | ExpectEnvelope (i: Z) (state: list Z) (cur: list Z)
  (* the entry-stream step of offset k, from the twelve old state words *)
  | ExpectEntries (k: Z) (state: list Z) (cur: list Z)
  (* the admission result, with its ten arguments *)
  | ExpectResult (args: list Z) (cur: list Z).

(* An outcome: the status the function returns, and the APIC ID it writes to the APIC ID record (None:
   it writes nothing). *)
Definition outcome : Type := (Z * option Z)%type.

Inductive progress : Type :=
  | Go (s: stage)
  | Return (o: outcome).

(* ---------------------------------------------------------------------- *)
(* The result.                                                            *)
(* ---------------------------------------------------------------------- *)

(* The result's verdict on its answers a (words 0..3), for its arguments args. *)
Definition result_check (args: list Z) (a: list Z) : Z :=
  if negb (Znth 0 a =? 1) then S_RESULT_ABI
  else if negb (Znth 1 a =? 1) then S_RESULT_STATUS
  else if negb (Znth 2 a =? 0) then S_RESULT_ERROR
  else if negb (Znth 3 a <? 2 ^ 32) || negb (Znth 3 a =? Znth 8 args) || negb (Znth 3 a =? Znth 9 args)
  then S_RESULT_APIC_ID
  else S_OK.

(* The function returns status r, writing id on OK only (the result is the last step of every function that
   reaches it). *)
Definition result_end (r id: Z) : progress := Return (r, if r =? S_OK then Some id else None).

(* After the answers a of the result: another call while fewer than 4, else the verdict. *)
Definition result_collect (args: list Z) (a: list Z) : progress :=
  if Zlength a <? 4 then Go (ExpectResult args a) else result_end (result_check args a) (Znth 3 a).

(* ---------------------------------------------------------------------- *)
(* The entry stream.                                                      *)
(* ---------------------------------------------------------------------- *)

(* Where the entries' status r (and on OK the admitted APIC ID id) leads: on OK the entries alone return OK,
   writing id, and an admission asks the result; otherwise the function returns r and writes nothing. *)
Definition entries_end (x: inputs) (r id: Z) : progress :=
  if r =? S_OK then
    match i_call x with
    | FEntries => Return (S_OK, Some id)
    | _ => Go (ExpectResult (admission_args x id) nil)
    end
  else Return (r, None).

(* The entries' verdict on the final state s0..s11 (words 3..14 of the last answers). *)
Definition entries_final (x: inputs) (st: list Z) : Z :=
  if negb ((Znth 1 st =? 0) && (Znth 2 st =? 0) && (Znth 3 st =? 0) && (Znth 4 st =? 0) && (Znth 5 st =? 0))
  then S_ENTRIES_RECORD
  else if negb (Znth 6 st =? 1) then S_ENTRIES_ENABLED
  else if negb (Znth 7 st =? i_executing x) then S_ENTRIES_APIC_ID
  else if (Znth 8 st =? 0) && (Znth 9 st =? 0) && (Znth 10 st =? 0) && (Znth 11 st =? 0) then S_ENTRIES_SEEN
  else S_OK.

(* After the last byte: the final checks, then entries_end with s7. *)
Definition entries_done (x: inputs) (st: list Z) : progress := entries_end x (entries_final x st) (Znth 7 st).

(* Offset k with the old state st: its transition, or after the last byte the final checks. *)
Definition entries_from (x: inputs) (k: Z) (st: list Z) : progress :=
  if k =? i_length x then entries_done x st else Go (ExpectEntries k st nil).

(* The entries' turn: their bounds, then offset 44 with the initial state. *)
Definition begin_entries (x: inputs) : progress :=
  if (i_length x <=? 44) || (255 <? i_executing x) then Return (S_ENTRIES_BOUNDS, None)
  else entries_from x 44 initial_entries.

(* The entries' verdict on the answers a (words 0..15) of offset k's transition. *)
Definition entries_check (x: inputs) (k: Z) (a: list Z) : Z :=
  if negb (Znth 0 a =? 1) then S_ENTRIES_ABI
  else if negb (Znth 1 a =? (if k + 1 =? i_length x then 3 else 1)) then S_ENTRIES_STATUS
  else if negb (Znth 2 a =? 0) then S_ENTRIES_ERROR
  else if negb (Znth 3 a =? k + 1) then S_ENTRIES_NEXT_OFFSET
  else if negb (Znth 15 a =? Znth k (i_bytes x)) then S_ENTRIES_EXPOSED
  else S_OK.

(* After the answers a of offset k's transition: another call while fewer than 16; else on acceptance the next
   offset from words 3..14, and on rejection the status. *)
Definition entries_collect (x: inputs) (k: Z) (st: list Z) (a: list Z) : progress :=
  if Zlength a <? 16 then Go (ExpectEntries k st a)
  else let r := entries_check x k a in
       if r =? S_OK then entries_from x (k + 1) (sublist 3 15 a) else Return (r, None).

(* ---------------------------------------------------------------------- *)
(* The envelope.                                                          *)
(* ---------------------------------------------------------------------- *)

(* Where the envelope's status r leads: on OK the envelope alone returns OK and an admission begins the entries;
   otherwise the function returns r and writes nothing. *)
Definition envelope_end (x: inputs) (r: Z) : progress :=
  if r =? S_OK then
    match i_call x with
    | FEnvelope => Return (S_OK, None)
    | _ => begin_entries x
    end
  else Return (r, None).

(* The envelope's verdict on the final state (offset, declared length, checksum): the declared length must be
   the copy's length and the checksum 0.  (The header also compares the final offset with the length: it is
   always the length, word 3 of each accepted transition being the next byte.) *)
Definition envelope_final (x: inputs) (st: list Z) : Z :=
  if negb (Znth 1 st =? i_length x) then S_ENVELOPE_LENGTH
  else if negb (Znth 2 st =? 0) then S_ENVELOPE_CHECKSUM
  else S_OK.

(* After the last byte (at once for an empty copy): the final checks, then envelope_end. *)
Definition envelope_done (x: inputs) (st: list Z) : progress := envelope_end x (envelope_final x st).

(* Byte i with the old state st: its transition, or after the last byte the final checks. *)
Definition envelope_from (x: inputs) (i: Z) (st: list Z) : progress :=
  if i =? i_length x then envelope_done x st else Go (ExpectEnvelope i st nil).

(* The envelope's verdict on the answers a (words 0..6) of byte i's transition. *)
Definition envelope_check (x: inputs) (i: Z) (a: list Z) : Z :=
  if negb (Znth 0 a =? 1) then S_ENVELOPE_ABI
  else if negb (Znth 1 a =? (if i + 1 =? i_length x then 3 else 1)) then S_ENVELOPE_STATUS
  else if negb (Znth 2 a =? 0) then S_ENVELOPE_ERROR
  else if negb (Znth 3 a =? i + 1) then S_ENVELOPE_NEXT_BYTE
  else if negb (Znth 6 a =? Znth i (i_bytes x)) then S_ENVELOPE_EXPOSED
  else S_OK.

(* After the answers a of byte i's transition: another call while fewer than 7; else on acceptance the next
   byte from words 3, 4, 5, and on rejection the status. *)
Definition envelope_collect (x: inputs) (i: Z) (st: list Z) (a: list Z) : progress :=
  if Zlength a <? 7 then Go (ExpectEnvelope i st a)
  else let r := envelope_check x i a in
       if r =? S_OK then envelope_from x (i + 1) [Znth 3 a; Znth 4 a; Znth 5 a] else Return (r, None).

(* ---------------------------------------------------------------------- *)
(* The machine.                                                           *)
(* ---------------------------------------------------------------------- *)

(* Before the first call: the envelope from byte 0 (the envelope and the admission), the entries' bounds and
   offset 44 (the entries), or the result with a0..a9 (the result). *)
Definition start (x: inputs) : progress :=
  match i_call x with
  | FEnvelope | FAdmission => envelope_from x 0 initial_envelope
  | FEntries => begin_entries x
  | FResult => Go (ExpectResult (i_args x) nil)
  end.

(* The call the function makes in stage s: the word is the number of answers so far. *)
Definition expected (x: inputs) (s: stage) : call :=
  match s with
  | ExpectEnvelope i st cur => EnvelopeStep st (i_length x) i (Znth i (i_bytes x)) (terminal x i) (Zlength cur)
  | ExpectEntries k st cur => EntryStep st (i_length x) (i_executing x) k (Znth k (i_bytes x)) (Zlength cur)
  | ExpectResult args cur => ResultQuery args (Zlength cur)
  end.

(* One answer v in stage s. *)
Definition step (x: inputs) (s: stage) (v: Z) : progress :=
  match s with
  | ExpectEnvelope i st cur => envelope_collect x i st (cur ++ [v])
  | ExpectEntries k st cur => entries_collect x k st (cur ++ [v])
  | ExpectResult args cur => result_collect args (cur ++ [v])
  end.

Definition call_eq_dec (a b: call) : {a = b} + {a <> b}.
Proof. decide equality; first [ apply Z.eq_dec | apply (list_eq_dec Z.eq_dec) ]. Defined.

(* The function after the answers h from progress p: Some (Go s) while it would call again, Some (Return o)
   when it returned o after the last answer (or before any), None when h is not its sequence of calls. *)
Fixpoint run (x: inputs) (p: progress) (h: list answer) : option progress :=
  match h with
  | nil => Some p
  | (c, v) :: rest =>
    match p with
    | Go s => if call_eq_dec c (expected x s) then run x (step x s v) rest else None
    | Return _ => None
    end
  end.

(* The call the function makes after the answers h, if it calls again. *)
Definition next_call (x: inputs) (h: list answer) : option call :=
  match run x (start x) h with Some (Go s) => Some (expected x s) | _ => None end.

(* The function's outcome when it returns after the answers h. *)
Definition returns (x: inputs) (h: list answer) : option outcome :=
  match run x (start x) h with Some (Return o) => Some o | _ => None end.

(* ---------------------------------------------------------------------- *)
(* How the machine moves (for the body proofs and the law's oracle).      *)
(* ---------------------------------------------------------------------- *)

Lemma run_app (x: inputs) (p: progress) (h1 h2: list answer) :
  run x p (h1 ++ h2) = match run x p h1 with Some q => run x q h2 | None => None end.
Proof.
  revert p; induction h1 as [| [c v] rest IH]; intros p; simpl; [reflexivity |].
  destruct p as [s | o]; [| reflexivity].
  destruct (call_eq_dec c (expected x s)); [apply IH | reflexivity].
Qed.

(* Answering the expected call of stage s with v moves to step x s v. *)
Lemma run_snoc (x: inputs) (p: progress) (h: list answer) (s: stage) (v: Z) :
  run x p h = Some (Go s) -> run x p (h ++ [(expected x s, v)]) = Some (step x s v).
Proof.
  intros E. rewrite run_app, E. simpl.
  destruct (call_eq_dec (expected x s) (expected x s)); [reflexivity | contradiction].
Qed.

Lemma next_call_go (x: inputs) (h: list answer) (s: stage) :
  run x (start x) h = Some (Go s) -> next_call x h = Some (expected x s).
Proof. unfold next_call. intros E. rewrite E. reflexivity. Qed.

Lemma returns_return (x: inputs) (h: list answer) (o: outcome) :
  run x (start x) h = Some (Return o) -> returns x h = Some o.
Proof. unfold returns. intros E. rewrite E. reflexivity. Qed.
