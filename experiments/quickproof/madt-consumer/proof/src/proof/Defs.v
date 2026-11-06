(* Pure definitions shared by every proof of leanos_madt (include/qotom_bsp_consumer.h): the consumer
   qotom_bind_validated_madt_entries as a state machine over the answers of the three Lean exports it calls.  No
   program here.  Words are Z values in their C type's range (uint64_t, bytes 0..255); every definition follows the
   C it names. *)
Require Import VST.floyd.proofauto.
Local Open Scope Z_scope.
Local Open Scope bool_scope.   (* && and || are andb and orb here, not VST's andp and orp *)

Definition MAX_LENGTH : Z := 65536 - 44.

(* struct qotom_bsp_observation: executing, cpuid_edx, available, apic_base, sample_id, routing authority. *)
Record observation : Type := mk_observation {
  o_executing : Z; o_cpuid_edx : Z; o_available : Z; o_apic_base : Z; o_sample_id : Z; o_routing : Z }.

(* The consumer's inputs: the span's bytes and the observation. *)
Definition inputs : Type := (list Z * observation)%type.

(* The initial stream state [44,0,0,0,0,0,0,256,0,0,0,0]. *)
Definition initial_state : list Z := [44; 0; 0; 0; 0; 0; 0; 256; 0; 0; 0; 0].

(* A call to one of the three exports, with its arguments. *)
Inductive call : Type :=
  (* leanos_qotom_madt_stream_byte_step_query(state[0..11], table_length, executing, offset, byte, word) *)
  | Step (state: list Z) (table_length executing offset byte word: Z)
  (* leanos_qotom_madt_nmi_policy_query(count, nmi[0..3], routing, word) *)
  | Nmi (count: Z) (nmi: list Z) (routing word: Z)
  (* leanos_qotom_madt_stream_finish_query(status, error, state[0..11], table_length, executing, cpuid_edx,
     available, apic_base, sample_id, word) *)
  | Finish (status error: Z) (state: list Z) (table_length executing cpuid_edx available apic_base sample_id word: Z).

(* One answered call: the call and the value the export returned. *)
Definition answer : Type := (call * Z)%type.

(* The record walk over the span after the stream: Some (count, nmi) when the records tile it, each at least 2
   bytes long (byte 1 is the length) and each NMI record (type 4) exactly 6, with the number of NMI records and the
   first four of them packed little-endian (0 where absent); None when the consumer rejects (status 3). *)
Definition pack6 (bytes: list Z) (pos: Z) : Z :=
  fold_right Z.lor 0 (map (fun b => Z.shiftl (Znth (pos + Z.of_nat b) bytes) (8 * Z.of_nat b)) (seq 0 6)).

Fixpoint walk_records (fuel: nat) (bytes: list Z) (pos count: Z) (nmi: list Z) : option (Z * list Z) :=
  match fuel with
  | O => None
  | S f =>
    let n := Zlength bytes in
    if n <=? pos then Some (count, nmi)
    else if n - pos <? 2 then None
    else
      let len := Znth (pos + 1) bytes in
      if (len <? 2) || (n - pos <? len) then None
      else if Znth pos bytes =? 4 then
        if negb (len =? 6) then None
        else walk_records f bytes (pos + len) (count + 1)
               (if count <? 4 then upd_Znth count nmi (pack6 bytes pos) else nmi)
      else walk_records f bytes (pos + len) count nmi
  end.

Definition records (bytes: list Z) : option (Z * list Z) :=
  walk_records (S (Z.to_nat (Zlength bytes))) bytes 0 0 [0; 0; 0; 0].

(* Where the consumer is between calls. *)
Inductive stage : Type :=
  (* stepping byte i from the old state, with the answers cur of its transition so far *)
  | Stream (i: Z) (state: list Z) (cur: list Z)
  (* querying the NMI policy after the stream: last = the last transition's 16 answers, state the final state *)
  | Policy (last: list Z) (state: list Z) (count: Z) (nmi: list Z) (cur: list Z)
  (* querying the finish *)
  | Bound (last: list Z) (state: list Z) (cur: list Z).

(* An outcome: status, detail, offset, APIC ID, processor count, APIC base (struct qotom_bsp_result). *)
Definition outcome : Type := (Z * Z * Z * Z * Z * Z)%type.

Definition reject (status detail offset: Z) : outcome := (status, detail, offset, 0, 0, 0).

Inductive progress : Type :=
  | Go (s: stage)
  | Return (o: outcome).

(* The call the consumer makes in stage s. *)
Definition expected (x: inputs) (s: stage) : call :=
  let '(bytes, ob) := x in
  let tl := 44 + Zlength bytes in
  match s with
  | Stream i state cur => Step state tl (o_executing ob) (44 + i) (Znth i bytes) (Zlength cur)
  | Policy _ _ count nmi cur => Nmi count nmi (o_routing ob) (Zlength cur)
  | Bound last state cur =>
      Finish (Znth 1 last) (Znth 2 last) state tl (o_executing ob) (o_cpuid_edx ob) (o_available ob)
             (o_apic_base ob) (o_sample_id ob) (Zlength cur)
  end.

(* After the last transition: the record walk, then the policy. *)
Definition after_stream (bytes: list Z) (last state: list Z) : progress :=
  match records bytes with
  | None => Return (reject 3 0 (Znth 0 state))
  | Some (count, nmi) => Go (Policy last state count nmi nil)
  end.

(* One answer v in stage s. *)
Definition step (x: inputs) (s: stage) (v: Z) : progress :=
  let '(bytes, ob) := x in
  let n := Zlength bytes in
  match s with
  | Stream i state cur =>
    let r := cur ++ [v] in
    if Zlength r <? 16 then Go (Stream i state r)
    else
      let offset := 44 + i in
      if negb (Znth 0 r =? 1) then Return (reject 3 0 offset)
      else if Znth 1 r =? 2 then Return (reject 2 (Znth 2 r) offset)
      else if negb (Znth 1 r =? (if i + 1 =? n then 3 else 1)) || negb (Znth 2 r =? 0) ||
              negb (Znth 3 r =? offset + 1) || negb (Znth 15 r =? Znth i bytes)
      then Return (reject 3 0 offset)
      else
        let state' := sublist 3 15 r in
        if i + 1 =? n then after_stream bytes r state' else Go (Stream (i + 1) state' nil)
  | Policy last state count nmi cur =>
    let p := cur ++ [v] in
    if Zlength p <? 5 then Go (Policy last state count nmi p)
    else
      let off := Znth 0 state in
      if negb (Znth 0 p =? 1) || (1 <? Znth 3 p) || (4 <? Znth 4 p) then Return (reject 3 0 off)
      else if negb (Znth 1 p =? 1) then Return (reject 5 (Znth 2 p) off)
      else if negb (Znth 2 p =? 0) || negb (Znth 3 p =? 1) || negb (Znth 4 p =? 4) then Return (reject 3 0 off)
      else Go (Bound last state nil)
  | Bound last state cur =>
    let b := cur ++ [v] in
    if Zlength b <? 6 then Go (Bound last state b)
    else
      let off := Znth 0 state in
      if negb (Znth 0 b =? 1) || negb (Znth 5 b =? 0) then Return (reject 3 0 off)
      else if (Znth 1 b =? 2) || (Znth 1 b =? 5) then Return (reject 4 (Znth 2 b) off)
      else if negb (Znth 1 b =? 1) || negb (Znth 2 b =? o_executing ob) || negb (Znth 3 b =? Znth 6 state) ||
              negb (Znth 4 b =? o_apic_base ob)
      then Return (reject 3 0 off)
      else Return (0, 0, off, Znth 2 b, Znth 3 b, Znth 4 b)
  end.

(* Whether the inputs pass the consumer's argument test (the span and the observation present, checked by the
   caller of `start`): a length in 1..65536-44. *)
Definition length_ok (length: Z) : bool := (0 <? length) && (length <=? MAX_LENGTH).

(* The consumer with present span, observation and result record, before its first call. *)
Definition start (x: inputs) : progress :=
  if length_ok (Zlength (fst x)) then Go (Stream 0 initial_state nil) else Return (reject 1 0 44).

(* Decidable equality of calls, argument by argument. *)
Definition list_eqb (a b: list Z) : bool := (Zlength a =? Zlength b) && forallb (fun p => fst p =? snd p) (combine a b).

Definition call_eqb (a b: call) : bool :=
  match a, b with
  | Step s t e o y w, Step s' t' e' o' y' w' =>
      list_eqb s s' && (t =? t') && (e =? e') && (o =? o') && (y =? y') && (w =? w')
  | Nmi c m r w, Nmi c' m' r' w' => (c =? c') && list_eqb m m' && (r =? r') && (w =? w')
  | Finish st er s t e c a ab si w, Finish st' er' s' t' e' c' a' ab' si' w' =>
      (st =? st') && (er =? er') && list_eqb s s' && (t =? t') && (e =? e') && (c =? c') && (a =? a') &&
      (ab =? ab') && (si =? si') && (w =? w')
  | _, _ => false
  end.

(* The consumer after the answers ans from progress p: Some (Go s) while it would call again, Some (Return o) when
   it returned pos the last answer (or before any, from `start`), None when ans is not its sequence of calls. *)
Fixpoint run (x: inputs) (p: progress) (ans: list answer) : option progress :=
  match ans with
  | nil => Some p
  | (c, v) :: rest =>
    match p with
    | Go s => if call_eqb c (expected x s) then run x (step x s v) rest else None
    | Return _ => None
    end
  end.

(* The call the consumer makes after the answers h, if it calls again. *)
Definition next_call (x: inputs) (h: list answer) : option call :=
  match run x (start x) h with Some (Go s) => Some (expected x s) | _ => None end.

(* The consumer's outcome when it returns after the answers h. *)
Definition consume (x: inputs) (h: list answer) : option outcome :=
  match run x (start x) h with Some (Return o) => Some o | _ => None end.
