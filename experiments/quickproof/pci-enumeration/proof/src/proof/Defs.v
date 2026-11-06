(* Pure definitions shared by every proof of leanos_enum (boot/pci-enumeration.h): the segment scan of
   pci_enumerate_segment as a state machine over the answers the device gives.  No program here.  Words are Z values
   in their C type's range; every definition follows the C it names. *)
Require Import VST.floyd.proofauto.
Local Open Scope Z_scope.
Local Open Scope bool_scope.   (* && and || are andb and orb here, not VST's andp and orp *)

(* enum pci_enumeration_status *)
Definition S_OK : Z := 0.
Definition S_READ_FAILED : Z := 1.
Definition S_CAPACITY_EXCEEDED : Z := 2.
Definition S_INVALID_ARGUMENT : Z := 3.

Definition FUNCTIONS : Z := 65536.
Definition CAPACITY : Z := 16.
Definition WORDS : Z := 16.

(* A function of the segment by its index bus * 256 + device * 8 + function, 0 <= index < 65536. *)
Definition bus_of (i: Z) : Z := Z.shiftr i 8.
Definition dev_of (i: Z) : Z := Z.land (Z.shiftr i 3) 31.
Definition fn_of (i: Z) : Z := Z.land i 7.

(* One answered read: the function's index and the offset asked for, whether the read succeeded, and the value it
   returned (meaningless when it failed). *)
Definition answer : Type := (Z * Z * bool * Z)%type.

(* A header found: the function's index and the dwords read so far, in offset order. *)
Definition found : Type := (Z * list Z)%type.

(* The scan's state between reads: the index of the next identity read; 0 when that is the next read, else w in
   1..15 when the next read is dword w of the function just found (index next - 1); and the headers found, latest
   first. *)
Definition state : Type := (Z * Z * list found)%type.

Definition start : state := (0, 0, nil).

(* The read the scan makes next in state s: the function's index and the offset. *)
Definition request (s: state) : Z * Z :=
  let '(next, w, _) := s in if w =? 0 then (next, 0) else (next - 1, 4 * w).

(* Whether the scan reads again in state s (else it has read every identity, and its last header is whole). *)
Definition live (s: state) : bool :=
  let '(next, w, _) := s in negb ((w =? 0) && (next =? FUNCTIONS)).

(* After a step: the next state, or a return with a status and the location (index, offset) it names. *)
Inductive progress : Type :=
  | Go (s: state)
  | Stop (status index offset: Z).

(* Append v to the dwords of the latest header. *)
Definition add_word (v: Z) (fs: list found) : list found :=
  match fs with
  | (i, ws) :: rest => (i, ws ++ [v]) :: rest
  | nil => nil
  end.

(* One answered read in state s (the answer is to request s). *)
Definition step (s: state) (a: answer) : progress :=
  let '(next, w, fs) := s in
  let '(i, o, ok, v) := a in
  if negb ok then Stop S_READ_FAILED i o
  else if w =? 0 then
    if Z.land v 65535 =? 65535 then Go (next + 1, 0, fs)
    else if Zlength fs =? CAPACITY then Stop S_CAPACITY_EXCEEDED i 0
    else Go (next + 1, 1, (i, [v]) :: fs)
  else Go (next, if w =? WORDS - 1 then 0 else w + 1, add_word v fs).

(* Whether answer a answers request r. *)
Definition answers (r: Z * Z) (a: answer) : bool :=
  let '(i, o, _, _) := a in (i =? fst r) && (o =? snd r).

(* The scan after the answers ans from state s: Some (Go s') while it would read again or has read everything,
   Some (Stop ...) when it returned at the last answer, None when ans is not the sequence of reads it makes. *)
Fixpoint run (s: state) (ans: list answer) : option progress :=
  match ans with
  | nil => Some (Go s)
  | a :: rest =>
    if live s && answers (request s) a then
      match step s a with
      | Go s' => run s' rest
      | Stop st i o => match rest with nil => Some (Stop st i o) | _ => None end
      end
    else None
  end.

(* The read the scan makes after the answers h, if it reads again. *)
Definition next_read (h: list answer) : option (Z * Z) :=
  match run start h with
  | Some (Go s) => if live s then Some (request s) else None
  | _ => None
  end.

(* An outcome: the status, the location (index, offset) it names, and the published headers. *)
Definition outcome : Type := (Z * Z * Z * list found)%type.

(* The outcome of the scan when it returns after the answers h: OK with location 0 and the headers found, in the order
   found, once every identity is read; the status and location of a return, with no header; None while it would
   read again, or when h is not its sequence of reads. *)
Definition scan (h: list answer) : option outcome :=
  match run start h with
  | Some (Go (next, w, fs)) => if live (next, w, fs) then None else Some (S_OK, 0, 0, rev fs)
  | Some (Stop st i o) => Some (st, i, o, nil)
  | None => None
  end.
