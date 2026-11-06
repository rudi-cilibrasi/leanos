(* Pure definitions shared by every proof of leanos_caps (boot/pci-capabilities.h): the capability walk of
   pci_collect_capabilities as a function of the answers the device gives.  No program here.  Words are Z values in
   their C type's range; every definition follows the C expression it names. *)
Require Import VST.floyd.proofauto.
Local Open Scope Z_scope.
Local Open Scope bool_scope.   (* && and || are andb and orb here, not VST's andp and orp *)

(* enum pci_capability_status *)
Definition S_OK : Z := 0.
Definition S_ARGUMENT : Z := 1.
Definition S_READ_FAILED : Z := 2.
Definition S_HEADER_CHANGED : Z := 3.
Definition S_POINTER : Z := 4.
Definition S_CYCLE : Z := 5.
Definition S_ABSENT : Z := 6.

(* One answered read: the offset asked for, whether the read succeeded, the value it returned (meaningless when it
   failed). *)
Definition answer : Type := (Z * bool * Z)%type.

(* The argument test: device <= 31, function <= 7, header type ((word 3 >> 16) & 0x7f) <= 1, vendor (word 0 & 0xffff)
   other than 0xffff. *)
Definition args_ok (dev fn: Z) (words: list Z) : bool :=
  (dev <=? 31) && (fn <=? 7) && (Z.land (Z.shiftr (Znth 3 words) 16) 127 <=? 1) &&
  negb (Z.land (Znth 0 words) 65535 =? 65535).

(* The list head: (uint8_t)words[13] when the status word's capability bit (bit 20 of word 1) is set, else 0. *)
Definition list_head (words: list Z) : Z :=
  if Z.land (Znth 1 words) 1048576 =? 0 then 0 else Z.land (Znth 13 words) 255.

(* The four header reads: offset and mask. *)
Definition header_checks : list (Z * Z) := [(0, 4294967295); (4, 1048576); (12, 16711680); (52, 255)].

(* An outcome: the status, the offset it names (0 on success), and the published headers (offset, raw word): the
   whole list on success, none on failure. *)
Definition outcome : Type := (Z * Z * list (Z * Z))%type.

(* An outcome that ends the walk, if no answer is left. *)
Definition final (o: outcome) (ans: list answer) : option outcome :=
  match ans with nil => Some o | _ => None end.

(* The list loop from pointer `next`, with `count` headers read, the offsets `seen` already read, and the headers
   `acc` read so far (latest first). *)
Fixpoint walk_chain (fuel: nat) (next count: Z) (seen: list Z) (acc: list (Z * Z)) (ans: list answer) :
    option outcome :=
  match fuel with
  | O => None
  | S f =>
    if next =? 0 then final (S_OK, 0, rev acc) ans
    else if (next <? 64) || negb (Z.land next 3 =? 0) then final (S_POINTER, next, nil) ans
    else if existsb (Z.eqb next) seen then final (S_CYCLE, next, nil) ans
    else if count =? 48 then final (S_POINTER, next, nil) ans
    else match ans with
         | (o, ok, v) :: rest =>
           if negb (o =? next) then None
           else if negb ok then final (S_READ_FAILED, next, nil) rest
           else if Z.land v 255 =? 255 then final (S_ABSENT, next, nil) rest
           else walk_chain f (Z.land (Z.shiftr v 8) 255) (count + 1) (next :: seen) ((next, v) :: acc) rest
         | nil => None
         end
  end.

(* The header reads, then the list. *)
Fixpoint walk_header (hs: list (Z * Z)) (words: list Z) (ans: list answer) : option outcome :=
  match hs with
  | nil => walk_chain 50 (list_head words) 0 nil nil ans
  | (o, m) :: hs' =>
    match ans with
    | (o', ok, v) :: rest =>
      if negb (o' =? o) then None
      else if negb ok then final (S_READ_FAILED, o, nil) rest
      else if negb (Z.land v m =? Z.land (Znth (o / 4) words) m) then final (S_HEADER_CHANGED, o, nil) rest
      else walk_header hs' words rest
    | nil => None
    end
  end.

(* The walk of pci_collect_capabilities on valid arguments: Some outcome exactly when `ans` is the sequence of reads
   it makes, given the answers in `ans`. *)
Definition walk (words: list Z) (ans: list answer) : option outcome := walk_header header_checks words ans.
