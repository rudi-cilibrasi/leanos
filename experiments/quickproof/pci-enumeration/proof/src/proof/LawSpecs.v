(* Law enumeration_exact: the law's device (Dev_exact, the harness's struct device as a function of the answers it
   gave) and the specification of the harness's device_read, under the compspecs of the law's whole program
   (LawProg.LCS). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosEnum.harness.enumeration_exact.code.
Require Import LeanosEnum.proof.Defs.
Require LeanosEnum.proof.EnumSpecs.
Require Import LeanosEnum.proof.LawProg LeanosEnum.proof.LawRun.
Local Open Scope Z_scope.

#[export] Existing Instance LawProg.LCS.

Definition t_device := Tstruct _device noattr.

(* struct pci_enumeration_header, as a value: bus, device, function, words[16]. *)
Definition hv : Type := (val * (val * (val * list val)))%type.
(* The four last_* fields of struct device. *)
Definition loc : Type := (val * (val * (val * val)))%type.

Definition words_v (ws: list Z) : list val := map (fun w => Vint (Int.repr w)) ws.

(* The header of the function of index i with the words ws. *)
Definition hdr_v (i: Z) (ws: list val) : hv :=
  (Vint (Int.repr (bus_of i)), (Vint (Int.repr (dev_of i)), (Vint (Int.repr (fn_of i)), ws))).

(* The entry x of seen[] holds the header found f: its location, and its dwords so far first. *)
Definition holds (f: found) (x: hv) : Prop :=
  exists tail, x = hdr_v (fst f) (words_v (snd f) ++ tail) /\ Zlength (snd f) + Zlength tail = WORDS.

(* seen[] holds the headers found fs (latest first) in the order found; the entries after them hold anything. *)
Definition seen_ok (fs: list found) (seen: list hv) : Prop :=
  Zlength seen = CAPACITY /\ Forall (fun x: hv => Zlength (snd (snd (snd x))) = WORDS) seen /\
  forall k, 0 <= k < Zlength fs -> holds (Znth k (rev fs)) (Znth k seen).

(* The location of the read of offset o of the function of index i. *)
Definition loc_of (i o: Z) : loc :=
  (Vint (Int.repr (bus_of i)), (Vint (Int.repr (dev_of i)), (Vint (Int.repr (fn_of i)), Vint (Int.repr o)))).

(* The last_* fields after the answers h: the location of the last one (uninitialized before any). *)
Definition last_loc (h: list answer) : loc :=
  match rev h with
  | (i, o, _, _) :: _ => loc_of i o
  | nil => (Vundef, (Vundef, (Vundef, Vundef)))
  end.

(* struct device: next, word, found, stopped, failed, reads, last_bus, last_device, last_function, last_offset,
   seen[16]. *)
Definition dev_val (next w nfound stopped failed reads: Z) (l: loc) (seen: list hv) : reptype t_device :=
  (Vint (Int.repr next), (Vint (Int.repr w), (Vint (Int.repr nfound), (Vint (Int.repr stopped),
   (Vint (Int.repr failed), (Vint (Int.repr reads),
   (fst l, (fst (snd l), (fst (snd (snd l)), (snd (snd (snd l)), seen)))))))))).

Definition dev_at (ctx: val) (next w nfound stopped failed reads: Z) (l: loc) (fs: list found) : mpred :=
  EX seen: list hv, !! seen_ok fs seen && data_at Tsh t_device (dev_val next w nfound stopped failed reads l seen) ctx.

(* The law's device after the answers h.  While the scan reads (or after its last identity read): its next
   identity read, its dword, the headers found, not stopped, no failure.  After the return at the last answer
   (a failed read, or the 17th function found): as the device left itself on that answer, from the state
   before it.  Never anything else: no other answers reach the device (read_spec). *)
Definition Dev_exact (ctx: val) (h: list answer) : mpred :=
  match run start h with
  | Some (Go (next, w, fs)) => dev_at ctx next w (Zlength fs) 0 0 (Zlength h) (last_loc h) fs
  | Some (Stop st _ _) =>
      match run start (removelast h) with
      | Some (Go (next, w, fs)) =>
          if st =? S_READ_FAILED then dev_at ctx next w (Zlength fs) 1 1 (Zlength h) (last_loc h) fs
          else dev_at ctx (next + 1) 0 (CAPACITY + 1) 1 0 (Zlength h) (last_loc h) fs
      | _ => FF
      end
  | None => FF
  end.

(* device_read obeys the read protocol of Dev_exact. *)
Definition device_read_spec : ident * funspec := (_device_read, EnumSpecs.read_spec Dev_exact).

Definition Vh : varspecs := nil.
(* The context of device_read: the environment functions it calls. *)
Definition Gh : funspecs := [gp_assert_spec; nondet_u8_spec; nondet_u32_spec].
