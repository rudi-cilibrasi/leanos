(* Law copy_roots_exact (harness/copy_roots_exact.c): the specifications of the harness's static helpers,
   under the unit's compspecs RootsSpecs.CS (the harness's three structs are the unit's), and the pure
   restatements of the harness's checks. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env.
Require Import LeanosRoots.proof.Defs.
Require Import LeanosRoots.proof.RootsSpecs.
Require LeanosRoots.harness.copy_roots_exact.code.
Module H := LeanosRoots.harness.copy_roots_exact.code.
Local Open Scope Z_scope.

(* tables_at(r, phys, ignore) != 0. *)
Definition tables_ok (r: root) (phys ig: Z) : bool :=
  ((Z.land (Znth 0 (pml4 r)) (Z.lnot ig) =? table_entry phys 1) &&
   (Z.land (Znth 0 (pdpt r)) (Z.lnot ig) =? table_entry phys 2) &&
   forallb (fun i => (Znth i (pml4 r) =? 0) && (Znth i (pdpt r) =? 0)) (map (Z.add 1) (idx 511)) &&
   forallb (fun i => Z.land (Znth i (pd r)) (Z.lnot ig) =? pd_entry phys i) (idx 512))%bool.

(* The harness's alias search at page p over the leaf d: the last alias of al at p wins. *)
Fixpoint pick (al: list alias) (p d: Z) : Z :=
  match al with
  | nil => d
  | a :: t => pick t p (if a_page a =? p then alias_leaf a else d)
  end.

Definition root_fill_spec :=
  DECLARE H._root_fill
  WITH r: val
  PRE [ tptr t_root ]
    PROP () PARAMS (r) SEP (data_at_ Tsh t_root r)
  POST [ tvoid ]
    EX rv: root, PROP (root_ok rv) RETURN () SEP (data_at Tsh t_root (root_val rv) r).

Definition root_copy_spec :=
  DECLARE H._root_copy
  WITH d: val, s: val, sh: share, rv: root
  PRE [ tptr t_root, tptr t_root ]
    PROP (readable_share sh; root_ok rv) PARAMS (d; s)
    SEP (data_at_ Tsh t_root d; data_at sh t_root (root_val rv) s)
  POST [ tvoid ]
    PROP () RETURN () SEP (data_at Tsh t_root (root_val rv) d; data_at sh t_root (root_val rv) s).

(* root_same on two roots of the same words returns 1. *)
Definition root_same_spec :=
  DECLARE H._root_same
  WITH a: val, b: val, sha: share, shb: share, rv: root
  PRE [ tptr t_root, tptr t_root ]
    PROP (readable_share sha; readable_share shb; root_ok rv) PARAMS (a; b)
    SEP (data_at sha t_root (root_val rv) a; data_at shb t_root (root_val rv) b)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr 1))
    SEP (data_at sha t_root (root_val rv) a; data_at shb t_root (root_val rv) b).

Definition member_spec :=
  DECLARE H._member
  WITH f: Z, p: val, sh: share, fs: list Z, n: Z
  PRE [ tulong, tptr tulong, tulong ]
    PROP (readable_share sh; word_ok f; words_ok fs; 0 <= n <= Zlength fs; Zlength fs <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr f); p; Vlong (Int64.repr n))
    SEP (data_at sh (tarray tulong (Zlength fs)) (longs fs) p)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (b2z (member f (sublist 0 n fs)))))
    SEP (data_at sh (tarray tulong (Zlength fs)) (longs fs) p).

Definition h_phys_ok_spec :=
  DECLARE H._phys_ok
  WITH a: Z
  PRE [ tulong ] PROP (word_ok a) PARAMS (Vlong (Int64.repr a)) SEP ()
  POST [ tint ] PROP () RETURN (Vint (Int.repr (b2z (phys_ok a)))) SEP ().

(* apart on addresses phys_ok accepts (neither sum wraps). *)
Definition apart_spec :=
  DECLARE H._apart
  WITH a: Z, b: Z
  PRE [ tulong, tulong ]
    PROP (word_ok a; word_ok b; a <= 2 ^ 52 - ROOT_BYTES; b <= 2 ^ 52 - ROOT_BYTES)
    PARAMS (Vlong (Int64.repr a); Vlong (Int64.repr b)) SEP ()
  POST [ tint ] PROP () RETURN (Vint (Int.repr (b2z (disjoint a b)))) SEP ().

Definition table_spec :=
  DECLARE H._table
  WITH phys: Z, k: Z
  PRE [ tulong, tulong ]
    PROP (word_ok phys; 0 <= k <= 10) PARAMS (Vlong (Int64.repr phys); Vlong (Int64.repr k)) SEP ()
  POST [ tulong ] PROP () RETURN (Vlong (Int64.repr (table_entry phys k))) SEP ().

Definition tables_at_spec :=
  DECLARE H._tables_at
  WITH r: val, sh: share, rv: root, phys: Z, ig: Z
  PRE [ tptr t_root, tulong, tulong ]
    PROP (readable_share sh; root_ok rv; word_ok phys; word_ok ig)
    PARAMS (r; Vlong (Int64.repr phys); Vlong (Int64.repr ig))
    SEP (data_at sh t_root (root_val rv) r)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (b2z (tables_ok rv phys ig))))
    SEP (data_at sh t_root (root_val rv) r).

Definition inventory_ok_spec :=
  DECLARE H._inventory_ok
  WITH p: val, sh: share, fs: list Z, n: Z
  PRE [ tptr tulong, tulong ]
    PROP (readable_share sh; words_ok fs; 16 <= Zlength fs <= Int64.max_unsigned; word_ok n)
    PARAMS (p; Vlong (Int64.repr n))
    SEP (data_at sh (tarray tulong (Zlength fs)) (longs fs) p)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (b2z (inventory_ok fs n))))
    SEP (data_at sh (tarray tulong (Zlength fs)) (longs fs) p).

(* aliases_ok after inventory_ok accepted the count n. *)
Definition aliases_ok_spec :=
  DECLARE H._aliases_ok
  WITH a: val, ash: share, al: list alias, m: Z, s: val, ssh: share, src: root,
       fp: val, fsh: share, fs: list Z, n: Z
  PRE [ tptr t_alias, tulong, tptr t_root, tptr tulong, tulong ]
    PROP (readable_share ash; readable_share ssh; readable_share fsh; Forall alias_wf al;
          2 <= Zlength al <= Int64.max_unsigned; word_ok m; root_ok src; words_ok fs;
          1 <= n <= Zlength fs; Zlength fs <= Int64.max_unsigned)
    PARAMS (a; Vlong (Int64.repr m); s; fp; Vlong (Int64.repr n))
    SEP (data_at ash (tarray t_alias (Zlength al)) (map alias_val al) a;
         data_at ssh t_root (root_val src) s;
         data_at fsh (tarray tulong (Zlength fs)) (longs fs) fp)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (b2z (aliases_ok src (sublist 0 n fs) al m))))
    SEP (data_at ash (tarray t_alias (Zlength al)) (map alias_val al) a;
         data_at ssh t_root (root_val src) s;
         data_at fsh (tarray tulong (Zlength fs)) (longs fs) fp).

Definition Vharness : varspecs := nil.

(* The context of the harness's functions. *)
Definition Gharness : funspecs :=
  [root_fill_spec; root_copy_spec; root_same_spec; member_spec; h_phys_ok_spec; apart_spec; table_spec;
   tables_at_spec; inventory_ok_spec; aliases_ok_spec; roots_build_spec;
   nondet_size_spec; nondet_u8_spec; gp_assert_spec].
