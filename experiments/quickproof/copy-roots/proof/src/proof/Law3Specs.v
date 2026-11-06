(* Law window_scan_exact: specifications of the harness's static helpers (member, table, tables_at, root_fill,
   root_copy, root_same), under the compspecs of the harness unit, and tactics for their body proofs
   (Law3Small.v, Law3Tables.v, Law3Roots.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env.
Require Import LeanosRoots.harness.window_scan_exact.code.
Require Import LeanosRoots.proof.Defs.
Require LeanosRoots.proof.RootsSpecs.
Require Import LeanosRoots.proof.Law3Facts.
Require LeanosRoots.proof.Law3Prog.
Local Open Scope Z_scope.

(* The compspecs of the law's whole program (Law3Prog). *)
Notation HCS := LeanosRoots.proof.Law3Prog.LCS.
#[export] Existing Instance LeanosRoots.proof.Law3Prog.LCS.

Definition t_root := Tstruct _qotom_root_pages noattr.
Notation longs := RootsSpecs.longs.
(* RootsSpecs.root_val, under the harness's compspecs. *)
Definition root_val (r: root) : reptype t_root :=
  (longs (pml4 r), (longs (pdpt r), (longs (pd r), longs (pt r)))).
Notation b2z := RootsSpecs.b2z.

Definition member_spec :=
  DECLARE _member
  WITH f: Z, p: val, sh: share, fs: list Z, n: Z
  PRE [ tulong, tptr tulong, tulong ]
    PROP (readable_share sh; word_ok f; words_ok fs; 0 <= n <= Zlength fs; Zlength fs <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr f); p; Vlong (Int64.repr n))
    SEP (data_at sh (tarray tulong (Zlength fs)) (longs fs) p)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (b2z (member f (sublist 0 n fs)))))
    SEP (data_at sh (tarray tulong (Zlength fs)) (longs fs) p).

Definition table_spec :=
  DECLARE _table
  WITH phys: Z, k: Z
  PRE [ tulong, tulong ]
    PROP (word_ok phys; 0 <= k <= 10)
    PARAMS (Vlong (Int64.repr phys); Vlong (Int64.repr k))
    SEP ()
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (table_entry phys k))) SEP ().

Definition tables_at_spec :=
  DECLARE _tables_at
  WITH r: val, sh: share, rv: root, phys: Z
  PRE [ tptr t_root, tulong ]
    PROP (readable_share sh; root_ok rv; word_ok phys)
    PARAMS (r; Vlong (Int64.repr phys))
    SEP (data_at sh t_root (root_val rv) r)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (b2z (ancestors_ok rv phys))))
    SEP (data_at sh t_root (root_val rv) r).

Definition root_fill_spec :=
  DECLARE _root_fill
  WITH r: val
  PRE [ tptr t_root ]
    PROP () PARAMS (r) SEP (data_at_ Tsh t_root r)
  POST [ tvoid ]
    EX rv: root,
    PROP (root_ok rv) RETURN () SEP (data_at Tsh t_root (root_val rv) r).

Definition root_copy_spec :=
  DECLARE _root_copy
  WITH d: val, s: val, sh: share, rv: root
  PRE [ tptr t_root, tptr t_root ]
    PROP (readable_share sh; root_ok rv)
    PARAMS (d; s)
    SEP (data_at_ Tsh t_root d; data_at sh t_root (root_val rv) s)
  POST [ tvoid ]
    PROP () RETURN () SEP (data_at Tsh t_root (root_val rv) d; data_at sh t_root (root_val rv) s).

Definition root_same_spec :=
  DECLARE _root_same
  WITH a: val, b: val, sha: share, shb: share, rv: root
  PRE [ tptr t_root, tptr t_root ]
    PROP (readable_share sha; readable_share shb; root_ok rv)
    PARAMS (a; b)
    SEP (data_at sha t_root (root_val rv) a; data_at shb t_root (root_val rv) b)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr 1))
    SEP (data_at sha t_root (root_val rv) a; data_at shb t_root (root_val rv) b).

(* A struct qotom_root_pages of any values, field by field. *)
Definition root_part (a b c d: list val) : reptype t_root := (a, (b, (c, d))).

Lemma root_val_part: forall r, root_val r = root_part (longs (pml4 r)) (longs (pdpt r)) (longs (pd r)) (longs (pt r)).
Proof. reflexivity. Qed.

Lemma default_root_part: default_val t_root = root_part (Zrepeat Vundef 512) (Zrepeat Vundef 512) (Zrepeat Vundef 512)
  (Zrepeat Vundef 4096).
Proof. reflexivity. Qed.

(* The words 0 .. i - 1 of l, then undefined words up to n. *)
Lemma upd_prefix: forall (l: list Z) i n, 0 <= i < n -> Zlength l = n ->
  upd_Znth i (longs (sublist 0 i l) ++ Zrepeat Vundef (n - i)) (Vlong (Int64.repr (Znth i l))) =
  longs (sublist 0 (i + 1) l) ++ Zrepeat Vundef (n - (i + 1)).
Proof. intros. unfold RootsSpecs.longs. list_solve. Qed.

Lemma prefix_full: forall (l: list Z) n, Zlength l = n -> longs (sublist 0 n l) ++ Zrepeat Vundef (n - n) = longs l.
Proof. intros. unfold RootsSpecs.longs. list_solve. Qed.

Lemma prefix_0: forall (l: list Z) n, longs (sublist 0 0 l) ++ Zrepeat Vundef (n - 0) = Zrepeat Vundef n.
Proof. intros. unfold RootsSpecs.longs. list_solve. Qed.

Lemma upd_app: forall (a: list Z) x i n, Zlength a = i -> 0 <= i < n ->
  upd_Znth i (longs a ++ Zrepeat Vundef (n - i)) (Vlong (Int64.repr x)) =
  longs (a ++ [x]) ++ Zrepeat Vundef (n - (i + 1)).
Proof. intros. unfold RootsSpecs.longs. list_solve. Qed.

Lemma app_full: forall (a: list Z) n, Zlength a = n -> longs a ++ Zrepeat Vundef (n - n) = longs a.
Proof. intros. unfold RootsSpecs.longs. list_solve. Qed.

Lemma words_ok_snoc: forall a x, words_ok a -> 0 <= x <= Int64.max_unsigned -> words_ok (a ++ [x]).
Proof. intros. apply Forall_app. split; [ assumption | constructor; [ exact H0 | constructor ] ]. Qed.

Lemma Znth_longs: forall i l, 0 <= i < Zlength l -> Znth i (longs l) = Vlong (Int64.repr (Znth i l)).
Proof. intros. unfold RootsSpecs.longs. rewrite Znth_map by lia. reflexivity. Qed.

(* A load of a word of a root: its type check. *)
Ltac ld :=
  forward;
  try (entailer!; unfold RootsSpecs.longs; rewrite Znth_map by (unfold LEAVES in *; lia); exact I);
  repeat rewrite Znth_longs by (unfold LEAVES in *; lia).

Ltac neq_absurd :=
  exfalso;
  first [ match goal with N: ?x <> ?x |- _ => apply N; reflexivity end
        | match goal with E: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact E end
        | match goal with N: Int.repr 0 <> Int.zero |- _ => apply N; reflexivity end
        | lia | congruence ].

(* Int64 equalities of words, as equalities of Z. *)
Ltac eq_to_z :=
  repeat match goal with
  | E: context [Int64.eq (Int64.repr ?a) (Int64.repr ?b)] |- _ =>
      rewrite (eq_repr a b) in E by (unfold word_ok in *; rep_lia)
  end.

(* Unsigned comparisons as comparisons of Z (the pilot's to_z). *)
Ltac to_z :=
  repeat match goal with
  | H: context [Int.unsigned (Int.repr ?n)] |- _ => rewrite (Int.unsigned_repr n) in H by rep_lia
  | H: context [Int64.unsigned (Int64.repr ?n)] |- _ => rewrite (Int64.unsigned_repr n) in H by rep_lia
  | H: Int64.ltu ?a ?b = true |- _ =>
      unfold Int64.ltu in H; match type of H with context [zlt ?x ?y] => destruct (zlt x y); [ clear H | discriminate ] end
  | H: Int64.ltu ?a ?b = false |- _ =>
      unfold Int64.ltu in H; match type of H with context [zlt ?x ?y] => destruct (zlt x y); [ discriminate | clear H ] end
  | H: negb ?c = true |- _ => apply negb_true_iff in H
  | H: negb ?c = false |- _ => apply negb_false_iff in H
  end.

(* Ranges of the words the harness computes. *)
Ltac rng :=
  first [ rep_lia | apply clear_accessed_range; rep_lia | apply table_entry_range | apply pd_entry_range
        | apply scan_leaf_range; rep_lia | apply frame_range; rep_lia | apply pages_range ].

(* The uint64_t comparisons of the harness, as boolean equalities of Z. *)
Ltac z64 :=
  change Int64.zero with (Int64.repr 0) in *;
  repeat match goal with
  | E: context [Int64.and (Int64.repr ?x) (Int64.not (Int64.repr 32))] |- _ =>
      rewrite (clear_accessed_repr x) in E by rng
  | |- context [Int64.and (Int64.repr ?x) (Int64.not (Int64.repr 32))] =>
      rewrite (clear_accessed_repr x) by rng
  | E: context [Int64.eq (Int64.repr ?a) (Int64.repr ?b)] |- _ => rewrite (eq_repr a b) in E by rng
  | |- context [Int64.eq (Int64.repr ?a) (Int64.repr ?b)] => rewrite (eq_repr a b) by rng
  | E: Int64.repr ?a <> Int64.repr ?b |- _ => apply (neq_repr a b) in E; [ | rng | rng ]
  | E: Int64.repr ?a = Int64.repr ?b |- _ => apply (eq_repr_inj a b) in E; [ | rng | rng ]
  | |- context [Int64.cmpu Cne _ _] => unfold Int64.cmpu
  | E: context [Int64.cmpu Cne _ _] |- _ => unfold Int64.cmpu in E
  end.

(* Rewrite the goal with the boolean facts of the context. *)
Ltac bsubst :=
  repeat match goal with
  | E: Z.eqb ?a ?b = ?c |- context [Z.eqb ?a ?b] => rewrite E
  | E: ?f ?x = ?c |- context [?f ?x] => match type of c with bool => rewrite E end
  end.

Definition Vh : varspecs := nil.
Definition Gh : funspecs :=
  [member_spec; table_spec; tables_at_spec; root_fill_spec; root_copy_spec; root_same_spec; nondet_size_spec].

