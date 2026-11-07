(* Law table_copy_exact: what main's proof needs besides the harness's functions: the program's global variables
   as main finds them (the three string literals of the acpi unit, the zeroed law). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosAcpi.harness.table_copy_exact.code.
Require LeanosAcpi.acpi.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.LawProg LeanosAcpi.proof.LawDefs LeanosAcpi.proof.LawZero.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Definition sl1 := LeanosAcpi.acpi.code.___stringlit_acpi_1.
Definition sl2 := LeanosAcpi.acpi.code.___stringlit_acpi_2.
Definition sl3 := LeanosAcpi.acpi.code.___stringlit_acpi_3.

(* The program's global variables, in the order of QPprog_vars. *)
Definition main_vars : list (ident * globvar type) :=
  [(sl2, LeanosAcpi.acpi.code.v___stringlit_acpi_2); (sl1, LeanosAcpi.acpi.code.v___stringlit_acpi_1);
   (sl3, LeanosAcpi.acpi.code.v___stringlit_acpi_3); (_law, v_law)].

Ltac lit_tac :=
  intros gv H;
  eapply derives_trans; [ apply (@globvar2pred_cstring AcpiSpecs.CS); [ exact H | split; reflexivity | reflexivity
    | reflexivity | reflexivity | reflexivity ] | ];
  unfold cstring, literal, lit_val; Intros; apply derives_refl'; reflexivity.

Lemma lit_apic: forall gv, headptr (gv sl1) ->
  globvar2pred gv (sl1, LeanosAcpi.acpi.code.v___stringlit_acpi_1) |-- literal APIC (gv sl1).
Proof. lit_tac. Qed.

Lemma lit_xsdt: forall gv, headptr (gv sl2) ->
  globvar2pred gv (sl2, LeanosAcpi.acpi.code.v___stringlit_acpi_2) |-- literal XSDT (gv sl2).
Proof. lit_tac. Qed.

Lemma lit_rsdt: forall gv, headptr (gv sl3) ->
  globvar2pred gv (sl3, LeanosAcpi.acpi.code.v___stringlit_acpi_3) |-- literal RSDT (gv sl3).
Proof. lit_tac. Qed.

(* struct law with the arguments given apart from inputs. *)
Definition lfields2 (q: val) (k ad: Z) (pl: place) (rc tc: Z) (re te: val) (hx: list Z) (s: lst) : mpred :=
 (field_at Ews t_law (DOT _kind) (vl k) q *
  field_at Ews t_law (DOT _address) (vl ad) q *
  field_at Ews t_law (DOT _header) (p_header pl) q *
  field_at Ews t_law (DOT _root) (p_root pl) q *
  field_at Ews t_law (DOT _tables) (p_tables pl) q *
  field_at Ews t_law (DOT _root_capacity) (vi rc) q *
  field_at Ews t_law (DOT _table_capacity) (vi tc) q *
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

Lemma lfields2_lfields: forall q x pl re te hx s,
  lfields2 q (i_kind x) (i_address x) pl (root_capacity x) (table_capacity x) re te hx s = lfields q x pl re te hx s.
Proof. reflexivity. Qed.

(* A pointer malloc returned. *)
Definition mres (t: type) (p: val) : mpred :=
  if eq_dec p nullval then emp else (malloc_token Ews t p * data_at_ Ews t p)%logic.

Definition isnul (p: val) : bool := if eq_dec p nullval then true else false.

Lemma mres_tc: forall t p (P: mpred), (mres t p * P)%logic |-- denote_tc_test_eq p (Vlong (Int64.repr 0)).
Proof.
  intros t p P. unfold mres. destruct (eq_dec p nullval) as [E | N].
  - subst. apply denote_tc_test_eq_split; apply valid_pointer_zero64; reflexivity.
  - apply denote_tc_test_eq_split; [ | apply valid_pointer_zero64; reflexivity ].
    rewrite sepcon_assoc.
    destruct (Z_le_gt_dec (sizeof t) 0) as [Z | Z].
    + apply sepcon_valid_pointer1. apply malloc_token_valid_pointer; auto.
    + apply sepcon_valid_pointer2. apply sepcon_valid_pointer1.
      apply data_at__valid_ptr; [ apply readable_nonidentity, writable_readable, writable_Ews | lia ].
Qed.

Lemma mres_cmp: forall p, is_pointer_or_null p ->
  force_val (sem_cmp_pp Ceq p (Vlong (Int64.repr 0))) = Vint (if isnul p then Int.one else Int.zero).
Proof.
  intros p P. unfold isnul. destruct (eq_dec p nullval) as [E | N].
  - subst. reflexivity.
  - destruct p; try contradiction; simpl in *; try reflexivity.
    + subst. exfalso. apply N. reflexivity.
Qed.

Lemma mres_ptr: forall t p, isnul p = false -> mres t p = (malloc_token Ews t p * data_at_ Ews t p)%logic.
Proof. intros t p E. unfold mres, isnul in *. destruct (eq_dec p nullval); [ discriminate | reflexivity ]. Qed.

Lemma mres_tc': forall t p (P Q: mpred), P |-- (mres t p * Q)%logic -> P |-- denote_tc_test_eq p (Vlong (Int64.repr 0)).
Proof. intros. eapply derives_trans; [ exact H | apply mres_tc ]. Qed.

Lemma null_test: forall p, is_pointer_or_null p ->
  force_val (sem_cast tint tbool (eval_binop Oeq (tptr tuchar) (tptr tvoid) p (eval_cast tint (tptr tvoid) (Vint (Int.repr 0))))) =
  Vint (Int.repr (Z.b2z (isnul p))).
Proof.
  intros p P. unfold isnul. destruct (eq_dec p nullval) as [E | N].
  - subst. vm_compute. reflexivity.
  - destruct p; try contradiction; simpl in *.
    + subst. exfalso. apply N. reflexivity.
    + vm_compute. reflexivity.
Qed.

Lemma isnul_false: forall p, p <> nullval -> isnul p = false.
Proof. intros. unfold isnul. destruct (eq_dec p nullval); [ contradiction | reflexivity ]. Qed.

Lemma isnul_true: isnul nullval = true.
Proof. reflexivity. Qed.

Lemma null_test2: forall p, is_pointer_or_null p ->
  force_val (sem_cast_i2bool (force_val (sem_cmp_pp Ceq p (Vlong (Int64.repr 0))))) = Vint (Int.repr (Z.b2z (isnul p))).
Proof.
  intros p P. unfold isnul. destruct (eq_dec p nullval) as [E | N].
  - subst. vm_compute. reflexivity.
  - destruct p; try contradiction; simpl in *.
    + subst. exfalso. apply N. reflexivity.
    + vm_compute. reflexivity.
Qed.

(* Freeze every SEP item but the law's fields named in L and the data_at/data_at_ whose addresses are in A. *)
Ltac keep_item2 x L A :=
  lazymatch x with
  | field_at _ _ (StructField ?f :: nil) _ _ => lazymatch L with context [f] => constr:(true) | _ => constr:(false) end
  | data_at _ _ _ ?p => lazymatch A with context [p] => constr:(true) | _ => constr:(false) end
  | data_at_ _ _ ?p => lazymatch A with context [p] => constr:(true) | _ => constr:(false) end
  | _ => constr:(false)
  end.
Ltac idx_frozen2 R L A i :=
  lazymatch R with
  | nil => constr:(@nil Z)
  | ?x :: ?R' =>
      let rest := idx_frozen2 R' L A (Z.succ i) in
      let k := keep_item2 x L A in
      lazymatch k with true => rest | false => let i' := eval cbn in i in constr:(i' :: rest) end
  end.
Ltac freeze_but2 L A F :=
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
    let I := idx_frozen2 R L A 0 in freeze_tac I F
  end.
