(* Law table_copy_exact: main from nondet_bytes(m->header, 36) to its loop zeroing the copy slots: the prior bytes
   of the header scratch and the two arenas, and their copies into header_expect and the expectation arenas. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosAcpi.harness.table_copy_exact.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.LawProg LeanosAcpi.proof.LawDefs LeanosAcpi.proof.LawFacts LeanosAcpi.proof.LawLib
  LeanosAcpi.proof.LawLib2 LeanosAcpi.proof.LawOra LeanosAcpi.proof.LawZero LeanosAcpi.proof.LawMainLib
  LeanosAcpi.proof.LawMainDefs LeanosAcpi.proof.LawMainState LeanosAcpi.proof.LawMainCall LeanosAcpi.proof.LawMainSlots0.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.


Lemma copy_step: forall (R: list Z) n i, Zlength R = n -> 0 <= i < n ->
  upd_Znth i (bytes_val (sublist 0 i R) ++ Zrepeat Vundef (n - i)) (Vint (Int.repr (Znth i R))) =
  bytes_val (sublist 0 (i + 1) R) ++ Zrepeat Vundef (n - (i + 1)).
Proof.
  intros. unfold bytes_val. rewrite (sublist_split 0 i (i + 1)) by lia. rewrite map_app.
  rewrite sublist_len_1 by lia. simpl map. list_solve.
Qed.

Lemma tail_bytes {Espec: OracleKind} (TR: tail_ok s_root_check) gv k ad rc tc ph pr pt re te v_copies v_storage v_result v_madt:
  u64_ok k -> u64_ok ad -> 0 <= rc <= Int.max_unsigned -> 0 <= tc <= Int.max_unsigned ->
  isptr ph -> isptr pr -> isptr pt -> isptr re -> isptr te ->
  forall Delta Rp c, Delta = Delta0 -> Rp = Post0 -> c = s_bytes ->
  semax Delta
    (PROP ()
     LOCAL (temp _m (gv _law); lvar _madt tuint v_madt; lvar _result t_result' v_result;
            lvar _storage t_storage' v_storage; lvar _copies t_slots' v_copies; gvars gv)
     SEP (lfields2 (gv _law) k ad (mk_place ph pr pt) rc tc re te hx0 s0;
          data_at_ Ews (tarray tuchar 36) ph; data_at_ Ews (tarray tuchar rc) pr; data_at_ Ews (tarray tuchar tc) pt;
          data_at_ Ews (tarray tuchar rc) re; data_at_ Ews (tarray tuchar tc) te;
          literal RSDT (gv sl3); literal APIC (gv sl1); literal XSDT (gv sl2);
          data_at_ Tsh tuint v_madt; data_at_ Tsh t_result' v_result; data_at_ Tsh t_storage' v_storage;
          data_at_ Tsh t_slots' v_copies; TT))
    c Rp.
Proof.
  intros Hk Had Hrc Htc Pph Ppr Ppt Pre Pte Delta Rp c -> -> ->.
  unfold s_bytes. start_tail.
  unfold lfields2. Intros. cbn [p_header p_root p_tables].
  freeze_but2 [_header; _root; _tables; _root_capacity; _table_capacity; _header_expect; _root_expect; _tables_expect]
    [ph; pr; pt; re; te] FR.
  forward.
  forward_call (ph, 36, Ews).
  { rewrite if_false by (destruct ph; try contradiction; discriminate). cancel. }
  all: try rep_lia.
  Intros H. rewrite if_false by (destruct ph; try contradiction; discriminate).
  change (map (fun b => Vint (Int.repr b)) H) with (bytes_val H).
  forward. forward.
  forward_call (pr, rc, Ews).
  { rewrite if_false by (destruct pr; try contradiction; discriminate). cancel. }
  all: try rep_lia.
  Intros R. rewrite if_false by (destruct pr; try contradiction; discriminate).
  change (map (fun b => Vint (Int.repr b)) R) with (bytes_val R).
  forward. forward.
  forward_call (pt, tc, Ews).
  { rewrite if_false by (destruct pt; try contradiction; discriminate). cancel. }
  all: try rep_lia.
  Intros T. rewrite if_false by (destruct pt; try contradiction; discriminate).
  change (map (fun b => Vint (Int.repr b)) T) with (bytes_val T).
  (* header_expect *)
  freeze_but2 [_header; _header_expect] [ph] FZ.
  forward_for_simple_bound 36
    (EX i: Z, PROP ()
     LOCAL (temp _m (gv _law); lvar _madt tuint v_madt; lvar _result t_result' v_result;
            lvar _storage t_storage' v_storage; lvar _copies t_slots' v_copies; gvars gv)
     SEP (FRZL FZ; data_at Ews (tarray tuchar 36) (bytes_val H) ph; field_at Ews t_law (DOT _header) ph (gv _law);
          field_at Ews t_law (DOT _header_expect) (bytes_val (sublist 0 i H ++ sublist i 36 hx0)) (gv _law)))%assert.
  { entailer!. }
  { assert (Rb: 0 <= Znth i H <= 255) by (apply byte_at; auto; lia).
    forward. forward.
    { entailer!. rewrite Znth_bytes_val by lia. apply tc_byte; auto. }
    rewrite Znth_bytes_val by lia.
    forward. entailer!. rewrite header_copy_step by (unfold hx0, HEADER_BYTES in *; try list_solve; lia).
    apply derives_refl. }
  thaw FZ.
  replace (sublist 0 36 H ++ sublist 36 36 hx0) with H by list_solve.
  (* the root's copy *)
  forward.
  freeze_but2 [_root; _root_capacity; _root_expect] [pr; re] FZ.
  rewrite data_at__eq. change (default_val (tarray tuchar (Zlength R))) with (Zrepeat Vundef (Zlength R)).
  forward_loop
    (EX i: Z, PROP (0 <= i <= (Zlength R))
     LOCAL (temp _i__1 (Vint (Int.repr i)); temp _m (gv _law); lvar _madt tuint v_madt;
            lvar _result t_result' v_result; lvar _storage t_storage' v_storage; lvar _copies t_slots' v_copies;
            gvars gv)
     SEP (FRZL FZ; data_at Ews (tarray tuchar (Zlength R)) (bytes_val R) pr; field_at Ews t_law (DOT _root) pr (gv _law);
          field_at Ews t_law (DOT _root_capacity) (vi (Zlength R)) (gv _law); field_at Ews t_law (DOT _root_expect) re (gv _law);
          data_at Ews (tarray tuchar (Zlength R)) (bytes_val (sublist 0 i R) ++ Zrepeat Vundef ((Zlength R) - i)) re))%assert
    continue:
    (EX i: Z, PROP (0 <= i < (Zlength R))
     LOCAL (temp _i__1 (Vint (Int.repr i)); temp _m (gv _law); lvar _madt tuint v_madt;
            lvar _result t_result' v_result; lvar _storage t_storage' v_storage; lvar _copies t_slots' v_copies;
            gvars gv)
     SEP (FRZL FZ; data_at Ews (tarray tuchar (Zlength R)) (bytes_val R) pr; field_at Ews t_law (DOT _root) pr (gv _law);
          field_at Ews t_law (DOT _root_capacity) (vi (Zlength R)) (gv _law); field_at Ews t_law (DOT _root_expect) re (gv _law);
          data_at Ews (tarray tuchar (Zlength R)) (bytes_val (sublist 0 (i + 1) R) ++ Zrepeat Vundef ((Zlength R) - (i + 1))) re))%assert
    break:
    (PROP ()
     LOCAL (temp _m (gv _law); lvar _madt tuint v_madt;
            lvar _result t_result' v_result; lvar _storage t_storage' v_storage; lvar _copies t_slots' v_copies;
            gvars gv)
     SEP (FRZL FZ; data_at Ews (tarray tuchar (Zlength R)) (bytes_val R) pr; field_at Ews t_law (DOT _root) pr (gv _law);
          field_at Ews t_law (DOT _root_capacity) (vi (Zlength R)) (gv _law); field_at Ews t_law (DOT _root_expect) re (gv _law);
          data_at Ews (tarray tuchar (Zlength R)) (bytes_val R) re)).
  { Exists 0. entailer!. rewrite sublist_nil. replace ((Zlength R) - 0) with (Zlength R) by lia. apply derives_refl. }
  { Intros i. unfold vi. forward. forward_if.
    2: { forward. entailer!. wordp. replace i with (Zlength R) by lia.
         rewrite sublist_same, Z.sub_diag, app_nil_r by lia. apply derives_refl. }
    wordp.
    assert (Rb: 0 <= Znth i R <= 255) by (apply byte_at; auto; lia).
    forward. forward. forward.
    { entailer!. rewrite Znth_bytes_val by lia. apply tc_byte; auto. }
    rewrite Znth_bytes_val by lia.
    forward. Exists i. entailer!. rewrite copy_step by lia. apply derives_refl. }
  { Intros i. forward. Exists (i + 1). entailer!. }
  thaw FZ.
  subst tc.
  (* the tables' copy *)
  forward.
  freeze_but2 [_tables; _table_capacity; _tables_expect] [pt; te] FZ.
  rewrite data_at__eq. change (default_val (tarray tuchar (Zlength T))) with (Zrepeat Vundef (Zlength T)).
  forward_loop
    (EX i: Z, PROP (0 <= i <= (Zlength T))
     LOCAL (temp _i__2 (Vint (Int.repr i)); temp _m (gv _law); lvar _madt tuint v_madt;
            lvar _result t_result' v_result; lvar _storage t_storage' v_storage; lvar _copies t_slots' v_copies;
            gvars gv)
     SEP (FRZL FZ; data_at Ews (tarray tuchar (Zlength T)) (bytes_val T) pt; field_at Ews t_law (DOT _tables) pt (gv _law);
          field_at Ews t_law (DOT _table_capacity) (vi (Zlength T)) (gv _law); field_at Ews t_law (DOT _tables_expect) te (gv _law);
          data_at Ews (tarray tuchar (Zlength T)) (bytes_val (sublist 0 i T) ++ Zrepeat Vundef ((Zlength T) - i)) te))%assert
    continue:
    (EX i: Z, PROP (0 <= i < (Zlength T))
     LOCAL (temp _i__2 (Vint (Int.repr i)); temp _m (gv _law); lvar _madt tuint v_madt;
            lvar _result t_result' v_result; lvar _storage t_storage' v_storage; lvar _copies t_slots' v_copies;
            gvars gv)
     SEP (FRZL FZ; data_at Ews (tarray tuchar (Zlength T)) (bytes_val T) pt; field_at Ews t_law (DOT _tables) pt (gv _law);
          field_at Ews t_law (DOT _table_capacity) (vi (Zlength T)) (gv _law); field_at Ews t_law (DOT _tables_expect) te (gv _law);
          data_at Ews (tarray tuchar (Zlength T)) (bytes_val (sublist 0 (i + 1) T) ++ Zrepeat Vundef ((Zlength T) - (i + 1))) te))%assert
    break:
    (PROP ()
     LOCAL (temp _m (gv _law); lvar _madt tuint v_madt;
            lvar _result t_result' v_result; lvar _storage t_storage' v_storage; lvar _copies t_slots' v_copies;
            gvars gv)
     SEP (FRZL FZ; data_at Ews (tarray tuchar (Zlength T)) (bytes_val T) pt; field_at Ews t_law (DOT _tables) pt (gv _law);
          field_at Ews t_law (DOT _table_capacity) (vi (Zlength T)) (gv _law); field_at Ews t_law (DOT _tables_expect) te (gv _law);
          data_at Ews (tarray tuchar (Zlength T)) (bytes_val T) te)).
  { Exists 0. entailer!. rewrite sublist_nil. replace ((Zlength T) - 0) with (Zlength T) by lia. apply derives_refl. }
  { Intros i. unfold vi. forward. forward_if.
    2: { forward. entailer!. wordp. replace i with (Zlength T) by lia.
         rewrite sublist_same, Z.sub_diag, app_nil_r by lia. apply derives_refl. }
    wordp.
    assert (Rb: 0 <= Znth i T <= 255) by (apply byte_at; auto; lia).
    forward. forward. forward.
    { entailer!. rewrite Znth_bytes_val by lia. apply tc_byte; auto. }
    rewrite Znth_bytes_val by lia.
    forward. Exists i. entailer!. rewrite copy_step by lia. apply derives_refl. }
  { Intros i. forward. Exists (i + 1). entailer!. }
  thaw FZ. thaw FR.
  eapply semax_pre;
    [ | apply (tail_slots0 TR gv k ad (mk_place ph pr pt) re te H R T v_copies v_storage v_result v_madt);
        first [ reflexivity | assumption | lia | auto ] ].
  unfold slots0_pre, lfields2. cbn [p_header p_root p_tables]. entailer!.
Qed.
