(* Law table_copy_exact: main from its loop zeroing the copy slots to m->root_done = 0: the copy slots, the storage
   record and the result record. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosAcpi.harness.table_copy_exact.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.LawProg LeanosAcpi.proof.LawDefs LeanosAcpi.proof.LawFacts LeanosAcpi.proof.LawLib
  LeanosAcpi.proof.LawLib2 LeanosAcpi.proof.LawOra LeanosAcpi.proof.LawZero LeanosAcpi.proof.LawMainLib
  LeanosAcpi.proof.LawMainDefs LeanosAcpi.proof.LawMainState LeanosAcpi.proof.LawMainCall LeanosAcpi.proof.LawMainFields.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

(* The state at main's loop zeroing the copy slots (LawMainSlots0). *)
Definition slots0_pre (gv: globals) (k ad: Z) (pl: place) (re te: val) (H R T: list Z)
    (v_copies v_storage v_result v_madt: val) : environ -> mpred :=
  PROP ()
  LOCAL (temp _m (gv _law); lvar _madt tuint v_madt; lvar _result t_result' v_result;
         lvar _storage t_storage' v_storage; lvar _copies t_slots' v_copies; gvars gv)
  SEP (lfields2 (gv _law) k ad pl (Zlength R) (Zlength T) re te H s0;
       data_at Ews (tarray tuchar 36) (bytes_val H) (p_header pl);
       data_at Ews (tarray tuchar (Zlength R)) (bytes_val R) (p_root pl);
       data_at Ews (tarray tuchar (Zlength T)) (bytes_val T) (p_tables pl);
       data_at Ews (tarray tuchar (Zlength R)) (bytes_val R) re;
       data_at Ews (tarray tuchar (Zlength T)) (bytes_val T) te;
       literal RSDT (gv sl3); literal APIC (gv sl1); literal XSDT (gv sl2);
       data_at_ Tsh tuint v_madt; data_at_ Tsh t_result' v_result; data_at_ Tsh t_storage' v_storage;
       data_at_ Tsh t_slots' v_copies; TT).


Lemma zrep_step: forall {A} {d: Inhabitant A} (a b: A) i n, 0 <= i < n ->
  upd_Znth i (Zrepeat a i ++ Zrepeat b (n - i)) a = Zrepeat a (i + 1) ++ Zrepeat b (n - (i + 1)).
Proof. intros. list_solve. Qed.

Lemma zrep_Znth: forall {A} {d: Inhabitant A} (a b: A) i n, 0 <= i < n -> Znth i (Zrepeat a i ++ Zrepeat b (n - i)) = b.
Proof. intros. list_solve. Qed.

Lemma tail_slots0 {Espec: OracleKind} (TR: tail_ok s_root_check) gv k ad pl re te H R T v_copies v_storage v_result v_madt:
  u64_ok k -> u64_ok ad -> Zlength H = 36 -> Forall byte_ok H -> Forall byte_ok R -> Forall byte_ok T ->
  Zlength R <= Int.max_unsigned -> Zlength T <= Int.max_unsigned ->
  isptr (p_header pl) -> isptr (p_root pl) -> isptr (p_tables pl) -> isptr re -> isptr te ->
  forall Delta Rp c, Delta = Delta0 -> Rp = Post0 -> c = s_slots0 ->
  semax Delta (slots0_pre gv k ad pl re te H R T v_copies v_storage v_result v_madt) c Rp.
Proof.
  intros Hk Had LH FH FR FT LR LT Pph Ppr Ppt Pre Pte Delta Rp c -> -> ->.
  unfold s_slots0, slots0_pre. start_tail.
  freeze_but2 (@nil ident) [v_copies] FR0.
  rewrite data_at__eq.
  change (default_val t_slots') with (Zrepeat usdt 256).
  forward_for_simple_bound 256
    (EX t: Z, PROP ()
     LOCAL (temp _m (gv _law); lvar _madt tuint v_madt; lvar _result t_result' v_result;
            lvar _storage t_storage' v_storage; lvar _copies t_slots' v_copies; gvars gv)
     SEP (FRZL FR0; data_at Tsh t_slots' (Zrepeat zsdt t ++ Zrepeat usdt (256 - t)) v_copies))%assert.
  { entailer!. }
  { forward. forward. forward. forward. entailer!.
    apply derives_refl'. f_equal.
    rewrite !upd_Znth_same by list_solve. rewrite !upd_Znth_twice by list_solve.
    rewrite (zrep_Znth zsdt usdt i 256) by lia. unfold usdt. cbn [fst snd].
    apply (zrep_step zsdt usdt i 256). lia. }
  thaw FR0. replace (Zrepeat zsdt 256 ++ Zrepeat usdt (256 - 256)) with (Zrepeat zsdt 256) by list_solve.
  unfold lfields2. Intros.
  freeze_but2 [_header; _root; _root_capacity; _tables; _table_capacity] [v_storage; v_result] FR1.
  forward. forward. forward. forward. forward. forward. forward. forward. forward. forward. forward.
  forward. forward. forward. forward. forward. forward. forward. forward. forward.
  thaw FR1.
  eapply semax_pre;
    [ | apply (tail_fields TR gv k ad pl re te H R T v_copies v_storage v_result v_madt); first [ reflexivity | assumption ] ].
  unfold fields_pre, lfields2. entailer!.
Qed.
