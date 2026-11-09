(* Law table_copy_exact: main from m->root_done = 0 to the call of acpi_pipeline: the law's record before the call,
   the selection (stop or begin_sdt), the law's oracle at the call. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosAcpi.harness.table_copy_exact.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.LawProg LeanosAcpi.proof.LawDefs LeanosAcpi.proof.LawFacts LeanosAcpi.proof.LawLib
  LeanosAcpi.proof.LawLib2 LeanosAcpi.proof.LawOra LeanosAcpi.proof.LawZero LeanosAcpi.proof.LawMainLib
  LeanosAcpi.proof.LawMainDefs LeanosAcpi.proof.LawModel LeanosAcpi.proof.LawMainPure LeanosAcpi.proof.LawMainState
  LeanosAcpi.proof.LawMainCall.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.


(* A zeroed copy slot, and an uninitialized one. *)
Definition usdt : sdt_rep := (Vundef, (Vundef, (Vundef, Vundef))).



Lemma isptr_pn: forall v, isptr v -> is_pointer_or_null v.
Proof. destruct v; simpl; tauto. Qed.

Ltac side_only t := match goal with |- semax _ _ _ _ => idtac | _ => t end.

(* The state at m->root_done = 0. *)
Definition fields_pre (gv: globals) (k ad: Z) (pl: place) (re te: val) (H R T: list Z)
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
       data_at_ Tsh tuint v_madt;
       data_at Tsh t_result' (zroot, (zentries, (vi 0, nullval))) v_result;
       data_at Tsh t_storage' (p_header pl, (p_root pl, (vi (Zlength R), (p_tables pl, (vi (Zlength T), v_copies)))))
         v_storage;
       data_at Tsh t_slots' (Zrepeat zsdt 256) v_copies; TT).

Lemma tail_fields {Espec: OracleKind} (TR: tail_ok s_root_check) gv k ad pl re te H R T v_copies v_storage v_result v_madt:
  u64_ok k -> u64_ok ad -> Zlength H = 36 -> Forall byte_ok H -> Forall byte_ok R -> Forall byte_ok T ->
  Zlength R <= Int.max_unsigned -> Zlength T <= Int.max_unsigned ->
  isptr (p_header pl) -> isptr (p_root pl) -> isptr (p_tables pl) -> isptr re -> isptr te ->
  forall Delta Rp c, Delta = Delta0 -> Rp = Post0 -> c = s_fields ->
  semax Delta (fields_pre gv k ad pl re te H R T v_copies v_storage v_result v_madt) c Rp.
Proof.
  intros Hk Had LH FH FR FT LR LT Pph Ppr Ppt Pre Pte Delta Rp c -> -> ->.
  unfold s_fields, fields_pre. start_tail.
  unfold lfields2. Intros.
  set (x := mk_inputs k ad H R T).
  assert (Ix: inputs_ok x).
  { unfold inputs_ok, x, root_capacity, table_capacity, HEADER_BYTES. cbn [i_kind i_address i_header i_root i_tables].
    unfold u64_ok in *. repeat split; auto; lia. }
  freeze_but2 [_kind; _address; _header; _root; _tables; _root_capacity; _table_capacity; _header_expect; _root_expect; _tables_expect; _expect; _verdict; _is_root; _table; _sdt_address; _destination; _destination_expect; _capacity; _length; _cursor; _byte; _word; _answer; _root_done; _root_length; _entries_done; _width; _count; _root_cursor; _addresses; _arena; _ended; _offsets; _lengths; _finals; _ordinal] (@nil val) FR0.
  unfold u64_ok in Hk, Had.
  forward. forward. forward. forward. forward. forward. forward.
  forward.
  forward_if (temp _t'14 (Vint (Int.repr (Z.b2z (negb (k =? 1) && negb (k =? 2)))))).
  { forward. forward. entailer!. bool_fin. }
  { forward. entailer!. bool_fin. }
  forward_if (temp _t'15 (Vint (Int.repr (Z.b2z (negb ((k =? 1) || (k =? 2)) || (ad =? 0)))))).
  { forward. entailer!. try b2z_hyp. rewrite negb_orb. rw_bools. reflexivity. }
  { forward. forward. entailer!. try b2z_hyp. rewrite negb_orb. rw_bools. bool_fin. }
  forward_if (PROP ()
              LOCAL (temp _m (gv _law); lvar _madt tuint v_madt; lvar _result t_result' v_result;
                     lvar _storage t_storage' v_storage; lvar _copies t_slots' v_copies; gvars gv)
              SEP (FRZL FR0; lfields2 (gv _law) k ad pl (Zlength R) (Zlength T) re te H (s_start x pl re))).
  - (* the selection *)
    try b2z_hyp.
    forward_call (gv _law, Vint (Int.repr (w_expect s0)), Vint (Int.repr (w_verdict s0)), S_ROOT_SELECTION).
    { unfold u32_ok, S_ROOT_SELECTION; rep_lia. }
    entailer!. unfold lfields2, s_start. cbn [x i_kind i_address].
    match goal with E: (_ || _)%bool = true |- _ => rewrite E end.
    unfold s_stop, s_main, s0. lst_cbn. unfold vi, vl. entailer!.
  - try b2z_hyp. forward.
    forward_if.
    + forward_call (gv _law, Vint (Int.repr (w_expect s0)), Vint (Int.repr (w_verdict s0)), S_SDT_ADDRESS_WIDTH).
      { unfold u32_ok, S_SDT_ADDRESS_WIDTH; rep_lia. }
      entailer!. unfold lfields2, s_start. cbn [x i_kind i_address].
      match goal with E: (_ || _)%bool = false |- _ => rewrite E end.
      wordp. try change (Int.unsigned (Int.repr (-1))) with MAX_U32 in *. replace (MAX_U32 <? ad) with true by (symmetry; apply Z.ltb_lt; lia).
      unfold s_stop, s_main, s0. lst_cbn. unfold vi, vl. entailer!.
    + forward. forward. forward. forward.
      forward_call (gv _law, ad, p_root pl, re, Zlength R, 0, Vlong (Int64.repr (w_sdt_address s0)), w_dest s0,
                    w_dexp s0, Vint (Int.repr (w_capacity s0)), Vlong (Int64.repr (w_cursor s0)),
                    Vlong (Int64.repr (w_byte s0)), Vint (Int.repr (w_word s0)), Vint (Int.repr (w_expect s0))).
      { unfold u32_ok, u64_ok. split; rep_lia. }
      entailer!. unfold lfields2, s_start. cbn [x i_kind i_address].
      match goal with E: (_ || _)%bool = false |- _ => rewrite E end.
      wordp. try change (Int.unsigned (Int.repr (-1))) with MAX_U32 in *. replace (MAX_U32 <? ad) with false by (symmetry; apply Z.ltb_ge; lia).
      unfold s_begin, s_main, s0. lst_cbn. unfold vi, vl. cbn [x i_address root_capacity i_root]. entailer!.
  - thaw FR0.
    eapply semax_pre;
      [ | apply (tail_call TR gv x pl re te (s_start x pl re) v_copies v_storage v_result v_madt);
          first [ reflexivity | assumption | apply J_start; auto ] ].
    unfold call_pre. rewrite <- lfields2_lfields. cbn [x i_kind i_address i_header i_root i_tables root_capacity
      table_capacity]. entailer!.
Qed.
