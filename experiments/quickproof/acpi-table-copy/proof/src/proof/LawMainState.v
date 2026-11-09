(* Law table_copy_exact: the states of main the parts of its proof share: at the call of acpi_pipeline, and after it
   (its checks). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosAcpi.harness.table_copy_exact.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.LawProg LeanosAcpi.proof.LawDefs LeanosAcpi.proof.LawFacts LeanosAcpi.proof.LawLib
  LeanosAcpi.proof.LawLib2 LeanosAcpi.proof.LawModel LeanosAcpi.proof.LawOra LeanosAcpi.proof.LawVerdict
  LeanosAcpi.proof.LawZero LeanosAcpi.proof.LawMainLib LeanosAcpi.proof.LawMainDefs LeanosAcpi.proof.LawMainPure
  LeanosAcpi.proof.LawMainModel.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Definition t_storage' := Tstruct _acpi_table_copy_storage noattr.
Definition t_result' := Tstruct _acpi_table_copy_result noattr.
Definition t_slots' := tarray (Tstruct _copied_acpi_sdt noattr) 256.
Definition zsdt : sdt_rep := (vl 0, (nullval, (vi 0, vi 0))).
Definition zroot : sdt_rep := (vl 0, (nullval, (vi 0, vi 0))).
Definition zentries : entries_rep := (nullval, (vi 0, vi 0)).

(* The state at the call. *)
Definition call_pre (gv: globals) (x: inputs) (pl: place) (re te: val) (s: lst)
    (v_copies v_storage v_result v_madt: val) : environ -> mpred :=
  PROP ()
  LOCAL (temp _m (gv _law); lvar _madt tuint v_madt; lvar _result t_result' v_result;
         lvar _storage t_storage' v_storage; lvar _copies t_slots' v_copies; gvars gv)
  SEP (lfields (gv _law) x pl re te (i_header x) s;
       data_at Ews (tarray tuchar 36) (bytes_val (i_header x)) (p_header pl);
       data_at Ews (tarray tuchar (root_capacity x)) (bytes_val (i_root x)) (p_root pl);
       data_at Ews (tarray tuchar (table_capacity x)) (bytes_val (i_tables x)) (p_tables pl);
       data_at Ews (tarray tuchar (root_capacity x)) (bytes_val (i_root x)) re;
       data_at Ews (tarray tuchar (table_capacity x)) (bytes_val (i_tables x)) te;
       literal RSDT (gv sl3); literal APIC (gv sl1); literal XSDT (gv sl2);
       data_at_ Tsh tuint v_madt;
       data_at Tsh t_result' (zroot, (zentries, (vi 0, nullval))) v_result;
       data_at Tsh t_storage' (p_header pl, (p_root pl, (vi (root_capacity x), (p_tables pl, (vi (table_capacity x),
         v_copies))))) v_storage;
       data_at Tsh t_slots' (Zrepeat zsdt 256) v_copies; TT).

Lemma storage_cs: forall sh (v: val * (val * (val * (val * (val * val))))) p,
  @data_at LCS sh t_storage' v p = @data_at AcpiSpecs.CS sh t_storage v p.
Proof.
  intros. apply equal_f. symmetry.
  apply (@data_at_change_composite AcpiSpecs.CS LCS LCR); [ apply JMeq_refl | reflexivity ].
Qed.

Lemma result_cs: forall sh (v: sdt_rep * (entries_rep * (val * val))) p,
  @data_at LCS sh t_result' v p = @data_at AcpiSpecs.CS sh t_result v p.
Proof.
  intros. apply equal_f. symmetry.
  apply (@data_at_change_composite AcpiSpecs.CS LCS LCR); [ apply JMeq_refl | reflexivity ].
Qed.

Lemma slots_cs: forall sh (v: list sdt_rep) p,
  @data_at LCS sh t_slots' v p = @data_at AcpiSpecs.CS sh (tarray t_sdt MAX_ENTRIES) v p.
Proof.
  intros. apply equal_f. symmetry.
  apply (@data_at_change_composite AcpiSpecs.CS LCS LCR); [ apply JMeq_refl | reflexivity ].
Qed.


(* The state after the call, at main's checks: the oracle unfolded (the law's record s, the arenas' copies), the
   pipeline's outcome (st, pub, mm), the madt local mv. *)
Definition check_pre (gv: globals) (x: inputs) (pl: place) (re te: val) (s: lst) (st: Z) (pub: option (Z * Z))
    (mm: mem) (mv: val) (v_copies v_storage v_result v_madt: val) : environ -> mpred :=
  PROP (J x pl re te (Return st pub mm) s; inputs_ok x; eok x mm;
        st = S_OK -> exists i, pub = Some (w_count s, i) /\ mv = vi i)
  LOCAL (temp _status (vi st); temp _m (gv _law); lvar _madt tuint v_madt; lvar _result t_result' v_result;
         lvar _storage t_storage' v_storage; lvar _copies t_slots' v_copies; gvars gv)
  SEP (lfields (gv _law) x pl re te (m_header mm) s;
       data_at Ews (tarray tuchar (root_capacity x)) (bytes_val (m_root mm)) re;
       data_at Ews (tarray tuchar (table_capacity x)) (bytes_val (m_tables mm)) te;
       data_at Ews (tarray tuchar 36) (bytes_val (m_header mm)) (p_header pl);
       data_at Ews (tarray tuchar (root_capacity x)) (bytes_val (m_root mm)) (p_root pl);
       data_at Ews (tarray tuchar (table_capacity x)) (bytes_val (m_tables mm)) (p_tables pl);
       data_at Tsh tuint mv v_madt;
       data_at Tsh t_result' (result_val pl v_copies mm pub zroot zentries (vi 0) nullval) v_result;
       data_at Tsh t_storage' (p_header pl, (p_root pl, (vi (root_capacity x), (p_tables pl, (vi (table_capacity x),
         v_copies))))) v_storage;
       data_at Tsh t_slots' (slots_val pl mm (Zrepeat zsdt 256)) v_copies; TT).

(* A tail of main's checks, from the statement c0 on, from check_pre. *)
Definition tail_ok {Espec: OracleKind} (c0: statement) : Prop :=
  forall gv x pl re te s st pub mm mv v_copies v_storage v_result v_madt Delta Rp c,
  Delta = Delta0 -> Rp = Post0 -> c = c0 ->
  semax Delta (check_pre gv x pl re te s st pub mm mv v_copies v_storage v_result v_madt) c Rp.
