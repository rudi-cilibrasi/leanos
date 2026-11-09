(* The body proofs of the unit's functions, for every oracle predicate, under the names the contracts use.  Each is
   proved in a Pipe*.v file: PipeSig.v (acpi_signature_matches, acpi_validate_copied_sdt), PipeEntry.v
   (acpi_decode_root_entries, acpi_decode_root_entry), PipeAddr.v (acpi_decode_root_addresses), PipeMadt.v
   (acpi_select_unique_madt), PipeCopy.v (acpi_copy_sdt), PipeTables.v (acpi_copy_root_tables), PipeRoot.v
   (acpi_copy_root_and_tables), PipeWrap.v (acpi_pipeline); with the lemmas of PipeLemmas.v, PipeModel.v,
   PipeSlots.v and the faster LOCAL simplification of PipeFast.v. *)
Require Import VST.floyd.proofauto.
Require Import LeanosAcpi.acpi.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.InternalSpecs.
Require LeanosAcpi.proof.PipeSig LeanosAcpi.proof.PipeEntry LeanosAcpi.proof.PipeAddr LeanosAcpi.proof.PipeMadt
        LeanosAcpi.proof.PipeCopy LeanosAcpi.proof.PipeTables LeanosAcpi.proof.PipeRoot LeanosAcpi.proof.PipeWrap.
#[local] Existing Instance AcpiSpecs.CS.

Lemma body_acpi_signature_matches (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_acpi_signature_matches signature_matches_spec.
Proof. exact (PipeSig.body_acpi_signature_matches Ora). Qed.
Lemma body_acpi_copy_sdt (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_acpi_copy_sdt (copy_sdt_spec Ora).
Proof. exact (PipeCopy.body_acpi_copy_sdt Ora). Qed.
Lemma body_acpi_validate_copied_sdt (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_acpi_validate_copied_sdt validate_spec.
Proof. exact (PipeSig.body_acpi_validate_copied_sdt Ora). Qed.
Lemma body_acpi_select_unique_madt (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_acpi_select_unique_madt select_unique_madt_spec.
Proof. exact (PipeMadt.body_acpi_select_unique_madt Ora). Qed.
Lemma body_acpi_decode_root_entries (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_acpi_decode_root_entries decode_root_entries_spec.
Proof. exact (PipeEntry.body_acpi_decode_root_entries Ora). Qed.
Lemma body_acpi_decode_root_entry (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_acpi_decode_root_entry decode_root_entry_spec.
Proof. exact (PipeEntry.body_acpi_decode_root_entry Ora). Qed.
Lemma body_acpi_decode_root_addresses (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_acpi_decode_root_addresses decode_root_addresses_spec.
Proof. exact (PipeAddr.body_acpi_decode_root_addresses Ora). Qed.
Lemma body_acpi_copy_root_tables (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_acpi_copy_root_tables (copy_root_tables_spec Ora).
Proof. exact (PipeTables.body_acpi_copy_root_tables Ora). Qed.
Lemma body_acpi_copy_root_and_tables (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_acpi_copy_root_and_tables (copy_root_and_tables_spec Ora).
Proof. exact (PipeRoot.body_acpi_copy_root_and_tables Ora). Qed.
Lemma body_acpi_pipeline (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_acpi_pipeline (pipeline_spec Ora).
Proof. exact (PipeWrap.body_acpi_pipeline Ora). Qed.
