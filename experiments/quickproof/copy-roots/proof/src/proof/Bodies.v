(* The body proofs of the unit's functions, under the names the contracts use: SmallProof.v (the small functions
   and the three wrappers), BuildProof.v (qotom_build_copy_roots) and WindowProof.v (frame_window_root_exact and
   frame_window_build). *)
Require Import VST.floyd.proofauto.
Require Import LeanosRoots.roots.code.
Require Import LeanosRoots.proof.Defs.
Require Import LeanosRoots.proof.RootsSpecs.
Require LeanosRoots.proof.SmallProof LeanosRoots.proof.BuildProof LeanosRoots.proof.WindowProof.
#[local] Existing Instance RootsSpecs.CS.

Lemma body_qotom_root_table_entry : semax_body Vprog Gprog f_qotom_root_table_entry table_entry_spec. Proof. exact SmallProof.body_qotom_root_table_entry. Qed.
Lemma body_qotom_root_phys_ok : semax_body Vprog Gprog f_qotom_root_phys_ok phys_ok_spec. Proof. exact SmallProof.body_qotom_root_phys_ok. Qed.
Lemma body_qotom_root_phys_disjoint : semax_body Vprog Gprog f_qotom_root_phys_disjoint phys_disjoint_spec. Proof. exact SmallProof.body_qotom_root_phys_disjoint. Qed.
Lemma body_qotom_root_protected_frame :
  semax_body Vprog Gprog f_qotom_root_protected_frame protected_frame_spec. Proof. exact SmallProof.body_qotom_root_protected_frame. Qed.
Lemma body_qotom_root_source_ancestors :
  semax_body Vprog Gprog f_qotom_root_source_ancestors source_ancestors_spec. Proof. exact SmallProof.body_qotom_root_source_ancestors. Qed.
Lemma body_qotom_build_copy_roots :
  semax_body Vprog Gprog f_qotom_build_copy_roots build_copy_roots_spec. Proof. exact BuildProof.body_qotom_build_copy_roots. Qed.
Lemma body_frame_window_pages : semax_body Vprog Gprog f_frame_window_pages window_pages_spec. Proof. exact SmallProof.body_frame_window_pages. Qed.
Lemma body_frame_window_geometry_ok :
  semax_body Vprog Gprog f_frame_window_geometry_ok geometry_ok_spec. Proof. exact SmallProof.body_frame_window_geometry_ok. Qed.
Lemma body_frame_window_root_exact : semax_body Vprog Gprog f_frame_window_root_exact root_exact_spec. Proof. exact WindowProof.body_frame_window_root_exact. Qed.
Lemma body_frame_window_build : semax_body Vprog Gprog f_frame_window_build frame_window_build_spec. Proof. exact WindowProof.body_frame_window_build. Qed.
Lemma body_roots_build : semax_body Vprog Gprog f_roots_build roots_build_spec. Proof. exact SmallProof.body_roots_build. Qed.
Lemma body_window_build : semax_body Vprog Gprog f_window_build window_build_spec. Proof. exact SmallProof.body_window_build. Qed.
Lemma body_window_root_exact : semax_body Vprog Gprog f_window_root_exact window_root_exact_spec. Proof. exact SmallProof.body_window_root_exact. Qed.
