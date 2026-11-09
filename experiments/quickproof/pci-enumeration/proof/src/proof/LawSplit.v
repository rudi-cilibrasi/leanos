(* Law enumeration_exact: struct device field by field.  VST's loads and stores on the whole struct (16 headers of
   16 words) are slow; the proofs split it once into its fields with this lemma and join it back with it. *)
Require Import VST.floyd.proofauto.
Require Import LeanosEnum.harness.enumeration_exact.code.
Require Import LeanosEnum.proof.LawProg LeanosEnum.proof.LawSpecs.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Definition dev_fields (next w nfound stopped failed reads: Z) (l: loc) (seen: list hv) (ctx: val) : mpred :=
  (field_at Tsh t_device (DOT _next) (Vint (Int.repr next)) ctx *
  field_at Tsh t_device (DOT _word) (Vint (Int.repr w)) ctx *
  field_at Tsh t_device (DOT _found) (Vint (Int.repr nfound)) ctx *
  field_at Tsh t_device (DOT _stopped) (Vint (Int.repr stopped)) ctx *
  field_at Tsh t_device (DOT _failed) (Vint (Int.repr failed)) ctx *
  field_at Tsh t_device (DOT _reads) (Vint (Int.repr reads)) ctx *
  field_at Tsh t_device (DOT _last_bus) (fst l) ctx *
  field_at Tsh t_device (DOT _last_device) (fst (snd l)) ctx *
  field_at Tsh t_device (DOT _last_function) (fst (snd (snd l))) ctx *
  field_at Tsh t_device (DOT _last_offset) (snd (snd (snd l))) ctx *
  field_at Tsh t_device (DOT _seen) seen ctx)%logic.

Lemma dev_split: forall next w nfound stopped failed reads l seen ctx,
  data_at Tsh t_device (dev_val next w nfound stopped failed reads l seen) ctx =
  dev_fields next w nfound stopped failed reads l seen ctx.
Proof.
  intros. unfold dev_val, dev_fields.
  unfold_data_at (data_at _ _ _ ctx).
  rewrite !sepcon_assoc. reflexivity.
Qed.
