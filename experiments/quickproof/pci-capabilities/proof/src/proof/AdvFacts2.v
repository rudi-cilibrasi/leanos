(* Law capabilities_adversarial: more facts of a walk (AdvFacts), for the harness's checks. *)
Require Import VST.floyd.proofauto.
Require Import LeanosCaps.proof.Defs.
Require Import LeanosCaps.proof.AdvWalk LeanosCaps.proof.AdvFacts.
Local Open Scope Z_scope.

(* The offset of every outcome is a byte (it is stored into the result's uint8_t field). *)
Lemma f_off_range: forall words h st off caps, walk words h = Some (st, off, caps) -> 0 <= off <= 255.
Proof.
  intros words h st off caps W.
  destruct (walk_view _ _ _ _ _ W) as [HO [(k & Hk & Lk & G & Ec & Eo & C)|(L & G & R & A & O)]].
  - rewrite Eo, (HO k) by lia. unfold hc_off.
    assert (E: k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
    destruct E as [ -> | [ -> | [ -> | -> ] ] ]; simpl; lia.
  - pose proof (Zlength_chain h L) as Lc.
    assert (P: forall i, 0 <= i <= Zlength (chain h) -> 0 <= Znth i (ptrs (list_head words) (chain h)) <= 255).
    { intros. apply ptrs_range; [ apply list_head_range | lia ]. }
    unfold chain_out in O. destruct O as [O|[O|[O|[O|O]]]].
    + destruct O as (_ & -> & _). lia.
    + destruct O as (_ & O1 & _ & -> & _). apply P. lia.
    + destruct O as (_ & O1 & _ & _ & -> & _). apply P. lia.
    + destruct O as (_ & _ & -> & _). apply P. lia.
    + destruct O as (_ & _ & -> & _). apply P. lia.
Qed.
