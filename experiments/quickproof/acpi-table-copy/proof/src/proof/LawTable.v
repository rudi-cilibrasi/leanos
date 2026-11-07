(* Law table_copy_exact: the bodies of begin_table (against its fields) and table_copied (against the model's
   table_copied, LawModel). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosAcpi.harness.table_copy_exact.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.LawProg LeanosAcpi.proof.LawDefs LeanosAcpi.proof.LawFacts LeanosAcpi.proof.LawLib
  LeanosAcpi.proof.LawModel.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Lemma body_begin_table : semax_body nil [stop_spec; begin_sdt_spec] f_begin_table begin_table_spec.
Proof.
  start_function.
  assert (Ra: 0 <= Znth t addrs <= Int64.max_unsigned) by (apply (Forall_Znth' _ _ t H1); lia).
  unfold u32_ok, u64_ok, MAX_ENTRIES in *. unfold vi, vl in *.
  forward. forward.
  forward_if.
  - forward_call (q, e0, v0, S_BUDGET).
    forward.
    wordc. replace (cap <=? arena) with true by (symmetry; apply Z.leb_le; lia).
    entailer!.
  - wordc. forward. forward. forward. forward.
    forward. forward. forward. forward. forward. forward. forward. forward.
    forward_call (q, Znth t addrs, offset_val arena tb, offset_val arena te, cap - arena, arena,
                  sa0, d0, de0, c0, cu0, by0, w0, e0).
    all: try (unfold u32_ok, u64_ok; split; [ lia | split; [ lia | split; [ lia | ] ] ];
                destruct tb, te; try contradiction; simpl; auto).
    replace (cap <=? arena) with false by (symmetry; apply Z.leb_gt; lia).
    rewrite (upd_Znth_map (fun v => Vint (Int.repr v))).
    entailer!.
Qed.

Ltac destruct_lst_ok L :=
  let L' := fresh "L" in pose proof L as L';
  unfold lst_ok in L';
  destruct L' as (?L1 & ?L2 & ?L3 & ?L4 & ?L5 & ?L6 & ?L7 & ?L8 & ?L9 & ?L10 & ?L11 & ?L12 & ?L13 & ?L14 & ?L15 &
                  ?L16 & ?L17 & ?L18 & ?L19 & ?L20 & ?L21 & ?L22 & ?L23 & ?L24 & ?L25 & ?L26 & ?L27 & ?L28 & ?L29).

Lemma body_table_copied : semax_body nil [padded_spec; stop_spec] f_table_copied table_copied_spec.
Proof.
  start_function.
  rename H into P.
  pose proof P as (L & F & R & SI & TI & Ln & Cu & LO & I). subst len cursor.
  destruct_lst_ok L.
  pose proof TI as ((T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10) & U1 & U2 & U3).
  unfold len_ok, HEADER_BYTES, MAX_SDT_BYTES in LO. cbn [capacity_of] in LO.
  pose proof (padded_range (w_length s) ltac:(unfold MAX_SDT_BYTES; lia)) as (P1 & P2).
  assert (Rc: table_capacity x <= Int.max_unsigned) by (destruct I as (_ & _ & _ & _ & I5 & _); auto).
  unfold u32_ok, u64_ok, MAX_ENTRIES in *.
  unfold lfields. Intros. unfold vi, vl.
  freeze_but [_table; _length; _lengths; _cursor; _finals; _ended; _arena; _table_capacity; _expect; _verdict; _word]
    (@nil val) FR.
  forward. forward. forward.
  forward. forward. forward.
  forward. forward.
  forward. forward_call (w_length s). { unfold MAX_SDT_BYTES; lia. }
  forward. forward. forward.
  forward_if.
  - (* past the capacity *)
    forward_call (q, Vint (Int.repr (w_expect s)), Vint (Int.repr (w_verdict s)), S_BUDGET).
    forward.
    assert (HJ: J x pl re te (table_copied x l (w_length s) (w_cursor s) m) (s_stop (tc_s1 s) S_BUDGET)).
    { apply J_tc_budget; auto. wordc. lia. }
    Exists (s_stop (tc_s1 s) S_BUDGET). thaw FR. unfold lfields, s_stop, tc_s1. lst_cbn. unfold vi, vl.
    rewrite !(upd_Znth_map (fun v => Vint (Int.repr v))), !(upd_Znth_map (fun v => Vlong (Int64.repr v))).
    entailer!.
  - forward. forward_if.
    + (* the final cursor is not the advanced arena cursor *)
      forward_call (q, Vint (Int.repr (w_expect s)), Vint (Int.repr (w_verdict s)), S_STREAM).
      forward.
      assert (HJ: J x pl re te (table_copied x l (w_length s) (w_cursor s) m) (s_stop (tc_s1 s) S_STREAM)).
      { apply J_tc_stream; auto.
        - wordc. lia.
        - wordc. zmod_norm. rewrite ?Int.unsigned_repr_eq in *. change Int.modulus with (2 ^ 32) in *. lia. }
      Exists (s_stop (tc_s1 s) S_STREAM). thaw FR. unfold lfields, s_stop, tc_s1. lst_cbn. unfold vi, vl.
      rewrite !(upd_Znth_map (fun v => Vint (Int.repr v))), !(upd_Znth_map (fun v => Vlong (Int64.repr v))).
      entailer!.
    + (* placed *)
      forward. forward. forward.
      assert (HJ: J x pl re te (table_copied x l (w_length s) (w_cursor s) m)
                    (set_expect (set_word (set_arena (tc_s1 s) (w_arena s + padded (w_length s))) 0) E_SEQUENCE)).
      { apply J_tc_ok; auto.
        - wordc. lia.
        - wordc. zmod_norm. rewrite ?Int.unsigned_repr_eq in *. change Int.modulus with (2 ^ 32) in *. lia. }
      Exists (set_expect (set_word (set_arena (tc_s1 s) (w_arena s + padded (w_length s))) 0) E_SEQUENCE).
      thaw FR. unfold lfields, tc_s1. lst_cbn. unfold vi, vl.
      rewrite !(upd_Znth_map (fun v => Vint (Int.repr v))), !(upd_Znth_map (fun v => Vlong (Int64.repr v))).
      entailer!.
      rewrite ?Int64.Z_mod_modulus_eq.
      rewrite (Z.mod_small (w_arena s) Int64.modulus), (Z.mod_small (padded (w_length s)) Int64.modulus),
        (Z.mod_small (w_arena s + padded (w_length s)) Int64.modulus) by rep_lia.
      cancel.
Qed.
