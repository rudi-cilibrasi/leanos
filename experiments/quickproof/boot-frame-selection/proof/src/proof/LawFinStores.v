(* Law frame_selection_exact: the 64 stores of leanos_boot_projection_finish's local array
   (`const uint64_t words[64] = {w00, ..., w63};`), proved once for any continuation REST, frame R and
   postcondition: the array then holds the 64 free words. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosFrameSelection.harness.frame_selection_exact.code.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
Require Import LeanosFrameSelection.proof.LawProg LeanosFrameSelection.proof.LawDefs LeanosFrameSelection.proof.LawFacts
  LeanosFrameSelection.proof.LawLib.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Definition Gfinish : funspecs := [gp_assert_spec; any_u64_spec; stop_spec].

Definition finish_stores (REST: statement) : statement :=
(Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 0) tint) (tptr tulong)) tulong) (Etempvar _w00 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 1) tint) (tptr tulong)) tulong) (Etempvar _w01 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 2) tint) (tptr tulong)) tulong) (Etempvar _w02 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 3) tint) (tptr tulong)) tulong) (Etempvar _w03 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 4) tint) (tptr tulong)) tulong) (Etempvar _w04 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 5) tint) (tptr tulong)) tulong) (Etempvar _w05 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 6) tint) (tptr tulong)) tulong) (Etempvar _w06 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 7) tint) (tptr tulong)) tulong) (Etempvar _w07 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 8) tint) (tptr tulong)) tulong) (Etempvar _w08 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 9) tint) (tptr tulong)) tulong) (Etempvar _w09 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 10) tint) (tptr tulong)) tulong) (Etempvar _w10 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 11) tint) (tptr tulong)) tulong) (Etempvar _w11 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 12) tint) (tptr tulong)) tulong) (Etempvar _w12 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 13) tint) (tptr tulong)) tulong) (Etempvar _w13 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 14) tint) (tptr tulong)) tulong) (Etempvar _w14 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 15) tint) (tptr tulong)) tulong) (Etempvar _w15 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 16) tint) (tptr tulong)) tulong) (Etempvar _w16 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 17) tint) (tptr tulong)) tulong) (Etempvar _w17 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 18) tint) (tptr tulong)) tulong) (Etempvar _w18 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 19) tint) (tptr tulong)) tulong) (Etempvar _w19 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 20) tint) (tptr tulong)) tulong) (Etempvar _w20 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 21) tint) (tptr tulong)) tulong) (Etempvar _w21 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 22) tint) (tptr tulong)) tulong) (Etempvar _w22 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 23) tint) (tptr tulong)) tulong) (Etempvar _w23 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 24) tint) (tptr tulong)) tulong) (Etempvar _w24 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 25) tint) (tptr tulong)) tulong) (Etempvar _w25 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 26) tint) (tptr tulong)) tulong) (Etempvar _w26 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 27) tint) (tptr tulong)) tulong) (Etempvar _w27 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 28) tint) (tptr tulong)) tulong) (Etempvar _w28 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 29) tint) (tptr tulong)) tulong) (Etempvar _w29 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 30) tint) (tptr tulong)) tulong) (Etempvar _w30 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 31) tint) (tptr tulong)) tulong) (Etempvar _w31 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 32) tint) (tptr tulong)) tulong) (Etempvar _w32 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 33) tint) (tptr tulong)) tulong) (Etempvar _w33 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 34) tint) (tptr tulong)) tulong) (Etempvar _w34 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 35) tint) (tptr tulong)) tulong) (Etempvar _w35 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 36) tint) (tptr tulong)) tulong) (Etempvar _w36 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 37) tint) (tptr tulong)) tulong) (Etempvar _w37 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 38) tint) (tptr tulong)) tulong) (Etempvar _w38 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 39) tint) (tptr tulong)) tulong) (Etempvar _w39 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 40) tint) (tptr tulong)) tulong) (Etempvar _w40 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 41) tint) (tptr tulong)) tulong) (Etempvar _w41 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 42) tint) (tptr tulong)) tulong) (Etempvar _w42 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 43) tint) (tptr tulong)) tulong) (Etempvar _w43 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 44) tint) (tptr tulong)) tulong) (Etempvar _w44 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 45) tint) (tptr tulong)) tulong) (Etempvar _w45 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 46) tint) (tptr tulong)) tulong) (Etempvar _w46 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 47) tint) (tptr tulong)) tulong) (Etempvar _w47 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 48) tint) (tptr tulong)) tulong) (Etempvar _w48 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 49) tint) (tptr tulong)) tulong) (Etempvar _w49 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 50) tint) (tptr tulong)) tulong) (Etempvar _w50 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 51) tint) (tptr tulong)) tulong) (Etempvar _w51 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 52) tint) (tptr tulong)) tulong) (Etempvar _w52 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 53) tint) (tptr tulong)) tulong) (Etempvar _w53 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 54) tint) (tptr tulong)) tulong) (Etempvar _w54 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 55) tint) (tptr tulong)) tulong) (Etempvar _w55 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 56) tint) (tptr tulong)) tulong) (Etempvar _w56 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 57) tint) (tptr tulong)) tulong) (Etempvar _w57 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 58) tint) (tptr tulong)) tulong) (Etempvar _w58 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 59) tint) (tptr tulong)) tulong) (Etempvar _w59 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 60) tint) (tptr tulong)) tulong) (Etempvar _w60 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 61) tint) (tptr tulong)) tulong) (Etempvar _w61 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 62) tint) (tptr tulong)) tulong) (Etempvar _w62 tulong))
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _words (tarray tulong 64)) (Econst_int (Int.repr 63) tint) (tptr tulong)) tulong) (Etempvar _w63 tulong))
  REST)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition finish_locals (fw: list Z) (q: val) (vw: val) (gv: globals) : list localdef :=
  [temp _w00 (vl (Znth 0 fw));
         temp _w01 (vl (Znth 1 fw));
         temp _w02 (vl (Znth 2 fw));
         temp _w03 (vl (Znth 3 fw));
         temp _w04 (vl (Znth 4 fw));
         temp _w05 (vl (Znth 5 fw));
         temp _w06 (vl (Znth 6 fw));
         temp _w07 (vl (Znth 7 fw));
         temp _w08 (vl (Znth 8 fw));
         temp _w09 (vl (Znth 9 fw));
         temp _w10 (vl (Znth 10 fw));
         temp _w11 (vl (Znth 11 fw));
         temp _w12 (vl (Znth 12 fw));
         temp _w13 (vl (Znth 13 fw));
         temp _w14 (vl (Znth 14 fw));
         temp _w15 (vl (Znth 15 fw));
         temp _w16 (vl (Znth 16 fw));
         temp _w17 (vl (Znth 17 fw));
         temp _w18 (vl (Znth 18 fw));
         temp _w19 (vl (Znth 19 fw));
         temp _w20 (vl (Znth 20 fw));
         temp _w21 (vl (Znth 21 fw));
         temp _w22 (vl (Znth 22 fw));
         temp _w23 (vl (Znth 23 fw));
         temp _w24 (vl (Znth 24 fw));
         temp _w25 (vl (Znth 25 fw));
         temp _w26 (vl (Znth 26 fw));
         temp _w27 (vl (Znth 27 fw));
         temp _w28 (vl (Znth 28 fw));
         temp _w29 (vl (Znth 29 fw));
         temp _w30 (vl (Znth 30 fw));
         temp _w31 (vl (Znth 31 fw));
         temp _w32 (vl (Znth 32 fw));
         temp _w33 (vl (Znth 33 fw));
         temp _w34 (vl (Znth 34 fw));
         temp _w35 (vl (Znth 35 fw));
         temp _w36 (vl (Znth 36 fw));
         temp _w37 (vl (Znth 37 fw));
         temp _w38 (vl (Znth 38 fw));
         temp _w39 (vl (Znth 39 fw));
         temp _w40 (vl (Znth 40 fw));
         temp _w41 (vl (Znth 41 fw));
         temp _w42 (vl (Znth 42 fw));
         temp _w43 (vl (Znth 43 fw));
         temp _w44 (vl (Znth 44 fw));
         temp _w45 (vl (Znth 45 fw));
         temp _w46 (vl (Znth 46 fw));
         temp _w47 (vl (Znth 47 fw));
         temp _w48 (vl (Znth 48 fw));
         temp _w49 (vl (Znth 49 fw));
         temp _w50 (vl (Znth 50 fw));
         temp _w51 (vl (Znth 51 fw));
         temp _w52 (vl (Znth 52 fw));
         temp _w53 (vl (Znth 53 fw));
         temp _w54 (vl (Znth 54 fw));
         temp _w55 (vl (Znth 55 fw));
         temp _w56 (vl (Znth 56 fw));
         temp _w57 (vl (Znth 57 fw));
         temp _w58 (vl (Znth 58 fw));
         temp _w59 (vl (Znth 59 fw));
         temp _w60 (vl (Znth 60 fw));
         temp _w61 (vl (Znth 61 fw));
         temp _w62 (vl (Znth 62 fw));
         temp _w63 (vl (Znth 63 fw));
   temp _m q; lvar _words (tarray tulong 64) vw; gvars gv].

Lemma fill_step: forall (l: list Z) n k k1 r r1, Zlength l = n -> 0 <= k < n -> k1 = k + 1 -> r = n - k ->
  r1 = n - k1 ->
  upd_Znth k (map vl (sublist 0 k l) ++ Zrepeat Vundef r) (vl (Znth k l)) = map vl (sublist 0 k1 l) ++ Zrepeat Vundef r1.
Proof. intros. subst. list_solve. Qed.

(* The store words[k] = w_k, with the array kept as the words so far and the rest undefined. *)
Ltac fill_one l n k :=
  forward;
  let k1 := eval cbv in (k + 1) in let r := eval cbv in (n - k) in let r1 := eval cbv in (n - k1) in
  rewrite (fill_step l n k k1 r r1) by (auto; lia).

Ltac fill_all l n k :=
  lazymatch eval cbv in (k <? n) with
  | true => fill_one l n k; let k' := eval cbv in (k + 1) in fill_all l n k'
  | false => idtac
  end.

Lemma semax_finish_stores {Espec: OracleKind}: forall gv q fw vw (Fr: mpred) REST Pst Delta,
  Delta = func_tycontext f_leanos_boot_projection_finish Vlaw Gfinish nil ->
  Zlength fw = 64 ->
  semax Delta (PROPx nil (LOCALx (finish_locals fw q vw gv)
                 (SEPx (Fr :: data_at Tsh (tarray tulong 64) (map vl fw) vw :: nil)))) REST Pst ->
  semax Delta (PROPx nil (LOCALx (finish_locals fw q vw gv)
                 (SEPx (Fr :: data_at_ Tsh (tarray tulong 64) vw :: nil)))) (finish_stores REST) Pst.
Proof.
  intros gv q fw vw Fr REST Pst Delta -> L H.
  unfold finish_stores, finish_locals in *.
  simplify_func_tycontext.
  rewrite data_at__eq.
  replace (default_val (tarray tulong 64)) with (map vl (sublist 0 0 fw) ++ Zrepeat Vundef 64) by reflexivity.
  fill_all fw 64 0.
  replace (map vl (sublist 0 64 fw) ++ Zrepeat Vundef 0) with (map vl fw) by (rewrite sublist_same by lia; list_solve).
  exact H.
Qed.
