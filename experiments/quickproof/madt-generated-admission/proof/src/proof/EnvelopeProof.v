(* The body proof of madt_generated_envelope (include/madt_generated_admission.h): the byte loop (the invariant
   `run ... = Some (envelope_from x i st)`, with next_byte, declared_length and checksum the words of st and
   next_byte = i), its inner loop of 7 step calls (`envelope_collect x i st cur`, the answer array holding cur),
   the checks of envelope_check, each early return the model's envelope_end, and the final checks of
   envelope_final (the header's next_byte == length holds by next_byte = i). *)
Require Import VST.floyd.proofauto.
Require Import LeanosMadtAdmission.madt_admission.code.
Require Import LeanosMadtAdmission.proof.Defs.
Require Import LeanosMadtAdmission.proof.MgaSpecs.
Require Import LeanosMadtAdmission.proof.InternalSpecs.
Require Import LeanosMadtAdmission.proof.BodyLemmas.
#[local] Existing Instance MgaSpecs.CS.
Local Open Scope Z_scope.

Lemma body_madt_generated_envelope (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_madt_generated_envelope (generated_envelope_spec Ora).
Proof.
  start_function.
  match goal with H: inputs_ok x |- _ => destruct H as (Ulen & Lbytes & Ubytes & Uex & Largs & Uargs & Uprior) end.
  match goal with H: run _ _ h = _ |- _ => rename H into Hrun end.
  assert (Rlen: 0 <= i_length x <= Int.max_unsigned) by exact Ulen.
  forward. forward. forward.
  forward_for_simple_bound (i_length x) (EX i: Z, EX hs: list answer, EX st: list Z,
    PROP (run x (start x) (h ++ hs) = Some (envelope_from x i st); Zlength st = 3; Forall u64_ok st;
          Znth 0 st = i)
    LOCAL (temp _next_byte (vl (Znth 0 st)); temp _declared_length (vl (Znth 1 st));
           temp _checksum (vl (Znth 2 st)); lvar _answer (tarray tulong 7) v_answer; gvars gv;
           temp _bytes bp; temp _length (Vint (Int.repr (i_length x))))
    SEP (data_at_ Tsh (tarray tulong 7) v_answer; Ora gv x (h ++ hs);
         data_at sh (tarray tuchar (i_length x)) (bytes_val (i_bytes x)) bp))%assert.
  { Exists (@nil answer) initial_envelope. rewrite app_nil_r. entailer!.
    unfold initial_envelope; repeat constructor; unfold u64_ok; rep_lia. }
  { (* byte i *)
    cbv beta. Intros hs st.
    match goal with H: run _ _ (h ++ hs) = _ |- _ => rename H into Hr end.
    rewrite env_from_go in Hr by lia.
    assert (Bi: byte_ok (Znth i (i_bytes x))) by (apply Forall_Znth; auto; lia).
    forward.
    { rewrite Znth_bytes_val by lia. entailer!. all: first [ apply tc_byte; auto | unfold byte_ok in *; rep_lia ]. }
    rewrite Znth_bytes_val by lia.
    forward.
    rewrite Int.unsigned_repr by (unfold byte_ok in Bi; rep_lia).
    forward.
    match goal with |- context [temp _terminal ?T] => replace T with (vl (terminal x i)) end.
    2: { unfold vl, terminal. f_equal. unfold Int64.cmpu.
         change (Int.signed (Int.repr 1)) with 1. rewrite Int.unsigned_repr by rep_lia.
         rewrite add64_repr, eq64_repr by (unfold u64_ok; rep_lia).
         destruct (Z.eqb_spec (i + 1) (i_length x)); reflexivity. }
    assert (Ut: u64_ok (terminal x i)) by (unfold terminal; u64).
    rewrite (data_at__eq _ (tarray tulong 7) v_answer).
    change (default_val (tarray tulong 7)) with (Zrepeat Vundef 7).
    forward_for_simple_bound 7 (EX k: Z, EX hs': list answer, EX cur: list Z,
      PROP (run x (start x) (h ++ hs') = Some (envelope_collect x i st cur); Zlength cur = k; Forall u64_ok cur)
      LOCAL (temp _terminal (vl (terminal x i)); temp _value (Vlong (Int64.repr (Znth i (i_bytes x))));
             temp _byte (Vlong (Int64.repr i)); temp _next_byte (vl (Znth 0 st));
             temp _declared_length (vl (Znth 1 st)); temp _checksum (vl (Znth 2 st));
             lvar _answer (tarray tulong 7) v_answer; gvars gv;
             temp _bytes bp; temp _length (Vint (Int.repr (i_length x))))
      SEP (data_at Tsh (tarray tulong 7) (map vl cur ++ Zrepeat Vundef (7 - k)) v_answer; Ora gv x (h ++ hs');
           data_at sh (tarray tuchar (i_length x)) (bytes_val (i_bytes x)) bp))%assert.
    { Exists hs (@nil Z). entailer!. }
    { (* word k *)
      cbv beta. Intros.
      match goal with H: Zlength cur = ?k |- _ => subst k end.
      freeze FR := (data_at _ _ _ v_answer) (data_at _ _ _ bp).
      forward_call (gv, x, h ++ hs', st, i_length x, i, Znth i (i_bytes x), terminal x i, Zlength cur).
      { apply (env_call x _ i st cur); [ assumption | lia ]. }
      Intros v. thaw FR.
      forward.
      Exists (hs' ++ [(EnvelopeStep st (i_length x) i (Znth i (i_bytes x)) (terminal x i) (Zlength cur), v)])
        (cur ++ [v]).
      rewrite <- app_assoc.
      entailer!.
      { split; [ rewrite app_assoc; apply env_answer; [ assumption | lia ] |
          split; [ rewrite Zlength_app, Zlength_cons, Zlength_nil; lia |
                   apply Forall_app; split; [ assumption | constructor; auto ] ] ]. }
      apply derives_refl'. f_equal. apply upd_answers; lia. }
    Intros hs' a.
    match goal with H: run _ _ (h ++ hs') = Some (envelope_collect x i st a) |- _ => rename H into Ha end.
    match goal with H: Zlength a = 7 |- _ => rename H into La end.
    match goal with H: Forall u64_ok a |- _ => rename H into Ua end.
    match goal with |- context [data_at Tsh (tarray tulong 7) ?X v_answer] =>
      replace X with (map vl a) by list_solve end.
    forward.
    forward_if.
    { (* word 0 *)
      z64. forward.
      Exists hs' 1. entailer!.
      rewrite Ha. f_equal. apply env_reject; [ assumption | unfold envelope_check; zrw; reflexivity | unfold S_OK; lia ]. }
    z64.
    forward_if (temp _t'2 (Vint (Int.repr (if i + 1 =? i_length x then 3 else 1)))).
    { z64. unfold terminal in *. destruct (i + 1 =? i_length x); [ forward; entailer! | contradiction ]. }
    { z64. unfold terminal in *. destruct (i + 1 =? i_length x); [ discriminate | forward; entailer! ]. }
    forward.
    forward_if.
    { (* word 1 *)
      z64. forward.
      Exists hs' 2. entailer!.
      rewrite Ha. f_equal. apply env_reject; [ assumption | unfold envelope_check; zrw; reflexivity | unfold S_OK; lia ]. }
    z64.
    forward.
    forward_if.
    { (* word 2 *)
      z64. forward.
      Exists hs' 3. entailer!.
      rewrite Ha. f_equal. apply env_reject; [ assumption | unfold envelope_check; zrw; reflexivity | unfold S_OK; lia ]. }
    z64.
    forward.
    forward_if.
    { (* word 3 *)
      z64. forward.
      Exists hs' 4. entailer!.
      rewrite Ha. f_equal. apply env_reject; [ assumption | unfold envelope_check; zrw; reflexivity | unfold S_OK; lia ]. }
    z64.
    forward.
    forward_if.
    { (* word 6 *)
      z64. forward.
      Exists hs' 5. entailer!.
      rewrite Ha. f_equal. apply env_reject; [ assumption | unfold envelope_check; zrw; reflexivity | unfold S_OK; lia ]. }
    z64.
    forward. forward. forward.
    Exists hs' [Znth 3 a; Znth 4 a; Znth 5 a].
    entailer!.
    split; [ rewrite Ha; f_equal; apply env_accept; [ assumption | unfold envelope_check; zrw; reflexivity ] | ].
    repeat constructor; u64. }
  (* the final checks *)
  Intros hs st.
  match goal with H: run _ _ (h ++ hs) = _ |- _ => rename H into Hr end.
  match goal with H: Znth 0 st = i_length x |- _ => rename H into S0 end.
  rewrite env_from_done in Hr.
  forward_if (temp _t'3 (Vint (Int.repr (b2z (negb (Znth 1 st =? i_length x)))))).
  { z64. contradiction. }
  { z64. forward. entailer!. bnorm. bclose. }
  forward_if.
  { bfix. forward.
    Exists hs 6. entailer!.
    rewrite Hr. f_equal. f_equal. unfold envelope_final. zrw. reflexivity. }
  bfix.
  forward_if.
  { z64. forward.
    Exists hs 7. entailer!.
    rewrite Hr. f_equal. f_equal. unfold envelope_final. zrw. reflexivity. }
  z64. forward.
  Exists hs 0. entailer!.
  rewrite Hr. f_equal. f_equal. unfold envelope_final. zrw. reflexivity.
Qed.
