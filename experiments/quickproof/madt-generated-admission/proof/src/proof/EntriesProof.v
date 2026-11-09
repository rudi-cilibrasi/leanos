(* The body proof of madt_generated_entries (include/madt_generated_admission.h): the bounds (begin_entries), the
   initial state, the offset loop (the invariant `run ... = Some (entries_from x k st)`, the state array holding
   st, state[0] = k) with its inner loop of 16 step calls (`entries_collect x k st cur`, the answer array holding
   cur), the checks of entries_check, each early return the model's entries_end, the copy state[word] =
   answer[word + 3] (sublist 3 15 of the answers), and the final checks of entries_final (the header's
   state[0] == length holds by state[0] = k, its state[7] > 255 is no other test than state[7] != executing by
   executing <= 255). *)
Require Import VST.floyd.proofauto.
Require Import LeanosMadtAdmission.madt_admission.code.
Require Import LeanosMadtAdmission.proof.Defs.
Require Import LeanosMadtAdmission.proof.MgaSpecs.
Require Import LeanosMadtAdmission.proof.InternalSpecs.
Require Import LeanosMadtAdmission.proof.BodyLemmas.
#[local] Existing Instance MgaSpecs.CS.
Local Open Scope Z_scope.

Lemma body_madt_generated_entries (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_madt_generated_entries (generated_entries_spec Ora).
Proof.
  start_function.
  match goal with H: inputs_ok x |- _ => destruct H as (Ulen & Lbytes & Ubytes & Uex & Largs & Uargs & Uprior) end.
  match goal with H: run _ _ h = _ |- _ => rename H into Hrun end.
  assert (Rlen: 0 <= i_length x <= Int.max_unsigned) by exact Ulen.
  assert (Rex: 0 <= i_executing x <= Int.max_unsigned) by exact Uex.
  forward_if (temp _t'1 (Vint (Int.repr (b2z ((i_length x <=? 44) || (255 <? i_executing x))%bool)))).
  { z64. forward. entailer!. rewrite (proj2 (Z.leb_le (i_length x) 44)) by lia. reflexivity. }
  { z64. forward. entailer!. rewrite (proj2 (Z.leb_gt (i_length x) 44)) by lia.
    destruct (zlt 255 (i_executing x)); destruct (Z.ltb_spec 255 (i_executing x)); try lia; reflexivity. }
  forward_if.
  { (* the bounds *)
    bfix. forward.
    Exists (@nil answer) 8 0. rewrite app_nil_r. entailer!. u32_split.
    rewrite Hrun. f_equal. apply begin_reject. assumption. }
  bfix.
  match goal with H: ((_ <=? 44) || _)%bool = false |- _ => rename H into Hb end.
  rewrite begin_accept in Hrun by exact Hb.
  apply orb_false_iff in Hb as [L44 E255]. apply Z.leb_gt in L44. apply Z.ltb_ge in E255.
  forward. forward. forward. forward. forward. forward. forward. forward. forward. forward. forward. forward.
  match goal with |- context [data_at Tsh (tarray tulong 12) ?X v_state] =>
    replace X with (map vl initial_entries) by (unfold initial_entries, vl; reflexivity) end.
  forward_for_simple_bound (i_length x) (EX k: Z, EX hs: list answer, EX st: list Z,
    PROP (run x (start x) (h ++ hs) = Some (entries_from x k st); Zlength st = 12; Forall u64_ok st;
          Znth 0 st = k)
    LOCAL (lvar _answer (tarray tulong 16) v_answer; lvar _state (tarray tulong 12) v_state; gvars gv;
           temp _bytes bp; temp _length (Vint (Int.repr (i_length x)));
           temp _executing_apic_id (Vint (Int.repr (i_executing x))); temp _admitted_apic_id rp)
    SEP (data_at_ Tsh (tarray tulong 16) v_answer; data_at Tsh (tarray tulong 12) (map vl st) v_state;
         Ora gv x (h ++ hs); data_at sh (tarray tuchar (i_length x)) (bytes_val (i_bytes x)) bp;
         data_at rsh tuint rold rp))%assert.
  { Exists (@nil answer) initial_entries. rewrite app_nil_r. entailer!.
    unfold initial_entries; repeat constructor; unfold u64_ok; rep_lia. }
  { (* offset k *)
    cbv beta. Intros hs st.
    match goal with H: run _ _ (h ++ hs) = _ |- _ => rename H into Hr end.
    rewrite ent_from_go in Hr by lia.
    assert (Bk: byte_ok (Znth i (i_bytes x))) by (apply Forall_Znth; auto; lia).
    forward.
    { rewrite Znth_bytes_val by lia. entailer!. all: first [ apply tc_byte; auto | unfold byte_ok in *; rep_lia ]. }
    rewrite Znth_bytes_val by lia.
    forward.
    rewrite Int.unsigned_repr by (unfold byte_ok in Bk; rep_lia).
    forward.
    match goal with |- context [temp _terminal ?T] => replace T with (vl (terminal x i)) end.
    2: { unfold vl, terminal. f_equal. unfold Int64.cmpu.
         change (Int.unsigned (Int.repr 1)) with 1. rewrite Int.unsigned_repr by rep_lia.
         rewrite add64_repr, eq64_repr by (unfold u64_ok; rep_lia).
         destruct (Z.eqb_spec (i + 1) (i_length x)); reflexivity. }
    rewrite (data_at__eq _ (tarray tulong 16) v_answer).
    change (default_val (tarray tulong 16)) with (Zrepeat Vundef 16).
    forward_for_simple_bound 16 (EX w: Z, EX hs': list answer, EX cur: list Z,
      PROP (run x (start x) (h ++ hs') = Some (entries_collect x i st cur); Zlength cur = w; Forall u64_ok cur)
      LOCAL (temp _terminal (vl (terminal x i)); temp _value (Vlong (Int64.repr (Znth i (i_bytes x))));
             temp _offset (Vlong (Int64.repr i));
             lvar _answer (tarray tulong 16) v_answer; lvar _state (tarray tulong 12) v_state; gvars gv;
             temp _bytes bp; temp _length (Vint (Int.repr (i_length x)));
             temp _executing_apic_id (Vint (Int.repr (i_executing x))); temp _admitted_apic_id rp)
      SEP (data_at Tsh (tarray tulong 16) (map vl cur ++ Zrepeat Vundef (16 - w)) v_answer;
           data_at Tsh (tarray tulong 12) (map vl st) v_state;
           Ora gv x (h ++ hs'); data_at sh (tarray tuchar (i_length x)) (bytes_val (i_bytes x)) bp;
           data_at rsh tuint rold rp))%assert.
    { Exists hs (@nil Z). entailer!. }
    { (* word w *)
      cbv beta. Intros.
      match goal with H: Zlength cur = ?k |- _ => subst k end.
      forward. forward. forward. forward. forward. forward. forward. forward. forward. forward. forward. forward.
      freeze FR := (data_at _ _ _ v_answer) (data_at _ _ _ v_state) (data_at _ _ _ bp) (data_at _ _ _ rp).
      forward_call (gv, x, h ++ hs', st, i_length x, i_executing x, i, Znth i (i_bytes x), Zlength cur).
      { apply (ent_call x _ i st cur); [ assumption | lia ]. }
      Intros v. thaw FR.
      forward.
      Exists (hs' ++ [(EntryStep st (i_length x) (i_executing x) i (Znth i (i_bytes x)) (Zlength cur), v)])
        (cur ++ [v]).
      rewrite <- app_assoc.
      entailer!.
      { split; [ rewrite app_assoc; apply ent_answer; [ assumption | lia ] |
          split; [ rewrite Zlength_app, Zlength_cons, Zlength_nil; lia |
                   apply Forall_app; split; [ assumption | constructor; auto ] ] ]. }
      apply derives_refl'. f_equal. apply upd_answers; lia. }
    Intros hs' a.
    match goal with H: run _ _ (h ++ hs') = Some (entries_collect x i st a) |- _ => rename H into Ha end.
    match goal with H: Zlength a = 16 |- _ => rename H into La end.
    match goal with H: Forall u64_ok a |- _ => rename H into Ua end.
    match goal with |- context [data_at Tsh (tarray tulong 16) ?X v_answer] =>
      replace X with (map vl a) by list_solve end.
    forward.
    forward_if.
    { (* word 0 *)
      z64. forward.
      Exists hs' 9 0. entailer!. u32_split.
      rewrite Ha. f_equal. apply ent_reject; [ assumption | unfold entries_check; zrw; reflexivity | unfold S_OK; lia ]. }
    z64.
    forward_if (temp _t'3 (Vint (Int.repr (if i + 1 =? i_length x then 3 else 1)))).
    { z64. unfold terminal in *. destruct (i + 1 =? i_length x); [ forward; entailer! | contradiction ]. }
    { z64. unfold terminal in *. destruct (i + 1 =? i_length x); [ discriminate | forward; entailer! ]. }
    forward.
    forward_if.
    { (* word 1 *)
      z64. forward.
      Exists hs' 10 0. entailer!. u32_split.
      rewrite Ha. f_equal. apply ent_reject; [ assumption | unfold entries_check; zrw; reflexivity | unfold S_OK; lia ]. }
    z64.
    forward.
    forward_if.
    { (* word 2 *)
      z64. forward.
      Exists hs' 11 0. entailer!. u32_split.
      rewrite Ha. f_equal. apply ent_reject; [ assumption | unfold entries_check; zrw; reflexivity | unfold S_OK; lia ]. }
    z64.
    forward.
    forward_if.
    { (* word 3 *)
      z64. forward.
      Exists hs' 12 0. entailer!. u32_split.
      rewrite Ha. f_equal. apply ent_reject; [ assumption | unfold entries_check; zrw; reflexivity | unfold S_OK; lia ]. }
    z64.
    forward.
    forward_if.
    { (* word 15 *)
      z64. forward.
      Exists hs' 13 0. entailer!. u32_split.
      rewrite Ha. f_equal. apply ent_reject; [ assumption | unfold entries_check; zrw; reflexivity | unfold S_OK; lia ]. }
    z64.
    assert (Hc: entries_check x i a = S_OK) by (unfold entries_check; zrw; reflexivity).
    rewrite (ent_accept x i st a La Hc) in Ha.
    forward_for_simple_bound 12 (EX w: Z,
      PROP ()
      LOCAL (temp _offset (Vlong (Int64.repr i));
             lvar _answer (tarray tulong 16) v_answer; lvar _state (tarray tulong 12) v_state; gvars gv;
             temp _bytes bp; temp _length (Vint (Int.repr (i_length x)));
             temp _executing_apic_id (Vint (Int.repr (i_executing x))); temp _admitted_apic_id rp)
      SEP (data_at Tsh (tarray tulong 16) (map vl a) v_answer;
           data_at Tsh (tarray tulong 12) (map vl (sublist 3 (3 + w) a) ++ sublist w 12 (map vl st)) v_state;
           Ora gv x (h ++ hs'); data_at sh (tarray tuchar (i_length x)) (bytes_val (i_bytes x)) bp;
           data_at rsh tuint rold rp))%assert.
    { replace (map vl (sublist 3 (3 + 0) a) ++ sublist 0 12 (map vl st)) with (map vl st) by list_solve.
      entailer!. }
    { cbv beta. Intros.
      forward. forward.
      entailer!.
      apply derives_refl'. f_equal. apply upd_copy; auto; lia. }
    replace (map vl (sublist 3 (3 + 12) a) ++ sublist 12 12 (map vl st)) with (map vl (sublist 3 15 a))
      by list_solve.
    Exists hs' (sublist 3 15 a).
    entailer!.
    split; [ list_solve | split; [ apply Forall_sublist; auto | rewrite Znth_sublist by lia; auto ] ]. }
  (* the final checks *)
  Intros hs st.
  match goal with H: run _ _ (h ++ hs) = _ |- _ => rename H into Hr end.
  match goal with H: Znth 0 st = i_length x |- _ => rename H into S0 end.
  match goal with H: Zlength st = 12 |- _ => rename H into Ls end.
  match goal with H: Forall u64_ok st |- _ => rename H into Us end.
  rewrite ent_from_done in Hr.
  forward.
  forward_if (temp _t'4 (Vint (Int.repr (b2z (negb (Znth 1 st =? 0)))))).
  { z64. contradiction. }
  { z64. forward. forward. entailer!. bnorm. bclose. }
  forward_if (temp _t'5 (Vint (Int.repr (b2z (negb (Znth 1 st =? 0) || negb (Znth 2 st =? 0))%bool)))).
  { bfix. forward. entailer!. zrw. reflexivity. }
  { bfix. forward. forward. entailer!. zrw. bnorm. bclose. }
  forward_if (temp _t'6 (Vint (Int.repr (b2z (negb (Znth 1 st =? 0) || negb (Znth 2 st =? 0) ||
                                                negb (Znth 3 st =? 0))%bool)))).
  { bfix. forward. entailer!. zrw. reflexivity. }
  { bfix. forward. forward. entailer!. zrw. bnorm. bclose. }
  forward_if (temp _t'7 (Vint (Int.repr (b2z (negb (Znth 1 st =? 0) || negb (Znth 2 st =? 0) ||
                                                negb (Znth 3 st =? 0) || negb (Znth 4 st =? 0))%bool)))).
  { bfix. forward. entailer!. zrw. reflexivity. }
  { bfix. forward. forward. entailer!. zrw. bnorm. bclose. }
  forward_if (temp _t'8 (Vint (Int.repr (b2z (negb (Znth 1 st =? 0) || negb (Znth 2 st =? 0) ||
                                                negb (Znth 3 st =? 0) || negb (Znth 4 st =? 0) ||
                                                negb (Znth 5 st =? 0))%bool)))).
  { bfix. forward. entailer!. zrw. reflexivity. }
  { bfix. forward. forward. entailer!. zrw. bnorm. bclose. }
  forward_if.
  { (* an unfinished record *)
    bfix. forward.
    Exists hs 14 0. entailer!. u32_split.
    rewrite Hr. f_equal.
    apply ent_final_reject; [ unfold entries_final; rewrite rec_demorgan; zrw; reflexivity | unfold S_OK; lia ]. }
  bfix.
  match goal with H: (_ || negb (Znth 5 st =? 0))%bool = false |- _ => rename H into Hrec end.
  rewrite <- rec_demorgan in Hrec.
  deadvars!.
  forward.
  forward_if.
  { (* the enabled count *)
    z64. forward.
    Exists hs 15 0. entailer!. u32_split.
    rewrite Hr. f_equal. apply ent_final_reject; [ unfold entries_final; zrw; reflexivity | unfold S_OK; lia ]. }
  z64.
  forward.
  forward_if (temp _t'9 (Vint (Int.repr (b2z (negb (Znth 7 st =? i_executing x)))))).
  { z64. forward. entailer!. rewrite (proj2 (Z.eqb_neq (Znth 7 st) (i_executing x))) by lia. reflexivity. }
  { z64. forward. forward. entailer!. bnorm. bclose. }
  forward_if.
  { (* the admitted APIC ID *)
    bfix. forward.
    Exists hs 16 0. entailer!. u32_split.
    rewrite Hr. f_equal. apply ent_final_reject; [ unfold entries_final; zrw; reflexivity | unfold S_OK; lia ]. }
  bfix.
  match goal with H: (Znth 7 st =? i_executing x) = true |- _ => apply Z.eqb_eq in H; rename H into Hid end.
  assert (U8: u64_ok (Znth 8 st)) by u64. assert (U9: u64_ok (Znth 9 st)) by u64.
  assert (U10: u64_ok (Znth 10 st)) by u64. assert (U11: u64_ok (Znth 11 st)) by u64.
  deadvars!.
  forward. forward. forward. forward.
  forward_if.
  { (* an empty seen set *)
    match goal with H: Int64.or _ _ = Int64.zero |- _ => rewrite (or4_zero _ _ _ _ U8 U9 U10 U11) in H end.
    forward.
    Exists hs 17 0. entailer!. u32_split.
    rewrite Hr. f_equal. apply ent_final_reject; [ unfold entries_final; zrw; reflexivity | unfold S_OK; lia ]. }
  assert (Hseen: ((Znth 8 st =? 0) && (Znth 9 st =? 0) && (Znth 10 st =? 0) && (Znth 11 st =? 0))%bool = false).
  { match goal with H: Int64.or _ _ <> _ |- _ => rename H into Hn end.
    destruct ((Znth 8 st =? 0) && (Znth 9 st =? 0) && (Znth 10 st =? 0) && (Znth 11 st =? 0))%bool eqn:E;
      [ | reflexivity ].
    exfalso. apply Hn. change (Int64.repr 0) with Int64.zero. apply (or4_zero _ _ _ _ U8 U9 U10 U11). exact E. }
  assert (U7: 0 <= Znth 7 st < Int64.modulus)
    by (pose proof (u64_ok_Znth st 7 Us ltac:(lia)) as U; unfold u64_ok in U; rep_lia).
  assert (I7: u32_ok (Znth 7 st)) by (rewrite Hid; exact Uex).
  forward. forward.
  rewrite ?Int64.Z_mod_modulus_eq, ?(Z.mod_small (Znth 7 st)) by exact U7.
  rewrite ?(Int64.unsigned_repr (Znth 7 st)) by rep_lia.
  forward.
  Exists hs 0 (Znth 7 st). entailer!.
  rewrite Hr. f_equal. f_equal. unfold entries_final. zrw. reflexivity.
Qed.
