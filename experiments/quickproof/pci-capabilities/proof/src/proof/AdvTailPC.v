(* Law capabilities_adversarial: main from the check of POINTER and CYCLE on (the walker walked the four header
   reads; the last read succeeded and is not an absent header). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosCaps.harness.capabilities_adversarial.code.
Require Import LeanosCaps.proof.Defs.
Require LeanosCaps.proof.CapsSpecs.
Require Import LeanosCaps.proof.AdvProg LeanosCaps.proof.AdvWalk LeanosCaps.proof.AdvFacts LeanosCaps.proof.AdvSpecs
  LeanosCaps.proof.AdvLib LeanosCaps.proof.AdvMainDefs LeanosCaps.proof.AdvFacts2 LeanosCaps.proof.AdvTables
  LeanosCaps.proof.AdvTailOK.
Local Open Scope Z_scope.

(* The statement of main from `if (status == PCI_CAPABILITY_POINTER || status == PCI_CAPABILITY_CYCLE)` on. *)
Definition s_pc : statement := ltac:(
  let b := eval cbv delta [f_main] beta iota zeta in (fn_body f_main) in
  match b with
  | context [Ssequence (Ssequence (Sifthenelse (Ebinop Oeq (Etempvar _status tint) (Econst_int (Int.repr 4) tint) tint)
                                    (Sset _t'39 ?a) ?b) ?c) ?d] =>
      exact (Ssequence (Ssequence (Ssequence (Sifthenelse (Ebinop Oeq (Etempvar _status tint)
                                                  (Econst_int (Int.repr 4) tint) tint) (Sset _t'39 a) b) c) d)
               (Sreturn (Some (Econst_int (Int.repr 0) tint))))
  end).

Definition pc_pre (gv: globals) (v_initial v_d v_snapshot v_result v_header_offsets v_masks: val)
    (bus dev fn: Z) (ws: list Z) (ro: Z) (qb: bool) (h: list answer) (st off: Z) (caps: list (Z * Z))
    (rest: list (reptype CapsSpecs.t_cap)) (offs oks vals: list val) : environ -> mpred :=
    (PROP ()
     LOCAL (temp _offset (Vint (Int.repr (if qb then ro else off)));
            temp _status (Vint (Int.repr st));
            temp _result_arg (if qb then nullval else v_result);
            lvar _masks (tarray tuint 4) v_masks; lvar _header_offsets (tarray tuchar 4) v_header_offsets;
            lvar _result t_res v_result; lvar _snapshot t_snap v_snapshot; lvar _d t_device v_d;
            lvar _initial t_header v_initial; gvars gv)
     SEP (data_at Tsh t_header (hdr_val bus dev fn ws) v_initial;
          data_at Tsh t_device
            (Vint (Int.repr bus), (Vint (Int.repr dev), (Vint (Int.repr fn),
             (Vint (Int.repr (Zlength h)), (offs, (oks, vals)))))) v_d;
          data_at Tsh CapsSpecs.t_snapshot (Vint (Int.repr (Zlength caps)), map CapsSpecs.cap_val caps ++ rest)
            v_snapshot;
          data_at Tsh CapsSpecs.t_result
            (Vint (Int.repr (if qb then 0 else st)), Vint (Int.repr (if qb then ro else off))) v_result;
          TT; data_at Tsh (tarray tuint 4) ML v_masks; data_at Tsh (tarray tuchar 4) OL v_header_offsets;
          has_ext tt)).

(* bool_fin, also for the sumbool of equality. *)
Ltac bool_fin2 :=
  bsubst;
  rewrite ?shru_and_repr by rep_lia;
  rewrite ?Int_ltu_repr by rng;
  rewrite ?Int_eq_repr by rng;
  repeat match goal with
  | |- context [zlt ?a ?b] => destruct (zlt a b)
  | |- context [zeq ?a ?b] => destruct (zeq a b)
  | |- context [?a <? ?b] => destruct (Z.ltb_spec a b)
  | |- context [?a =? ?b] => destruct (Z.eqb_spec a b)
  end; try lia; reflexivity.

(* The loop of `repeated`: k from 4, repeated = f k. *)
Ltac loop_rep n f :=
  match goal with |- semax _ (PROPx ?Ps (LOCALx (temp _k__2 _ :: temp _repeated _ :: ?Q) (SEPx ?R))) _ _ =>
    forward_loop (EX k: Z, PROPx ((4 <= k <= n) :: Ps)
                   (LOCALx (temp _k__2 (Vint (Int.repr k)) :: temp _repeated (Vint (Int.repr (CapsSpecs.b2z (f k))))
                           :: Q) (SEPx R)))
      break: (PROPx Ps (LOCALx (temp _repeated (Vint (Int.repr (CapsSpecs.b2z (f n)))) :: Q) (SEPx R)))
  end.

(* The device's struct, back as Dev_adv. *)
Lemma to_dev: forall bus dev fn h offs oks vals p,
  Zlength h <= 52 -> answers_ok h -> log_at h offs oks vals ->
  data_at Tsh t_device
    (Vint (Int.repr bus), (Vint (Int.repr dev), (Vint (Int.repr fn),
     (Vint (Int.repr (Zlength h)), (offs, (oks, vals)))))) p |-- Dev_adv p (bus, dev, fn) h.
Proof.
  intros. unfold Dev_adv. Exists offs oks vals. unfold dev_val. simpl. entailer!.
Qed.

Lemma existsb_sublist_snoc {A} {d: Inhabitant A}: forall (f: A -> bool) (l: list A) lo k, 0 <= lo <= k -> k < Zlength l ->
  existsb f (sublist lo (k + 1) l) = (existsb f (sublist lo k l) || f (Znth k l))%bool.
Proof.
  intros. rewrite (sublist_split lo k (k + 1)) by lia. rewrite existsb_app.
  rewrite sublist_len_1 by lia. simpl. rewrite orb_false_r. reflexivity.
Qed.

Lemma tail_pc {Espec: OracleKind} gv v_initial v_d v_snapshot v_result v_header_offsets v_masks
    bus dev fn ws ro (qb: bool) h st off caps (rest: list (reptype CapsSpecs.t_cap)) offs oks vals:
  isptr v_result -> Zlength ws = 16 -> Forall CapsSpecs.u32_ok ws -> 0 <= ro <= Byte.max_unsigned ->
  Zlength caps + Zlength rest = 48 ->
  walk ws h = Some (st, off, caps) -> st <> 1 -> st <> 2 -> st <> 3 -> st <> 6 ->
  Zlength h <= 52 -> answers_ok h -> log_at h offs oks vals ->
  forall Delta R c, Delta = Delta0 -> R = Post0 -> c = s_pc ->
  semax Delta
    (pc_pre gv v_initial v_d v_snapshot v_result v_header_offsets v_masks bus dev fn ws ro qb h st off caps rest
       offs oks vals)
    c R.
Proof.
  intros until c. intros -> -> ->.
  unfold s_pc, pc_pre.
  start_tail.
  rename H4 into W. rename H5 into N1. rename H6 into N2. rename H7 into N3. rename H8 into N6.
  rename H9 into Lh52. rename H10 into Ans. rename H11 into LA.
  pose proof LA as (L1 & L2 & L3 & F).
  pose proof (f_len ws h st off caps W) as Lh1.
  pose proof (f_st_range ws h st off caps W) as [Rst _].
  pose proof (f_n4 ws h st off caps W ltac:(unfold S_READ_FAILED; lia) ltac:(unfold S_HEADER_CHANGED; lia)) as N4.
  pose proof (f_okL ws h st off caps W ltac:(unfold S_READ_FAILED; lia)) as OkL.
  forward_if (temp _t'39 (Vint (Int.repr (CapsSpecs.b2z ((st =? 4) || (st =? 5))%bool)))).
  { forward. entailer!. }
  { forward. entailer!. bool_fin2. }
  forward_if.
  { b2z_hyps.
    assert (Ept: st = S_POINTER \/ st = S_CYCLE).
    { unfold S_POINTER, S_CYCLE.
      match goal with E: ((st =? 4) || (st =? 5))%bool = true |- _ =>
        apply orb_true_iff in E; destruct E as [E|E]; apply Z.eqb_eq in E; lia end. }
    pose proof (f_PC ws h st off caps W Ept) as [Pn Po].
    pose proof (named_range ws h N4) as Rn.
    (* p = named_pointer(&d, &initial) *)
    sep_apply (to_dev bus dev fn h offs oks vals v_d Lh52 Ans LA).
    forward_call (v_d, (bus, dev, fn), h, v_initial, Tsh, bus, dev, fn, ws).
    (* p names the failure *)
    forward_if (temp _t'34 (Vint Int.one)).
    { forward_if (temp _t'34 (Vint Int.one)).
      { tc_sel. }
      { forward. entailer!. }
      { match goal with E: (if _ then nullval else _) <> nullval |- _ => apply sel_ne_null in E end. subst qb.
        forward. forward. all: try (entailer!; rewrite Po, Int.eq_true; reflexivity). }
      all: try entailer!. }
    { exfalso. lia. }
    gp_call.
    (* repeated: some list read asked for p *)
    forward. forward.
    unfold Dev_adv. Intros offs2 oks2 vals2.
    match goal with L: log_at h offs2 oks2 vals2 |- _ => pose proof L as (M1 & M2 & M3 & F2) end.
    unfold dev_val, CapsSpecs.bus_of, CapsSpecs.dev_of, CapsSpecs.fn_of. simpl fst; simpl snd.
    loop_rep (Zlength h) (fun k => existsb (fun a => aoff a =? named ws h) (sublist 4 k h)).
    { Exists 4. entailer!. rewrite sublist_nil. reflexivity. }
    { Intros k.
      fw.
      forward_if.
      { destruct (F2 k ltac:(lia)) as (Fo2 & _ & _).
        pose proof (answers_ok_Znth h k Ans ltac:(lia)) as [Rak _].
        ldv Fo2.
        forward_if (temp _repeated (Vint (Int.repr (CapsSpecs.b2z
                       (existsb (fun a => aoff a =? named ws h) (sublist 4 (k + 1) h)))))).
        { forward. entailer!. rewrite existsb_sublist_snoc by lia.
          replace (aoff (Znth k h) =? named ws h) with true by (symmetry; apply Z.eqb_eq; auto).
          rewrite orb_true_r. reflexivity. }
        { forward. entailer!. rewrite existsb_sublist_snoc by lia.
          replace (aoff (Znth k h) =? named ws h) with false by (symmetry; apply Z.eqb_neq; auto).
          rewrite orb_false_r. reflexivity. }
        forward.
        Exists (k + 1). entailer!. }
      { forward. entailer!. replace k with (Zlength h) by lia. reflexivity. }
      }
    change (existsb (fun a => aoff a =? named ws h) (sublist 4 (Zlength h) h)) with (seen_in h (named ws h)).
    if_same.
    { (* POINTER: p is below 0x40, misaligned, or the 49th *)
      pose proof (f_P ws h st off caps W ltac:(unfold S_POINTER; lia)) as FP.
      forward_if (temp _t'35 (Vint (Int.repr (CapsSpecs.b2z
                    ((named ws h <? 64) || negb (Z.land (named ws h) 3 =? 0))%bool)))).
      { forward. entailer!. bool_fin2. }
      { forward. entailer!. rewrite ?and_repr. bool_fin2. }
      forward_if (temp _t'36 (Vint Int.one)).
      { forward. entailer!. }
      { b2z_hyps.
        assert (SF: seen_in h (named ws h) = false /\ Zlength h = 52).
        { match goal with E: (_ || _)%bool = false |- _ =>
            apply orb_false_iff in E; destruct E as [E1 E2]; apply Z.ltb_ge in E1;
            apply negb_false_iff, Z.eqb_eq in E2 end.
          destruct FP as [FP|[FP|FP]]; [ lia | contradiction | exact FP ]. }
        destruct SF as [SF E52]. rewrite SF. simpl CapsSpecs.b2z.
        forward_if (temp _t'36 (Vint Int.one)).
        { fw. forward. forward. all: try (entailer!; rewrite E52; reflexivity). }
        { exfalso. match goal with N: Int.repr 0 <> Int.zero |- _ => apply N; reflexivity end. }
        rewrite SF. entailer!. }
      gp_call.
      all: try entailer!. }
    { (* CYCLE: p is a valid pointer some list read asked for *)
      assert (E5: st = S_CYCLE).
      { unfold S_CYCLE. destruct Ept as [E|E]; [ unfold S_POINTER in E; lia | exact E ]. }
      pose proof (f_C ws h st off caps W E5) as (C1 & C2 & C3).
      rewrite C3. simpl CapsSpecs.b2z.
      forward_if (temp _t'37 (Vint Int.one)).
      { forward. entailer!. rewrite ?and_repr. rewrite C2. reflexivity. }
      { exfalso. lia. }
      forward_if (temp _t'38 (Vint Int.one)).
      { forward. entailer!. }
      { discriminate. }
      gp_call.
      all: try (rewrite C3; entailer!). }
    free_locals v_initial v_d v_snapshot v_result.
    forward.
    Exists (Int.repr 0). entailer!. }
  (* none of the failures: OK *)
  assert (E0: st = S_OK).
  { pose proof (f_st ws h st off caps W) as Est.
    match goal with E: ((st =? 4) || (st =? 5))%bool = false |- _ =>
      apply orb_false_iff in E; destruct E as [E4 E5]; apply Z.eqb_neq in E4; apply Z.eqb_neq in E5 end.
    unfold S_OK, S_READ_FAILED, S_HEADER_CHANGED, S_POINTER, S_CYCLE, S_ABSENT in *. lia. }
  deadvars!.
  eapply semax_pre;
    [ | apply (tail_ok gv v_initial v_d v_snapshot v_result v_header_offsets v_masks bus dev fn ws ro qb h st off
                 caps rest offs oks vals); first [ reflexivity | assumption ] ].
  unfold ok_pre. entailer!.
Qed.
