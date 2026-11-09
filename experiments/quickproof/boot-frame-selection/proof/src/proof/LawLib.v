(* Law frame_selection_exact: what the proofs of the harness's functions share: the law's pointer valid, the
   objects between the unit's compspecs and the law's, the law's fields folded, the oracle re-established after
   an answer, and the tactics of the branches and checks. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosFrameSelection.harness.frame_selection_exact.code.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
Require Import LeanosFrameSelection.proof.LawProg LeanosFrameSelection.proof.LawDefs LeanosFrameSelection.proof.LawFacts.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[export] Existing Instance LawProg.LCS.

Lemma law_valid: forall v q, field_at Ews t_law (DOT _call) v q |-- valid_pointer q.
Proof.
  intros. apply field_at_valid_ptr0; [ apply readable_nonidentity, writable_readable, writable_Ews | | ];
    reflexivity.
Qed.
#[export] Hint Resolve law_valid : valid_pointer.

Lemma Znth_map_vl: forall l i, 0 <= i < Zlength l -> Znth i (map vl l) = vl (Znth i l).
Proof. intros. rewrite Znth_map by auto. reflexivity. Qed.

Lemma upd_Znth_map_vl: forall l i v, upd_Znth i (map vl l) (vl v) = map vl (upd_Znth i l v).
Proof. intros. rewrite upd_Znth_map. reflexivity. Qed.

Lemma upd_Znth_map_vl': forall l i v, upd_Znth i (map vl l) (Vlong (Int64.repr v)) = map vl (upd_Znth i l v).
Proof. intros. apply upd_Znth_map_vl. Qed.

Ltac upd_vl := rewrite ?upd_Znth_map_vl, ?upd_Znth_map_vl'.

(* ---------------------------------------------------------------------- *)
(* The objects between the compspecs                                       *)
(* ---------------------------------------------------------------------- *)

Lemma data_at_arr_cs: forall (cs1 cs2: compspecs) sh n (v: list val) p,
  @data_at cs1 sh (tarray tulong n) v p = @data_at cs2 sh (tarray tulong n) v p.
Proof.
  intros. apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [ apply JMeq_refl | reflexivity ].
Qed.

Lemma data_at__arr_cs: forall (cs1 cs2: compspecs) sh n p,
  @data_at_ cs1 sh (tarray tulong n) p = @data_at_ cs2 sh (tarray tulong n) p.
Proof.
  intros. apply (f_equal (fun f => f p)).
  apply (@data_at__change_composite cs1 cs2 (CCE_any cs1 cs2)); reflexivity.
Qed.

Lemma data_at_states_cs: forall (cs1 cs2: compspecs) sh (v: list (list val)) p,
  @data_at cs1 sh t_states v p = @data_at cs2 sh t_states v p.
Proof.
  intros. apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [ apply JMeq_refl | reflexivity ].
Qed.

Lemma data_at_ulong_cs: forall (cs1 cs2: compspecs) sh v p,
  @data_at cs1 sh tulong v p = @data_at cs2 sh tulong v p.
Proof.
  intros. apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [ apply JMeq_refl | reflexivity ].
Qed.

Lemma data_at_uint_cs: forall (cs1 cs2: compspecs) sh v p,
  @data_at cs1 sh tuint v p = @data_at cs2 sh tuint v p.
Proof.
  intros. apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite cs1 cs2 (CCE_any cs1 cs2)); [ apply JMeq_refl | reflexivity ].
Qed.

(* ---------------------------------------------------------------------- *)
(* The law's fields and the oracle                                         *)
(* ---------------------------------------------------------------------- *)

Lemma lfields_fold: forall q x sp mm s,
 (field_at Ews t_law (DOT _call) (vi (w_call s)) q *
  field_at Ews t_law (DOT _take_next) (vi (i_take_next x)) q *
  field_at Ews t_law (DOT _selected) (vl (i_selected x)) q *
  field_at Ews t_law (DOT _selected_manifest) (vl (i_selected_manifest x)) q *
  field_at Ews t_law (DOT _published) (vl (i_published x)) q *
  field_at Ews t_law (DOT _next) (vl (i_next x)) q *
  field_at Ews t_law (DOT _running) (vi (w_running s)) q *
  field_at Ews t_law (DOT _manifest) (map vl (i_manifest x)) q *
  field_at Ews t_law (DOT _decoded) (map vl (i_decoded x)) q *
  field_at Ews t_law (DOT _usable) (map vl (i_usable x)) q *
  field_at Ews t_law (DOT _blocked) (map vl (i_blocked x)) q *
  field_at Ews t_law (DOT _reserved_expect) (map vl (m_reserved mm)) q *
  field_at Ews t_law (DOT _terminal_expect) (map vl (m_terminal mm)) q *
  field_at Ews t_law (DOT _states_expect) (states_val (m_states mm)) q *
  field_at Ews t_law (DOT _publication_expect) (map vl (m_publication mm)) q *
  field_at Ews t_law (DOT _rescan_expect) (map vl (m_rescan mm)) q *
  field_at Ews t_law (DOT _selected_expect) (vl (m_selected mm)) q *
  field_at Ews t_law (DOT _manifest_expect) (vl (m_selected_manifest mm)) q *
  field_at Ews t_law (DOT _next_expect) (vl (m_next mm)) q *
  field_at Ews t_law (DOT _decoder_expect) (vi (m_decoder mm)) q *
  field_at Ews t_law (DOT _states) sp q *
  field_at Ews t_law (DOT _step) (vi (w_step s)) q *
  field_at Ews t_law (DOT _expect) (vi (w_expect s)) q *
  field_at Ews t_law (DOT _verdict) (vi (w_verdict s)) q *
  field_at Ews t_law (DOT _block) (vl (w_block s)) q *
  field_at Ews t_law (DOT _word) (vl (w_word s)) q *
  field_at Ews t_law (DOT _candidate) (vl (w_candidate s)) q *
  field_at Ews t_law (DOT _scan) (vi (w_scan s)) q *
  field_at Ews t_law (DOT _manifest_status) (vl (w_ms s)) q *
  field_at Ews t_law (DOT _manifest_error) (vl (w_me s)) q *
  field_at Ews t_law (DOT _free_words) (map vl (w_free s)) q *
  field_at Ews t_law (DOT _candidate_manifest) (vl (w_cm s)) q *
  field_at Ews t_law (DOT _first) (vl (w_first s)) q *
  field_at Ews t_law (DOT _first_manifest) (vl (w_fm s)) q *
  field_at Ews t_law (DOT _second) (vl (w_second s)) q *
  field_at Ews t_law (DOT _answer) (map vl (w_answer s)) q *
  field_at Ews t_law (DOT _scrubbed) (vi (w_scrubbed s)) q)%logic |-- lfields q x sp mm s.
Proof. intros. unfold lfields. apply derives_refl. Qed.

(* The oracle after the answer r to the call c, the model then at p and the record s. *)
Lemma ora_close: forall gv sp x h c r p s,
  inputs_ok x -> answers_ok h -> reply_ok c r -> run x (start x) (h ++ [(c, r)]) = Some p -> J x p s ->
  lfields (gv _law) x sp (mem_of p) s |-- Ora_law gv (gv _law) (gv _law) sp x (h ++ [(c, r)]).
Proof.
  intros gv sp x h c r p s Ix A R Rn HJ. unfold Ora_law. Exists p s. entailer!.
  apply answers_ok_snoc; auto.
Qed.

(* The oracle before any call. *)
Lemma ora_start: forall gv sp x s, inputs_ok x -> J x (start x) s ->
  lfields (gv _law) x sp (i_mem x) s |-- Ora_law gv (gv _law) (gv _law) sp x nil.
Proof.
  intros gv sp x s Ix HJ. unfold Ora_law. Exists (start x) s. rewrite mem_of_start. entailer!.
  constructor.
Qed.

(* ---------------------------------------------------------------------- *)
(* Tactics                                                                 *)
(* ---------------------------------------------------------------------- *)

Ltac first_stmt c := lazymatch c with Ssequence ?c1 _ => first_stmt c1 | _ => c end.

Ltac uns64_hyps :=
  repeat match goal with E: context [Int64.unsigned (Int64.repr ?k)] |- _ =>
    rewrite (Int64.unsigned_repr k) in E by rep_lia end.
Ltac uns32_hyps :=
  repeat match goal with E: context [Int.unsigned (Int.repr ?k)] |- _ =>
    rewrite (Int.unsigned_repr k) in E by rep_lia end.

(* The branch conditions of 64- and 32-bit arithmetic as facts on Z. *)
Ltac u64c :=
  change Int64.zero with (Int64.repr 0) in *; change Int64.one with (Int64.repr 1) in *;
  change Int.zero with (Int.repr 0) in *; change Int.one with (Int.repr 1) in *;
  rewrite ?add64_repr', ?add_repr' in *; uns64_hyps; uns32_hyps;
  repeat match goal with E: context [Int.signed (Int.repr ?k)] |- _ =>
    rewrite (Int.signed_repr k) in E by rep_lia end;
  repeat match goal with
  | E: (_ =? _) = true |- _ => apply Z.eqb_eq in E
  | E: (_ =? _) = false |- _ => apply Z.eqb_neq in E
  | E: (_ <? _) = true |- _ => apply Z.ltb_lt in E
  | E: (_ <? _) = false |- _ => apply Z.ltb_ge in E
  | E: Int.repr _ = Int.repr _ |- _ => apply repr_inj_unsigned in E; [ | rep_lia | rep_lia ]
  | E: Int.repr _ <> Int.repr _ |- _ => apply repr_neq_e in E
  | E: Int64.repr _ = Int64.repr _ |- _ => apply repr64_inj in E; [ | rep_lia | rep_lia ]
  | E: Int64.repr _ <> Int64.repr _ |- _ => apply repr64_neq in E
  | E: context [Int64.ltu (Int64.repr ?a) (Int64.repr ?b)] |- _ => rewrite (Int64_ltu_repr a b) in E by rep_lia
  | E: context [Int64.eq (Int64.repr ?a) (Int64.repr ?b)] |- _ => rewrite (Int64_eq_repr a b) in E by rep_lia
  | E: context [Int.ltu (Int.repr ?a) (Int.repr ?b)] |- _ => rewrite (Int_ltu_repr a b) in E by rep_lia
  | E: context [Int.eq (Int.repr ?a) (Int.repr ?b)] |- _ => rewrite (Int_eq_repr a b) in E by rep_lia
  end.

Ltac cmp_close :=
  unfold bool2val, Int64.cmpu, Int.cmpu; cbv beta iota;
  rewrite ?Int.unsigned_repr by rep_lia;
  rewrite ?Int64.eq_true, ?Int.eq_true;
  rewrite ?Int64_ltu_repr, ?Int64_eq_repr, ?Int_ltu_repr, ?Int_eq_repr by rep_lia;
  repeat match goal with
  | |- context [zlt ?a ?b] => destruct (zlt a b); try lia
  | |- context [zeq ?a ?b] => destruct (zeq a b); try lia
  | |- context [?a <? ?b] => destruct (Z.ltb_spec a b); try lia
  | |- context [?a =? ?b] => destruct (Z.eqb_spec a b); try lia
  | |- context [Int64.ltu (Int64.repr ?a) (Int64.repr ?b)] => rewrite (Int64_ltu_repr a b) by rep_lia
  | |- context [Int64.eq (Int64.repr ?a) (Int64.repr ?b)] => rewrite (Int64_eq_repr a b) by rep_lia
  | |- context [Int.eq (Int.repr ?a) (Int.repr ?b)] => rewrite (Int_eq_repr a b) by rep_lia
  end; try reflexivity.

Ltac else_false :=
  exfalso;
  change Int64.zero with (Int64.repr 0) in *; change Int.zero with (Int.repr 0) in *;
  uns32_hyps;
  match goal with
  | E: Int.repr 1 = Int.repr 0 |- _ => exact (Int.one_not_zero E)
  | E: Int.one = Int.repr 0 |- _ => exact (Int.one_not_zero E)
  | _ => solve [ u64c; first [ lia | contradiction ] ]
  | E: Int64.repr _ = Int64.repr _ |- _ => apply repr64_inj in E; [ lia | rep_lia | rep_lia ]
  | E: ?a <> ?a |- _ => apply E; reflexivity
  | E: Int64.repr _ <> Int64.repr _ |- _ => apply E; f_equal; lia
  | E: Int.repr _ <> Int.repr _ |- _ => apply E; f_equal; lia
  | E: Int.repr _ = Int.repr _ |- _ => apply repr_inj_unsigned in E; [ lia | rep_lia | rep_lia ]
  | E: Int64.ltu _ _ = false |- _ => rewrite Int64_ltu_repr in E by rep_lia; apply Z.ltb_ge in E; lia
  | E: Int64.ltu _ _ = true |- _ => rewrite Int64_ltu_repr in E by rep_lia; apply Z.ltb_lt in E; lia
  | E: context [Int64.unsigned (Int64.repr _)] |- _ => rewrite !Int64.unsigned_repr in E by rep_lia; lia
  | E: context [Int.unsigned (Int.repr _)] |- _ => rewrite !Int.unsigned_repr in E by rep_lia; lia
  | _ => lia
  end.

(* Statements before the next if or call. *)
Ltac to_branch :=
  repeat match goal with |- semax _ _ ?c _ =>
    let s := first_stmt c in
    lazymatch s with Sifthenelse _ _ _ => fail | Scall _ _ _ => fail | _ => forward end
  end.

(* `if (c) t = (bool) c'; else t = 0;` with c and c' true. *)
Ltac if1 :=
  to_branch;
  match goal with |- semax _ _ ?c _ =>
    let s := first_stmt c in
    lazymatch s with
    | Sifthenelse _ _ (Sset ?t (Econst_int (Int.repr 0) tint)) => forward_if (temp t (Vint Int.one))
    end
  end;
  [ solve [ repeat forward; entailer!; cmp_close ] | solve [ else_false ] | ].

(* qp_assert(t) with t = 1. *)
Ltac gp := to_branch; forward_call Int.one.

(* Freeze every SEP item but the law's fields named in L and the data_at whose addresses are in A. *)
Ltac keep_item x L A :=
  lazymatch x with
  | field_at _ _ (StructField ?f :: nil) _ _ => lazymatch L with context [f] => constr:(true) | _ => constr:(false) end
  | data_at _ _ _ ?p => lazymatch A with context [p] => constr:(true) | _ => constr:(false) end
  | data_at_ _ _ ?p => lazymatch A with context [p] => constr:(true) | _ => constr:(false) end
  | _ => constr:(false)
  end.
Ltac idx_frozen R L A i :=
  lazymatch R with
  | nil => constr:(@nil Z)
  | ?x :: ?R' =>
      let rest := idx_frozen R' L A (Z.succ i) in
      let k := keep_item x L A in
      lazymatch k with true => rest | false => let i' := eval cbn in i in constr:(i' :: rest) end
  end.
Ltac freeze_but L A F :=
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
    let I := idx_frozen R L A 0 in freeze_tac I F
  end.

(* Enter a tail lemma: VST's canonical form of the goal, as start_function leaves it. *)
Ltac start_tail :=
  repeat match goal with
  | |- context [Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s) Sskip] => fold (Swhile e s)
  | |- context [Ssequence ?s1 (Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s2) ?s3) ] =>
      match s3 with
      | Sset ?i _ => match s1 with Sset ?i' _ => unify i i' | Sskip => idtac end
      end;
      fold (Sfor s1 e s2 s3)
  end;
  simplify_func_tycontext;
  abbreviate_semax.

(* The facts of the invariants, named. *)
Ltac lst_facts H :=
  let L := fresh "L" in pose proof H as L; unfold lst_ok in L;
  destruct L as (?Lc & ?Lr & ?Lst & ?Le & ?Lv & ?Lb & ?Lw & ?Lca & ?Lsc & ?Lms & ?Lme & ?Lfl & ?Lff & ?Lcm &
                 ?Lf & ?Lfm & ?Lse & ?Lal & ?Laf & ?Lsb);
  unfold u32_ok, u64_ok in *.
Ltac inputs_facts H :=
  let I := fresh "I" in pose proof H as I; unfold inputs_ok in I;
  destruct I as (?It & ?Is & ?Ism & ?Ip & ?In & ?Iml & ?Imf & ?Idl & ?Idf & ?Iul & ?Iuf & ?Ibl & ?Ibf & ?Im);
  unfold u32_ok, u64_ok in *.
Ltac mem_facts H :=
  let M := fresh "M" in pose proof H as M; unfold mem_ok in M;
  destruct M as (?Mrl & ?Mrf & ?Mtl & ?Mtf & ?Msl & ?Msf & ?Mpl & ?Mpf & ?Mql & ?Mqf & ?Ms & ?Msm & ?Mn & ?Md);
  unfold u32_ok, u64_ok in *.

(* The range of each word of a list. *)
Ltac rng_list l n :=
  let rec go k :=
    lazymatch eval cbv in (k <? n) with
    | true =>
        assert (0 <= Znth k l <= Int64.max_unsigned) by (apply Forall_u64_Znth; [ assumption | rep_lia ]);
        let k' := eval cbv in (k + 1) in go k'
    | false => idtac
    end in
  go 0.

Ltac unfold_E := unfold E_MANIFEST, E_FREE, E_FINISH, E_DECODE, E_CANDIDATE, E_CONSUME, E_SCRUB, E_AUTHORITY,
  E_NOTHING, ST_TERMINAL, ST_SELECT, ST_CROSS_CHECK, ST_SCRUB, ST_PUBLICATION_RESULT, ST_PUBLICATION_CHECK,
  ST_RESCAN in *.

(* The oracle at a callee's entry, opened: its hypotheses named. *)
Ltac ora_open p s :=
  unfold Ora_law; Intros p s;
  repeat match goal with H: ?c = ?g _law |- _ => is_var c; subst c end;
  match goal with H: inputs_ok _ |- _ => rename H into Ix end;
  match goal with H: answers_ok _ |- _ => rename H into Ah end;
  match goal with H: run _ (start _) _ = Some _ |- _ => rename H into Hrun end;
  match goal with H: J _ _ _ |- _ => rename H into HJ end.

(* ---------------------------------------------------------------------- *)
(* A local array initialised word by word (`const uint64_t words[n] = {...}`) *)
(* ---------------------------------------------------------------------- *)

(* The stores of vs from index k on into D, as VST leaves them. *)
Fixpoint stores (D: list val) (vs: list val) (k: Z) : list val :=
  match vs with nil => D | v :: rest => stores (upd_Znth k D v) rest (k + 1) end.

Lemma stores_app: forall vs D k, 0 <= k -> k + Zlength vs <= Zlength D ->
  stores D vs k = sublist 0 k D ++ vs ++ sublist (k + Zlength vs) (Zlength D) D.
Proof.
  induction vs as [| v rest IH]; intros D k K L; cbn [stores].
  - rewrite Zlength_nil in *. rewrite app_nil_l, Z.add_0_r. rewrite <- sublist_split by list_solve.
    rewrite sublist_same by lia. reflexivity.
  - rewrite Zlength_cons in L. rewrite IH by list_solve. list_solve.
Qed.

Lemma stores_all: forall vs D, Zlength vs = Zlength D -> stores D vs 0 = vs.
Proof.
  intros vs D L. rewrite stores_app by lia. rewrite sublist_nil, Z.add_0_l, L, sublist_nil, app_nil_r.
  reflexivity.
Qed.

Lemma map_Znth_seq: forall (l: list Z) k,
  map (fun i => vl (Znth (Z.of_nat i - Z.of_nat k) l)) (seq k (length l)) = map vl l.
Proof.
  induction l as [| a l IH]; intros k; [ reflexivity | ].
  cbn [length seq map]. f_equal.
  - rewrite Z.sub_diag. reflexivity.
  - rewrite <- (IH (S k)). apply map_ext_in. intros i Hi. apply in_seq in Hi.
    rewrite (Znth_pos_cons (Z.of_nat i - Z.of_nat k)) by lia. do 2 f_equal. lia.
Qed.

(* The words of l stored at 0 .. n - 1 of an array of n words. *)
Lemma stores_words: forall (l: list Z) n, Zlength l = Z.of_nat n ->
  stores (Zrepeat Vundef (Z.of_nat n)) (map (fun i => vl (Znth (Z.of_nat i - Z.of_nat 0) l)) (seq 0 n)) 0 =
  map vl l.
Proof.
  intros l n L. assert (E: length l = n) by (rewrite Zlength_correct in L; lia).
  rewrite stores_all.
  - rewrite <- E. apply map_Znth_seq.
  - rewrite Zlength_map, Zlength_correct, length_seq, Zlength_Zrepeat by lia. reflexivity.
Qed.

(* The array words at p, as VST leaves it after the n stores of the words of l. *)
Ltac words_init l n :=
  match goal with |- context [data_at Tsh (tarray tulong ?m) ?L ?p] =>
    lazymatch L with context [upd_Znth] =>
      replace L with (map vl l)
        by (transitivity (stores (Zrepeat Vundef (Z.of_nat n))
                            (map (fun i => vl (Znth (Z.of_nat i - Z.of_nat 0) l)) (seq 0 n)) 0);
            [ reflexivity | apply stores_words; assumption ])
    end
  end.
