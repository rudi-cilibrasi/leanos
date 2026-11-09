(* Law frame_selection_exact: main from its objects' values on: each object word drawn and copied into the law's
   model, the records and the decoder record, the states pointer, scrubbed 0, running 1, the sequence and the status
   OK; then the terminal's turn, with the inputs and memory main drew. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosFrameSelection.harness.frame_selection_exact.code.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
Require Import LeanosFrameSelection.proof.LawProg LeanosFrameSelection.proof.LawDefs LeanosFrameSelection.proof.LawFacts
  LeanosFrameSelection.proof.LawLib LeanosFrameSelection.proof.LawSplit LeanosFrameSelection.proof.LawMainDefs
  LeanosFrameSelection.proof.LawMainLib LeanosFrameSelection.proof.LawFast.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.
#[local] Ltac simplify_remove_localdef_temp ::= fast_remove_localdef_temp.

(* From the first loop of the objects' values (`for (i = 0; i < MANIFEST; ++i)`). *)
Definition s_init : statement :=
  ltac:(main_from ltac:(fun s => match s with Sset _i (Econst_int (Int.repr 0) tint) => idtac end)).

(* The law's fields after the draws: the function c, take_next tn and the four frame arguments; the rest 0. *)
Definition ldrawn (q: val) (c tn sel sm pub nx: Z) : mpred :=
 (field_at Ews t_law (DOT _call) (vi c) q *
  field_at Ews t_law (DOT _take_next) (vi tn) q *
  field_at Ews t_law (DOT _selected) (vl sel) q *
  field_at Ews t_law (DOT _selected_manifest) (vl sm) q *
  field_at Ews t_law (DOT _published) (vl pub) q *
  field_at Ews t_law (DOT _next) (vl nx) q *
  field_at Ews t_law (DOT _running) (vi 0) q *
  field_at Ews t_law (DOT _manifest) (z64 18) q *
  field_at Ews t_law (DOT _decoded) (z64 41) q *
  field_at Ews t_law (DOT _usable) (z64 64) q *
  field_at Ews t_law (DOT _blocked) (z64 64) q *
  field_at Ews t_law (DOT _reserved_expect) (z64 64) q *
  field_at Ews t_law (DOT _terminal_expect) (z64 9) q *
  field_at Ews t_law (DOT _states_expect) (Zrepeat (z64 41) 2) q *
  field_at Ews t_law (DOT _publication_expect) (z64 5) q *
  field_at Ews t_law (DOT _rescan_expect) (z64 5) q *
  field_at Ews t_law (DOT _selected_expect) (vl 0) q *
  field_at Ews t_law (DOT _manifest_expect) (vl 0) q *
  field_at Ews t_law (DOT _next_expect) (vl 0) q *
  field_at Ews t_law (DOT _decoder_expect) (vi 0) q *
  field_at Ews t_law (DOT _states) nullval q *
  field_at Ews t_law (DOT _step) (vi 0) q *
  field_at Ews t_law (DOT _expect) (vi 0) q *
  field_at Ews t_law (DOT _verdict) (vi 0) q *
  field_at Ews t_law (DOT _block) (vl 0) q *
  field_at Ews t_law (DOT _word) (vl 0) q *
  field_at Ews t_law (DOT _candidate) (vl 0) q *
  field_at Ews t_law (DOT _scan) (vi 0) q *
  field_at Ews t_law (DOT _manifest_status) (vl 0) q *
  field_at Ews t_law (DOT _manifest_error) (vl 0) q *
  field_at Ews t_law (DOT _free_words) (z64 64) q *
  field_at Ews t_law (DOT _candidate_manifest) (vl 0) q *
  field_at Ews t_law (DOT _first) (vl 0) q *
  field_at Ews t_law (DOT _first_manifest) (vl 0) q *
  field_at Ews t_law (DOT _second) (vl 0) q *
  field_at Ews t_law (DOT _answer) (z64 4) q *
  field_at Ews t_law (DOT _scrubbed) (vi 0) q)%logic.

(* main's objects as malloc gave them. *)
Definition objs0 (P: ptrs) : mpred :=
 (data_at_ Ews (tarray tulong 18) (p_manifest P) * data_at_ Ews (tarray tulong 41) (p_decoded P) *
  data_at_ Ews (tarray tulong 64) (p_usable P) * data_at_ Ews (tarray tulong 64) (p_blocked P) *
  data_at_ Ews (tarray tulong 64) (p_reserved P) * data_at_ Ews (tarray tulong 9) (p_terminal P) *
  data_at_ Ews t_states (p_states P) * data_at_ Ews (tarray tulong 5) (p_publication P) *
  data_at_ Ews (tarray tulong 5) (p_rescan P) * data_at_ Ews (tarray tulong 3) (p_records P) *
  data_at_ Ews tuint (p_decoder P))%logic.

Lemma fill_obj: forall (l: list Z) n i v, Zlength l = i -> 0 <= i < n ->
  upd_Znth i (map vl l ++ Zrepeat Vundef (n - i)) (vl v) = map vl (l ++ [v]) ++ Zrepeat Vundef (n - (i + 1)).
Proof. intros. list_solve. Qed.

Lemma fill_fld: forall (l: list Z) n i v, Zlength l = i -> 0 <= i < n ->
  upd_Znth i (map vl l ++ z64 (n - i)) (vl v) = map vl (l ++ [v]) ++ z64 (n - (i + 1)).
Proof. intros. unfold z64. list_solve. Qed.

Lemma fill_get: forall {d: Inhabitant val} (l: list Z) n i v, Zlength l = i -> 0 <= i < n ->
  Znth i (map vl (l ++ [v]) ++ Zrepeat Vundef (n - (i + 1))) = vl v.
Proof.
  intros d l n i v L N. rewrite map_app, <- app_assoc. rewrite app_Znth2 by (rewrite Zlength_map; lia).
  rewrite Zlength_map, L, Z.sub_diag. reflexivity.
Qed.

Lemma fin_obj: forall (l: list Z) n, map vl l ++ Zrepeat Vundef (n - n) = map vl l.
Proof. intros. rewrite Z.sub_diag. apply app_nil_r. Qed.

Lemma fin_fld: forall (l: list Z) n, map vl l ++ z64 (n - n) = map vl l.
Proof. intros. rewrite Z.sub_diag. apply app_nil_r. Qed.

(* The rows of the states. *)
Lemma row_get: forall {A} {d: Inhabitant A} (pre post: list A) r k, Zlength pre = k -> Znth k (pre ++ [r] ++ post) = r.
Proof. intros. subst. list_solve. Qed.

Lemma row_upd: forall {A} (pre post: list A) r r' k, Zlength pre = k -> upd_Znth k (pre ++ [r] ++ post) r' = pre ++ [r'] ++ post.
Proof.
  intros. subst. rewrite upd_Znth_app2.
  - rewrite Z.sub_diag. change ([r] ++ post) with (r :: post). rewrite upd_Znth0. reflexivity.
  - pose proof (Zlength_nonneg ([r] ++ post)). lia.
Qed.

Lemma rows_snoc: forall (ss: list (list Z)) (l: list Z) (pad: list val) (rest: list (list val)), pad = [] ->
  map (map vl) ss ++ [map vl l ++ pad] ++ rest = map (map vl) (ss ++ [l]) ++ rest.
Proof. intros. subst. rewrite app_nil_r, map_app, <- app_assoc. reflexivity. Qed.

Lemma rows_open: forall {A} (ss: list (list Z)) (x: A) (f: list Z -> A) k, 0 <= k < 2 ->
  map f ss ++ Zrepeat x (2 - k) = map f ss ++ [x] ++ Zrepeat x (2 - k - 1).
Proof. intros. assert (k = 0 \/ k = 1) as [-> | ->] by lia; reflexivity. Qed.

Lemma Forall_rows_snoc: forall (ss: list (list Z)) l, Forall (fun r => Zlength r = 41 /\ Forall u64_ok r) ss ->
  Zlength l = 41 -> Forall u64_ok l -> Forall (fun r => Zlength r = 41 /\ Forall u64_ok r) (ss ++ [l]).
Proof. intros. apply Forall_app; split; auto. Qed.

Lemma upd3_0: forall {A} (a b c x: A), upd_Znth 0 [a; b; c] x = [x; b; c].
Proof. reflexivity. Qed.
Lemma upd3_1: forall {A} (a b c x: A), upd_Znth 1 [a; b; c] x = [a; x; c].
Proof. reflexivity. Qed.
Lemma upd3_2: forall {A} (a b c x: A), upd_Znth 2 [a; b; c] x = [a; b; x].
Proof. reflexivity. Qed.

Lemma map_vl_zeros: forall n, map vl (Zrepeat 0 n) = z64 n.
Proof. intros. unfold z64, Zrepeat. rewrite map_repeat. reflexivity. Qed.

Lemma Forall_Zrepeat: forall (P: Z -> Prop) x n, P x -> Forall P (Zrepeat x n).
Proof. intros. unfold Zrepeat. apply Forall_forall. intros y Y. apply repeat_spec in Y. subst. auto. Qed.

(* A loop of n draws into the object at p and the law's field fld. *)
Ltac init_body :=
  forward_call tt; let v := fresh "v" in Intros v;
  forward;
  match goal with H: Zlength ?l = ?i |- context [upd_Znth ?i (map vl ?l ++ Zrepeat Vundef (?n' - ?i)) _] =>
    rewrite (fill_obj l n' i v) by (auto; lia);
    forward; try (solve [ entailer!; rewrite fill_get by (auto; lia); exact I ]);
    rewrite (fill_get l n' i v) by (auto; lia);
    forward;
    rewrite (fill_fld l n' i v) by (auto; lia);
    Exists (l ++ [v]); entailer!;
    first [ (split; [ list_solve | apply Forall_u64_app1; auto ]) | list_solve | (apply Forall_u64_app1; auto) ]
  end.

Lemma tail_init {Espec: OracleKind} (TTl: tail_ok s_terminal (at_step FTerminal))
    gv P c tn sel sm pub nx:
  ptrs_ok P -> u32_ok c -> u32_ok tn -> u64_ok sel -> u64_ok sm -> u64_ok pub -> u64_ok nx ->
  forall Delta R cmd, Delta = Delta0 -> R = Post0 -> cmd = s_init ->
  semax Delta
    (PROP ()
     LOCAL (temp _m (gv _law); temp _manifest (p_manifest P); temp _decoded (p_decoded P);
            temp _usable (p_usable P); temp _blocked (p_blocked P); temp _reserved (p_reserved P);
            temp _terminal (p_terminal P); temp _states (p_states P); temp _publication (p_publication P);
            temp _rescan (p_rescan P); temp _records (p_records P); temp _decoder_record (p_decoder P); gvars gv)
     SEP (ldrawn (gv _law) c tn sel sm pub nx; objs0 P; TT)) cmd R.
Proof.
  intros Pp Uc Utn Usel Usm Upub Unx Delta R cmd -> -> ->.
  unfold s_init. start_main_tail.
  pose proof Pp as (Pmp & Pdp & Pup & Pbp & Prp & Ptp & Psp & Ppp & Prsp & Precp & Pdsp).
  unfold ldrawn, objs0. Intros.
  rewrite !data_at__eq.
  (* _manifest *)
  freeze_but [_manifest] [p_manifest P] F1.
  change (default_val (tarray tulong 18)) with (map vl (@nil Z) ++ Zrepeat Vundef (18 - 0)).
  change (z64 18) with (map vl (@nil Z) ++ z64 (18 - 0)).
  forward_for_simple_bound 18 (EX i: Z, EX l: list Z,
     PROP (Zlength l = i; Forall u64_ok l)
     LOCAL (temp _m (gv _law); temp _manifest (p_manifest P); temp _decoded (p_decoded P);
            temp _usable (p_usable P); temp _blocked (p_blocked P); temp _reserved (p_reserved P);
            temp _terminal (p_terminal P); temp _states (p_states P); temp _publication (p_publication P);
            temp _rescan (p_rescan P); temp _records (p_records P); temp _decoder_record (p_decoder P); gvars gv)
     SEP (FRZL F1; data_at Ews (tarray tulong 18) (map vl l ++ Zrepeat Vundef (18 - i)) (p_manifest P);
          field_at Ews t_law (DOT _manifest) (map vl l ++ z64 (18 - i)) (gv _law)))%assert.
  { Exists (@nil Z). entailer!. }
  { try (Intros l). init_body. }
  Intros ms. rewrite fin_obj, fin_fld. thaw F1.
  match goal with H: Zlength ms = _ |- _ => rename H into L_ms end.
  match goal with H: Forall u64_ok ms |- _ => rename H into F_ms end.
  (* _decoded *)
  freeze_but [_decoded] [p_decoded P] F2.
  change (default_val (tarray tulong 41)) with (map vl (@nil Z) ++ Zrepeat Vundef (41 - 0)).
  change (z64 41) with (map vl (@nil Z) ++ z64 (41 - 0)).
  forward_for_simple_bound 41 (EX i: Z, EX l: list Z,
     PROP (Zlength l = i; Forall u64_ok l)
     LOCAL (temp _m (gv _law); temp _manifest (p_manifest P); temp _decoded (p_decoded P);
            temp _usable (p_usable P); temp _blocked (p_blocked P); temp _reserved (p_reserved P);
            temp _terminal (p_terminal P); temp _states (p_states P); temp _publication (p_publication P);
            temp _rescan (p_rescan P); temp _records (p_records P); temp _decoder_record (p_decoder P); gvars gv)
     SEP (FRZL F2; data_at Ews (tarray tulong 41) (map vl l ++ Zrepeat Vundef (41 - i)) (p_decoded P);
          field_at Ews t_law (DOT _decoded) (map vl l ++ z64 (41 - i)) (gv _law)))%assert.
  { Exists (@nil Z). entailer!. }
  { try (Intros l). init_body. }
  Intros ds. rewrite fin_obj, fin_fld. thaw F2.
  match goal with H: Zlength ds = _ |- _ => rename H into L_ds end.
  match goal with H: Forall u64_ok ds |- _ => rename H into F_ds end.
  (* _usable *)
  freeze_but [_usable] [p_usable P] F3.
  change (default_val (tarray tulong 64)) with (map vl (@nil Z) ++ Zrepeat Vundef (64 - 0)).
  change (z64 64) with (map vl (@nil Z) ++ z64 (64 - 0)).
  forward_for_simple_bound 64 (EX i: Z, EX l: list Z,
     PROP (Zlength l = i; Forall u64_ok l)
     LOCAL (temp _m (gv _law); temp _manifest (p_manifest P); temp _decoded (p_decoded P);
            temp _usable (p_usable P); temp _blocked (p_blocked P); temp _reserved (p_reserved P);
            temp _terminal (p_terminal P); temp _states (p_states P); temp _publication (p_publication P);
            temp _rescan (p_rescan P); temp _records (p_records P); temp _decoder_record (p_decoder P); gvars gv)
     SEP (FRZL F3; data_at Ews (tarray tulong 64) (map vl l ++ Zrepeat Vundef (64 - i)) (p_usable P);
          field_at Ews t_law (DOT _usable) (map vl l ++ z64 (64 - i)) (gv _law)))%assert.
  { Exists (@nil Z). entailer!. }
  { try (Intros l). init_body. }
  Intros us. rewrite fin_obj, fin_fld. thaw F3.
  match goal with H: Zlength us = _ |- _ => rename H into L_us end.
  match goal with H: Forall u64_ok us |- _ => rename H into F_us end.
  (* _blocked *)
  freeze_but [_blocked] [p_blocked P] F4.
  change (default_val (tarray tulong 64)) with (map vl (@nil Z) ++ Zrepeat Vundef (64 - 0)).
  change (z64 64) with (map vl (@nil Z) ++ z64 (64 - 0)).
  forward_for_simple_bound 64 (EX i: Z, EX l: list Z,
     PROP (Zlength l = i; Forall u64_ok l)
     LOCAL (temp _m (gv _law); temp _manifest (p_manifest P); temp _decoded (p_decoded P);
            temp _usable (p_usable P); temp _blocked (p_blocked P); temp _reserved (p_reserved P);
            temp _terminal (p_terminal P); temp _states (p_states P); temp _publication (p_publication P);
            temp _rescan (p_rescan P); temp _records (p_records P); temp _decoder_record (p_decoder P); gvars gv)
     SEP (FRZL F4; data_at Ews (tarray tulong 64) (map vl l ++ Zrepeat Vundef (64 - i)) (p_blocked P);
          field_at Ews t_law (DOT _blocked) (map vl l ++ z64 (64 - i)) (gv _law)))%assert.
  { Exists (@nil Z). entailer!. }
  { try (Intros l). init_body. }
  Intros bs. rewrite fin_obj, fin_fld. thaw F4.
  match goal with H: Zlength bs = _ |- _ => rename H into L_bs end.
  match goal with H: Forall u64_ok bs |- _ => rename H into F_bs end.
  (* _reserved_expect *)
  freeze_but [_reserved_expect] [p_reserved P] F5.
  change (default_val (tarray tulong 64)) with (map vl (@nil Z) ++ Zrepeat Vundef (64 - 0)).
  change (z64 64) with (map vl (@nil Z) ++ z64 (64 - 0)).
  forward_for_simple_bound 64 (EX i: Z, EX l: list Z,
     PROP (Zlength l = i; Forall u64_ok l)
     LOCAL (temp _m (gv _law); temp _manifest (p_manifest P); temp _decoded (p_decoded P);
            temp _usable (p_usable P); temp _blocked (p_blocked P); temp _reserved (p_reserved P);
            temp _terminal (p_terminal P); temp _states (p_states P); temp _publication (p_publication P);
            temp _rescan (p_rescan P); temp _records (p_records P); temp _decoder_record (p_decoder P); gvars gv)
     SEP (FRZL F5; data_at Ews (tarray tulong 64) (map vl l ++ Zrepeat Vundef (64 - i)) (p_reserved P);
          field_at Ews t_law (DOT _reserved_expect) (map vl l ++ z64 (64 - i)) (gv _law)))%assert.
  { Exists (@nil Z). entailer!. }
  { try (Intros l). init_body. }
  Intros rs. rewrite fin_obj, fin_fld. thaw F5.
  match goal with H: Zlength rs = _ |- _ => rename H into L_rs end.
  match goal with H: Forall u64_ok rs |- _ => rename H into F_rs end.
  (* _terminal_expect *)
  freeze_but [_terminal_expect] [p_terminal P] F6.
  change (default_val (tarray tulong 9)) with (map vl (@nil Z) ++ Zrepeat Vundef (9 - 0)).
  change (z64 9) with (map vl (@nil Z) ++ z64 (9 - 0)).
  forward_for_simple_bound 9 (EX i: Z, EX l: list Z,
     PROP (Zlength l = i; Forall u64_ok l)
     LOCAL (temp _m (gv _law); temp _manifest (p_manifest P); temp _decoded (p_decoded P);
            temp _usable (p_usable P); temp _blocked (p_blocked P); temp _reserved (p_reserved P);
            temp _terminal (p_terminal P); temp _states (p_states P); temp _publication (p_publication P);
            temp _rescan (p_rescan P); temp _records (p_records P); temp _decoder_record (p_decoder P); gvars gv)
     SEP (FRZL F6; data_at Ews (tarray tulong 9) (map vl l ++ Zrepeat Vundef (9 - i)) (p_terminal P);
          field_at Ews t_law (DOT _terminal_expect) (map vl l ++ z64 (9 - i)) (gv _law)))%assert.
  { Exists (@nil Z). entailer!. }
  { try (Intros l). init_body. }
  Intros ts. rewrite fin_obj, fin_fld. thaw F6.
  match goal with H: Zlength ts = _ |- _ => rename H into L_ts end.
  match goal with H: Forall u64_ok ts |- _ => rename H into F_ts end.
  (* the states *)
  freeze_but [_states_expect] [p_states P] F7.
  change (default_val t_states) with (map (map vl) (@nil (list Z)) ++ Zrepeat (Zrepeat Vundef 41) (2 - 0)).
  change (Zrepeat (z64 41) 2) with (map (map vl) (@nil (list Z)) ++ Zrepeat (z64 41) (2 - 0)).
  forward_for_simple_bound 2 (EX k: Z, EX ss: list (list Z),
     PROP (Zlength ss = k; Forall (fun r => Zlength r = 41 /\ Forall u64_ok r) ss)
     LOCAL (temp _m (gv _law); temp _manifest (p_manifest P); temp _decoded (p_decoded P);
            temp _usable (p_usable P); temp _blocked (p_blocked P); temp _reserved (p_reserved P);
            temp _terminal (p_terminal P); temp _states (p_states P); temp _publication (p_publication P);
            temp _rescan (p_rescan P); temp _records (p_records P); temp _decoder_record (p_decoder P); gvars gv)
     SEP (FRZL F7; data_at Ews t_states (map (map vl) ss ++ Zrepeat (Zrepeat Vundef 41) (2 - k)) (p_states P);
          field_at Ews t_law (DOT _states_expect) (map (map vl) ss ++ Zrepeat (z64 41) (2 - k)) (gv _law)))%assert.
  { Exists (@nil (list Z)). entailer!. }
  { try (Intros ss). Intros.
    match goal with H: Zlength ss = ?kk |- _ => rename H into Lss; try rename kk into k end.
    rewrite (rows_open ss (Zrepeat Vundef 41) (map vl) k) by lia.
    rewrite (rows_open ss (z64 41) (map vl) k) by lia.
    change (Zrepeat Vundef 41) with (map vl (@nil Z) ++ Zrepeat Vundef (41 - 0)) at 1.
    change (z64 41) with (map vl (@nil Z) ++ z64 (41 - 0)) at 1.
    forward_for_simple_bound 41 (EX i: Z, EX l: list Z,
       PROP (Zlength l = i; Forall u64_ok l)
       LOCAL (temp _k (Vint (Int.repr k)); temp _m (gv _law); temp _manifest (p_manifest P); temp _decoded (p_decoded P);
            temp _usable (p_usable P); temp _blocked (p_blocked P); temp _reserved (p_reserved P);
            temp _terminal (p_terminal P); temp _states (p_states P); temp _publication (p_publication P);
            temp _rescan (p_rescan P); temp _records (p_records P); temp _decoder_record (p_decoder P); gvars gv)
       SEP (FRZL F7;
            data_at Ews t_states (map (map vl) ss ++ [map vl l ++ Zrepeat Vundef (41 - i)] ++
                                   Zrepeat (Zrepeat Vundef 41) (2 - k - 1)) (p_states P);
            field_at Ews t_law (DOT _states_expect) (map (map vl) ss ++ [map vl l ++ z64 (41 - i)] ++
                                   Zrepeat (z64 41) (2 - k - 1)) (gv _law)))%assert.
    { Exists (@nil Z). entailer!. }
    { try (Intros l). Intros.
      match goal with H: Zlength l = i |- _ => rename H into Ll end.
      forward_call tt. Intros v.
      forward.
      rewrite (row_get (map (map vl) ss)) by (rewrite Zlength_map; auto).
      rewrite (fill_obj l 41 i v) by (auto; lia).
      rewrite (row_upd (map (map vl) ss)) by (rewrite Zlength_map; auto).
      forward.
      all: rewrite (row_get (map (map vl) ss)) by (rewrite Zlength_map; auto).
      all: rewrite (fill_get l 41 i v) by (auto; lia).
      all: try (solve [ entailer!; try exact I ]).
      forward.
      rewrite (row_get (map (map vl) ss)) by (rewrite Zlength_map; auto).
      rewrite (fill_fld l 41 i v) by (auto; lia).
      rewrite (row_upd (map (map vl) ss)) by (rewrite Zlength_map; auto).
      Exists (l ++ [v]). entailer!.
      all: first [ (split; [ list_solve | apply Forall_u64_app1; auto ]) | list_solve | (apply Forall_u64_app1; auto) ]. }
    Intros l.
    rewrite (rows_snoc ss l (Zrepeat Vundef (41 - 41))) by reflexivity.
    rewrite (rows_snoc ss l (z64 (41 - 41))) by reflexivity.
    replace (2 - k - 1) with (2 - (k + 1)) by lia.
    Exists (ss ++ [l]). entailer!.
    all: first [ (split; [ list_solve | apply Forall_rows_snoc; auto ]) | list_solve | (apply Forall_rows_snoc; auto) ]. }
  Intros ss.
  change (Zrepeat (Zrepeat Vundef 41) (2 - 2)) with (@nil (list val)).
  change (Zrepeat (z64 41) (2 - 2)) with (@nil (list val)).
  rewrite !app_nil_r. thaw F7.
  match goal with H: Zlength ss = _ |- _ => rename H into L_ss end.
  match goal with H: Forall _ ss |- _ => rename H into F_ss end.
  (* _publication_expect *)
  freeze_but [_publication_expect] [p_publication P] F8.
  change (default_val (tarray tulong 5)) with (map vl (@nil Z) ++ Zrepeat Vundef (5 - 0)).
  change (z64 5) with (map vl (@nil Z) ++ z64 (5 - 0)).
  forward_for_simple_bound 5 (EX i: Z, EX l: list Z,
     PROP (Zlength l = i; Forall u64_ok l)
     LOCAL (temp _m (gv _law); temp _manifest (p_manifest P); temp _decoded (p_decoded P);
            temp _usable (p_usable P); temp _blocked (p_blocked P); temp _reserved (p_reserved P);
            temp _terminal (p_terminal P); temp _states (p_states P); temp _publication (p_publication P);
            temp _rescan (p_rescan P); temp _records (p_records P); temp _decoder_record (p_decoder P); gvars gv)
     SEP (FRZL F8; data_at Ews (tarray tulong 5) (map vl l ++ Zrepeat Vundef (5 - i)) (p_publication P);
          field_at Ews t_law (DOT _publication_expect) (map vl l ++ z64 (5 - i)) (gv _law)))%assert.
  { Exists (@nil Z). entailer!. }
  { try (Intros l). init_body. }
  Intros ps. rewrite fin_obj, fin_fld. thaw F8.
  match goal with H: Zlength ps = _ |- _ => rename H into L_ps end.
  match goal with H: Forall u64_ok ps |- _ => rename H into F_ps end.
  (* _rescan_expect *)
  freeze_but [_rescan_expect] [p_rescan P] F9.
  change (default_val (tarray tulong 5)) with (map vl (@nil Z) ++ Zrepeat Vundef (5 - 0)).
  change (z64 5) with (map vl (@nil Z) ++ z64 (5 - 0)).
  forward_for_simple_bound 5 (EX i: Z, EX l: list Z,
     PROP (Zlength l = i; Forall u64_ok l)
     LOCAL (temp _m (gv _law); temp _manifest (p_manifest P); temp _decoded (p_decoded P);
            temp _usable (p_usable P); temp _blocked (p_blocked P); temp _reserved (p_reserved P);
            temp _terminal (p_terminal P); temp _states (p_states P); temp _publication (p_publication P);
            temp _rescan (p_rescan P); temp _records (p_records P); temp _decoder_record (p_decoder P); gvars gv)
     SEP (FRZL F9; data_at Ews (tarray tulong 5) (map vl l ++ Zrepeat Vundef (5 - i)) (p_rescan P);
          field_at Ews t_law (DOT _rescan_expect) (map vl l ++ z64 (5 - i)) (gv _law)))%assert.
  { Exists (@nil Z). entailer!. }
  { try (Intros l). init_body. }
  Intros qs. rewrite fin_obj, fin_fld. thaw F9.
  match goal with H: Zlength qs = _ |- _ => rename H into L_qs end.
  match goal with H: Forall u64_ok qs |- _ => rename H into F_qs end.
  (* the records *)
  change (default_val (tarray tulong 3)) with [Vundef; Vundef; Vundef].
  forward_call tt. Intros r0. forward. rewrite ?upd3_0.
  forward_call tt. Intros r1. forward. rewrite ?upd3_1.
  forward_call tt. Intros r2. forward. rewrite ?upd3_2.
  forward. forward. forward. forward. forward. forward.
  (* the decoder record *)
  forward_call tt. Intros d0. forward.
  unfold u64_ok in *. rewrite ?Int64.unsigned_repr by rep_lia.
  rewrite ?Int64.Z_mod_modulus_eq. rewrite ?(Z.mod_small d0 Int64.modulus) by rep_lia. rewrite ?(low32 d0).
  forward. forward.
  (* the states pointer, scrubbed, running *)
  forward. forward. forward.
  (* sequence and status *)
  forward. forward. forward.
  pose proof Uc as Uc'. unfold u32_ok in Uc'.
  match goal with |- semax _ (PROPx _ (LOCALx ?Q _)) _ _ =>
    match Q with context [temp _sequence ?v] =>
      replace v with (vi (Z.b2z (c =? 0))) by
        (destruct (Z.eqb_spec c 0);
         [ subst; reflexivity
         | first [ reflexivity
                 | (rewrite Int.eq_false; [ reflexivity | intro E; apply repr_inj_unsigned in E; rep_lia ])
                 | (destruct (zeq c 0); [ lia | reflexivity ]) ] ])
    end
  end.
  pose proof (low32_range d0) as Ud.
  eapply semax_pre; [ | apply (TTl gv P
     (mk_inputs FTerminal tn sel sm pub nx ms ds us bs (mk_mem rs ts ss ps qs r0 r1 r2 (d0 mod 2 ^ 32)))
     (mk_lst c 1 0 0 0 0 0 0 0 0 0 (Zrepeat 0 64) 0 0 0 0 (Zrepeat 0 4) 0) (Z.b2z (c =? 0)) 0) ].
  - unfold main_pre, lfields, objs. cbn [i_take_next i_selected i_selected_manifest i_published i_next i_manifest
      i_decoded i_usable i_blocked i_mem m_reserved m_terminal m_states m_publication m_rescan m_selected
      m_selected_manifest m_next m_decoder w_call w_running w_step w_expect w_verdict w_block w_word w_candidate
      w_scan w_ms w_me w_free w_cm w_first w_fm w_second w_answer w_scrubbed p_manifest p_decoded p_usable
      p_blocked p_reserved p_terminal p_states p_publication p_rescan p_records p_decoder map].
    rewrite !map_vl_zeros.
    unfold t_manifest, t_state, t_bitmap, t_terminal, t_publication, t_rescan, t_records, states_val.
    entailer!.
    all: try apply derives_refl.
  - unfold u32_ok, u64_ok in *.
    unfold main_ok, inputs_ok, mem_ok, lst_ok, u32_ok, u64_ok; cbn [i_take_next i_selected i_selected_manifest
      i_published i_next i_manifest i_decoded i_usable i_blocked i_mem m_reserved m_terminal m_states m_publication
      m_rescan m_selected m_selected_manifest m_next m_decoder w_call w_running w_step w_expect w_verdict w_block
      w_word w_candidate w_scan w_ms w_me w_free w_cm w_first w_fm w_second w_answer w_scrubbed].
    split_and; auto; try rep_lia; try (apply Forall_Zrepeat; rep_lia); try reflexivity.
    all: try (destruct (c =? 0); cbn; auto).
    all: try rep_lia.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
