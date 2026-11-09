(* Helpers of the window body proofs (WindowProof.v): a sealed root predicate, 64-bit word facts and the scan's
   per-page test. *)
Require Import VST.floyd.proofauto.
Require Import LeanosRoots.roots.code.
Require Import LeanosRoots.proof.Defs.
Require Import LeanosRoots.proof.RootsSpecs.
Require Import LeanosRoots.proof.WindowLemmas.
#[local] Existing Instance RootsSpecs.CS.
#[local] Existing Instance window_alias_default.

(* A root's storage, sealed: Floyd's cancel proves each frame item with conversion, and a failing conversion
   between two different data_at of the 4096-leaf root type unfolds both down to their words, which takes
   minutes.  Every root but the one a step reads is kept as rootp; rootp_eq opens it. *)
Definition rootp_sig : { f : share -> reptype t_root -> val -> mpred |
                         forall sh v p, f sh v p = data_at sh t_root v p }.
Proof. exists (fun sh v p => data_at sh t_root v p). intros. reflexivity. Qed.
Definition rootp : share -> reptype t_root -> val -> mpred := proj1_sig rootp_sig.
Lemma rootp_eq: forall sh v p, rootp sh v p = data_at sh t_root v p.
Proof. exact (proj2_sig rootp_sig). Qed.
Ltac seal := repeat rewrite <- rootp_eq.

Ltac bz :=
  repeat match goal with
  | H: Int.repr (b2z ?c) = Int.zero |- _ =>
      let E := fresh "E" in destruct c eqn:E; [ exfalso; apply Int.one_not_zero; exact H | clear H ]
  | H: Int.repr (b2z ?c) <> Int.zero |- _ =>
      let E := fresh "E" in destruct c eqn:E; [ clear H | exfalso; apply H; reflexivity ]
  end.

(* 64-bit words *)
Lemma repr_modW: forall x, Int64.repr (x mod W) = Int64.repr x.
Proof. intros. unfold W. rewrite <- Int64.unsigned_repr_eq. apply Int64.repr_unsigned. Qed.

Lemma eq64: forall x y, word_ok x -> word_ok y -> Int64.eq (Int64.repr x) (Int64.repr y) = (x =? y).
Proof.
  intros x y Hx Hy. unfold word_ok in *. unfold Int64.eq.
  rewrite !Int64.unsigned_repr by lia. destruct (zeq x y); symmetry; [ apply Z.eqb_eq | apply Z.eqb_neq ]; auto.
Qed.

Lemma ltu64: forall x y, word_ok x -> word_ok y -> Int64.ltu (Int64.repr x) (Int64.repr y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold word_ok in *. unfold Int64.ltu.
  rewrite !Int64.unsigned_repr by lia. destruct (zlt x y); symmetry; [ apply Z.ltb_lt | apply Z.ltb_ge ]; lia.
Qed.

Lemma repr64_inj: forall x y, word_ok x -> word_ok y -> Int64.repr x = Int64.repr y -> x = y.
Proof.
  intros x y Hx Hy E. unfold word_ok in *.
  rewrite <- (Int64.unsigned_repr x), <- (Int64.unsigned_repr y) by lia. rewrite E. reflexivity.
Qed.

Lemma land_word: forall a b, word_ok a -> 0 <= b -> word_ok (Z.land a b).
Proof.
  unfold word_ok. intros a b Ha Hb. rewrite max_unsigned_W, W_val in *.
  split; [ apply Z.land_nonneg; lia | ].
  assert (Z.land a b < 2 ^ 64); [ | change (2 ^ 64) with 18446744073709551616 in *; lia ].
  rewrite <- (Z.mod_small a (2 ^ 64)) by (change (2 ^ 64) with 18446744073709551616; lia).
  rewrite <- Z.land_ones by lia.
  rewrite <- Z.land_assoc, (Z.land_comm (Z.ones 64) b), Z.land_assoc, Z.land_ones by lia.
  pose proof (Z.mod_pos_bound (Z.land a b) (2 ^ 64)). lia.
Qed.

Lemma frame_of_word: forall c, word_ok c -> word_ok (frame_of c).
Proof.
  intros c Hc. pose proof (land_word c ADDRESS_MASK Hc ltac:(unfold ADDRESS_MASK; lia)) as L.
  unfold word_ok in *. unfold frame_of. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 12) with 4096.
  split; [ apply Z.div_pos; lia | ].
  apply Z.le_trans with (Z.land c ADDRESS_MASK); [ apply Z.div_le_upper_bound; lia | lia ].
Qed.

Lemma shru_and_frame: forall c, word_ok c ->
  Int64.shru (Int64.and (Int64.repr c) (Int64.repr 4503599627366400)) (Int64.repr 12) = Int64.repr (frame_of c).
Proof.
  intros c Hc. pose proof (land_word c ADDRESS_MASK Hc ltac:(unfold ADDRESS_MASK; lia)) as L.
  rewrite and64_repr. unfold Int64.shru. unfold word_ok in L.
  rewrite !Int64.unsigned_repr by (unfold ADDRESS_MASK in L; rep_lia). reflexivity.
Qed.

Lemma shru_land_frame: forall c, word_ok c ->
  Int64.shru (Int64.repr (Z.land c 4503599627366400)) (Int64.repr 12) = Int64.repr (frame_of c).
Proof. intros. rewrite <- and64_repr. apply shru_and_frame. auto. Qed.

Lemma and1_repr: forall c, Int64.and (Int64.repr c) (Int64.repr 1) = Int64.repr (if Z.odd c then 1 else 0).
Proof.
  intros. rewrite and64_repr. f_equal. rewrite <- Zmod_odd. apply (Z.land_ones c 1). lia.
Qed.

Lemma shiftr_word: forall b, word_ok b -> word_ok (Z.shiftr b 12).
Proof.
  intros b Hb. unfold word_ok in *. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 12) with 4096.
  split; [ apply Z.div_pos; lia | ]. apply Z.le_trans with b; [ apply Z.div_le_upper_bound; lia | lia ].
Qed.

Lemma expected_repr: forall base page slot (wb: bool), word_ok base ->
  Int64.or (Int64.or (Int64.or (Int64.shl (Int64.add (Int64.shru (Int64.repr base) (Int64.repr 12))
                                                     (Int64.sub (Int64.repr page) (Int64.repr slot)))
                                          (Int64.repr 12)) (Int64.repr 1))
                     (Int64.shl (Int64.repr 1) (Int64.repr 63)))
           (Int64.repr (if wb then 2 else 0))
  = Int64.repr (Z.lor (Z.lor (Z.lor (((Z.shiftr base 12 + (page - slot) mod W) mod W * 4096) mod W) 1) NX)
                      (if wb then 2 else 0)).
Proof.
  intros base page slot wb Hb. rewrite <- !or64_repr.
  replace (Int64.shl (Int64.repr 1) (Int64.repr 63)) with (Int64.repr NX) by reflexivity.
  f_equal. f_equal. f_equal.
  pose proof (shiftr_word base Hb) as Hs. unfold word_ok in *.
  unfold Int64.shl, Int64.add, Int64.sub, Int64.shru.
  rewrite (Int64.unsigned_repr 12) by rep_lia. rewrite (Int64.unsigned_repr base) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite repr_modW. f_equal.
  rewrite !Int64.unsigned_repr_eq. change Int64.modulus with W.
  rewrite (Z.mod_small (Z.shiftr base 12) W) by (rewrite max_unsigned_W in Hs; lia).
  rewrite <- Zminus_mod. reflexivity.
Qed.

Lemma scan_leaf_word: forall w wb p c, word_ok c -> word_ok (scan_leaf w wb p c).
Proof.
  intros. unfold scan_leaf. destruct (in_slots w p); [ | exact H ].
  repeat apply word_lor; try apply word_modW; unfold word_ok, NX; try rep_lia.
  destruct wb; rep_lia.
Qed.

(* The scan's test of page p. *)
Definition scan_chk (r k: root) (inv: list Z) (w: window) (wb: bool) (p: Z) : bool :=
  (negb (removes inv (Znth p (pt k))) && (Znth p (pt r) =? scan_leaf w wb p (Znth p (pt k))))%bool.
Lemma scan_ok_eq: forall r k rp kp inv w wb,
  scan_ok r k rp kp inv w wb =
  (ancestors_ok r rp && ancestors_ok k kp && forallb (scan_chk r k inv w wb) (idx LEAVES))%bool.
Proof. reflexivity. Qed.

Lemma scan_ok_false: forall r k rp kp inv w wb p, 0 <= p < LEAVES -> scan_chk r k inv w wb p = false ->
  scan_ok r k rp kp inv w wb = false.
Proof.
  intros. rewrite scan_ok_eq. rewrite (forallb_idx_false _ _ p H H0). apply andb_false_r.
Qed.

Lemma scan_ok_true: forall r k rp kp inv w wb, (ancestors_ok r rp && ancestors_ok k kp)%bool = true ->
  (forall p, 0 <= p < LEAVES -> scan_chk r k inv w wb p = true) -> scan_ok r k rp kp inv w wb = true.
Proof.
  intros. rewrite scan_ok_eq, H. cbn [andb]. apply forallb_idx. exact H0.
Qed.

Lemma scan_leaf_in: forall w wb p c, in_slots w p = true ->
  scan_leaf w wb p c =
  Z.lor (Z.lor (Z.lor (((Z.shiftr (w_base w) 12 + (p - w_slot w) mod W) mod W * 4096) mod W) 1) NX)
        (if wb then 2 else 0).
Proof. intros. unfold scan_leaf. rewrite H. reflexivity. Qed.

Lemma scan_leaf_out: forall w wb p c, in_slots w p = false -> scan_leaf w wb p c = c.
Proof. intros. unfold scan_leaf. rewrite H. reflexivity. Qed.

Lemma alias_word: forall x (wb: bool), word_ok (Z.lor (Z.lor (Z.lor (x mod W) 1) NX) (if wb then 2 else 0)).
Proof.
  intros. repeat apply word_lor; try apply word_modW; unfold word_ok, NX; try rep_lia. destruct wb; rep_lia.
Qed.

(* maybe_at of a valid pointer. *)
Lemma maybe_at_ptr: forall sh t v p, isptr p -> maybe_at sh t v p = data_at sh t v p.
Proof. intros. unfold maybe_at. destruct (Val.eq p nullval); [ subst; contradiction | reflexivity ]. Qed.

Lemma rootp_maybe: forall sh v p, isptr p -> rootp sh v p = maybe_at sh t_root v p.
Proof. intros. rewrite maybe_at_ptr by auto. apply rootp_eq. Qed.

Lemma frames_nil: forall sh fs p, data_at sh (tarray tulong (Zlength fs)) (longs fs) p =
  data_at sh (tarray tulong (Zlength fs + Zlength (@nil val))) (longs fs ++ []) p.
Proof. intros. rewrite Zlength_nil, Z.add_0_r, app_nil_r. reflexivity. Qed.

Lemma Znth_longs: forall l i, 0 <= i < Zlength l -> Znth i (longs l) = Vlong (Int64.repr (Znth i l)).
Proof. intros. unfold longs. rewrite Znth_map by lia. reflexivity. Qed.

Lemma Znth_word: forall l i, words_ok l -> 0 <= i < Zlength l -> word_ok (Znth i l).
Proof. intros. apply Forall_Znth; auto. Qed.

Lemma int_signed_zero: forall x, Int.min_signed <= x <= Int.max_signed -> Int.repr x = Int.zero -> x = 0.
Proof.
  intros x Hx E. apply (f_equal Int.signed) in E. rewrite Int.signed_repr in E by lia. exact E.
Qed.

(* ---------------------------------------------------------------------- *)
(* frame_window_build: its loop state and the facts its proof uses         *)
(* ---------------------------------------------------------------------- *)

(* Keep simpl (and entailer!) away from the 4096-leaf model. *)
#[local] Arguments idx : simpl never.
#[local] Arguments ancestors_ok : simpl never.
#[local] Arguments scan_ok : simpl never.
#[local] Arguments scan_leaf : simpl never.
#[local] Arguments in_slots : simpl never.
#[local] Arguments removes : simpl never.
#[local] Arguments member : simpl never.
#[local] Arguments build_ok : simpl never.
#[local] Arguments window_ok : simpl never.
#[local] Arguments geometry_ok : simpl never.
#[local] Arguments removed_count : simpl never.
#[local] Arguments retained_count : simpl never.
#[local] Arguments closed_out : simpl never.
#[local] Arguments copy_out : simpl never.
#[local] Arguments built_root : simpl never.
#[local] Arguments window_aliases : simpl never.
#[local] Arguments pages_of : simpl never.
#[local] Arguments disjoint : simpl never.
#[local] Arguments frame_of : simpl never.

Definition cnt_ok (src: root) (fs: list Z) (n: Z) (fr: counts) (built: Z) : bool :=
  ((built =? 0) || ((c_protected fr =? n) && (c_removed fr =? removed_count (sublist 0 n fs) (pt src)) &&
                    (c_retained fr =? retained_count (sublist 0 n fs) (pt src))))%bool.

Lemma window_ok_eq: forall src sp kp fs n w built fr,
  window_ok src sp kp fs n w built fr =
  (geometry_ok w && disjoint (w_fetch_phys w) (w_send_phys w) &&
   build_ok src sp kp (w_fetch_phys w) fs n (window_aliases w 1) (pages_of w) &&
   build_ok src sp kp (w_send_phys w) fs n (window_aliases w 0) (pages_of w) && cnt_ok src fs n fr built)%bool.
Proof. reflexivity. Qed.

Definition first_after (src: root) (fs: list Z) (n: Z) (w: window) (fr: counts) (built: Z) : counts :=
  if built =? 0
  then mkcounts n (removed_count (sublist 0 n fs) (pt src)) (retained_count (sublist 0 n fs) (pt src)) (pages_of w)
  else fr.

(* The loop state of frame_window_build before iteration j (1, 0) or after both (-1). *)
Definition wfacts (src: root) (sp kp: Z) (fs: list Z) (n: Z) (w: window) (kold fold sold: reptype t_root)
    (fr: counts) (built: Z) (j: Z) (kc fc sc: reptype t_root) (rc: counts) (bc: Z) : Prop :=
  (j = 1 \/ j = 0 \/ j = -1) /\
  (j = 1 -> kc = kold /\ fc = fold /\ sc = sold /\ rc = fr /\ bc = built) /\
  (j <= 0 -> build_ok src sp kp (w_fetch_phys w) fs n (window_aliases w 1) (pages_of w) = true /\
             cnt_ok src fs n fr built = true /\
             kc = root_val (closed_out src (sublist 0 n fs) kp) /\
             fc = root_val (copy_out src (sublist 0 n fs) (window_aliases w 1) (w_fetch_phys w)) /\
             rc = first_after src fs n w fr built /\ bc = (if built =? 0 then 1 else built)) /\
  (j = 0 -> sc = sold) /\
  (j = -1 -> build_ok src sp kp (w_send_phys w) fs n (window_aliases w 0) (pages_of w) = true /\
             sc = root_val (copy_out src (sublist 0 n fs) (window_aliases w 0) (w_send_phys w))).

Lemma fail_post: forall (X: Prop) (b: bool) s, 0 < s <= 4 -> b = false ->
  0 <= s <= 4 /\ (s = 0 <-> b = true) /\ (s = 0 -> X).
Proof. intros. split; [ lia | split; [ split; intro; [ lia | congruence ] | intro; lia ] ]. Qed.

Lemma fail_iff: forall (b: bool) s, s <> 0 -> b = false -> (s = 0 <-> b = true).
Proof. intros. split; intro; [ lia | congruence ]. Qed.

Definition fillv (w: window) (wr i: Z) : reptype (tarray t_alias 2) :=
  map alias_val (sublist 0 i (window_aliases w wr)) ++ Zrepeat (default_val t_alias) (2 - i).
Lemma fillv0: forall w wr, fillv w wr 0 = default_val (tarray t_alias 2).
Proof. intros. unfold fillv. rewrite sublist_nil. reflexivity. Qed.

Lemma Zlength_upd: forall {A} i (l: list A) x, Zlength (upd_Znth i l x) = Zlength l.
Proof.
  intros. unfold upd_Znth. destruct (Sumbool.sumbool_and _ _ _ _ _ _); [ | reflexivity ].
  rewrite Zlength_app, Zlength_cons, !Zlength_sublist by lia. lia.
Qed.

Lemma Zlength_fillv: forall w wr i, 0 <= i <= pages_of w -> pages_of w <= 2 -> Zlength (fillv w wr i) = 2.
Proof.
  intros. unfold fillv. rewrite Zlength_app, Zlength_map, Zlength_sublist by (rewrite ?window_aliases_len; lia).
  rewrite Zlength_Zrepeat by lia. lia.
Qed.

Lemma fillv_step: forall w wr i, 0 <= i < pages_of w -> pages_of w <= 2 ->
  upd_Znth i (fillv w wr i) (alias_val (window_alias w wr i)) = fillv w wr (i + 1).
Proof.
  intros w wr i Hi HP. unfold fillv.
  pose proof (window_aliases_len w wr) as HA.
  rewrite (sublist_split 0 i (i + 1)) by lia. rewrite sublist_len_1 by lia.
  rewrite Znth_window_aliases by lia. rewrite map_app.
  replace (2 - i) with (1 + (2 - (i + 1))) by lia. rewrite <- Zrepeat_app by lia.
  rewrite upd_Znth_app2 by (rewrite Zlength_map, Zlength_sublist, Zlength_app, !Zlength_Zrepeat by lia; lia).
  rewrite Zlength_map, Zlength_sublist by lia. replace (i - (i - 0)) with 0 by lia.
  change (Zrepeat (default_val t_alias) 1) with [default_val t_alias]. rewrite <- app_comm_cons.
  rewrite upd_Znth0. rewrite <- app_assoc. reflexivity.
Qed.

Lemma alias_store: forall w wr i, word_ok (w_base w) -> 0 <= i -> (wr = 1 \/ wr = 0) ->
  (Vlong (Int64.add (Int64.repr (w_slot w)) (Int64.repr i)),
   (Vlong (Int64.add (Int64.shru (Int64.repr (w_base w)) (Int64.repr (Int.unsigned (Int.repr 12)))) (Int64.repr i)),
    Vlong (Int64.repr (Int.signed (Int.repr wr))))) = alias_val (window_alias w wr i).
Proof.
  intros w wr i Hb Hi Hw. unfold alias_val, window_alias; cbn [a_page a_frame a_writable].
  rewrite !repr_modW, !add64_repr. change (Int.unsigned (Int.repr 12)) with 12.
  unfold Int64.shru. unfold word_ok in Hb. rewrite (Int64.unsigned_repr (w_base w)) by lia.
  rewrite (Int64.unsigned_repr 12) by rep_lia. rewrite add64_repr.
  rewrite Int.signed_repr by (destruct Hw; subst; rep_lia). reflexivity.
Qed.

Definition pick {A} (wr: Z) (a b: A) : A := if wr =? 0 then a else b.
Lemma pick0: forall {A} (a b: A), pick 0 a b = a.
Proof. reflexivity. Qed.
Lemma pick1: forall {A} (a b: A), pick 1 a b = b.
Proof. reflexivity. Qed.
Lemma pickm1: forall {A} (a b: A), pick (-1) a b = b.
Proof. reflexivity. Qed.
Lemma pick_ptr: forall wr a b, isptr a -> isptr b -> isptr (pick wr a b).
Proof. intros. unfold pick. destruct (wr =? 0); auto. Qed.

#[local] Arguments pick : simpl never.
#[local] Arguments fillv : simpl never.

Lemma wfacts_init: forall src sp kp fs n w kold fold sold fr built,
  wfacts src sp kp fs n w kold fold sold fr built 1 kold fold sold fr built.
Proof. intros. unfold wfacts. repeat split; intros; auto; lia. Qed.

Ltac absurd_wr := exfalso; first [ apply Int.one_not_zero; assumption
  | match goal with H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity
                  | H: ?x <> ?x |- _ => apply H; reflexivity
                  | H: Int64.eq ?x ?x = false |- _ => rewrite Int64.eq_true in H; discriminate H end
  | lia | discriminate | auto ].

Lemma ptr_neq_null: forall p, isptr p -> p <> nullval.
Proof. intros p H E. subst. simpl in H. contradiction. Qed.

Lemma int_eq0: forall s, 0 <= s <= 4 -> Int.repr s = Int.repr 0 -> s = 0.
Proof. intros. apply repr_inj_unsigned in H0; rep_lia. Qed.

Ltac bnorm := bz;
  repeat match goal with
  | Hx: negb _ = true |- _ => apply negb_true_iff in Hx
  | Hx: negb _ = false |- _ => apply negb_false_iff in Hx
  end.

Ltac cnt_fin :=
  repeat match goal with
  | H: Int64.eq (Int64.repr ?a) (Int64.repr ?b) = _ |- _ => rewrite (eq64 a b) in H by assumption
  | H: Int64.repr ?a <> Int64.repr ?b |- _ =>
      let E := fresh "E" in
      assert (E: (a =? b) = false)
        by (apply Z.eqb_neq; let E2 := fresh "E2" in intro E2; apply H; rewrite E2; reflexivity); clear H
  end;
  try change (Int64.cmpu Cne) with (fun a b => negb (Int64.eq a b)); cbv beta;
  repeat match goal with |- context [Int64.eq (Int64.repr ?a) (Int64.repr ?b)] => rewrite (eq64 a b) by assumption end;
  repeat match goal with H: (?a =? ?b) = _ |- _ => rewrite H; clear H end;
  repeat match goal with |- context [?a =? ?b] => destruct (a =? b) end; reflexivity.

Lemma fillv_full: forall w wr, 0 <= pages_of w ->
  fillv w wr (pages_of w) = map alias_val (window_aliases w wr) ++ Zrepeat (default_val t_alias) (2 - pages_of w).
Proof. intros. unfold fillv. rewrite sublist_same by (rewrite ?window_aliases_len; lia). reflexivity. Qed.

Lemma alias_len: forall w wr, 0 <= pages_of w <= 2 ->
  Zlength (window_aliases w wr) + Zlength (Zrepeat (default_val t_alias) (2 - pages_of w)) = 2.
Proof. intros. rewrite window_aliases_len, Zlength_Zrepeat by lia. lia. Qed.

Lemma alias_maybe: forall sh (al: list alias) (arest: list (reptype t_alias)) p, isptr p ->
  Zlength al + Zlength arest = 2 ->
  data_at sh (tarray t_alias 2) (map alias_val al ++ arest) p =
  maybe_at sh (tarray t_alias (Zlength al + Zlength arest)) (map alias_val al ++ arest) p.
Proof. intros. rewrite maybe_at_ptr by auto. rewrite H0. reflexivity. Qed.

Lemma result_maybe: forall sh p, isptr p -> data_at_ sh t_result p = maybe_at sh t_result (default_val t_result) p.
Proof. intros. rewrite maybe_at_ptr by auto. reflexivity. Qed.

Lemma if_false: forall {T} (a b: T), (if false then a else b) = b.
Proof. reflexivity. Qed.
Lemma if_eqb0: forall {T} (a b: T), (if 0 =? 0 then a else b) = a.
Proof. reflexivity. Qed.

Lemma window_aliases_wf: forall w wr, (wr = 1 \/ wr = 0) -> Forall alias_wf (window_aliases w wr).
Proof.
  intros. unfold window_aliases. apply Forall_forall. intros a Ha. apply in_map_iff in Ha.
  destruct Ha as [i [Hi _]]. subst. unfold alias_wf, window_alias; cbn [a_page a_frame a_writable].
  split; [ apply word_modW | split; [ apply word_modW | unfold word_ok; destruct H; subst; rep_lia ] ].
Qed.

Lemma window_ok_false_fetch: forall src sp kp fs n w built fr,
  build_ok src sp kp (w_fetch_phys w) fs n (window_aliases w 1) (pages_of w) = false ->
  window_ok src sp kp fs n w built fr = false.
Proof. intros. rewrite window_ok_eq, H, andb_false_r. reflexivity. Qed.

Lemma window_ok_false_send: forall src sp kp fs n w built fr,
  build_ok src sp kp (w_send_phys w) fs n (window_aliases w 0) (pages_of w) = false ->
  window_ok src sp kp fs n w built fr = false.
Proof. intros. rewrite window_ok_eq, H, andb_false_r. reflexivity. Qed.

Lemma window_ok_false_cnt: forall src sp kp fs n w built fr,
  cnt_ok src fs n fr built = false -> window_ok src sp kp fs n w built fr = false.
Proof. intros. rewrite window_ok_eq, H, andb_false_r. reflexivity. Qed.

Lemma wfacts_counts_wf: forall src sp kp fs n w kold fold sold fr built wr kc fc sc rc bc,
  wfacts src sp kp fs n w kold fold sold fr built wr kc fc sc rc bc -> (wr = 1 \/ wr = 0) ->
  counts_wf fr -> word_ok n -> Zlength (pt src) = LEAVES -> counts_wf rc.
Proof.
  intros until bc. intros (_ & H1 & H0 & _ & _) Hw Hf Hn HL. destruct Hw; subst.
  - destruct (H1 eq_refl) as (_ & _ & _ & -> & _). exact Hf.
  - destruct (H0 ltac:(lia)) as (_ & _ & _ & _ & -> & _). unfold first_after. destruct (built =? 0); [ | exact Hf ].
    unfold counts_wf; cbn. split; [ exact Hn | split; [ apply removed_word; auto | split; [ apply retained_word; auto | apply pages_word ] ] ].
Qed.

Lemma wfacts_bc: forall src sp kp fs n w kold fold sold fr built wr kc fc sc rc bc,
  wfacts src sp kp fs n w kold fold sold fr built wr kc fc sc rc bc -> (wr = 1 \/ wr = 0) ->
  Int.min_signed <= built <= Int.max_signed -> Int.min_signed <= bc <= Int.max_signed /\ (wr = 0 -> bc <> 0).
Proof.
  intros until bc. intros (_ & H1 & H0 & _ & _) Hw Hb. destruct Hw; subst.
  - destruct (H1 eq_refl) as (_ & _ & _ & _ & ->). split; [ exact Hb | lia ].
  - destruct (H0 ltac:(lia)) as (_ & _ & _ & _ & _ & ->).
    destruct (built =? 0) eqn:E; [ split; [ rep_lia | lia ] | apply Z.eqb_neq in E; split; [ exact Hb | auto ] ].
Qed.

Lemma mismatch_window: forall src sp kp fs n w kold fold sold fr built wr kc fc sc rc bc,
  wfacts src sp kp fs n w kold fold sold fr built wr kc fc sc rc bc -> (wr = 1 \/ wr = 0) -> bc <> 0 ->
  ((n =? c_protected rc) && (removed_count (sublist 0 n fs) (pt src) =? c_removed rc) &&
   (retained_count (sublist 0 n fs) (pt src) =? c_retained rc))%bool = false ->
  wr = 1 /\ window_ok src sp kp fs n w built fr = false.
Proof.
  intros until bc. intros (_ & H1 & H0 & _ & _) Hw Hbc Hm. destruct Hw; subst.
  - destruct (H1 eq_refl) as (_ & _ & _ & -> & ->). split; [ reflexivity | ]. apply window_ok_false_cnt.
    unfold cnt_ok. rewrite (proj2 (Z.eqb_neq built 0) Hbc). cbn [orb].
    rewrite (Z.eqb_sym (c_protected fr)), (Z.eqb_sym (c_removed fr)), (Z.eqb_sym (c_retained fr)). exact Hm.
  - exfalso. destruct (H0 ltac:(lia)) as (_ & Hc & _ & _ & -> & _). unfold first_after, cnt_ok in *.
    destruct (built =? 0); cbn [orb] in Hc.
    + cbn [c_protected c_removed c_retained] in Hm. rewrite !Z.eqb_refl in Hm. discriminate.
    + rewrite (Z.eqb_sym (c_protected fr)), (Z.eqb_sym (c_removed fr)), (Z.eqb_sym (c_retained fr)) in Hc.
      congruence.
Qed.

Lemma wfacts_step1: forall src sp kp fs n w kold fold sold fr built kc fc sc rc bc,
  wfacts src sp kp fs n w kold fold sold fr built 1 kc fc sc rc bc ->
  build_ok src sp kp (w_fetch_phys w) fs n (window_aliases w 1) (pages_of w) = true ->
  (bc <> 0 -> c_protected rc = n /\ c_removed rc = removed_count (sublist 0 n fs) (pt src) /\
              c_retained rc = retained_count (sublist 0 n fs) (pt src)) ->
  wfacts src sp kp fs n w kold fold sold fr built 0 (root_val (closed_out src (sublist 0 n fs) kp))
    (root_val (copy_out src (sublist 0 n fs) (window_aliases w 1) (w_fetch_phys w))) sc
    (if bc =? 0 then mkcounts n (removed_count (sublist 0 n fs) (pt src)) (retained_count (sublist 0 n fs) (pt src))
                                (pages_of w) else rc)
    (if bc =? 0 then 1 else bc).
Proof.
  intros until bc. intros (_ & H1 & _ & _ & _) Hb Hc. destruct (H1 eq_refl) as (-> & -> & -> & -> & ->).
  unfold wfacts. split; [ lia | ]. split; [ intro; lia | ]. split; [ | split; [ auto | intro; lia ] ].
  intros _. split; [ exact Hb | ]. split; [ | split; [ reflexivity | split; [ reflexivity | split; [ | reflexivity ] ] ] ].
  - unfold cnt_ok. destruct (built =? 0) eqn:E; [ reflexivity | ]. apply Z.eqb_neq in E.
    destruct (Hc E) as (-> & -> & ->). rewrite !Z.eqb_refl. reflexivity.
  - unfold first_after. reflexivity.
Qed.

Lemma wfacts_step0: forall src sp kp fs n w kold fold sold fr built kc fc sc rc bc,
  wfacts src sp kp fs n w kold fold sold fr built 0 kc fc sc rc bc ->
  build_ok src sp kp (w_send_phys w) fs n (window_aliases w 0) (pages_of w) = true ->
  wfacts src sp kp fs n w kold fold sold fr built (-1) (root_val (closed_out src (sublist 0 n fs) kp)) fc
    (root_val (copy_out src (sublist 0 n fs) (window_aliases w 0) (w_send_phys w)))
    (if bc =? 0 then mkcounts n (removed_count (sublist 0 n fs) (pt src)) (retained_count (sublist 0 n fs) (pt src))
                                (pages_of w) else rc)
    (if bc =? 0 then 1 else bc).
Proof.
  intros until bc. intros (_ & _ & H0 & _ & _) Hb. destruct (H0 ltac:(lia)) as (Hf & Hc & -> & -> & -> & ->).
  assert (Hbc: (if built =? 0 then 1 else built) =? 0 = false).
  { destruct (built =? 0) eqn:E; [ reflexivity | exact E ]. }
  rewrite Hbc.
  unfold wfacts. split; [ lia | ]. split; [ intro; lia | ]. split; [ | split; [ intro; lia | ] ].
  - intros _. repeat split; auto.
  - intros _. split; [ exact Hb | reflexivity ].
Qed.
