(* Bodies of frame_window_root_exact and frame_window_build (include/frame_copy_window.h). *)
Require Import VST.floyd.proofauto.
Require Import LeanosRoots.roots.code.
Require Import LeanosRoots.proof.Defs.
Require Import LeanosRoots.proof.RootsSpecs.
Require Import LeanosRoots.proof.WindowLemmas.
Require Import LeanosRoots.proof.WindowLib.
#[local] Existing Instance RootsSpecs.CS.
#[local] Existing Instance window_alias_default.

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
#[local] Arguments pick : simpl never.
#[local] Arguments fillv : simpl never.

Lemma body_frame_window_root_exact : semax_body Vprog Gprog f_frame_window_root_exact root_exact_spec.
Proof.
  start_function.
  destruct H as (Rl1 & Rl2 & Rl3 & RL & Rw1 & Rw2 & Rw3 & RW).
  destruct H0 as (Kl1 & Kl2 & Kl3 & KL & Kw1 & Kw2 & Kw3 & KW).
  unfold LEAVES in RL, KL.
  forward_call (r, rsh, rv, rp).
  { repeat split; auto. }
  rewrite <- (rootp_eq rsh (root_val rv) r).
  forward_if (temp _t'2 (Vint (Int.repr (b2z (negb (ancestors_ok rv rp && ancestors_ok kv kp)))))).
  { forward. bz. entailer!. }
  { bz. forward_call (k, ksh, kv, kp).
    { repeat split; auto. }
    forward. entailer!. destruct (ancestors_ok kv kp); reflexivity. }
  forward_if.
  { forward. seal. entailer!. rewrite scan_ok_eq.
    destruct (ancestors_ok rv rp && ancestors_ok kv kp)%bool; [ discriminate | reflexivity ]. }
  bz.
  forward_call (wp, wsh, fetch, send, w).
  rewrite <- (rootp_eq ksh (root_val kv) k).
  forward_for_simple_bound 4096 (EX page: Z,
    PROP (forall p, 0 <= p < page -> scan_chk rv kv (sublist 0 n fs) w (negb (writable =? 0)) p = true)
    LOCAL (temp _pages (Vlong (Int64.repr (pages_of w))); temp _root r; temp _root_phys (Vlong (Int64.repr rp));
           temp _closed k; temp _closed_phys (Vlong (Int64.repr kp)); temp _protected_frames frames;
           temp _protected_count (Vlong (Int64.repr n)); temp _w wp; temp _writable (Vint (Int.repr writable)))
    SEP (data_at wsh t_window (window_val fetch send w) wp; rootp rsh (root_val rv) r; rootp ksh (root_val kv) k;
         data_at fsh (tarray tulong (Zlength fs)) (longs fs) frames)).
  { entailer!; intros; lia. }
  { cbv beta. rename i into pg. unfold window_val.
    destruct H6 as (Wf & Ws & Wb & Wlim & Wsl). pose proof (pages_word w) as WP.
    assert (Wc: word_ok (Znth pg (pt kv))) by (apply Znth_word; [ exact KW | lia ]).
    assert (Wl: word_ok (Znth pg (pt rv))) by (apply Znth_word; [ exact RW | lia ]).
    rewrite (rootp_eq ksh (root_val kv) k). unfold root_val.
    forward.
    { entailer!. rewrite Znth_longs by lia. exact I. }
    rewrite Znth_longs by lia. fold (root_val kv) (root_val rv).
    rewrite <- (rootp_eq ksh (root_val kv) k).
    forward_if (temp _t'5 (Vint (Int.repr (b2z (removes (sublist 0 n fs) (Znth pg (pt kv))))))).
    { rewrite and1_repr in *. destruct (Z.odd (Znth pg (pt kv))) eqn:Odd; [ | exfalso; auto ].
      rewrite frames_nil.
      forward_call (frame_of (Znth pg (pt kv)), frames, fsh, fs, @nil val, n).
      { entailer!. simpl. rewrite ?and64_repr, (shru_land_frame (Znth pg (pt kv)) Wc). reflexivity. }
      { apply frame_of_word; auto. }
      rewrite <- frames_nil.
      forward. entailer!. unfold removes. rewrite Odd. destruct (member (frame_of (Znth pg (pt kv))) (sublist 0 n fs)); reflexivity. }
    { rewrite and1_repr in *. destruct (Z.odd (Znth pg (pt kv))) eqn:Odd; [ exfalso; apply Int64.one_not_zero; auto | ].
      forward. entailer!. unfold removes. rewrite Odd. reflexivity. }
    forward_if.
    { bz. forward. seal. entailer!.
      rewrite (scan_ok_false _ _ _ _ _ _ _ pg); [ reflexivity | unfold LEAVES; lia | ].
      unfold scan_chk. match goal with Hr: removes _ (Znth pg (pt kv)) = true |- _ => rewrite Hr end. reflexivity. }
    bz.
    rewrite (rootp_eq rsh (root_val rv) r). unfold root_val.
    forward.
    { entailer!. rewrite Znth_longs by lia. exact I. }
    rewrite Znth_longs by lia. fold (root_val kv) (root_val rv).
    rewrite <- (rootp_eq rsh (root_val rv) r).
    match goal with Hr: removes _ (Znth pg (pt kv)) = false |- _ => rename Hr into Hrem end.
    forward.
    forward_if (temp _t'8 (Vint (Int.repr (b2z (in_slots w pg))))).
    { forward. forward. entailer!.
      match goal with Hs: Int64.ltu _ _ = false |- _ => rewrite ltu64 in Hs by (unfold word_ok in *; rep_lia) end.
      unfold in_slots. change (Int64.cmpu Clt) with Int64.ltu.
      rewrite <- (repr_modW (w_slot w + pages_of w)).
      rewrite ltu64 by (try apply word_modW; unfold word_ok in *; rep_lia).
      rewrite (proj2 (Z.leb_le (w_slot w) pg)) by (apply Z.ltb_ge; assumption).
      cbn [andb]. destruct (pg <? _); reflexivity. }
    { forward. entailer!.
      match goal with Hs: Int64.ltu _ _ = true |- _ => rewrite ltu64 in Hs by (unfold word_ok in *; rep_lia) end.
      unfold in_slots. rewrite (proj2 (Z.leb_gt (w_slot w) pg)) by (apply Z.ltb_lt; assumption). reflexivity. }
    forward_if.
    { match goal with Hi: in_slots w pg = true |- _ => rename Hi into Hin end.
      forward. forward. forward.
      forward_if (temp _t'7 (Vlong (Int64.repr (if negb (writable =? 0) then 2 else 0)))).
      { forward. entailer!. rewrite (proj2 (Z.eqb_neq writable 0)) by (intro; subst; contradiction). reflexivity. }
      { forward. entailer!. rewrite (int_signed_zero writable) by assumption. reflexivity. }
      forward.
      change (Int.unsigned (Int.repr 12)) with 12 in *. change (Int.unsigned (Int.repr 63)) with 63 in *.
      rewrite expected_repr by assumption.
      forward_if.
      { match goal with Hn: Int64.repr (Znth pg (pt rv)) <> _ |- _ => rename Hn into Hne end.
        forward. seal. entailer!.
        rewrite (scan_ok_false _ _ _ _ _ _ _ pg); [ reflexivity | unfold LEAVES; lia | ].
        unfold scan_chk. rewrite Hrem, scan_leaf_in by assumption.
        cbn [negb andb]. apply Z.eqb_neq. intro E. apply Hne. rewrite E. reflexivity. }
      { match goal with He: Int64.eq (Int64.repr (Znth pg (pt rv))) _ = true |- _ =>
          rewrite eq64 in He by (auto; apply alias_word); apply Z.eqb_eq in He; rename He into Heq end.
        forward. entailer!.
        intros p Hp. destruct (zlt p pg); [ match goal with Hall: forall p, 0 <= p < pg -> _ |- _ => apply Hall; lia end | ]. assert (p = pg) by lia. subst p.
        unfold scan_chk. rewrite Hrem, scan_leaf_in by assumption. cbn [negb andb].
        apply Z.eqb_eq. exact Heq. }
    }
    { match goal with Hi: in_slots w pg = false |- _ => rename Hi into Hin end.
      forward_if.
      { match goal with Hn: Int64.repr (Znth pg (pt rv)) <> Int64.repr (Znth pg (pt kv)) |- _ => rename Hn into Hne end.
        forward. seal. entailer!.
        rewrite (scan_ok_false _ _ _ _ _ _ _ pg); [ reflexivity | unfold LEAVES; lia | ].
        unfold scan_chk. rewrite Hrem, scan_leaf_out by assumption.
        cbn [negb andb]. apply Z.eqb_neq. intro E. apply Hne. rewrite E. reflexivity. }
      { match goal with He: Int64.eq (Int64.repr (Znth pg (pt rv))) (Int64.repr (Znth pg (pt kv))) = true |- _ =>
          rewrite eq64 in He by auto; apply Z.eqb_eq in He; rename He into Heq end.
        forward. entailer!.
        intros p Hp. destruct (zlt p pg); [ match goal with Hall: forall p, 0 <= p < pg -> _ |- _ => apply Hall; lia end | ]. assert (p = pg) by lia. subst p.
        unfold scan_chk. rewrite Hrem, scan_leaf_out by assumption. cbn [negb andb].
        apply Z.eqb_eq. exact Heq. } }
    }
  forward. seal. entailer!. rewrite scan_ok_true; [ reflexivity | assumption | ].
  intros p Hp. unfold LEAVES in Hp. auto.
Qed.

Lemma body_frame_window_build : semax_body Vprog Gprog f_frame_window_build frame_window_build_spec.
Proof.
  start_function.
  assert_PROP (isptr source /\ isptr closed /\ isptr frames /\ isptr fetch /\ isptr send /\ isptr first /\
               isptr builtp) as PTRS by entailer!.
  destruct PTRS as (Psrc & Pcl & Pfr & Pfe & Pse & Pfi & Pbu).
  seal.
  forward_call (wp, wsh, fetch, send, w).
  forward_if.
  { bz. forward. Exists 1 kold fold sold (counts_val fr) built. seal. entailer!.
    apply fail_iff; [ lia | ]. rewrite window_ok_eq.
    match goal with Hg: geometry_ok w = false |- _ => rewrite Hg end. reflexivity. }
  bz. match goal with Hg: geometry_ok w = true |- _ => rename Hg into Hgeo end.
  unfold window_val. forward. forward.
  forward_call (w_fetch_phys w, w_send_phys w).
  { destruct H6 as (? & ? & _); auto. }
  forward_if.
  { bz. forward. Exists 2 kold fold sold (counts_val fr) built. seal. entailer!.
    apply fail_iff; [ lia | ]. rewrite window_ok_eq, Hgeo.
    match goal with Hg: disjoint _ _ = false |- _ => rewrite Hg end. reflexivity. }
  bz. match goal with Hg: disjoint _ _ = true |- _ => rename Hg into Hdis end.
  fold (window_val fetch send w).
  forward_call (wp, wsh, fetch, send, w).
  forward_loop (EX wr: Z, EX kc: reptype t_root, EX fc: reptype t_root, EX sc: reptype t_root, EX rc: counts,
                EX bc: Z,
    PROP (wfacts src sp kp fs n w kold fold sold fr built wr kc fc sc rc bc)
    LOCAL (temp _writable (Vint (Int.repr wr)); temp _pages (Vlong (Int64.repr (pages_of w)));
           lvar _result t_result v_result; lvar _aliases (tarray t_alias 2) v_aliases;
           temp _source source; temp _source_phys (Vlong (Int64.repr sp)); temp _closed closed;
           temp _closed_phys (Vlong (Int64.repr kp)); temp _protected_frames frames;
           temp _protected_count (Vlong (Int64.repr n)); temp _w wp; temp _first first; temp _built builtp)
    SEP (rootp ssh (root_val src) source; rootp Tsh kc closed; rootp Tsh (pick wr sc fc) (pick wr send fetch);
         data_at fsh (tarray tulong (Zlength fs)) (longs fs) frames;
         data_at_ Tsh (tarray t_alias 2) v_aliases; data_at_ Tsh t_result v_result;
         rootp Tsh (pick wr fc sc) (pick wr fetch send); data_at wsh t_window (window_val fetch send w) wp;
         data_at Tsh t_result (counts_val rc) first; data_at Tsh tint (Vint (Int.repr bc)) builtp))
  continue: (EX wr: Z, EX kc: reptype t_root, EX fc: reptype t_root, EX sc: reptype t_root, EX rc: counts,
                EX bc: Z,
    PROP (wr = 1 \/ wr = 0; wfacts src sp kp fs n w kold fold sold fr built (wr - 1) kc fc sc rc bc)
    LOCAL (temp _writable (Vint (Int.repr wr)); temp _pages (Vlong (Int64.repr (pages_of w)));
           lvar _result t_result v_result; lvar _aliases (tarray t_alias 2) v_aliases;
           temp _source source; temp _source_phys (Vlong (Int64.repr sp)); temp _closed closed;
           temp _closed_phys (Vlong (Int64.repr kp)); temp _protected_frames frames;
           temp _protected_count (Vlong (Int64.repr n)); temp _w wp; temp _first first; temp _built builtp)
    SEP (rootp ssh (root_val src) source; rootp Tsh kc closed; rootp Tsh (pick wr sc fc) (pick wr send fetch);
         data_at fsh (tarray tulong (Zlength fs)) (longs fs) frames;
         data_at_ Tsh (tarray t_alias 2) v_aliases; data_at_ Tsh t_result v_result;
         rootp Tsh (pick wr fc sc) (pick wr fetch send); data_at wsh t_window (window_val fetch send w) wp;
         data_at Tsh t_result (counts_val rc) first; data_at Tsh tint (Vint (Int.repr bc)) builtp))
  break: (EX kc: reptype t_root, EX fc: reptype t_root, EX sc: reptype t_root, EX rc: counts, EX bc: Z,
    PROP (wfacts src sp kp fs n w kold fold sold fr built (-1) kc fc sc rc bc)
    LOCAL (temp _writable (Vint (Int.repr (-1))); temp _pages (Vlong (Int64.repr (pages_of w)));
           lvar _result t_result v_result; lvar _aliases (tarray t_alias 2) v_aliases;
           temp _source source; temp _source_phys (Vlong (Int64.repr sp)); temp _closed closed;
           temp _closed_phys (Vlong (Int64.repr kp)); temp _protected_frames frames;
           temp _protected_count (Vlong (Int64.repr n)); temp _w wp; temp _first first; temp _built builtp)
    SEP (rootp ssh (root_val src) source; rootp Tsh kc closed; rootp Tsh fc fetch;
         data_at fsh (tarray tulong (Zlength fs)) (longs fs) frames;
         data_at_ Tsh (tarray t_alias 2) v_aliases; data_at_ Tsh t_result v_result;
         rootp Tsh sc send; data_at wsh t_window (window_val fetch send w) wp;
         data_at Tsh t_result (counts_val rc) first; data_at Tsh tint (Vint (Int.repr bc)) builtp)).
  { forward. Exists 1 kold fold sold fr built. rewrite !pick1. entailer!. apply wfacts_init. }
  { Intros wr kc fc sc rc bc.
    match goal with Hw: wfacts _ _ _ _ _ _ _ _ _ _ _ wr _ _ _ _ _ |- _ => rename Hw into WF end.
    assert (Hwr: wr = 1 \/ wr = 0 \/ wr = -1) by apply WF.
    forward_if.
    2: { forward. assert (wr = -1) by (destruct Hwr as [? | [? | ?]]; subst; try lia;
                                       match goal with Hg: _ < 0 |- _ => rewrite Int.signed_repr in Hg by rep_lia; lia end).
         subst wr. Exists kc fc sc rc bc. rewrite !pickm1. entailer!. }
    assert (Hwr2: wr = 1 \/ wr = 0) by lia. clear Hwr.
    assert_PROP (isptr v_aliases /\ isptr v_result) as PAR by entailer!. destruct PAR as (Pal & Pres).
    pose proof H as (_ & _ & _ & RL & _ & _ & _ & SW).
    pose proof (pages_word w) as WP.
    pose proof H6 as (Wf & Ws & Wb & Wlim & Wsl).
    destruct (geometry_slots w ltac:(unfold word_ok in Wsl; lia) Hgeo) as (HP & HS1 & HS2).
    forward_loop (EX i: Z,
      PROP (0 <= i <= pages_of w)
      LOCAL (temp _i (Vlong (Int64.repr i)); temp _writable (Vint (Int.repr wr)); temp _pages (Vlong (Int64.repr (pages_of w)));
           lvar _result t_result v_result; lvar _aliases (tarray t_alias 2) v_aliases;
           temp _source source; temp _source_phys (Vlong (Int64.repr sp)); temp _closed closed;
           temp _closed_phys (Vlong (Int64.repr kp)); temp _protected_frames frames;
           temp _protected_count (Vlong (Int64.repr n)); temp _w wp; temp _first first; temp _built builtp)
      SEP (rootp ssh (root_val src) source; rootp Tsh kc closed; rootp Tsh (pick wr sc fc) (pick wr send fetch);
           data_at fsh (tarray tulong (Zlength fs)) (longs fs) frames;
           data_at Tsh (tarray t_alias 2) (fillv w wr i) v_aliases; data_at_ Tsh t_result v_result;
           rootp Tsh (pick wr fc sc) (pick wr fetch send); data_at wsh t_window (window_val fetch send w) wp;
           data_at Tsh t_result (counts_val rc) first; data_at Tsh tint (Vint (Int.repr bc)) builtp))
    continue: (EX i: Z,
      PROP (0 <= i < pages_of w)
      LOCAL (temp _i (Vlong (Int64.repr i)); temp _writable (Vint (Int.repr wr)); temp _pages (Vlong (Int64.repr (pages_of w)));
           lvar _result t_result v_result; lvar _aliases (tarray t_alias 2) v_aliases;
           temp _source source; temp _source_phys (Vlong (Int64.repr sp)); temp _closed closed;
           temp _closed_phys (Vlong (Int64.repr kp)); temp _protected_frames frames;
           temp _protected_count (Vlong (Int64.repr n)); temp _w wp; temp _first first; temp _built builtp)
      SEP (rootp ssh (root_val src) source; rootp Tsh kc closed; rootp Tsh (pick wr sc fc) (pick wr send fetch);
           data_at fsh (tarray tulong (Zlength fs)) (longs fs) frames;
           data_at Tsh (tarray t_alias 2) (fillv w wr (i + 1)) v_aliases; data_at_ Tsh t_result v_result;
           rootp Tsh (pick wr fc sc) (pick wr fetch send); data_at wsh t_window (window_val fetch send w) wp;
           data_at Tsh t_result (counts_val rc) first; data_at Tsh tint (Vint (Int.repr bc)) builtp))
    break: (PROP ()
      LOCAL (temp _writable (Vint (Int.repr wr)); temp _pages (Vlong (Int64.repr (pages_of w)));
           lvar _result t_result v_result; lvar _aliases (tarray t_alias 2) v_aliases;
           temp _source source; temp _source_phys (Vlong (Int64.repr sp)); temp _closed closed;
           temp _closed_phys (Vlong (Int64.repr kp)); temp _protected_frames frames;
           temp _protected_count (Vlong (Int64.repr n)); temp _w wp; temp _first first; temp _built builtp)
      SEP (rootp ssh (root_val src) source; rootp Tsh kc closed; rootp Tsh (pick wr sc fc) (pick wr send fetch);
           data_at fsh (tarray tulong (Zlength fs)) (longs fs) frames;
           data_at Tsh (tarray t_alias 2) (fillv w wr (pages_of w)) v_aliases; data_at_ Tsh t_result v_result;
           rootp Tsh (pick wr fc sc) (pick wr fetch send); data_at wsh t_window (window_val fetch send w) wp;
           data_at Tsh t_result (counts_val rc) first; data_at Tsh tint (Vint (Int.repr bc)) builtp)).
    { forward. Exists 0. rewrite fillv0. entailer!. }
    { Intros i. forward_if.
      2: { forward. entailer!. replace i with (pages_of w) by lia. cancel. }
      unfold window_val. forward. forward. forward. forward. forward.
      rewrite !upd_Znth_same by (rewrite ?Zlength_upd, Zlength_fillv; lia).
      cbn [fst snd].
      rewrite !upd_Znth_twice by (rewrite ?Zlength_upd, Zlength_fillv; lia).
      rewrite alias_store by (auto; lia).
      rewrite fillv_step by lia.
      Exists i. entailer!. }
    { Intros i. forward. Exists (i + 1). entailer!. }
    forward_if (temp _t'4 (pick wr send fetch)).
    { unfold window_val. forward. forward. entailer!. destruct Hwr2 as [-> | ->]; [ reflexivity | absurd_wr ]. }
    { unfold window_val. forward. forward. entailer!. destruct Hwr2 as [-> | ->]; [ absurd_wr | reflexivity ]. }
    forward.
    forward_if (temp _t'5 (Vlong (Int64.repr (pick wr (w_send_phys w) (w_fetch_phys w))))).
    { unfold window_val. forward. forward. entailer!. destruct Hwr2 as [-> | ->]; [ reflexivity | absurd_wr ]. }
    { unfold window_val. forward. forward. entailer!. destruct Hwr2 as [-> | ->]; [ absurd_wr | reflexivity ]. }
    forward.
    rewrite fillv_full by lia.
    rewrite (rootp_maybe ssh (root_val src) source) by auto.
    rewrite (rootp_maybe Tsh kc closed) by auto.
    rewrite (rootp_maybe Tsh (pick wr sc fc) (pick wr send fetch)) by (apply pick_ptr; auto).
    rewrite <- (maybe_at_ptr fsh (tarray tulong (Zlength fs)) (longs fs) frames) by auto.
    rewrite (alias_maybe Tsh (window_aliases w wr) (Zrepeat (default_val t_alias) (2 - pages_of w)) v_aliases)
      by (auto; apply alias_len; lia).
    rewrite (result_maybe Tsh v_result) by auto.
    forward_call (source, ssh, src, sp, closed, kc, kp, pick wr send fetch, pick wr sc fc,
                  pick wr (w_send_phys w) (w_fetch_phys w), frames, fsh, fs, n, v_aliases, Tsh, window_aliases w wr,
                  Zrepeat (default_val t_alias) (2 - pages_of w), pages_of w, v_result, default_val t_result).
    { rewrite window_aliases_len. split; [ unfold pick; destruct (wr =? 0); auto | ].
      split; [ apply window_aliases_wf; auto | ]. split; [ rewrite Zlength_Zrepeat by lia; rep_lia | ].
      split; [ right; lia | ]. apply isptr_is_pointer_or_null. apply pick_ptr; auto. }
    Intros status.
    match goal with Hs: _ <-> _ |- _ => rename Hs into Hiff end.
    forward_if.
    { assert (Hst: status <> 0) by (intro; subst; absurd_wr).
      assert (Hbf: build_ok src sp kp (pick wr (w_send_phys w) (w_fetch_phys w)) fs n (window_aliases w wr)
                     (pages_of w) = false).
      { destruct (build_ok _ _ _ _ _ _ _ _) eqn:EB; [ | reflexivity ]. exfalso. apply Hst. apply Hiff.
        repeat split; auto; apply ptr_neq_null; auto; apply pick_ptr; auto. }
      forward.
      rewrite !maybe_at_ptr by (auto; apply pick_ptr; auto).
      rewrite alias_len by lia.
      destruct Hwr2 as [-> | ->]; rewrite ?pick0, ?pick1 in *.
      - Exists 2 (if status =? 0 then root_val (closed_out src (sublist 0 n fs) kp) else kc)
          (if status =? 0 then root_val (copy_out src (sublist 0 n fs)
                                  (sublist 0 (pages_of w) (window_aliases w 1)) (w_fetch_phys w)) else fc)
          sc (counts_val rc) bc.
        seal. entailer!. apply fail_iff; [ lia | apply window_ok_false_fetch; auto ].
      - Exists 2 (if status =? 0 then root_val (closed_out src (sublist 0 n fs) kp) else kc) fc
          (if status =? 0 then root_val (copy_out src (sublist 0 n fs)
                                  (sublist 0 (pages_of w) (window_aliases w 0)) (w_send_phys w)) else sc)
          (counts_val rc) bc.
        seal. entailer!. apply fail_iff; [ lia | apply window_ok_false_send; auto ]. }
    destruct (Z.eq_dec status 0) as [-> | Hne];
      [ | exfalso; first [ lia
        | match goal with Hz: Int.repr status = _ |- _ => apply Hne; apply int_eq0; [ lia | exact Hz ] end
        | match goal with Hz: Int.eq _ _ = true |- _ =>
            apply Int.same_if_eq in Hz; apply Hne; apply int_eq0; [ lia | exact Hz ] end
        | match goal with Hz: _ = false |- _ => apply negb_false_iff in Hz; apply Int.same_if_eq in Hz;
            apply Hne; apply int_eq0; [ lia | exact Hz ] end ] ].
    destruct (proj1 Hiff eq_refl) as (_ & _ & _ & _ & _ & _ & Hbo).
    change (0 =? 0) with true. cbv beta iota.
    rewrite (sublist_same 0 (pages_of w) (window_aliases w wr)) by (rewrite ?window_aliases_len; lia).
    rewrite !maybe_at_ptr by (auto; apply pick_ptr; auto).
    rewrite alias_len by lia.
    seal.
    destruct (wfacts_bc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ WF Hwr2 H8) as (Hbcr & Hbc0).
    destruct (wfacts_counts_wf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ WF Hwr2 H7 H2 RL) as (Cp & Cr & Ct & Ca).
    pose proof (removed_word (sublist 0 n fs) (pt src) RL) as WREM.
    pose proof (retained_word (sublist 0 n fs) (pt src) RL) as WRET.
    unfold result_val, counts_val.
    forward.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx [?s0; ?s1; ?s2; ?s3; ?s4; ?s5; ?s6; ?s7; ?s8; ?s9]))) _ _ =>
      forward_if (PROPx ((bc <> 0 -> c_protected rc = n /\ c_removed rc = removed_count (sublist 0 n fs) (pt src) /\
                                    c_retained rc = retained_count (sublist 0 n fs) (pt src)) :: P)
                  (LOCALx L (SEPx [s0; s1; s2; s3; s4; s5; s6; s7;
                    data_at Tsh t_result (counts_val (if bc =? 0 then mkcounts n (removed_count (sublist 0 n fs) (pt src))
                        (retained_count (sublist 0 n fs) (pt src)) (pages_of w) else rc)) first;
                    data_at Tsh tint (Vint (Int.repr (if bc =? 0 then 1 else bc))) builtp])))
    end.
    { assert (Hbc: bc <> 0) by (intro; subst; absurd_wr).
      forward. forward.
      forward_if (temp _t'7 (Vint (Int.repr (b2z (negb ((n =? c_protected rc) &&
                                    (removed_count (sublist 0 n fs) (pt src) =? c_removed rc))%bool))))).
      { forward. entailer!. cnt_fin. }
      { forward. forward. forward. entailer!. cnt_fin. }
      forward_if (temp _t'8 (Vint (Int.repr (b2z (negb ((n =? c_protected rc) &&
                                    (removed_count (sublist 0 n fs) (pt src) =? c_removed rc) &&
                                    (retained_count (sublist 0 n fs) (pt src) =? c_retained rc))%bool))))).
      { forward. entailer!. bnorm.
        match goal with Hx: ((_ =? _) && (_ =? _))%bool = false |- _ => rewrite Hx end. reflexivity. }
      { forward. forward. forward. entailer!. bnorm.
        match goal with Hx: ((_ =? _) && (_ =? _))%bool = true |- _ => rewrite Hx end. cnt_fin. }
      forward_if.
      { bnorm. match goal with Hx: ((_ =? _) && (_ =? _) && (_ =? _))%bool = false |- _ => rename Hx into Hmis end.
        destruct (mismatch_window _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ WF Hwr2 Hbc Hmis) as (-> & Hwf).
        forward.
        Exists 3 (root_val (closed_out src (sublist 0 n fs) kp))
          (root_val (copy_out src (sublist 0 n fs) (window_aliases w 1) (w_fetch_phys w))) sc (counts_val rc) bc.
        rewrite ?pick1 in *. seal. unfold counts_val, result_val. entailer!. apply fail_iff; [ lia | exact Hwf ]. }
      { bnorm. match goal with Hx: ((_ =? _) && (_ =? _) && (_ =? _))%bool = true |- _ => rename Hx into E end.
        apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1, E2, E3.
        forward. rewrite (proj2 (Z.eqb_neq bc 0) Hbc). cbv beta iota. entailer!. }
    }
    { match goal with Hz: Int.repr bc = Int.zero |- _ => apply int_signed_zero in Hz; [ subst bc | exact Hbcr ] end.
      forward. forward. forward. forward. forward. forward. forward. forward. forward.
      change (0 =? 0) with true. cbv beta iota. entailer!. }
    Intros. match goal with Hc: bc <> 0 -> _ |- _ => rename Hc into Hcnt end.
    pose proof (build_ok_facts _ _ _ _ _ _ _ _ Hbo) as (PK & PC & N16).
    forward.
    forward_if (temp _t'9 (Vint (Int.repr 0))).
    { absurd_wr. }
    { rewrite (rootp_eq Tsh (root_val (copy_out src (sublist 0 n fs) (window_aliases w wr)
                                    (pick wr (w_send_phys w) (w_fetch_phys w)))) (pick wr send fetch)).
      rewrite (rootp_eq Tsh (root_val (closed_out src (sublist 0 n fs) kp)) closed).
      focus_SEP 2.
      forward_call (pick wr send fetch, Tsh,
                    copy_out src (sublist 0 n fs) (window_aliases w wr) (pick wr (w_send_phys w) (w_fetch_phys w)),
                    pick wr (w_send_phys w) (w_fetch_phys w), closed, Tsh, closed_out src (sublist 0 n fs) kp, kp,
                    frames, fsh, fs, n, wp, wsh, fetch, send, w, wr).
      { repeat match goal with
        | |- _ /\ _ => split
        | |- root_ok (copy_out _ _ _ _) => apply copy_out_ok; auto
        | |- root_ok (closed_out _ _ _) => apply closed_out_ok; auto
        | |- word_ok (pick _ _ _) => unfold pick; destruct (wr =? 0); auto
        | |- 0 <= n <= Zlength fs => lia
        | |- Int.min_signed <= wr <= Int.max_signed => destruct Hwr2; subst; rep_lia
        end; auto. }
      rewrite scan_built by (auto; try (apply phys_ok_page; auto); unfold word_ok in *; lia).
      forward. seal. entailer!. }
    forward_if; try (absurd_wr; fail).
    all: try forward.
    destruct Hwr2 as [-> | ->].
    - Exists 1 (root_val (closed_out src (sublist 0 n fs) kp))
        (root_val (copy_out src (sublist 0 n fs) (window_aliases w 1) (w_fetch_phys w))) sc
        (if bc =? 0 then mkcounts n (removed_count (sublist 0 n fs) (pt src))
                                    (retained_count (sublist 0 n fs) (pt src)) (pages_of w) else rc)
        (if bc =? 0 then 1 else bc).
      rewrite ?pick1 in *. entailer!. change (1 - 1) with 0. eapply wfacts_step1; eauto.
    - Exists 0 (root_val (closed_out src (sublist 0 n fs) kp)) fc
        (root_val (copy_out src (sublist 0 n fs) (window_aliases w 0) (w_send_phys w)))
        (if bc =? 0 then mkcounts n (removed_count (sublist 0 n fs) (pt src))
                                    (retained_count (sublist 0 n fs) (pt src)) (pages_of w) else rc)
        (if bc =? 0 then 1 else bc).
      rewrite ?pick0 in *. entailer!. change (0 - 1) with (-1). eapply wfacts_step0; eauto.
  }

  { Intros wr kc fc sc rc bc. forward. Exists (wr - 1) kc fc sc rc bc. entailer!.
    match goal with Hw: wr = 1 \/ wr = 0 |- _ => destruct Hw as [-> | ->] end.
    - rewrite !pick1. change (1 - 1) with 0. rewrite !pick0. cancel.
    - rewrite !pick0. change (0 - 1) with (-1). rewrite !pickm1. cancel. }
  Intros kc fc sc rc bc. forward. Exists 0 kc fc sc (counts_val rc) bc. seal. entailer!.
  match goal with Hw: wfacts _ _ _ _ _ _ _ _ _ _ _ (-1) _ _ _ _ _ |- _ => destruct Hw as (_ & _ & Hj0 & _ & Hjm) end.
  destruct (Hj0 ltac:(lia)) as (Bf & Cn & Ek & Ef & Er & Eb).
  destruct (Hjm eq_refl) as (Bs & Es).
  split.
  - split; [ intros _ | intros _; reflexivity ]. rewrite window_ok_eq, Hgeo, Hdis, Bf, Bs, Cn. reflexivity.
  - intros _. repeat split; auto. rewrite Er. unfold first_after. destruct (built =? 0); reflexivity.
Qed.
