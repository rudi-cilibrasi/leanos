(* Law enumeration_exact: the law's device before the scan (main's initialisation) and after it, field by
   field, from the scan's outcome. *)
Require Import VST.floyd.proofauto.
Require Import LeanosEnum.harness.enumeration_exact.code.
Require Import LeanosEnum.proof.Defs.
Require LeanosEnum.proof.EnumSpecs.
Require Import LeanosEnum.proof.LawProg LeanosEnum.proof.LawRun LeanosEnum.proof.LawSpecs LeanosEnum.proof.LawDev
  LeanosEnum.proof.LawSplit LeanosEnum.proof.LawLib.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

(* seen[] of main's uninitialized device. *)
Definition seen_undef : list hv := Zrepeat (Vundef, (Vundef, (Vundef, Zrepeat Vundef 16))) 16.

Definition loc_undef : loc := (Vundef, (Vundef, (Vundef, Vundef))).

(* main's device after its six stores: Dev_exact before any answer. *)
Lemma dev_init: forall ctx, dev_fields 0 0 0 0 0 0 loc_undef seen_undef ctx |-- Dev_exact ctx nil.
Proof.
  intros. rewrite (Dev_go ctx nil 0 0 nil eq_refl). unfold dev_at. Exists seen_undef.
  rewrite dev_split. rewrite Zlength_nil. change (last_loc nil) with loc_undef.
  apply andp_right; [ | apply derives_refl ].
  apply prop_right. split; [ reflexivity | ]. split.
  - unfold seen_undef. simpl. repeat constructor.
  - intros k Hk. rewrite Zlength_nil in Hk. lia.
Qed.

(* After INVALID_ARGUMENT: no answer. *)
Lemma dev_nil: forall ctx, Dev_exact ctx nil |-- EX seen: list hv, dev_fields 0 0 0 0 0 0 loc_undef seen ctx.
Proof.
  intros. rewrite (Dev_go ctx nil 0 0 nil eq_refl). unfold dev_at. Intros seen. Exists seen.
  rewrite dev_split. rewrite Zlength_nil. apply derives_refl.
Qed.

Lemma scan_status: forall h st i off pub, scan h = Some (st, i, off, pub) ->
  st = S_OK \/ st = S_READ_FAILED \/ st = S_CAPACITY_EXCEEDED.
Proof.
  intros h st i off pub S. unfold scan in S.
  destruct (run start h) as [ [ [ [next w] fs ] | st' i' o' ] | ] eqn:R; try discriminate.
  - destruct (live (next, w, fs)); inv S. auto.
  - inv S. destruct (run_stop_status h st i off R); auto.
Qed.

(* After READ_FAILED or CAPACITY_EXCEEDED: stopped, failed exactly on READ_FAILED, 17 functions found exactly
   on CAPACITY_EXCEEDED, at least one read, the last at the location of the outcome. *)
Lemma dev_stop: forall ctx h st i off pub, scan h = Some (st, i, off, pub) -> st <> S_OK ->
  Dev_exact ctx h |--
  EX nx: Z, EX wx: Z, EX fx: Z, EX seen: list hv,
    !! (pub = nil /\
        (st = S_READ_FAILED /\ 0 <= fx <= CAPACITY \/ st = S_CAPACITY_EXCEEDED /\ fx = CAPACITY + 1) /\
        1 <= Zlength h <= FUNCTIONS + WORDS * CAPACITY + 1 /\ 0 <= i < FUNCTIONS /\ 0 <= off <= 60) &&
    dev_fields nx wx fx 1 (b2z (st =? S_READ_FAILED)) (Zlength h) (loc_of i off) seen ctx.
Proof.
  intros ctx h st i off pub S N. unfold scan in S.
  destruct (run start h) as [ [ [ [next w] fs ] | st' i' o' ] | ] eqn:R; try discriminate.
  - destruct (live (next, w, fs)); inv S. contradiction.
  - inv S.
    destruct (run_stop h st i off R) as (h' & a & s & E & R' & L & A & ST). subst h.
    destruct s as [[next w] fs]. destruct a as [[[ia oa] ok] v].
    destruct (step_stop next w fs ia oa ok v st i off A ST) as (-> & -> & C).
    destruct (run_go h' _ R') as [I Nr]. pose proof (nreads_bound _ I) as NB.
    destruct (request_range _ ia oa ok v I L A) as [Ri Ro].
    pose proof I as (_ & _ & Rf & _ & _).
    rewrite (Dev_snoc_stop ctx h' (ia, oa, ok, v) next w fs st ia oa R' L A ST).
    rewrite last_loc_snoc. rewrite Zlength_app, Zlength_cons, Zlength_nil.
    pose proof (Zlength_nonneg h') as L0. pose proof (Zlength_nonneg fs) as F0.
    destruct C as [ (-> & ->) | (-> & -> & Cf & -> & ->) ].
    + simpl Z.eqb. cbv iota. unfold dev_at. Intros seen. rewrite dev_split.
      Exists next w (Zlength fs) seen. simpl b2z.
      apply andp_right; [ apply prop_right | apply derives_refl ].
      unfold FUNCTIONS, WORDS, CAPACITY in *. split; [ reflexivity | ]. split; [ left; split; [ reflexivity | lia ] | lia ].
    + simpl Z.eqb. cbv iota. unfold dev_at. Intros seen. rewrite dev_split.
      Exists (next + 1) 0 (CAPACITY + 1) seen. simpl b2z.
      apply andp_right; [ apply prop_right | apply derives_refl ].
      unfold FUNCTIONS, WORDS, CAPACITY in *. split; [ reflexivity | ]. split; [ right; split; reflexivity | lia ].
Qed.

(* After OK: every identity read, no failure, the headers found with all their dwords, at most 16. *)
Lemma dev_ok: forall ctx h i off pub, scan h = Some (S_OK, i, off, pub) ->
  Dev_exact ctx h |--
  EX fs: list found, EX seen: list hv,
    !! (i = 0 /\ off = 0 /\ pub = rev fs /\ seen_ok fs seen /\ Zlength fs <= CAPACITY /\ Forall complete fs /\
        Forall (fun f => 0 <= fst f < FUNCTIONS) fs /\ Zlength h <= FUNCTIONS + WORDS * CAPACITY) &&
    dev_fields FUNCTIONS 0 (Zlength fs) 0 0 (Zlength h) (last_loc h) seen ctx.
Proof.
  intros ctx h i off pub S. unfold scan in S.
  destruct (run start h) as [ [ [ [next w] fs ] | st' i' o' ] | ] eqn:R; try discriminate.
  - destruct (live (next, w, fs)) eqn:L; [ discriminate | ]. inv S.
    unfold live in L. apply negb_false_iff in L. apply andb_prop in L. destruct L as [W Nx].
    apply Z.eqb_eq in W. apply Z.eqb_eq in Nx. subst w next.
    destruct (run_go h _ R) as [I Nr]. pose proof (nreads_bound _ I) as NB.
    pose proof I as (_ & _ & Rf & Fi & Fc). simpl in Fc.
    rewrite (Dev_go ctx h FUNCTIONS 0 fs R). unfold dev_at. Intros seen. rewrite dev_split.
    Exists fs seen. entailer!.
  - inv S. destruct (run_stop_status h S_OK i off R) as [E|E]; discriminate.
Qed.

(* Before main returns: the device as the local it frees. *)
Lemma dev_free: forall next w nfound stopped failed reads l seen ctx,
  dev_fields next w nfound stopped failed reads l seen ctx |-- data_at_ Tsh t_device ctx.
Proof. intros. rewrite <- dev_split. apply data_at_data_at_. Qed.
