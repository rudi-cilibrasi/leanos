(* Specifications of the functions of the unit patch/roots_unit.c (include/qotom_copy_root_builder.h,
   include/frame_copy_window.h and three wrappers), under the unit's compspecs.  One specification per
   function serves all three laws.  The functions' integer results are stated with the definitions of
   Defs.v; their memory effects with root_val and friends below. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require LeanosRoots.units.Roots.
Require Import LeanosRoots.roots.code.
Require Import LeanosRoots.proof.Defs.

#[export] Instance CS : compspecs := LeanosRoots.units.Roots.CS.
Definition Vprog : varspecs. mk_varspecs LeanosRoots.roots.code.prog. Defined.

Definition t_root := Tstruct _qotom_root_pages noattr.
Definition t_alias := Tstruct _qotom_copy_alias noattr.
Definition t_result := Tstruct _qotom_root_build_result noattr.
Definition t_window := Tstruct _frame_window noattr.

Definition longs (l: list Z) : list val := map (fun x => Vlong (Int64.repr x)) l.

(* struct qotom_root_pages: pml4, pdpt, pd, pt. *)
Definition root_val (r: root) : reptype t_root :=
  (longs (pml4 r), (longs (pdpt r), (longs (pd r), longs (pt r)))).

(* struct qotom_copy_alias: page, frame, writable. *)
Definition alias_val (a: alias) : reptype t_alias :=
  (Vlong (Int64.repr (a_page a)), (Vlong (Int64.repr (a_frame a)), Vlong (Int64.repr (a_writable a)))).
Definition alias_wf (a: alias) : Prop := word_ok (a_page a) /\ word_ok (a_frame a) /\ word_ok (a_writable a).

(* struct qotom_root_build_result: protected_count, removed_aliases, retained_present, alias_count. *)
Definition result_val (c0 c1 c2 c3: Z) : reptype t_result :=
  (Vlong (Int64.repr c0), (Vlong (Int64.repr c1), (Vlong (Int64.repr c2), Vlong (Int64.repr c3)))).

(* The four counts of a record, for frame_window_build's first record. *)
Record counts := mkcounts { c_protected: Z; c_removed: Z; c_retained: Z; c_aliases: Z }.
Definition counts_val (c: counts) : reptype t_result :=
  result_val (c_protected c) (c_removed c) (c_retained c) (c_aliases c).
Definition counts_wf (c: counts) : Prop :=
  word_ok (c_protected c) /\ word_ok (c_removed c) /\ word_ok (c_retained c) /\ word_ok (c_aliases c).

(* struct frame_window: fetch, send, fetch_phys, send_phys, base, limit, slot. *)
Definition window_val (fetch send: val) (w: window) : reptype t_window :=
  (fetch, (send, (Vlong (Int64.repr (w_fetch_phys w)), (Vlong (Int64.repr (w_send_phys w)),
   (Vlong (Int64.repr (w_base w)), (Vlong (Int64.repr (w_limit w)), Vlong (Int64.repr (w_slot w)))))))).
Definition window_wf (w: window) : Prop :=
  word_ok (w_fetch_phys w) /\ word_ok (w_send_phys w) /\ word_ok (w_base w) /\ word_ok (w_limit w) /\
  word_ok (w_slot w).

(* An object of type t at p, or nothing when p is NULL. *)
Definition maybe_at (sh: share) (t: type) (v: reptype t) (p: val) : mpred :=
  if Val.eq p nullval then emp else data_at sh t v p.

Definition b2z (b: bool) : Z := if b then 1 else 0.

Definition table_entry_spec :=
  DECLARE _qotom_root_table_entry
  WITH phys: Z, k: Z
  PRE [ tulong, tulong ]
    PROP (word_ok phys; 0 <= k <= 10)
    PARAMS (Vlong (Int64.repr phys); Vlong (Int64.repr k))
    SEP ()
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (table_entry phys k))) SEP ().

Definition phys_ok_spec :=
  DECLARE _qotom_root_phys_ok
  WITH a: Z
  PRE [ tulong ]
    PROP (word_ok a) PARAMS (Vlong (Int64.repr a)) SEP ()
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (b2z (phys_ok a)))) SEP ().

Definition phys_disjoint_spec :=
  DECLARE _qotom_root_phys_disjoint
  WITH a: Z, b: Z
  PRE [ tulong, tulong ]
    PROP (word_ok a; word_ok b) PARAMS (Vlong (Int64.repr a); Vlong (Int64.repr b)) SEP ()
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (b2z (disjoint a b)))) SEP ().

(* qotom_root_protected_frame on the first n words of an array that starts with the defined words fs and may
   continue with anything: the builder passes its local copy of the inventory, whose words past the count are
   undefined. *)
Definition protected_frame_spec :=
  DECLARE _qotom_root_protected_frame
  WITH f: Z, p: val, sh: share, fs: list Z, rest: list val, n: Z
  PRE [ tulong, tptr tulong, tulong ]
    PROP (readable_share sh; word_ok f; words_ok fs; 0 <= n <= Zlength fs;
          Zlength fs + Zlength rest <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr f); p; Vlong (Int64.repr n))
    SEP (data_at sh (tarray tulong (Zlength fs + Zlength rest)) (longs fs ++ rest) p)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (b2z (member f (sublist 0 n fs)))))
    SEP (data_at sh (tarray tulong (Zlength fs + Zlength rest)) (longs fs ++ rest) p).

Definition source_ancestors_spec :=
  DECLARE _qotom_root_source_ancestors
  WITH r: val, sh: share, rv: root, phys: Z
  PRE [ tptr t_root, tulong ]
    PROP (readable_share sh; root_ok rv; word_ok phys)
    PARAMS (r; Vlong (Int64.repr phys))
    SEP (data_at sh t_root (root_val rv) r)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (b2z (ancestors_ok rv phys))))
    SEP (data_at sh t_root (root_val rv) r).

(* qotom_build_copy_roots.  Each pointer is NULL or its object; closed, copy and the result record may hold
   anything, even undefined words.  The inventory array holds at least the n words the builder reads when
   n <= 16, and the alias array starts with the m aliases it reads when m <= 2.  Both arrays are nonempty:
   the NULL tests of a non-NULL pointer need it to be valid, which a zero-length array does not give.
   The builder returns 0
   exactly when no pointer is NULL and build_ok holds; then it writes closed_out, copy_out and the counts.
   Otherwise it returns 1..4 and changes nothing. *)
Definition build_pre_post (name: ident) :=
  DECLARE name
  WITH source: val, ssh: share, src: root, sp: Z,
       closed: val, kold: reptype t_root, kp: Z,
       copy: val, cold: reptype t_root, cp: Z,
       frames: val, fsh: share, fs: list Z, n: Z,
       aliases: val, ash: share, al: list alias, arest: list (reptype t_alias), m: Z,
       result: val, rold: reptype t_result
  PRE [ tptr t_root, tulong, tptr t_root, tulong, tptr t_root, tulong,
        tptr tulong, tulong, tptr t_alias, tulong, tptr t_result ]
    PROP (readable_share ssh; readable_share fsh; readable_share ash; root_ok src;
          word_ok sp; word_ok kp; word_ok cp; word_ok n; word_ok m;
          words_ok fs; 0 < Zlength fs <= Int64.max_unsigned; 16 < n \/ n <= Zlength fs;
          Forall alias_wf al; 0 < Zlength al + Zlength arest <= Int64.max_unsigned; 2 < m \/ m <= Zlength al;
          is_pointer_or_null source; is_pointer_or_null closed; is_pointer_or_null copy;
          is_pointer_or_null frames; is_pointer_or_null aliases; is_pointer_or_null result)
    PARAMS (source; Vlong (Int64.repr sp); closed; Vlong (Int64.repr kp); copy; Vlong (Int64.repr cp);
            frames; Vlong (Int64.repr n); aliases; Vlong (Int64.repr m); result)
    SEP (maybe_at ssh t_root (root_val src) source;
         maybe_at Tsh t_root kold closed;
         maybe_at Tsh t_root cold copy;
         maybe_at fsh (tarray tulong (Zlength fs)) (longs fs) frames;
         maybe_at ash (tarray t_alias (Zlength al + Zlength arest)) (map alias_val al ++ arest) aliases;
         maybe_at Tsh t_result rold result)
  POST [ tint ]
    EX status: Z,
    PROP (0 <= status <= 4;
          status = 0 <-> (source <> nullval /\ closed <> nullval /\ copy <> nullval /\ frames <> nullval /\
                          aliases <> nullval /\ result <> nullval /\ build_ok src sp kp cp fs n al m = true))
    RETURN (Vint (Int.repr status))
    SEP (maybe_at ssh t_root (root_val src) source;
         maybe_at Tsh t_root
           (if status =? 0 then root_val (closed_out src (sublist 0 n fs) kp) else kold) closed;
         maybe_at Tsh t_root
           (if status =? 0 then root_val (copy_out src (sublist 0 n fs) (sublist 0 m al) cp) else cold) copy;
         maybe_at fsh (tarray tulong (Zlength fs)) (longs fs) frames;
         maybe_at ash (tarray t_alias (Zlength al + Zlength arest)) (map alias_val al ++ arest) aliases;
         maybe_at Tsh t_result
           (if status =? 0
            then result_val n (removed_count (sublist 0 n fs) (pt src))
                   (retained_count (sublist 0 n fs) (pt src)) m
            else rold) result).

Definition build_copy_roots_spec := build_pre_post _qotom_build_copy_roots.
Definition roots_build_spec := build_pre_post _roots_build.

Definition window_pages_spec :=
  DECLARE _frame_window_pages
  WITH wp: val, wsh: share, fetch: val, send: val, w: window
  PRE [ tptr t_window ]
    PROP (readable_share wsh; window_wf w)
    PARAMS (wp)
    SEP (data_at wsh t_window (window_val fetch send w) wp)
  POST [ tulong ]
    PROP ()
    RETURN (Vlong (Int64.repr (pages_of w)))
    SEP (data_at wsh t_window (window_val fetch send w) wp).

Definition geometry_ok_spec :=
  DECLARE _frame_window_geometry_ok
  WITH wp: val, wsh: share, fetch: val, send: val, w: window
  PRE [ tptr t_window ]
    PROP (readable_share wsh; window_wf w)
    PARAMS (wp)
    SEP (data_at wsh t_window (window_val fetch send w) wp)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (b2z (geometry_ok w))))
    SEP (data_at wsh t_window (window_val fetch send w) wp).

(* frame_window_root_exact on an inventory array of at least n words. *)
Definition scan_pre_post (name: ident) :=
  DECLARE name
  WITH r: val, rsh: share, rv: root, rp: Z, k: val, ksh: share, kv: root, kp: Z,
       frames: val, fsh: share, fs: list Z, n: Z,
       wp: val, wsh: share, fetch: val, send: val, w: window, writable: Z
  PRE [ tptr t_root, tulong, tptr t_root, tulong, tptr tulong, tulong, tptr t_window, tint ]
    PROP (readable_share rsh; readable_share ksh; readable_share fsh; readable_share wsh;
          root_ok rv; root_ok kv; word_ok rp; word_ok kp; words_ok fs; 0 <= n <= Zlength fs;
          Zlength fs <= Int64.max_unsigned; window_wf w; Int.min_signed <= writable <= Int.max_signed)
    PARAMS (r; Vlong (Int64.repr rp); k; Vlong (Int64.repr kp); frames; Vlong (Int64.repr n); wp;
            Vint (Int.repr writable))
    SEP (data_at rsh t_root (root_val rv) r; data_at ksh t_root (root_val kv) k;
         data_at fsh (tarray tulong (Zlength fs)) (longs fs) frames;
         data_at wsh t_window (window_val fetch send w) wp)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (b2z (scan_ok rv kv rp kp (sublist 0 n fs) w (negb (writable =? 0))))))
    SEP (data_at rsh t_root (root_val rv) r; data_at ksh t_root (root_val kv) k;
         data_at fsh (tarray tulong (Zlength fs)) (longs fs) frames;
         data_at wsh t_window (window_val fetch send w) wp).

Definition root_exact_spec := scan_pre_post _frame_window_root_exact.
Definition window_root_exact_spec := scan_pre_post _window_root_exact.

(* What frame_window_build accepts: the geometry, disjoint window roots, both builds, and the first record
   when built is set. *)
Definition window_ok (src: root) (sp kp: Z) (fs: list Z) (n: Z) (w: window) (built: Z) (first: counts) :
    bool :=
  let inv := sublist 0 n fs in
  (geometry_ok w && disjoint (w_fetch_phys w) (w_send_phys w) &&
   build_ok src sp kp (w_fetch_phys w) fs n (window_aliases w 1) (pages_of w) &&
   build_ok src sp kp (w_send_phys w) fs n (window_aliases w 0) (pages_of w) &&
   ((built =? 0) || ((c_protected first =? n) && (c_removed first =? removed_count inv (pt src)) &&
                     (c_retained first =? retained_count inv (pt src)))))%bool.

(* frame_window_build.  The source, the inventory and the window are valid objects; closed, fetch and send
   may hold anything.  It returns 0 exactly when window_ok holds; then closed is closed_out, fetch and send
   copy_out with the window's writable and read-only aliases, built is set and first holds this build's
   counts.  On any other status the roots, first and built hold something else. *)
Definition window_build_pre_post (name: ident) :=
  DECLARE name
  WITH source: val, ssh: share, src: root, sp: Z, closed: val, kold: reptype t_root, kp: Z,
       frames: val, fsh: share, fs: list Z, n: Z,
       wp: val, wsh: share, fetch: val, fold: reptype t_root, send: val, sold: reptype t_root, w: window,
       first: val, fr: counts, builtp: val, built: Z
  PRE [ tptr t_root, tulong, tptr t_root, tulong, tptr tulong, tulong, tptr t_window,
        tptr t_result, tptr tint ]
    PROP (readable_share ssh; readable_share fsh; readable_share wsh; root_ok src;
          word_ok sp; word_ok kp; word_ok n; words_ok fs; 0 < Zlength fs <= Int64.max_unsigned;
          16 < n \/ n <= Zlength fs; window_wf w;
          counts_wf fr; Int.min_signed <= built <= Int.max_signed)
    PARAMS (source; Vlong (Int64.repr sp); closed; Vlong (Int64.repr kp); frames; Vlong (Int64.repr n); wp;
            first; builtp)
    SEP (data_at ssh t_root (root_val src) source; data_at Tsh t_root kold closed;
         data_at fsh (tarray tulong (Zlength fs)) (longs fs) frames;
         data_at wsh t_window (window_val fetch send w) wp;
         data_at Tsh t_root fold fetch; data_at Tsh t_root sold send;
         data_at Tsh t_result (counts_val fr) first; data_at Tsh tint (Vint (Int.repr built)) builtp)
  POST [ tint ]
    EX status: Z, EX k': reptype t_root, EX fe': reptype t_root, EX se': reptype t_root,
    EX r': reptype t_result, EX b': Z,
    PROP (0 <= status <= 4;
          status = 0 <-> window_ok src sp kp fs n w built fr = true;
          status = 0 ->
            let inv := sublist 0 n fs in
            k' = root_val (closed_out src inv kp) /\
            fe' = root_val (copy_out src inv (window_aliases w 1) (w_fetch_phys w)) /\
            se' = root_val (copy_out src inv (window_aliases w 0) (w_send_phys w)) /\
            b' = (if built =? 0 then 1 else built) /\
            r' = (if built =? 0
                  then result_val n (removed_count inv (pt src)) (retained_count inv (pt src)) (pages_of w)
                  else counts_val fr))
    RETURN (Vint (Int.repr status))
    SEP (data_at ssh t_root (root_val src) source; data_at Tsh t_root k' closed;
         data_at fsh (tarray tulong (Zlength fs)) (longs fs) frames;
         data_at wsh t_window (window_val fetch send w) wp;
         data_at Tsh t_root fe' fetch; data_at Tsh t_root se' send;
         data_at Tsh t_result r' first; data_at Tsh tint (Vint (Int.repr b')) builtp).

Definition frame_window_build_spec := window_build_pre_post _frame_window_build.
Definition window_build_spec := window_build_pre_post _window_build.

Definition Gprog : funspecs :=
  [table_entry_spec; phys_ok_spec; phys_disjoint_spec; protected_frame_spec; source_ancestors_spec;
   build_copy_roots_spec; window_pages_spec; geometry_ok_spec; root_exact_spec; frame_window_build_spec;
   roots_build_spec; window_build_spec; window_root_exact_spec].
