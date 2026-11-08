(* The pure part of the verification of [svar] and [sstore]: the invariant of a
   single variable (or reference), its prophecy and its transitions. *)

Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo.program_logic.identifier.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type g gₛ : nat.
Implicit Type v vₛ 𝑣 𝑣ₛ w : val.
Implicit Type id : identifier.

(* ------------------------------------------------------------------------ *)
(* Operations. *)

(* What an operation asks for: [xchg] is a [set] whose result is the old value. *)
Variant request :=
  | RequestGet
  | RequestSet v
  | RequestCas v1 v2.

Please derive EqDecision for request.

(* A prophesied operation: a [cas] also carries its prophesied outcome. *)
Variant opkind :=
  | OpGet
  | OpSet v
  | OpCas v1 v2 b.

Definition opkind۰request k :=
  match k with
  | OpGet =>
      RequestGet
  | OpSet v =>
      RequestSet v
  | OpCas v1 v2 _ =>
      RequestCas v1 v2
  end.

(* The relation between the outcome [b] and the value [w] seen by the operation. *)
Definition request۰rel req b w : Prop :=
  match req with
  | RequestCas v1 _ =>
      (if b then (≈) else (≉)) w v1
  | _ =>
      True
  end.
Definition request۰apply req b w :=
  match req with
  | RequestGet =>
      w
  | RequestSet v =>
      v
  | RequestCas _ v2 =>
      if b then v2 else w
  end.
Definition request۰result req b w :=
  match req with
  | RequestCas _ _ =>
      ValBool b
  | _ =>
      w
  end.

(* The outcome of a [cas] seeing [w], corrected so as to always agree with
   physical equality; it is the prophesied outcome whenever the [cas] runs. *)
Definition cas۰outcome w v1 b :=
  if b then bool_decide (w ≈ v1) else negb (bool_decide (w ≉ v1)).
Definition opkind۰outcome k w :=
  match k with
  | OpCas v1 _ b =>
      cas۰outcome w v1 b
  | _ =>
      false
  end.
Definition opkind۰apply k w :=
  request۰apply (opkind۰request k) (opkind۰outcome k w) w.
Definition opkind۰result k w :=
  request۰result (opkind۰request k) (opkind۰outcome k w) w.

Lemma opkind۰outcomeｰrel k w :
  request۰rel (opkind۰request k) (opkind۰outcome k w) w.
Proof.
  destruct k as [| v | v1 v2 []]; try done.
  all: rewrite /= /cas۰outcome.
  all: case_bool_decide; first done.
  all: destruct (valｰsimilarｰorｰnonsimilar w v1); done.
Qed.
Lemma cas۰outcomeｰconsistent w v1 b :
  (if b then (≈) else (≉)) w v1 →
  cas۰outcome w v1 b = b.
Proof.
  destruct b => /= H; rewrite /cas۰outcome bool_decide_eq_true_2 //.
Qed.
Lemma opkind۰applyｰcas w v1 v2 b :
  (if b then (≈) else (≉)) w v1 →
    opkind۰apply (OpCas v1 v2 b) w = (if b then v2 else w) ∧
    opkind۰result (OpCas v1 v2 b) w = ValBool b.
Proof.
  intros H. rewrite /opkind۰apply /opkind۰result /= cas۰outcomeｰconsistent //.
Qed.

(* ------------------------------------------------------------------------ *)
(* Prophecies. *)

Variant prophecy :=
  | ProphecyForward v g
  | ProphecyOp id (k : opkind).
Implicit Type proph : prophecy.
Implicit Type prophs past q : list prophecy.

Record operation := Operation
  { operation۰id : identifier
  ; operation۰kind : opkind
  }.
Add Printing Constructor operation.
Implicit Type op : operation.
Implicit Type ops helped help : list operation.

Definition prophecy۰operation proph :=
  match proph with
  | ProphecyForward _ _ =>
      None
  | ProphecyOp id v =>
      Some (Operation id v)
  end.
Definition prophecies۰ops prophs :=
  omap prophecy۰operation prophs.

Definition prophecy۰forward proph :=
  match proph with
  | ProphecyForward v g =>
      Some (v, g)
  | ProphecyOp _ _ =>
      None
  end.
Definition prophecies۰forwards prophs :=
  omap prophecy۰forward prophs.

Definition operations۰ids ops :=
  operation۰id <$> ops.

(* The value after applying [ops] to [𝑣]. *)
Definition ops۰apply ops 𝑣 :=
  foldl (λ w op, opkind۰apply op.(operation۰kind) w) 𝑣 ops.
(* The successive values after applying each of [ops] to [𝑣]. *)
Fixpoint ops۰trace 𝑣 ops : list val :=
  match ops with
  | [] =>
      []
  | op :: ops =>
      let w := opkind۰apply op.(operation۰kind) 𝑣 in
      w :: ops۰trace w ops
  end.

Lemma ops۰applyｰapp ops1 ops2 𝑣 :
  ops۰apply (ops1 ++ ops2) 𝑣 = ops۰apply ops2 (ops۰apply ops1 𝑣).
Proof.
  apply foldl_app.
Qed.
Lemma ops۰traceｰlookup ops 𝑣 k w :
  ops۰trace 𝑣 ops !! k = Some w →
  ops۰apply (take (S k) ops) 𝑣 = w.
Proof.
  move: 𝑣 k. induction ops as [| op ops IH] => 𝑣 k /=; first done.
  destruct k as [| k] => /=.
  - intros [= <-]. done.
  - apply IH.
Qed.

(* The prophecies preceding the first forward whose generation is at least [g]. *)
Fixpoint future۰pre g prophs :=
  match prophs with
  | [] =>
      []
  | ProphecyForward v g' :: prophs =>
      if decide (g ≤ g') then
        []
      else
        ProphecyForward v g' :: future۰pre g prophs
  | ProphecyOp id v :: prophs =>
      ProphecyOp id v :: future۰pre g prophs
  end.
(* The first forward whose generation is at least [g]. *)
Fixpoint future۰target g prophs :=
  match prophs with
  | [] =>
      None
  | ProphecyForward v g' :: prophs =>
      if decide (g ≤ g') then
        Some (v, g')
      else
        future۰target g prophs
  | ProphecyOp _ _ :: prophs =>
      future۰target g prophs
  end.

Lemma prophecies۰opsｰapp prophs1 prophs2 :
  prophecies۰ops (prophs1 ++ prophs2) = prophecies۰ops prophs1 ++ prophecies۰ops prophs2.
Proof.
  apply omap_app.
Qed.
Lemma prophecies۰forwardsｰapp prophs1 prophs2 :
  prophecies۰forwards (prophs1 ++ prophs2) = prophecies۰forwards prophs1 ++ prophecies۰forwards prophs2.
Proof.
  apply omap_app.
Qed.
Lemma prophecies۰opsｰprefix prophs1 prophs2 :
  prophs1 `prefix_of` prophs2 →
  prophecies۰ops prophs1 `prefix_of` prophecies۰ops prophs2.
Proof.
  intros (prophs & ->).
  rewrite prophecies۰opsｰapp.
  apply prefix_app_r. done.
Qed.

Lemma future۰preｰprefix g prophs :
  future۰pre g prophs `prefix_of` prophs.
Proof.
  induction prophs as [| [v g' | id v] prophs IH] => /=.
  - done.
  - case_decide.
    + apply prefix_nil.
    + apply prefix_cons. done.
  - apply prefix_cons. done.
Qed.
Lemma future۰preｰforwards g prophs v g' :
  ProphecyForward v g' ∈ future۰pre g prophs →
  g' < g.
Proof.
  induction prophs as [| [v'' g'' | id v''] prophs IH] => /=.
  - set_solver.
  - case_decide.
    + set_solver.
    + rewrite elem_of_cons. intros [[= -> ->] |]; [lia | auto].
  - rewrite elem_of_cons. intros [[=] |]; auto.
Qed.
Lemma future۰targetｰSome g prophs v g' :
  future۰target g prophs = Some (v, g') →
    g ≤ g' ∧
    future۰pre g prophs ++ [ProphecyForward v g'] `prefix_of` prophs.
Proof.
  induction prophs as [| [v'' g'' | id v''] prophs IH] => /=.
  - done.
  - case_decide.
    + intros [= -> ->]. split; first done.
      apply prefix_cons, prefix_nil.
    + intros (? & ?)%IH. split; first done.
      apply prefix_cons. done.
  - intros (? & ?)%IH. split; first done.
    apply prefix_cons. done.
Qed.
Lemma future۰targetｰNone g prophs :
  future۰target g prophs = None →
  future۰pre g prophs = prophs.
Proof.
  induction prophs as [| [v'' g'' | id v''] prophs IH] => /=.
  - done.
  - case_decide; first done.
    intros ->%IH. done.
  - intros ->%IH. done.
Qed.
Lemma future۰preｰmono g prophs :
  future۰pre g prophs `prefix_of` future۰pre (S g) prophs.
Proof.
  induction prophs as [| [v'' g'' | id v''] prophs IH] => /=.
  - done.
  - repeat case_decide; try lia.
    + done.
    + apply prefix_nil.
    + apply prefix_cons. done.
  - apply prefix_cons. done.
Qed.
Lemma future۰preｰno_forwards g prophs1 v g' prophs2 :
  prophecies۰forwards prophs1 = [] →
  g ≤ g' →
    future۰pre g (prophs1 ++ ProphecyForward v g' :: prophs2) = prophs1 ∧
    future۰target g (prophs1 ++ ProphecyForward v g' :: prophs2) = Some (v, g').
Proof.
  move=> + Hg.
  induction prophs1 as [| [v'' g'' | id v''] prophs1 IH] => /= Hprophs1.
  - rewrite !decide_True //.
  - done.
  - destruct IH as (-> & ->); done.
Qed.
Lemma future۰preｰlength_forward g prophs q v g' :
  q ++ [ProphecyForward v g'] `prefix_of` prophs →
  prophecies۰forwards (future۰pre g prophs) = [] →
  length q ≤ length (future۰pre g prophs) →
  q = future۰pre g prophs.
Proof.
  move: q. induction prophs as [| [v'' g'' | id v''] prophs IH] => q Hprefix /=.
  - apply prefix_nil_inv, app_eq_nil in Hprefix as (_ & [=]).
  - case_decide.
    + simpl. destruct q; simpl; [done | lia].
    + done.
  - intros Hforwards Hq.
    destruct q as [| proph q]; simpl in Hprefix.
    + apply prefix_cons_inv_1 in Hprefix as [=].
    + pose proof Hprefix as ->%prefix_cons_inv_1.
      apply prefix_cons_inv_2 in Hprefix.
      simpl in Hq. rewrite (IH q) //. lia.
Qed.

(* ------------------------------------------------------------------------ *)
(* Waiters & snapshots. *)

Record waiter :=
  { waiter۰request : request
  ; waiter۰post : gname
  ; waiter۰gen : nat
  }.
Implicit Type waiter : waiter.
Implicit Type waiters : gmap identifier waiter.

Record snap := Snap
  { snap۰bid : block_identifier
  ; snap۰val : val
  ; snap۰gen : nat
  ; snap۰inst : nat
  }.
Add Printing Constructor snap.
Implicit Type snap : snap.
Implicit Type snaps : list snap.

Please derive Inhabited for snap.

Definition snap۰to_val snap :=
  ValBlock (Generative (Some snap.(snap۰bid))) Tag0 (@cons val snap.(snap۰val) (@cons val #snap.(snap۰gen) nil)).

Lemma snap۰to_valｰsimilar snap1 snap2 :
  snap۰to_val snap1 ≈ snap۰to_val snap2 →
  snap1.(snap۰gen) = snap2.(snap۰gen).
Proof.
  intros (_ & _ & [= _ ?%(inj _)])%valｰsimilarｰblockｰgenerative; [lia | naive].
Qed.
Lemma snap۰to_valｰnonsimilar snap :
  ¬ snap۰to_val snap ≉ snap۰to_val snap.
Proof.
  intros [| []]%valｰnonsimilarｰblockｰgenerative; done.
Qed.

Variant mode :=
  | Good
  | Doomed (b : identifier) (g_d : nat).
Implicit Type mode : mode.

Please derive Inhabited for mode.

Definition mode۰doomed mode :=
  match mode with
  | Good =>
      0
  | Doomed _ _ =>
      1
  end.

(* ------------------------------------------------------------------------ *)
(* Pure invariant. *)

Definition future۰good g v vₛ helped prophs : Prop :=
  ( helped ≠ [] →
      ∃ q 𝑣 g',
      q ++ [ProphecyForward 𝑣 g'] `prefix_of` prophs ∧
      length q ≤ length (future۰pre g prophs) ∧
      helped `prefix_of` prophecies۰ops q ∧
      𝑣 = v
  ) ∧ (
    ∀ 𝑣,
    future۰target g prophs = Some (𝑣, g) →
    𝑣 ∈ v :: ops۰trace v (drop (length helped) (prophecies۰ops (future۰pre g prophs))) →
    vₛ = 𝑣
  ).

Definition future۰doomed g gₛ waiters past prophs (b : identifier) g_d : Prop :=
  g_d ≤ g ∧
  gₛ < g_d ∧
    ∃ q (w : opkind),
    q ++ [ProphecyOp b w] `prefix_of` prophs ∧
    (∀ 𝑣 g', ProphecyForward 𝑣 g' ∈ q → g' < g_d) ∧
    ∀ waiter,
    waiters !! b = Some waiter →
      g_d ≤ waiter.(waiter۰gen) ∨
      b ∈ operations۰ids (prophecies۰ops past) ∨
      b ∈ operations۰ids (prophecies۰ops q) ∨
      waiter.(waiter۰request) ≠ opkind۰request w.

Definition inv۰state g v vₛ snap waiters helped past prophs mode : Prop :=
  if decide (snap.(snap۰gen) = g) then
    helped = [] ∧
    snap.(snap۰val) = vₛ ∧
    mode = Good
  else
    snap.(snap۰gen) < g ∧
    match mode with
    | Good =>
        future۰good g v vₛ helped prophs
    | Doomed b g_d =>
        future۰doomed g snap.(snap۰gen) waiters past prophs b g_d
    end.

Record inv۰pure 𝑣 g v vₛ snaps snap (hist : list (val * nat)) waiters helped past prophs mode : Prop :=
  { inv۰pure۰snaps_last :
      last snaps = Some snap
  ; inv۰pure۰snaps_sorted i snap1 snap2 :
      snaps !! i = Some snap1 →
      snaps !! S i = Some snap2 →
        snap1.(snap۰gen) < snap2.(snap۰gen) ∧
        snap1.(snap۰inst) ≤ snap2.(snap۰gen)
  ; inv۰pure۰snaps_inst i snap' :
      snaps !! i = Some snap' →
        snap'.(snap۰gen) ≤ snap'.(snap۰inst) ∧
        snap'.(snap۰inst) ≤ g
  ; inv۰pure۰hist_length :
      length hist = S g
  ; inv۰pure۰hist_last :
      ∃ idx, hist !! g = Some (vₛ, idx)
  ; inv۰pure۰hist_idx h vh idx :
      hist !! h = Some (vh, idx) →
      idx < length snaps
  ; inv۰pure۰hist_snaps h vh idx i snap' :
      hist !! h = Some (vh, idx) →
      snaps !! i = Some snap' →
      idx < i →
      h ≤ snap'.(snap۰inst)
  ; inv۰pure۰forwards :
      length snaps = S (length (prophecies۰forwards past))
  ; inv۰pure۰helped_dom op :
      op ∈ helped →
      op.(operation۰id) ∈ dom waiters
  ; inv۰pure۰past_dom op :
      op ∈ prophecies۰ops past →
      op.(operation۰id) ∈ dom waiters
  ; inv۰pure۰model :
      v = ops۰apply helped 𝑣
  ; inv۰pure۰helped :
      helped `prefix_of` prophecies۰ops prophs
  ; inv۰pure۰state :
      inv۰state g v vₛ snap waiters helped past prophs mode
  }.

Fixpoint helpable waiters past helped help : Prop :=
  match help with
  | [] =>
      True
  | op :: help =>
      ( ∃ waiter,
        waiters !! op.(operation۰id) = Some waiter ∧
        waiter.(waiter۰request) = opkind۰request op.(operation۰kind)
      ) ∧
      op.(operation۰id) ∉ operations۰ids (prophecies۰ops past) ∧
      op.(operation۰id) ∉ operations۰ids helped ∧
      helpable waiters past (helped ++ [op]) help
  end.

(* ------------------------------------------------------------------------ *)
(* Pure lemmas. *)

Lemma prophecies۰opsｰlookup prophs n id (v : opkind) :
  prophecies۰ops prophs !! n = Some (Operation id v) →
    ∃ q,
    q ++ [ProphecyOp id v] `prefix_of` prophs ∧
    prophecies۰ops q = take n (prophecies۰ops prophs).
Proof.
  move: n. induction prophs as [| [v' g' | id' v'] prophs IH] => n /=.
  - done.
  - intros (q & Hq & Hops)%IH.
    exists (ProphecyForward v' g' :: q). split.
    + apply prefix_cons. done.
    + done.
  - destruct n as [| n] => /=.
    + intros [= -> ->].
      exists []. split.
      * apply prefix_cons, prefix_nil.
      * done.
    + intros (q & Hq & Hops)%IH.
      exists (ProphecyOp id' v' :: q). split.
      * apply prefix_cons. done.
      * rewrite /= Hops //.
Qed.
Lemma prophecies۰forwardsｰhead prophs v g :
  head (prophecies۰forwards prophs) = Some (v, g) →
    ∃ prophs1 prophs2,
    prophs = prophs1 ++ ProphecyForward v g :: prophs2 ∧
    prophecies۰forwards prophs1 = [].
Proof.
  induction prophs as [| [v' g' | id' v'] prophs IH] => /=.
  - done.
  - intros [= -> ->].
    exists [], prophs. done.
  - intros (prophs1 & prophs2 & -> & Hprophs1)%IH.
    exists (ProphecyOp id' v' :: prophs1), prophs2. done.
Qed.
Lemma prefixｰtotal {A} (l1 l2 l : list A) :
  l1 `prefix_of` l →
  l2 `prefix_of` l →
  length l1 ≤ length l2 →
  l1 `prefix_of` l2.
Proof.
  intros Hl1 Hl2 Hlen.
  destruct (prefix_weak_total l1 l2 l) as [| Hl21]; [done.. |].
  apply prefix_length_eq in Hl21 as ->; done.
Qed.

Lemma last_omap {A B} (f : A → option B) l y x :
  last l = Some y →
  f y = Some x →
  last (omap f l) = Some x.
Proof.
  intros Hl Hf.
  destruct l as [| a l _] using rev_ind; first done.
  rewrite last_snoc in Hl. injection Hl as ->.
  rewrite omap_app /= Hf last_snoc //.
Qed.

Lemma last_omap_cons {A B} (f : A → option B) x l :
  last (omap f (x :: l)) =
    match last (omap f l) with
    | Some y =>
        Some y
    | None =>
        f x
    end.
Proof.
  change (omap f (x :: l)) with (match f x with Some y => y :: omap f l | None => omap f l end).
  destruct (f x); [rewrite last_cons |]; destruct (last (omap f l)); done.
Qed.

Lemma snapsｰlookup_last snaps snap :
  last snaps = Some snap →
  snaps !! pred (length snaps) = Some snap.
Proof.
  rewrite last_lookup //.
Qed.
Lemma inv۰pureｰsnaps_lt {𝑣 g v vₛ snaps snap hist waiters helped past prophs mode} i j snap1 snap2 :
  inv۰pure 𝑣 g v vₛ snaps snap hist waiters helped past prophs mode →
  i < j →
  snaps !! i = Some snap1 →
  snaps !! j = Some snap2 →
  snap1.(snap۰gen) < snap2.(snap۰gen).
Proof.
  intros Hinv Hij. move: snap2. induction Hij as [| j Hij IH] => snap2 Hlookup1 Hlookup2.
  - eapply inv۰pure۰snaps_sorted; done.
  - destruct (snaps !! j) as [snap' |] eqn:Hlookup.
    + opose proof* (inv۰pure۰snaps_sorted _ _ _ _ _ _ _ _ _ _ _ _ Hinv j) as Hsorted; [done.. |].
      specialize (IH snap'). lia.
    + apply lookup_lt_Some in Hlookup2.
      apply lookup_ge_None in Hlookup. lia.
Qed.
Lemma inv۰pureｰsnaps_gen_inj {𝑣 g v vₛ snaps snap hist waiters helped past prophs mode} i j snap1 snap2 :
  inv۰pure 𝑣 g v vₛ snaps snap hist waiters helped past prophs mode →
  snaps !! i = Some snap1 →
  snaps !! j = Some snap2 →
  snap1.(snap۰gen) = snap2.(snap۰gen) →
  i = j.
Proof.
  intros Hinv Hlookup1 Hlookup2 Hgen.
  destruct (Nat.lt_trichotomy i j) as [Hij | [? | Hij]]; [| done |].
  - opose proof* (inv۰pureｰsnaps_lt i j); [done.. | lia].
  - opose proof* (inv۰pureｰsnaps_lt j i); [done.. | lia].
Qed.
Lemma inv۰pureｰsnaps_le_last {𝑣 g v vₛ snaps snap hist waiters helped past prophs mode} i snap' :
  inv۰pure 𝑣 g v vₛ snaps snap hist waiters helped past prophs mode →
  snaps !! i = Some snap' →
  snap'.(snap۰gen) ≤ snap.(snap۰gen).
Proof.
  intros Hinv Hlookup.
  pose proof (inv۰pure۰snaps_last _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as Hlast%snapsｰlookup_last.
  pose proof Hlookup as Hi%lookup_lt_Some.
  destruct (decide (i = pred (length snaps))) as [-> |].
  - simplify_eq. done.
  - opose proof* (inv۰pureｰsnaps_lt i (pred (length snaps))); [done | lia | done.. | lia].
Qed.
Lemma inv۰pureｰsnap_gen {𝑣 g v vₛ snaps snap hist waiters helped past prophs mode} :
  inv۰pure 𝑣 g v vₛ snaps snap hist waiters helped past prophs mode →
  snap.(snap۰gen) ≤ g.
Proof.
  intros Hinv.
  pose proof (inv۰pure۰snaps_last _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as Hlast%snapsｰlookup_last.
  opose proof* inv۰pure۰snaps_inst as (? & ?); [done.. | lia].
Qed.
Lemma inv۰pureｰstable {𝑣 g v vₛ snaps snap hist waiters helped past prophs mode} :
  inv۰pure 𝑣 g v vₛ snaps snap hist waiters helped past prophs mode →
  g ≤ snap.(snap۰gen) →
    snap.(snap۰gen) = g ∧
    snap.(snap۰val) = vₛ.
Proof.
  intros Hinv Hg.
  pose proof (inv۰pureｰsnap_gen Hinv).
  pose proof (inv۰pure۰state _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as Hstate.
  rewrite /inv۰state decide_True in Hstate; first lia.
  split; [lia | apply Hstate].
Qed.
Lemma inv۰pureｰreader {𝑣 g v vₛ snaps snap hist waiters helped past prophs} :
  inv۰pure 𝑣 g v vₛ snaps snap hist waiters helped past prophs Good →
  snap.(snap۰gen) < g →
  head (prophecies۰forwards prophs) = Some (𝑣, g) →
  vₛ = 𝑣.
Proof.
  intros Hinv Hgₛ (prophs1 & prophs2 & -> & Hprophs1)%prophecies۰forwardsｰhead.
  pose proof (inv۰pure۰state _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as Hstate.
  rewrite /inv۰state decide_False in Hstate; first lia.
  destruct Hstate as (_ & Hhelped & Htarget).
  odestruct (future۰preｰno_forwards g prophs1) as (Hpre & Htarget'); [done.. |].
  apply Htarget in Htarget'. apply Htarget'.
  destruct (decide (helped = [])) as [-> | (q & 𝑣' & g' & Hq & Hq_length & Hhelped_q & ->)%Hhelped].
  - rewrite (inv۰pure۰model _ _ _ _ _ _ _ _ _ _ _ _ Hinv).
    apply list_elem_of_here.
  - rewrite Hpre in Hq_length.
    opose proof* (future۰preｰlength_forward g) as Hq'; [done | rewrite Hpre // | rewrite Hpre // |].
    rewrite Hpre in Hq'. subst q.
    apply prefix_app_inv in Hq as Hq. apply prefix_cons_inv_1 in Hq as [= -> ->].
    apply list_elem_of_here.
Qed.

Lemma inv۰pureｰregister {𝑣 g v vₛ snaps snap hist waiters helped past prophs mode} id waiter :
  inv۰pure 𝑣 g v vₛ snaps snap hist waiters helped past prophs mode →
  waiters !! id = None →
  waiter.(waiter۰gen) = g →
  inv۰pure 𝑣 g v vₛ snaps snap hist (<[id := waiter]> waiters) helped past prophs mode.
Proof.
  intros [] Hlookup Hgen.
  split; try done.
  - intros. rewrite dom_insert. set_solver.
  - intros. rewrite dom_insert. set_solver.
  - move: inv۰pure۰state0. rewrite /inv۰state.
    case_decide; first done.
    destruct mode as [| b g_d]; first done.
    intros (? & ? & ? & q & w & Hq & Hq_forwards & Hb).
    do 3 (split; first done). exists q, w. do 2 (split; first done).
    intros waiter'.
    destruct (decide (b = id)) as [-> |].
    + rewrite lookup_insert_eq. intros [= <-]. left. lia.
    + rewrite lookup_insert_ne //. auto.
Qed.

Lemma inv۰pureｰwrite {𝑣 g v vₛ snaps snap hist waiters helped past prophs mode} id (w : opkind) waiter :
  inv۰pure 𝑣 g v vₛ snaps snap hist waiters helped past (ProphecyOp id w :: prophs) mode →
  waiters !! id = Some waiter →
  waiter.(waiter۰request) = opkind۰request w →
  id ∉ operations۰ids (prophecies۰ops past) →
  waiter.(waiter۰gen) ≤ snap.(snap۰gen) →
    (helped = [] ∨ head helped = Some (Operation id w)) ∧
    inv۰pure (opkind۰apply w 𝑣) g (if helped is [] then opkind۰apply w v else v) vₛ snaps snap hist waiters (tail helped) (past ++ [ProphecyOp id w]) prophs mode.
Proof.
  intros Hinv Hlookup Hval Hid Hgen.
  pose proof Hinv as [].
  assert (helped = [] ∨ ∃ helped', helped = Operation id w :: helped') as Hhelped.
  { destruct helped as [| op helped']; first auto.
    pose proof inv۰pure۰helped0 as ->%prefix_cons_inv_1.
    eauto.
  }
  split.
  { destruct Hhelped as [-> | (helped' & ->)]; auto. }
  split; try done.
  - rewrite prophecies۰forwardsｰapp right_id //.
  - destruct Hhelped as [-> | (helped' & ->)]; first done.
    intros op Hop. apply inv۰pure۰helped_dom0. set_solver.
  - rewrite prophecies۰opsｰapp. intros op [Hop | ->%list_elem_of_singleton]%elem_of_app; auto.
    apply elem_of_dom. naive.
  - destruct Hhelped as [-> | (helped' & ->)]; rewrite inv۰pure۰model0 //.
  - destruct Hhelped as [-> | (helped' & ->)].
    + apply prefix_nil.
    + apply prefix_cons_inv_2 in inv۰pure۰helped0. done.
  - move: inv۰pure۰state0. rewrite /inv۰state.
    case_decide.
    { destruct Hhelped as [-> | (helped' & ->)]; naive. }
    intros (Hgₛ & Hmode). split; first done.
    destruct mode as [| b g_d].
    + destruct Hmode as (Hhelped_ & Htarget). split.
      * intros Hhelped'.
        destruct Hhelped as [-> | (helped' & ->)]; first done.
        odestruct Hhelped_ as (q & 𝑣' & g' & Hq & Hq_length & Hhelped_q & Hlast); first done.
        destruct q as [| proph q].
        { apply prefix_nil_inv in Hhelped_q as [=]. }
        simpl in Hq. pose proof Hq as ->%prefix_cons_inv_1. apply prefix_cons_inv_2 in Hq.
        exists q, 𝑣', g'. split_and!.
        -- done.
        -- simpl in Hq_length. lia.
        -- apply prefix_cons_inv_2 in Hhelped_q. done.
        -- rewrite -Hlast /=. destruct helped' => //.
      * intros 𝑣' Htarget' H𝑣'.
        apply Htarget; first done.
        destruct Hhelped as [-> | (helped' & ->)].
        -- rewrite inv۰pure۰model0 /= in H𝑣' |- *. set_solver.
        -- done.
    + destruct Hmode as (Hg_d & Hgₛ_d & q & w_b & Hq & Hq_forwards & Hb).
      split_and!; [done.. |].
      destruct q as [| proph q].
      * simpl in Hq. apply prefix_cons_inv_1 in Hq as [= <- <-].
        exfalso.
        destruct (Hb waiter) as [| [| [|]]]; [done | lia | done | set_solver | done].
      * simpl in Hq. pose proof Hq as ->%prefix_cons_inv_1. apply prefix_cons_inv_2 in Hq.
        exists q, w_b. split_and!.
        -- done.
        -- set_solver.
        -- intros waiter' Hlookup'.
           rewrite /operations۰ids prophecies۰opsｰapp fmap_app.
           destruct (Hb waiter') as [| [Hb' | [Hb' |]]]; [done | auto | | | auto].
           ++ right. left. set_solver.
           ++ simpl in Hb'. rewrite elem_of_cons in Hb'. destruct Hb' as [-> | ?].
              ** right. left. set_solver.
              ** auto.
Qed.

Lemma inv۰pureｰforward {𝑣 g v vₛ snaps snap hist waiters helped past prophs mode} 𝑣' g' bid :
  inv۰pure 𝑣 g v vₛ snaps snap hist waiters helped past (ProphecyForward 𝑣' g' :: prophs) mode →
  snap.(snap۰gen) < g' →
  snap.(snap۰inst) ≤ g' →
  g' ≤ g →
  (g' = g → mode = Good → vₛ = 𝑣') →
  inv۰pure 𝑣 g v vₛ (snaps ++ [Snap bid 𝑣' g' g]) (Snap bid 𝑣' g' g) hist waiters helped (past ++ [ProphecyForward 𝑣' g']) prophs mode.
Proof.
  intros Hinv Hgen Hinst Hg' Hvₛ.
  pose proof Hinv as [].
  pose proof inv۰pure۰snaps_last0 as Hlast%snapsｰlookup_last.
  pose proof Hlast as Hlength%lookup_lt_Some.
  split; try done.
  - rewrite last_snoc //.
  - intros i snap1 snap2 Hlookup1 Hlookup2.
    destruct (decide (S i < length snaps)).
    + rewrite lookup_app_l in Hlookup1; first lia.
      rewrite lookup_app_l in Hlookup2; first lia.
      eauto.
    + pose proof Hlookup2 as Hi%lookup_lt_Some. rewrite length_app /= in Hi.
      rewrite lookup_app_l in Hlookup1; first lia.
      rewrite lookup_app_r in Hlookup2; first lia.
      apply list_lookup_singleton_Some in Hlookup2 as (_ & <-).
      assert (i = pred (length snaps)) as -> by lia.
      simplify_eq. done.
  - intros i snap' [Hlookup | (_ & (_ & <-)%list_lookup_singleton_Some)]%lookup_app_Some.
    + opose proof* inv۰pure۰snaps_inst0; [done | lia].
    + simpl. lia.
  - intros h vh idx Hlookup.
    opose proof* inv۰pure۰hist_idx0; first done.
    simp_length. lia.
  - intros h vh idx i snap' Hlookup [Hlookup' | (Hi & (_ & <-)%list_lookup_singleton_Some)]%lookup_app_Some Hidx.
    + eauto.
    + apply lookup_lt_Some in Hlookup. simpl. lia.
  - rewrite prophecies۰forwardsｰapp !length_app /=. lia.
  - rewrite prophecies۰opsｰapp right_id //.
  - move: inv۰pure۰state0. rewrite /inv۰state /=.
    rewrite decide_False; first lia.
    intros (Hgₛ & Hmode).
    case_decide as Hg; first subst g'.
    + destruct mode as [| b g_d].
      * destruct Hmode as (Hhelped & _).
        split_and!; [| symmetry; by apply Hvₛ | done].
        destruct (decide (helped = [])) as [| (q & 𝑣'' & g'' & Hq & Hq_length & Hhelped_q & _)%Hhelped]; first done.
        rewrite /= decide_True // in Hq_length.
        destruct q; last (simpl in Hq_length; lia).
        apply prefix_nil_inv in Hhelped_q. done.
      * destruct Hmode as (Hg_d & Hgₛ_d & q & w & Hq & Hq_forwards & _).
        destruct q as [| proph q].
        -- simpl in Hq. apply prefix_cons_inv_1 in Hq as [=].
        -- simpl in Hq. pose proof Hq as ->%prefix_cons_inv_1.
           opose proof* (Hq_forwards 𝑣' g); [apply elem_of_cons; by left | lia].
    + split; first lia.
      destruct mode as [| b g_d].
      * destruct Hmode as (Hhelped & Htarget).
        rewrite /= decide_False in Hhelped Htarget; first lia.
        split.
        -- intros Hne. destruct (Hhelped Hne) as (q & 𝑣'' & g'' & Hq & Hq_length & Hhelped_q & Hlast').
           destruct q as [| proph q].
           { apply prefix_nil_inv in Hhelped_q as ->. done. }
           simpl in Hq. pose proof Hq as ->%prefix_cons_inv_1. apply prefix_cons_inv_2 in Hq.
           exists q, 𝑣'', g''. split_and!; try done.
           simpl in Hq_length. lia.
        -- intros 𝑣'' Ht H𝑣''. apply Htarget; last done.
           rewrite decide_False //. lia.
      * destruct Hmode as (Hg_d & Hgₛ_d & q & w & Hq & Hq_forwards & Hb).
        destruct q as [| proph q].
        { simpl in Hq. apply prefix_cons_inv_1 in Hq as [=]. }
        simpl in Hq. pose proof Hq as ->%prefix_cons_inv_1. apply prefix_cons_inv_2 in Hq.
        split_and!.
        -- done.
        -- opose proof* (Hq_forwards 𝑣' g'); [apply elem_of_cons; by left | lia].
        -- exists q, w. split_and!.
           ++ done.
           ++ intros 𝑣'' g'' ?. apply (Hq_forwards 𝑣''). apply elem_of_cons. by right.
           ++ intros waiter Hlookup.
              rewrite prophecies۰opsｰapp right_id.
              exact (Hb waiter Hlookup).
Qed.

Lemma helpableｰdom waiters past helped help :
  helpable waiters past helped help →
  ∀ op,
  op ∈ help →
  op.(operation۰id) ∈ dom waiters.
Proof.
  move: helped. induction help as [| op' help IH] => helped /=.
  - set_solver.
  - intros ((waiter & Hlookup & _) & _ & _ & Hhelpable) op [-> | Hop]%elem_of_cons.
    + apply elem_of_dom. eauto.
    + eapply IH; done.
Qed.
Lemma helpableｰdecide waiters past helped help :
  helpable waiters past helped help ∨
    ∃ k op,
    help !! k = Some op ∧
    ( (∀ waiter, waiters !! op.(operation۰id) = Some waiter → waiter.(waiter۰request) ≠ opkind۰request op.(operation۰kind))
    ∨ op.(operation۰id) ∈ operations۰ids (prophecies۰ops past)
    ∨ op.(operation۰id) ∈ operations۰ids (helped ++ take k help)
    ).
Proof.
  move: helped. induction help as [| op help IH] => helped /=.
  - auto.
  - assert (
      (∃ waiter, waiters !! op.(operation۰id) = Some waiter ∧ waiter.(waiter۰request) = opkind۰request op.(operation۰kind)) ∨
      (∀ waiter, waiters !! op.(operation۰id) = Some waiter → waiter.(waiter۰request) ≠ opkind۰request op.(operation۰kind))
    ) as [Hwaiter | Hwaiter].
    { destruct (waiters !! op.(operation۰id)) as [waiter |].
      - destruct (decide (waiter.(waiter۰request) = opkind۰request op.(operation۰kind))); naive.
      - naive.
    }
    2: { right. exists 0, op. naive. }
    destruct (decide (op.(operation۰id) ∈ operations۰ids (prophecies۰ops past))).
    { right. exists 0, op. naive. }
    destruct (decide (op.(operation۰id) ∈ operations۰ids helped)).
    { right. exists 0, op. rewrite right_id. naive. }
    destruct (IH (helped ++ [op])) as [| (k & op' & Hlookup & Hop')].
    + left. naive.
    + right. exists (S k), op'. split; first done.
      rewrite /= -(assoc _ helped [op]) // in Hop'.
Qed.

Lemma inv۰pureｰclick' {𝑣 g v vₛ snaps snap hist waiters helped past prophs mode} help mode' :
  inv۰pure 𝑣 g v vₛ snaps snap hist waiters helped past prophs mode →
  let v' := ops۰apply help v in
  (∀ op, op ∈ help → op.(operation۰id) ∈ dom waiters) →
  helped ++ help `prefix_of` prophecies۰ops prophs →
  inv۰state (S g) v' v' snap waiters (helped ++ help) past prophs mode' →
  inv۰pure 𝑣 (S g) v' v' snaps snap (hist ++ [(v', pred (length snaps))]) waiters (helped ++ help) past prophs mode'.
Proof.
  intros [] v' Hdom Hprefix Hstate.
  pose proof inv۰pure۰snaps_last0 as Hlast%snapsｰlookup_last.
  pose proof Hlast as Hlength%lookup_lt_Some.
  split; try done.
  - intros. opose proof* inv۰pure۰snaps_inst0; [done | lia].
  - simp_length. simpl. lia.
  - exists (pred (length snaps)).
    rewrite lookup_app_r; first lia.
    rewrite inv۰pure۰hist_length0 Nat.sub_diag //.
  - intros h vh idx [Hlookup | (_ & (_ & [= _ <-])%list_lookup_singleton_Some)]%lookup_app_Some; eauto.
  - intros h vh idx i snap' [Hlookup | (Hh & (_ & [= _ <-])%list_lookup_singleton_Some)]%lookup_app_Some Hlookup' Hi; eauto.
    apply lookup_lt_Some in Hlookup'. lia.
  - intros op [|]%elem_of_app; auto.
  - rewrite /v' ops۰applyｰapp inv۰pure۰model0 //.
Qed.

Lemma inv۰pureｰclick {𝑣 g v vₛ snaps snap hist waiters helped past prophs mode} :
  inv۰pure 𝑣 g v vₛ snaps snap hist waiters helped past prophs mode →
    ∃ help mode',
    helpable waiters past helped help ∧
    mode۰doomed mode ≤ mode۰doomed mode' ∧
    let v' := ops۰apply help v in
    inv۰pure 𝑣 (S g) v' v' snaps snap (hist ++ [(v', pred (length snaps))]) waiters (helped ++ help) past prophs mode'.
Proof.
  intros Hinv.
  pose proof Hinv as [].
  pose proof (inv۰pureｰsnap_gen Hinv) as Hgₛ.
  assert (snap.(snap۰gen) ≠ S g) as Hgₛ' by lia.
  destruct mode as [| b g_d]; last first.
  { exists [], (Doomed b g_d). split_and!; [done | done |].
    apply (inv۰pureｰclick' _ _ Hinv); [set_solver | rewrite right_id // |].
    rewrite right_id {1}/inv۰state decide_False //=.
    move: inv۰pure۰state0. rewrite /inv۰state.
    case_decide; first (intros (_ & _ & [=])).
    intros (_ & Hg_d & Hmode). split; first lia.
    split; first lia. done.
  }
  (* the helped operations are justified by an upcoming forward *)
  assert (
    helped ≠ [] →
      ∃ q 𝑣' g',
      q ++ [ProphecyForward 𝑣' g'] `prefix_of` prophs ∧
      length q ≤ length (future۰pre g prophs) ∧
      helped `prefix_of` prophecies۰ops q ∧
      𝑣' = v
  ) as Hhelped.
  { move: inv۰pure۰state0. rewrite /inv۰state.
    case_decide.
    - intros (-> & _) ?. done.
    - intros (_ & Hh & _). exact Hh.
  }
  set X := prophecies۰ops (future۰pre (S g) prophs).
  assert (helped `prefix_of` X) as Hhelped_X.
  { destruct (decide (helped = [])) as [-> | (q & 𝑣' & g' & Hq & Hq_length & Hhelped_q & _)%Hhelped].
    - apply prefix_nil.
    - trans (prophecies۰ops q); first done.
      apply prophecies۰opsｰprefix.
      eapply prefixｰtotal.
      + eapply prefix_app_l. done.
      + apply future۰preｰprefix.
      + pose proof (prefix_length _ _ (future۰preｰmono g prophs)). lia.
  }
  assert (X `prefix_of` prophecies۰ops prophs) as HX.
  { apply prophecies۰opsｰprefix, future۰preｰprefix. }
  set rest := drop (length helped) X.
  assert (∀ k, helped ++ take k rest = take (length helped + k) X) as Hrest.
  { intros k. rewrite -take_take_drop.
    destruct Hhelped_X as (? & ->).
    rewrite take_app_length //.
  }
  (* no helping *)
  assert (
    (∀ 𝑣', future۰target (S g) prophs = Some (𝑣', S g) → 𝑣' ∈ ops۰trace v rest → 𝑣' = v) →
      ∃ help mode',
      helpable waiters past helped help ∧
      mode۰doomed Good ≤ mode۰doomed mode' ∧
      let v' := ops۰apply help v in
      inv۰pure 𝑣 (S g) v' v' snaps snap (hist ++ [(v', pred (length snaps))]) waiters (helped ++ help) past prophs mode'
  ) as Hno_help.
  { intros Hno.
    exists [], Good. split_and!; [done | done |].
    apply (inv۰pureｰclick' _ _ Hinv); [set_solver | rewrite right_id // |].
    rewrite /inv۰state decide_False // /= right_id.
    split; first lia. split.
    - intros (q & 𝑣' & g' & Hq & Hq_length & Hhelped_q & Hlast)%Hhelped.
      exists q, 𝑣', g'. split_and!; try done.
      pose proof (prefix_length _ _ (future۰preｰmono g prophs)). lia.
    - intros 𝑣' Htarget [-> | H𝑣']%elem_of_cons; first done.
      symmetry. apply Hno; done.
  }
  destruct (future۰target (S g) prophs) as [(vT & gT) |] eqn:Htarget; last first.
  { apply Hno_help. done. }
  destruct (decide (gT = S g ∧ vT ≠ v ∧ vT ∈ ops۰trace v rest)) as [(-> & Hne & Hin) | Hnot]; last first.
  { apply Hno_help. intros 𝑣' [= <-] H𝑣'.
    destruct (decide (vT = v)); first done.
    exfalso. apply Hnot. split_and!; done.
  }
  apply list_elem_of_lookup in Hin as (k & Hk).
  set help := take (S k) rest.
  pose proof Htarget as (_ & Htarget')%future۰targetｰSome.
  destruct (helpableｰdecide waiters past helped help) as [Hhelpable | (k' & op' & Hop' & Hbad)].
  - exists help, Good. split_and!; [done | done |].
    assert (ops۰apply help v = vT) as Hhelp_v.
    { apply ops۰traceｰlookup. done. }
    assert (helped ++ help `prefix_of` X) as Hhelp.
    { rewrite /help Hrest. apply prefix_take. }
    apply (inv۰pureｰclick' _ _ Hinv).
    + eapply helpableｰdom. done.
    + trans X; done.
    + rewrite Hhelp_v.
      rewrite /inv۰state decide_False //.
      split; first lia. split.
      * intros _.
        exists (future۰pre (S g) prophs), vT, (S g). split_and!; done.
      * intros 𝑣0. rewrite Htarget. intros [= ->] _. done.
  - exists [], (Doomed op'.(operation۰id) (S g)). split_and!; [done | simpl; lia |].
    apply (inv۰pureｰclick' _ _ Hinv); [set_solver | rewrite right_id // |].
    rewrite right_id /inv۰state decide_False //=.
    split; first lia.
    split; first lia. split; first lia.
    pose proof Hop' as Hk'%lookup_lt_Some.
    rewrite /help length_take in Hk'.
    assert (X !! (length helped + k') = Some op') as HX_lookup.
    { rewrite /help lookup_take_lt in Hop'; first lia.
      rewrite /rest lookup_drop in Hop'. done.
    }
    destruct op' as [id' w'].
    apply prophecies۰opsｰlookup in HX_lookup as (q & Hq & Hops_q).
    exists q, w'. split_and!.
    + trans (future۰pre (S g) prophs); last apply future۰preｰprefix. done.
    + intros 𝑣' g' H.
      apply (future۰preｰforwards (S g) prophs 𝑣').
      destruct Hq as (q' & Hq).
      rewrite Hq -assoc. apply elem_of_app. by left.
    + intros waiter Hlookup.
      destruct Hbad as [Hbad | [Hbad | Hbad]].
      * right. right. right. apply (Hbad waiter Hlookup).
      * right. left. done.
      * right. right. left.
        rewrite Hops_q -Hrest.
        rewrite /help take_take Nat.min_l in Hbad; first lia.
        done.
Qed.

(* The value returned to the helped operation [id]. *)
Fixpoint helped۰result 𝑣 helped id : val :=
  match helped with
  | [] =>
      𝑣
  | op :: helped =>
      if decide (op.(operation۰id) = id) then
        opkind۰result op.(operation۰kind) 𝑣
      else
        helped۰result (opkind۰apply op.(operation۰kind) 𝑣) helped id
  end.

Lemma helped۰resultｰapp_not_in 𝑣 helped help id :
  id ∉ operations۰ids helped →
  helped۰result 𝑣 (helped ++ help) id = helped۰result (ops۰apply helped 𝑣) help id.
Proof.
  move: 𝑣. induction helped as [| op helped IH] => 𝑣 /= Hid; first done.
  rewrite decide_False; first set_solver.
  rewrite IH //. set_solver.
Qed.
Lemma helped۰resultｰapp_in 𝑣 helped help id :
  id ∈ operations۰ids helped →
  helped۰result 𝑣 (helped ++ help) id = helped۰result 𝑣 helped id.
Proof.
  move: 𝑣. induction helped as [| op helped IH] => 𝑣 /= Hid.
  - set_solver.
  - case_decide; first done.
    apply IH. set_solver.
Qed.

Lemma inv۰pureｰfresh {𝑣 g v vₛ snaps snap hist waiters helped past prophs mode} id :
  inv۰pure 𝑣 g v vₛ snaps snap hist waiters helped past prophs mode →
  waiters !! id = None →
    id ∉ operations۰ids (prophecies۰ops past) ∧
    id ∉ operations۰ids helped.
Proof.
  intros Hinv Hlookup.
  split.
  all: intros (op & -> & Hop)%list_elem_of_fmap.
  - apply (inv۰pure۰past_dom _ _ _ _ _ _ _ _ _ _ _ _ Hinv), elem_of_dom in Hop as (? & ?). congruence.
  - apply (inv۰pure۰helped_dom _ _ _ _ _ _ _ _ _ _ _ _ Hinv), elem_of_dom in Hop as (? & ?). congruence.
Qed.
