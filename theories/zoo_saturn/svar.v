Require Import iris.base_logic.lib.ghost_map.

Require Import zoo.prelude.
Require Import zoo.iris.base_logic.lib.auth_nat_max.
Require Import zoo.iris.base_logic.lib.mono_list.
Require Import zoo.iris.base_logic.lib.saved_pred.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Import zoo.program_logic.prophet_wise.
Require Export zoo_saturn.svar__code.
Require Import zoo_saturn.svar__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type g gₛ : nat.
Implicit Type v vₛ 𝑣 𝑣ₛ w : val.
Implicit Type id : identifier.
Implicit Type ι : namespace.

(* ------------------------------------------------------------------------ *)
(* Prophecies. *)

Variant prophecy :=
  | ProphecyForward v g
  | ProphecyOp id (o : option val).
Implicit Type proph : prophecy.
Implicit Type prophs past q : list prophecy.

#[local] Definition prophet :=
  {|prophet_typed۰type :=
      prophecy
  ; prophet_typed۰of_val v w :=
      match w with
      | ValBlock _ Tag2 [ValId id] =>
          Some $ Some $ ProphecyOp id None
      | _ =>
          match v, w with
          | ValBool false, ValBlock _ Tag0 _ =>
              Some None
          | ValBool true, ValBlock _ Tag0 [v; ValInt g] =>
              Some $ Some $ ProphecyForward v ₊g
          | ()%V, ValBlock _ Tag1 [ValId id; v] =>
              Some $ Some $ ProphecyOp id (Some v)
          | _, _ =>
              None
          end
      end
  |}.

Record operation := Operation
  { operation۰id : identifier
  ; operation۰val : option val
  }.
Add Printing Constructor operation.
Implicit Type op : operation.
Implicit Type ops helped help : list operation.

#[local] Definition prophecy۰operation proph :=
  match proph with
  | ProphecyForward _ _ =>
      None
  | ProphecyOp id v =>
      Some (Operation id v)
  end.
#[local] Definition prophecies۰ops prophs :=
  omap prophecy۰operation prophs.

#[local] Definition prophecy۰forward proph :=
  match proph with
  | ProphecyForward v g =>
      Some (v, g)
  | ProphecyOp _ _ =>
      None
  end.
#[local] Definition prophecies۰forwards prophs :=
  omap prophecy۰forward prophs.

#[local] Definition operations۰ids ops :=
  operation۰id <$> ops.

(* The prophecies preceding the first forward whose generation is at least [g]. *)
#[local] Fixpoint future۰pre g prophs :=
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
#[local] Fixpoint future۰target g prophs :=
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

#[local] Lemma prophecies۰opsｰapp prophs1 prophs2 :
  prophecies۰ops (prophs1 ++ prophs2) = prophecies۰ops prophs1 ++ prophecies۰ops prophs2.
Proof.
  apply omap_app.
Qed.
#[local] Lemma prophecies۰forwardsｰapp prophs1 prophs2 :
  prophecies۰forwards (prophs1 ++ prophs2) = prophecies۰forwards prophs1 ++ prophecies۰forwards prophs2.
Proof.
  apply omap_app.
Qed.
#[local] Lemma prophecies۰opsｰprefix prophs1 prophs2 :
  prophs1 `prefix_of` prophs2 →
  prophecies۰ops prophs1 `prefix_of` prophecies۰ops prophs2.
Proof.
  intros (prophs & ->).
  rewrite prophecies۰opsｰapp.
  apply prefix_app_r. done.
Qed.

#[local] Lemma future۰preｰprefix g prophs :
  future۰pre g prophs `prefix_of` prophs.
Proof.
  induction prophs as [| [v g' | id v] prophs IH] => /=.
  - done.
  - case_decide.
    + apply prefix_nil.
    + apply prefix_cons. done.
  - apply prefix_cons. done.
Qed.
#[local] Lemma future۰preｰforwards g prophs v g' :
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
#[local] Lemma future۰targetｰSome g prophs v g' :
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
#[local] Lemma future۰targetｰNone g prophs :
  future۰target g prophs = None →
  future۰pre g prophs = prophs.
Proof.
  induction prophs as [| [v'' g'' | id v''] prophs IH] => /=.
  - done.
  - case_decide; first done.
    intros ->%IH. done.
  - intros ->%IH. done.
Qed.
#[local] Lemma future۰preｰmono g prophs :
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
#[local] Lemma future۰preｰno_forwards g prophs1 v g' prophs2 :
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
#[local] Lemma future۰preｰlength_forward g prophs q v g' :
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
  { waiter۰val : option val
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

#[local] Instance snapｰinhabited : Inhabited snap :=
  populate (Snap inhabitant inhabitant 0 0).
Implicit Type snaps : list snap.

#[local] Definition snap۰to_val snap :=
  (‘Snapshot@snap.(snap۰bid)[ snap.(snap۰val), #snap.(snap۰gen) ])%V.

#[local] Lemma snap۰to_valｰsimilar snap1 snap2 :
  snap۰to_val snap1 ≈ snap۰to_val snap2 →
  snap1.(snap۰gen) = snap2.(snap۰gen).
Proof.
  intros (_ & _ & [= _ ?%(inj _)])%valｰsimilarｰblockｰgenerative; [lia | naive].
Qed.
#[local] Lemma snap۰to_valｰnonsimilar snap :
  ¬ snap۰to_val snap ≉ snap۰to_val snap.
Proof.
  intros [| []]%valｰnonsimilarｰblockｰgenerative; done.
Qed.

Variant mode :=
  | Good
  | Doomed (b : identifier) (g_d : nat).
Implicit Type mode : mode.

#[local] Instance modeｰinhabited : Inhabited mode :=
  populate Good.

#[local] Definition mode۰doomed mode :=
  match mode with
  | Good =>
      0
  | Doomed _ _ =>
      1
  end.

(* ------------------------------------------------------------------------ *)
(* Pure invariant. *)

#[local] Definition future۰good g v vₛ helped prophs : Prop :=
  ( helped ≠ [] →
      ∃ q 𝑣 g',
      q ++ [ProphecyForward 𝑣 g'] `prefix_of` prophs ∧
      length q ≤ length (future۰pre g prophs) ∧
      helped `prefix_of` prophecies۰ops q ∧
      operation۰val <$> last helped = Some (Some 𝑣)
  ) ∧ (
    ∀ 𝑣,
    future۰target g prophs = Some (𝑣, g) →
    𝑣 ∈ v :: omap operation۰val (drop (length helped) (prophecies۰ops (future۰pre g prophs))) →
    vₛ = 𝑣
  ).

#[local] Definition future۰doomed g gₛ waiters past prophs (b : identifier) g_d : Prop :=
  g_d ≤ g ∧
  gₛ < g_d ∧
    ∃ q (w : option val),
    q ++ [ProphecyOp b w] `prefix_of` prophs ∧
    (∀ 𝑣 g', ProphecyForward 𝑣 g' ∈ q → g' < g_d) ∧
    ∀ waiter,
    waiters !! b = Some waiter →
      g_d ≤ waiter.(waiter۰gen) ∨
      b ∈ operations۰ids (prophecies۰ops past) ∨
      b ∈ operations۰ids (prophecies۰ops q) ∨
      waiter.(waiter۰val) ≠ w.

#[local] Definition inv۰state g v vₛ snap waiters helped past prophs mode : Prop :=
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
      v = default 𝑣 (last (omap operation۰val helped))
  ; inv۰pure۰helped :
      helped `prefix_of` prophecies۰ops prophs
  ; inv۰pure۰state :
      inv۰state g v vₛ snap waiters helped past prophs mode
  }.

#[local] Fixpoint helpable waiters past helped help : Prop :=
  match help with
  | [] =>
      True
  | op :: help =>
      ( ∃ waiter,
        waiters !! op.(operation۰id) = Some waiter ∧
        waiter.(waiter۰val) = op.(operation۰val)
      ) ∧
      op.(operation۰id) ∉ operations۰ids (prophecies۰ops past) ∧
      op.(operation۰id) ∉ operations۰ids helped ∧
      helpable waiters past (helped ++ [op]) help
  end.

(* ------------------------------------------------------------------------ *)
(* Pure lemmas. *)

#[local] Lemma prophecies۰opsｰlookup prophs n id (v : option val) :
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
#[local] Lemma prophecies۰forwardsｰhead prophs v g :
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
#[local] Lemma prefixｰtotal {A} (l1 l2 l : list A) :
  l1 `prefix_of` l →
  l2 `prefix_of` l →
  length l1 ≤ length l2 →
  l1 `prefix_of` l2.
Proof.
  intros Hl1 Hl2 Hlen.
  destruct (prefix_weak_total l1 l2 l) as [| Hl21]; [done.. |].
  apply prefix_length_eq in Hl21 as ->; done.
Qed.

#[local] Lemma last_omap {A B} (f : A → option B) l y x :
  last l = Some y →
  f y = Some x →
  last (omap f l) = Some x.
Proof.
  intros Hl Hf.
  destruct l as [| a l _] using rev_ind; first done.
  rewrite last_snoc in Hl. injection Hl as ->.
  rewrite omap_app /= Hf last_snoc //.
Qed.

#[local] Lemma last_omap_cons {A B} (f : A → option B) x l :
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

#[local] Lemma snapsｰlookup_last snaps snap :
  last snaps = Some snap →
  snaps !! pred (length snaps) = Some snap.
Proof.
  rewrite last_lookup //.
Qed.
#[local] Lemma inv۰pureｰsnaps_lt {𝑣 g v vₛ snaps snap hist waiters helped past prophs mode} i j snap1 snap2 :
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
#[local] Lemma inv۰pureｰsnaps_gen_inj {𝑣 g v vₛ snaps snap hist waiters helped past prophs mode} i j snap1 snap2 :
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
#[local] Lemma inv۰pureｰsnaps_le_last {𝑣 g v vₛ snaps snap hist waiters helped past prophs mode} i snap' :
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
#[local] Lemma inv۰pureｰsnap_gen {𝑣 g v vₛ snaps snap hist waiters helped past prophs mode} :
  inv۰pure 𝑣 g v vₛ snaps snap hist waiters helped past prophs mode →
  snap.(snap۰gen) ≤ g.
Proof.
  intros Hinv.
  pose proof (inv۰pure۰snaps_last _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as Hlast%snapsｰlookup_last.
  opose proof* inv۰pure۰snaps_inst as (? & ?); [done.. | lia].
Qed.
#[local] Lemma inv۰pureｰstable {𝑣 g v vₛ snaps snap hist waiters helped past prophs mode} :
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
#[local] Lemma inv۰pureｰreader {𝑣 g v vₛ snaps snap hist waiters helped past prophs} :
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
  pose proof (inv۰pure۰model _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as ->.
  destruct (decide (helped = [])) as [-> | (q & 𝑣' & g' & Hq & Hq_length & Hhelped_q & Hlast)%Hhelped].
  - apply list_elem_of_here.
  - rewrite Hpre in Hq_length.
    opose proof* (future۰preｰlength_forward g) as Hq'; [done | rewrite Hpre // | rewrite Hpre // |].
    rewrite Hpre in Hq'. subst q.
    apply prefix_app_inv in Hq as Hq. apply prefix_cons_inv_1 in Hq as [= -> ->].
    apply fmap_Some in Hlast as (op & Hop & Hval).
    erewrite last_omap; [| done | symmetry; done].
    apply list_elem_of_here.
Qed.

#[local] Lemma inv۰pureｰregister {𝑣 g v vₛ snaps snap hist waiters helped past prophs mode} id waiter :
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

#[local] Lemma inv۰pureｰwrite {𝑣 g v vₛ snaps snap hist waiters helped past prophs mode} id (w : option val) waiter :
  inv۰pure 𝑣 g v vₛ snaps snap hist waiters helped past (ProphecyOp id w :: prophs) mode →
  waiters !! id = Some waiter →
  waiter.(waiter۰val) = w →
  id ∉ operations۰ids (prophecies۰ops past) →
  waiter.(waiter۰gen) ≤ snap.(snap۰gen) →
    (helped = [] ∨ head helped = Some (Operation id w)) ∧
    inv۰pure (default 𝑣 w) g (if helped is [] then default v w else v) vₛ snaps snap hist waiters (tail helped) (past ++ [ProphecyOp id w]) prophs mode.
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
  - destruct Hhelped as [-> | (helped' & ->)].
    { rewrite inv۰pure۰model0 //. }
    rewrite inv۰pure۰model0 last_omap_cons /=.
    destruct (last (omap operation۰val helped')); done.
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
        -- destruct w as [x |]; simpl in *; set_solver.
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

#[local] Lemma inv۰pureｰforward {𝑣 g v vₛ snaps snap hist waiters helped past prophs mode} 𝑣' g' bid :
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
        -- intros (q & 𝑣'' & g'' & Hq & Hq_length & Hhelped_q & Hlast')%Hhelped.
           destruct q as [| proph q].
           { apply prefix_nil_inv in Hhelped_q as ->. by destruct Hhelped. }
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

#[local] Lemma helpableｰdom waiters past helped help :
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
#[local] Lemma helpableｰdecide waiters past helped help :
  helpable waiters past helped help ∨
    ∃ k op,
    help !! k = Some op ∧
    ( (∀ waiter, waiters !! op.(operation۰id) = Some waiter → waiter.(waiter۰val) ≠ op.(operation۰val))
    ∨ op.(operation۰id) ∈ operations۰ids (prophecies۰ops past)
    ∨ op.(operation۰id) ∈ operations۰ids (helped ++ take k help)
    ).
Proof.
  move: helped. induction help as [| op help IH] => helped /=.
  - auto.
  - assert (
      (∃ waiter, waiters !! op.(operation۰id) = Some waiter ∧ waiter.(waiter۰val) = op.(operation۰val)) ∨
      (∀ waiter, waiters !! op.(operation۰id) = Some waiter → waiter.(waiter۰val) ≠ op.(operation۰val))
    ) as [Hwaiter | Hwaiter].
    { destruct (waiters !! op.(operation۰id)) as [waiter |].
      - destruct (decide (waiter.(waiter۰val) = op.(operation۰val))); naive.
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

#[local] Lemma inv۰pureｰclick' {𝑣 g v vₛ snaps snap hist waiters helped past prophs mode} help mode' :
  inv۰pure 𝑣 g v vₛ snaps snap hist waiters helped past prophs mode →
  let v' := default v (last (omap operation۰val help)) in
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
  - rewrite /v' omap_app last_app inv۰pure۰model0.
    destruct (last (omap operation۰val help)); done.
Qed.

#[local] Lemma inv۰pureｰclick {𝑣 g v vₛ snaps snap hist waiters helped past prophs mode} :
  inv۰pure 𝑣 g v vₛ snaps snap hist waiters helped past prophs mode →
    ∃ help mode',
    helpable waiters past helped help ∧
    mode۰doomed mode ≤ mode۰doomed mode' ∧
    let v' := default v (last (omap operation۰val help)) in
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
      operation۰val <$> last helped = Some (Some 𝑣')
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
    (∀ 𝑣', future۰target (S g) prophs = Some (𝑣', S g) → 𝑣' ∈ omap operation۰val rest → 𝑣' = v) →
      ∃ help mode',
      helpable waiters past helped help ∧
      mode۰doomed Good ≤ mode۰doomed mode' ∧
      let v' := default v (last (omap operation۰val help)) in
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
  destruct (decide (gT = S g ∧ vT ≠ v ∧ vT ∈ omap operation۰val rest)) as [(-> & Hne & Hin) | Hnot]; last first.
  { apply Hno_help. intros 𝑣' [= <-] H𝑣'.
    destruct (decide (vT = v)); first done.
    exfalso. apply Hnot. split_and!; done.
  }
  apply list_elem_of_omap in Hin as (op & Hop & Hval).
  apply list_elem_of_lookup in Hop as (k & Hk).
  set help := take (S k) rest.
  pose proof Htarget as (_ & Htarget')%future۰targetｰSome.
  destruct (helpableｰdecide waiters past helped help) as [Hhelpable | (k' & op' & Hop' & Hbad)].
  - exists help, Good. split_and!; [done | done |].
    assert (last help = Some op) as Hlast_help.
    { rewrite /help last_lookup length_take.
      assert (k < length rest) by (eapply lookup_lt_Some; done).
      rewrite Nat.min_l; first lia.
      rewrite lookup_take_lt; first lia.
      rewrite /= Hk //.
    }
    assert (helped ++ help `prefix_of` X) as Hhelp.
    { rewrite /help Hrest. apply prefix_take. }
    apply (inv۰pureｰclick' _ _ Hinv).
    + eapply helpableｰdom. done.
    + trans X; done.
    + rewrite (last_omap _ _ _ _ Hlast_help Hval) /=.
      rewrite /inv۰state decide_False //.
      split; first lia. split.
      * intros _.
        exists (future۰pre (S g) prophs), vT, (S g). split_and!; try done.
        rewrite last_app Hlast_help /= Hval //.
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
#[local] Fixpoint helped۰result 𝑣 helped id : val :=
  match helped with
  | [] =>
      𝑣
  | op :: helped =>
      if decide (op.(operation۰id) = id) then
        𝑣
      else
        helped۰result (default 𝑣 op.(operation۰val)) helped id
  end.

#[local] Lemma helped۰resultｰapp_not_in 𝑣 helped help id :
  id ∉ operations۰ids helped →
  helped۰result 𝑣 (helped ++ help) id = helped۰result (default 𝑣 (last (omap operation۰val helped))) help id.
Proof.
  move: 𝑣. induction helped as [| op helped IH] => 𝑣 /= Hid; first done.
  rewrite decide_False; first set_solver.
  rewrite IH; first set_solver.
  rewrite last_omap_cons.
  destruct (last (omap operation۰val helped)); done.
Qed.
#[local] Lemma helped۰resultｰapp_in 𝑣 helped help id :
  id ∈ operations۰ids helped →
  helped۰result 𝑣 (helped ++ help) id = helped۰result 𝑣 helped id.
Proof.
  move: 𝑣. induction helped as [| op helped IH] => 𝑣 /= Hid.
  - set_solver.
  - case_decide; first done.
    apply IH. set_solver.
Qed.

(* ------------------------------------------------------------------------ *)
(* Ghost state. *)

Zoo name :=
  { self : location
  ; prophet : prophet_wise۰name
  ; model : gname
  ; scanner : gname
  ; generation : gname
  ; snapshot : gname
  ; snaps : gname
  ; hist : gname
  ; doom : gname
  ; waiters : gname
  }.

Zoo global :=
  { prophet : prophet_wise prophet
  ; model : twins val_O
  ; scanner : twins (leibnizO (val * nat))
  ; generation : auth_nat_max
  ; snapshot : auth_nat_max
  ; snaps : mono_list snap
  ; hist : mono_list (val * nat)
  ; doom : auth_nat_max
  ; waiters : ghost_map identifier waiter : iris
  ; waiter۰post : saved_pred val
  }.

Section svar_G.
  Context `{svar_G : SvarG Σ}.

  Implicit Type P : iProp Σ.
  Implicit Type Φ : val → iProp Σ.

  #[local] Definition prophet۰model γ past prophs :=
    prophet_wise۰model prophet γ.(svar۰name۰prophet) past prophs.
  #[local] Definition prophet۰snapshot γ past prophs :=
    prophet_wise۰snapshot prophet γ.(svar۰name۰prophet) past prophs.

  #[local] Definition model₁' γ_model v :=
    twins۰twin₁ (twins۰G := svar۰G۰model۰G) γ_model Own v.
  #[local] Definition model₁ γ :=
    model₁' γ.(svar۰name۰model).
  #[local] Definition model₂' γ_model v :=
    twins۰twin₂ (twins۰G := svar۰G۰model۰G) γ_model v.
  #[local] Definition model₂ γ :=
    model₂' γ.(svar۰name۰model).

  #[local] Definition scanner₁' γ_scanner dq vₛ g :=
    twins۰twin₁ γ_scanner dq (vₛ, g).
  #[local] Definition scanner₁ γ :=
    scanner₁' γ.(svar۰name۰scanner).
  #[local] Definition scanner₂' γ_scanner vₛ g :=
    twins۰twin₂ γ_scanner (vₛ, g).
  #[local] Definition scanner₂ γ :=
    scanner₂' γ.(svar۰name۰scanner).

  #[local] Definition generation۰auth' γ_generation g :=
    auth_nat_max۰auth γ_generation Own g.
  #[local] Definition generation۰auth γ :=
    generation۰auth' γ.(svar۰name۰generation).
  #[local] Definition generation۰lb γ g :=
    auth_nat_max۰lb γ.(svar۰name۰generation) g.

  #[local] Definition snapshot۰auth' γ_snapshot gₛ :=
    auth_nat_max۰auth γ_snapshot Own gₛ.
  #[local] Definition snapshot۰auth γ :=
    snapshot۰auth' γ.(svar۰name۰snapshot).
  #[local] Definition snapshot۰lb γ gₛ :=
    auth_nat_max۰lb γ.(svar۰name۰snapshot) gₛ.

  #[local] Definition snaps۰auth' γ_snaps snaps :=
    mono_list۰auth γ_snaps (DfracOwn 1) snaps.
  #[local] Definition snaps۰auth γ :=
    snaps۰auth' γ.(svar۰name۰snaps).
  #[local] Definition snaps۰lb γ snaps :=
    mono_list۰lb γ.(svar۰name۰snaps) snaps.

  #[local] Definition hist۰auth' γ_hist (hist : list (val * nat)) :=
    mono_list۰auth γ_hist (DfracOwn 1) hist.
  #[local] Definition hist۰auth γ :=
    hist۰auth' γ.(svar۰name۰hist).
  #[local] Definition hist۰at γ h (vh : val) (idx : nat) :=
    mono_list۰at γ.(svar۰name۰hist) h (vh, idx).

  #[local] Definition doom۰auth' γ_doom n :=
    auth_nat_max۰auth γ_doom Own n.
  #[local] Definition doom۰auth γ :=
    doom۰auth' γ.(svar۰name۰doom).
  #[local] Definition doom۰lb γ :=
    auth_nat_max۰lb γ.(svar۰name۰doom) 1.

  #[local] Definition waiters۰auth' γ_waiters waiters : iProp Σ :=
    ghost_map_auth γ_waiters (DfracOwn 1) waiters ∗
    [∗ set] id ∈ dom waiters, identifier۰model id.
  #[local] Definition waiters۰auth γ :=
    waiters۰auth' γ.(svar۰name۰waiters).
  #[local] Definition waiters۰elem γ id waiter :=
    ghost_map_elem γ.(svar۰name۰waiters) id (DfracOwn 1) waiter.

  #[local] Definition waiter۰au γ ι waiter Ψ : iProp Σ :=
    AU <{
      ∃∃ v,
      model₁ γ v
    }> @ ⊤ ∖ ↑ι, ∅ <{
      model₁ γ (default v waiter.(waiter۰val))
    , COMM
      Ψ v
    }>.

  #[local] Definition waiters۰statuses γ ι waiters 𝑣 helped past : iProp Σ :=
    [∗ map] id ↦ waiter ∈ waiters,
      if bool_decide (id ∈ operations۰ids (prophecies۰ops past)) then
        waiters۰elem γ id waiter
      else
        ∃ Ψ,
        saved_pred waiter.(waiter۰post) Ψ ∗
        if bool_decide (id ∈ operations۰ids helped) then
          Ψ (helped۰result 𝑣 helped id)
        else
          waiter۰au γ ι waiter Ψ.

  #[local] Definition inv۰inner γ ι : iProp Σ :=
    ∃ 𝑣 g v vₛ snaps snap hist waiters helped past prophs mode,
    γ.(svar۰name۰self).[value] ↦ 𝑣 ∗
    γ.(svar۰name۰self).[gen] ↦ #g ∗
    γ.(svar۰name۰self).[snapshot] ↦ snap۰to_val snap ∗
    model₂ γ v ∗
    scanner₂ γ vₛ g ∗
    generation۰auth γ g ∗
    snapshot۰auth γ snap.(snap۰gen) ∗
    snaps۰auth γ snaps ∗
    hist۰auth γ hist ∗
    doom۰auth γ (mode۰doomed mode) ∗
    waiters۰auth γ waiters ∗
    prophet۰model γ past prophs ∗
    waiters۰statuses γ ι waiters 𝑣 helped past ∗
    ⌜inv۰pure 𝑣 g v vₛ snaps snap hist waiters helped past prophs mode⌝.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %𝑣{}
      & %g{}
      & %v{}
      & %vₛ{}
      & %snaps{}
      & %snap{}
      & %hist{}
      & %waiters{}
      & %helped{}
      & %past{}
      & %prophs{}
      & %mode{}
      & >Ht_value
      & >Ht_gen
      & >Ht_snapshot
      & >Hmodel₂
      & >Hscanner₂
      & >Hgeneration_auth
      & >Hsnapshot_auth
      & >Hsnaps_auth
      & >Hhist_auth
      & >Hdoom_auth
      & >Hwaiters_auth
      & >Hprophet_model
      & Hwaiters
      & >%Hinv{}
      )
    ".
  #[local] Definition inv' γ ι :=
    inv ι (inv۰inner γ ι).
  Please Definition svar۰inv γ ι : iProp Σ :=
    γ.(svar۰name۰self).[proph] ↦□ γ.(svar۰name۰prophet) ∗
    inv' γ ι.
  #[local] Instance : CustomIpat "inv" :=
    " ( #Ht_proph
      & #Hinv
      )
    ".

  Please Definition svar۰model :=
    model₁.

  Please Definition svar۰scanner γ dq vₛ : iProp Σ :=
    ∃ g,
    scanner₁ γ dq vₛ g.
  #[local] Instance : CustomIpat "scanner" :=
    " ( %g{}
      & Hscanner₁{_{}}
      )
    ".

  Zoo derive Timeless for svar۰model.
  Zoo derive Timeless for svar۰scanner.

  Zoo derive Persistent for svar۰inv.
  Zoo derive Persistent for svar۰scanner:discarded.

  #[global] Instance svar۰scannerｰfractional γ vₛ :
    Fractional (λ (q : Qp), svar۰scanner γ (DfracOwn q) vₛ).
  Proof.
    intros q1 q2.
    iSplit.
    - iIntros "(:scanner)".
      iDestruct "Hscanner₁" as "($ & $)".
    - iIntros "((:scanner =1) & (:scanner =2))".
      iDestruct (twins۰twin₁ｰcombineｰL with "Hscanner₁_1 Hscanner₁_2") as "(% & $)".
  Qed.
  #[global] Instance svar۰scannerｰas_fractional γ (q : Qp) vₛ :
    AsFractional (svar۰scanner γ (DfracOwn q) vₛ) (λ (q : Qp), svar۰scanner γ (DfracOwn q) vₛ) q.
  Proof.
    split; [done | apply _].
  Qed.

  #[local] Lemma modelｰalloc v :
    ⊢ |==>
      ∃ γ_model,
      model₁' γ_model v ∗
      model₂' γ_model v.
  Proof.
    apply twinsｰalloc'.
  Qed.
  #[local] Lemma modelｰagree γ v1 v2 :
    model₁ γ v1 -∗
    model₂ γ v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply: twinsｰagreeｰL.
  Qed.
  #[local] Lemma modelｰupdate {γ v1 v2} v :
    model₁ γ v1 -∗
    model₂ γ v2 ==∗
      model₁ γ v ∗
      model₂ γ v.
  Proof.
    apply twinsｰupdate.
  Qed.

  #[local] Lemma scannerｰalloc vₛ :
    ⊢ |==>
      ∃ γ_scanner,
      scanner₁' γ_scanner Own vₛ 0 ∗
      scanner₂' γ_scanner vₛ 0.
  Proof.
    apply twinsｰalloc'.
  Qed.
  #[local] Lemma scannerｰagree γ dq vₛ1 g1 vₛ2 g2 :
    scanner₁ γ dq vₛ1 g1 -∗
    scanner₂ γ vₛ2 g2 -∗
      ⌜vₛ1 = vₛ2⌝ ∗
      ⌜g1 = g2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (twinsｰagreeｰL with "H1 H2") as %[= -> ->] => //.
  Qed.
  #[local] Lemma scannerｰupdate {γ vₛ1 g1 vₛ2 g2} vₛ g :
    scanner₁ γ Own vₛ1 g1 -∗
    scanner₂ γ vₛ2 g2 ==∗
      scanner₁ γ Own vₛ g ∗
      scanner₂ γ vₛ g.
  Proof.
    apply twinsｰupdate.
  Qed.

  #[local] Lemma generationｰalloc :
    ⊢ |==>
      ∃ γ_generation,
      generation۰auth' γ_generation 0.
  Proof.
    apply auth_nat_maxｰalloc.
  Qed.
  #[local] Lemma generation۰lbｰget γ g :
    generation۰auth γ g ⊢
    generation۰lb γ g.
  Proof.
    apply auth_nat_max۰lbｰget.
  Qed.
  #[local] Lemma generation۰lbｰvalid γ g1 g2 :
    generation۰auth γ g1 -∗
    generation۰lb γ g2 -∗
    ⌜g2 ≤ g1⌝.
  Proof.
    apply auth_nat_max۰lbｰvalid.
  Qed.
  #[local] Lemma generationｰupdate γ g :
    generation۰auth γ g ⊢ |==>
    generation۰auth γ (S g).
  Proof.
    apply auth_nat_maxｰupdate. lia.
  Qed.

  #[local] Lemma snapshotｰalloc :
    ⊢ |==>
      ∃ γ_snapshot,
      snapshot۰auth' γ_snapshot 0.
  Proof.
    apply auth_nat_maxｰalloc.
  Qed.
  #[local] Lemma snapshot۰lbｰget γ gₛ :
    snapshot۰auth γ gₛ ⊢
    snapshot۰lb γ gₛ.
  Proof.
    apply auth_nat_max۰lbｰget.
  Qed.
  #[local] Lemma snapshot۰lbｰvalid γ gₛ1 gₛ2 :
    snapshot۰auth γ gₛ1 -∗
    snapshot۰lb γ gₛ2 -∗
    ⌜gₛ2 ≤ gₛ1⌝.
  Proof.
    apply auth_nat_max۰lbｰvalid.
  Qed.
  #[local] Lemma snapshotｰupdate {γ gₛ} gₛ' :
    gₛ ≤ gₛ' →
    snapshot۰auth γ gₛ ⊢ |==>
    snapshot۰auth γ gₛ'.
  Proof.
    apply auth_nat_maxｰupdate.
  Qed.

  #[local] Lemma snapsｰalloc snaps :
    ⊢ |==>
      ∃ γ_snaps,
      snaps۰auth' γ_snaps snaps.
  Proof.
    apply mono_listｰalloc.
  Qed.
  #[local] Lemma snaps۰lbｰget γ snaps :
    snaps۰auth γ snaps ⊢
    snaps۰lb γ snaps.
  Proof.
    apply mono_list۰lbｰget.
  Qed.
  #[local] Lemma snaps۰lbｰvalid γ snaps1 snaps2 :
    snaps۰auth γ snaps1 -∗
    snaps۰lb γ snaps2 -∗
    ⌜snaps2 `prefix_of` snaps1⌝.
  Proof.
    apply mono_list۰lbｰvalid.
  Qed.
  #[local] Lemma snapsｰupdate {γ snaps} snap :
    snaps۰auth γ snaps ⊢ |==>
    snaps۰auth γ (snaps ++ [snap]).
  Proof.
    apply mono_listｰupdateｰsnoc.
  Qed.

  #[local] Lemma histｰalloc hist :
    ⊢ |==>
      ∃ γ_hist,
      hist۰auth' γ_hist hist.
  Proof.
    apply mono_listｰalloc.
  Qed.
  #[local] Lemma hist۰atｰget {γ hist} h vh idx :
    hist !! h = Some (vh, idx) →
    hist۰auth γ hist ⊢
    hist۰at γ h vh idx.
  Proof.
    apply mono_list۰atｰget.
  Qed.
  #[local] Lemma hist۰atｰvalid γ hist h vh idx :
    hist۰auth γ hist -∗
    hist۰at γ h vh idx -∗
    ⌜hist !! h = Some (vh, idx)⌝.
  Proof.
    apply mono_list۰atｰvalid.
  Qed.
  #[local] Lemma histｰupdate {γ hist} vh idx :
    hist۰auth γ hist ⊢ |==>
    hist۰auth γ (hist ++ [(vh, idx)]).
  Proof.
    apply mono_listｰupdateｰsnoc.
  Qed.

  #[local] Lemma doomｰalloc :
    ⊢ |==>
      ∃ γ_doom,
      doom۰auth' γ_doom 0.
  Proof.
    apply auth_nat_maxｰalloc.
  Qed.
  #[local] Lemma doom۰lbｰget γ mode :
    mode ≠ Good →
    doom۰auth γ (mode۰doomed mode) ⊢
    doom۰lb γ.
  Proof.
    destruct mode; first done.
    intros _. apply auth_nat_max۰lbｰget.
  Qed.
  #[local] Lemma doom۰lbｰvalid γ mode :
    doom۰auth γ (mode۰doomed mode) -∗
    doom۰lb γ -∗
    ⌜mode ≠ Good⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (auth_nat_max۰lbｰvalid with "Hauth Hlb") as %?.
    iPureIntro. intros ->. simpl in *. lia.
  Qed.
  #[local] Lemma doomｰupdate {γ mode} mode' :
    mode۰doomed mode ≤ mode۰doomed mode' →
    doom۰auth γ (mode۰doomed mode) ⊢ |==>
    doom۰auth γ (mode۰doomed mode').
  Proof.
    apply auth_nat_maxｰupdate.
  Qed.

  #[local] Lemma waitersｰalloc :
    ⊢ |==>
      ∃ γ_waiters,
      waiters۰auth' γ_waiters ∅.
  Proof.
    iMod ghost_map_alloc_empty as "(%γ_waiters & $)".
    iApply big_sepS_empty => //.
  Qed.
  #[local] Lemma waiters۰elemｰexclusive γ id waiter1 waiter2 :
    waiters۰elem γ id waiter1 -∗
    waiters۰elem γ id waiter2 -∗
    False.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %(? & _). done.
  Qed.
  #[local] Lemma waiters۰elemｰvalid γ waiters id waiter :
    waiters۰auth γ waiters -∗
    waiters۰elem γ id waiter -∗
    ⌜waiters !! id = Some waiter⌝.
  Proof.
    iIntros "(Hauth & _) Helem".
    iApply (ghost_map_lookup with "Hauth Helem").
  Qed.
  #[local] Lemma waitersｰinsert {γ waiters} id waiter :
    waiters۰auth γ waiters -∗
    identifier۰model id ==∗
      ⌜waiters !! id = None⌝ ∗
      waiters۰auth γ (<[id := waiter]> waiters) ∗
      waiters۰elem γ id waiter.
  Proof.
    iIntros "(Hauth & Hids) Hid".
    destruct (waiters !! id) eqn:Hlookup.
    { iDestruct (big_sepS_elem_of with "Hids") as "Hid'".
      { apply elem_of_dom. naive. }
      iDestruct (identifier۰modelｰexclusive with "Hid Hid'") as %[].
    }
    iMod (ghost_map_insert with "Hauth") as "($ & $)"; first done.
    iModIntro. iSplitR; first done.
    rewrite dom_insert_L big_sepS_insert; first (apply not_elem_of_dom; done).
    iFrame.
  Qed.

  #[local] Instance waiters۰authｰtimeless γ waiters :
    Timeless (waiters۰auth γ waiters).
  Proof.
    apply _.
  Qed.

  Opaque waiters۰auth'.

  Lemma svar٠makeｰspec ι v :
    {{{
      True
    }}}
      svar٠make v
    {{{
      γ
    , RET #γ.(svar۰name۰self);
      svar۰inv γ ι ∗
      svar۰model γ v ∗
      svar۰scanner γ Own v
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.
    wp۰apply+ (prophet_wiseｰwpｰproph prophet with "[//]") as (pid prophs) "Hprophet_model".
    wp۰block۰generative bid.
    wp۰block t as "Ht_value Ht_gen Ht_snapshot #Ht_proph".

    iMod (modelｰalloc v) as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod (scannerｰalloc v) as "(%γ_scanner & Hscanner₁ & Hscanner₂)".
    iMod generationｰalloc as "(%γ_generation & Hgeneration_auth)".
    iMod snapshotｰalloc as "(%γ_snapshot & Hsnapshot_auth)".
    iMod (snapsｰalloc [Snap bid v 0 0]) as "(%γ_snaps & Hsnaps_auth)".
    iMod (histｰalloc [(v, 0)]) as "(%γ_hist & Hhist_auth)".
    iMod doomｰalloc as "(%γ_doom & Hdoom_auth)".
    iMod waitersｰalloc as "(%γ_waiters & Hwaiters_auth)".

    pose γ :=
      {|svar۰name۰self := t
      ; svar۰name۰prophet := pid
      ; svar۰name۰model := γ_model
      ; svar۰name۰scanner := γ_scanner
      ; svar۰name۰generation := γ_generation
      ; svar۰name۰snapshot := γ_snapshot
      ; svar۰name۰snaps := γ_snaps
      ; svar۰name۰hist := γ_hist
      ; svar۰name۰doom := γ_doom
      ; svar۰name۰waiters := γ_waiters
      |}.

    iApply ("HΦ" $! γ).
    iFrameStep.
    iApply inv_alloc.
    iExists v, 0, v, v, [Snap bid v 0 0], (Snap bid v 0 0), [(v, 0)], ∅, [], [], prophs, Good.
    iFrame. iSplitL. { rewrite /waiters۰statuses big_sepM_empty //. }
    iPureIntro. split.
    all: try done.
    all: try (intros [| []]; simpl; intros; simplify_eq/=; simpl; lia).
    all: try (intros [| []]; simpl; intros; simplify_eq/=; set_solver).
    all: try set_solver.
    all: try apply prefix_nil.
    all: try (exists 0; done).
    all: rewrite /inv۰state decide_True //.
  Qed.


  #[local] Definition reader γ n g 𝑣 : iProp Σ :=
    ( ∃ snaps',
      snaps۰lb γ snaps' ∗
      ⌜n < length snaps'⌝
    ) ∨ (
      generation۰lb γ (S g)
    ) ∨ (
      doom۰lb γ
    ) ∨ (
      ∃ past prophs,
      prophet۰snapshot γ past prophs ∗
      ⌜S (length (prophecies۰forwards past)) = n⌝ ∗
      ( ⌜head (prophecies۰forwards prophs) = Some (𝑣, g)⌝ →
        ∃ idx,
        hist۰at γ g 𝑣 idx
      )
    ).
  #[local] Instance readerｰpersistent γ n g 𝑣 :
    Persistent (reader γ n g 𝑣).
  Proof.
    apply _.
  Qed.

  #[local] Lemma invｰinit γ ι :
    inv' γ ι ={⊤}=∗
      snaps۰lb γ [] ∗
      ∃ vh idx,
      hist۰at γ 0 vh idx.
  Proof.
    iIntros "#Hinv".
    iInv "Hinv" as "(:inv۰inner)".
    iDestruct (snaps۰lbｰget with "Hsnaps_auth") as "#Hsnaps_lb".
    destruct (hist !! 0) as [(vh & idx) |] eqn:Hhist_lookup; last first.
    { apply lookup_ge_None in Hhist_lookup.
      pose proof (inv۰pure۰hist_length _ _ _ _ _ _ _ _ _ _ _ _ Hinv). lia.
    }
    iDestruct (hist۰atｰget with "Hhist_auth") as "#Hhist_at"; first done.
    iSplitR "". { iFrameSteps. }
    iModIntro. iSplitL.
    - iApply (mono_list۰lbｰmono with "Hsnaps_lb"). apply prefix_nil.
    - iSteps.
  Qed.

  #[local] Lemma genｰspec γ ι g0 :
    {{{
      inv' γ ι ∗
      generation۰lb γ g0
    }}}
      (#γ.(svar۰name۰self)).{gen}
    {{{
      g
    , RET #g;
      ⌜g0 ≤ g⌝ ∗
      generation۰lb γ g
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hg0) HΦ".
    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    iDestruct (generation۰lbｰvalid with "Hgeneration_auth Hg0") as %?.
    iDestruct (generation۰lbｰget with "Hgeneration_auth") as "#Hg".
    iSplitR "HΦ". { iFrameSteps. }
    iSteps.
  Qed.

  #[local] Lemma genｰspecｰscanner γ ι dq vₛ g :
    {{{
      inv' γ ι ∗
      scanner₁ γ dq vₛ g
    }}}
      (#γ.(svar۰name۰self)).{gen}
    {{{
      RET #g;
      scanner₁ γ dq vₛ g
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Hscanner₁) HΦ".
    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰load.
    iDestruct (scannerｰagree with "Hscanner₁ Hscanner₂") as %(<- & <-).
    iSplitR "Hscanner₁ HΦ". { iFrameSteps. }
    iSteps.
  Qed.

  #[local] Lemma snapshotｰspec γ ι g0 L h vh idx :
    {{{
      inv' γ ι ∗
      generation۰lb γ g0 ∗
      snaps۰lb γ L ∗
      hist۰at γ h vh idx
    }}}
      (#γ.(svar۰name۰self)).{snapshot}
    {{{
      snaps snap
    , RET snap۰to_val snap;
      snaps۰lb γ snaps ∗
      ⌜L `prefix_of` snaps⌝ ∗
      ⌜last snaps = Some snap⌝ ∗
      ⌜snap.(snap۰gen) ≤ snap.(snap۰inst)⌝ ∗
      generation۰lb γ snap.(snap۰inst) ∗
      snapshot۰lb γ snap.(snap۰gen) ∗
      ⌜idx < pred (length snaps) → h ≤ snap.(snap۰inst)⌝ ∗
      ∃ gc vh' idx',
      hist۰at γ gc vh' idx' ∗
      ⌜g0 ≤ gc⌝ ∗
      ⌜idx' < length snaps⌝
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hg0 & #HL & #Hhist_at) HΦ".
    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    iDestruct (snaps۰lbｰvalid with "Hsnaps_auth HL") as %HL.
    iDestruct (snaps۰lbｰget with "Hsnaps_auth") as "#Hsnaps_lb".
    iDestruct (hist۰atｰvalid with "Hhist_auth Hhist_at") as %Hhist_lookup.
    iDestruct (generation۰lbｰvalid with "Hgeneration_auth Hg0") as %Hg0.
    iDestruct (generation۰lbｰget with "Hgeneration_auth") as "#Hg".
    iDestruct (snapshot۰lbｰget with "Hsnapshot_auth") as "#Hsnapshot_lb".
    pose proof (inv۰pure۰snaps_last _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as Hlast.
    pose proof Hlast as Hlast'%snapsｰlookup_last.
    opose proof* inv۰pure۰snaps_inst as (Hinst1 & Hinst2); [done.. |].
    opose proof* inv۰pure۰hist_last as (idx' & Hhist_last); first done.
    opose proof* inv۰pure۰hist_idx as Hidx'; [done.. |].
    iDestruct (hist۰atｰget with "Hhist_auth") as "#Hhist_at'"; first done.
    iSplitR "HΦ". { iFrameSteps. }
    iModIntro. iApply "HΦ".
    iFrame "#". iSplitR; first done. iSplitR; first done. iSplitR; first done.
    iSplitR. { iApply (auth_nat_max۰lbｰle with "Hg"). done. }
    iSplitR.
    { iPureIntro. intros Hidx.
      eapply (inv۰pure۰hist_snaps _ _ _ _ _ _ _ _ _ _ _ _ Hinv); done.
    }
    iSteps.
  Qed.

  #[local] Lemma valueｰspec γ ι snaps snap g :
    {{{
      inv' γ ι ∗
      snaps۰lb γ snaps ∗
      ⌜last snaps = Some snap⌝ ∗
      ⌜snap.(snap۰gen) < g⌝ ∗
      generation۰lb γ g
    }}}
      (#γ.(svar۰name۰self)).{value}
    {{{
      𝑣
    , RET 𝑣;
      reader γ (length snaps) g 𝑣
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hsnaps_lb & %Hlast & %Hgen & #Hg) HΦ".
    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰load.
    iDestruct (snaps۰lbｰvalid with "Hsnaps_auth Hsnaps_lb") as %Hsnaps.
    iDestruct (generation۰lbｰvalid with "Hgeneration_auth Hg") as %Hg.
    iDestruct (snaps۰lbｰget with "Hsnaps_auth") as "#Hsnaps_lb1".
    iDestruct (generation۰lbｰget with "Hgeneration_auth") as "#Hg1".
    iDestruct (prophet_wise۰snapshotｰget with "Hprophet_model") as "#Hprophet_snapshot".
    iAssert (if mode1 is Good then True else doom۰lb γ)%I as "#Hdoom".
    { destruct mode1; first done. iApply (doom۰lbｰget with "Hdoom_auth"). done. }
    opose proof* inv۰pure۰hist_last as (idx & Hhist_last); first done.
    iDestruct (hist۰atｰget with "Hhist_auth") as "#Hhist_at"; first done.
    iAssert (reader γ (length snaps) g 𝑣1)%I as "#Hreader".
    { destruct (decide (length snaps < length snaps1)).
      { iLeft. iExists snaps1. iFrame "#". done. }
      apply prefix_length_eq in Hsnaps as <-; last lia.
      assert (snap1 = snap) as ->.
      { pose proof (inv۰pure۰snaps_last _ _ _ _ _ _ _ _ _ _ _ _ Hinv1). congruence. }
      destruct (decide (g < g1)).
      { iRight. iLeft.
        iApply (auth_nat_max۰lbｰle with "Hg1"). lia.
      }
      assert (g1 = g) as -> by lia.
      destruct mode1 as [| b g_d]; last first.
      { iRight. iRight. iLeft. done. }
      iRight. iRight. iRight.
      iExists past1, prophs1.
      iSplitR. { iApply "Hprophet_snapshot". }
      iSplitR. { iPureIntro. symmetry. apply (inv۰pure۰forwards _ _ _ _ _ _ _ _ _ _ _ _ Hinv1). }
      iIntros "%Hhead".
      opose proof* (inv۰pureｰreader Hinv1) as <-; [done.. |].
      iExists idx. done.
    }
    iSplitR "HΦ". { iFrameSteps. }
    iModIntro. iApply "HΦ". done.
  Qed.

  #[local] Lemma waiters۰statusesｰforward γ ι waiters 𝑣' helped past 𝑣 g :
    waiters۰statuses γ ι waiters 𝑣' helped (past ++ [ProphecyForward 𝑣 g]) = waiters۰statuses γ ι waiters 𝑣' helped past.
  Proof.
    rewrite /waiters۰statuses prophecies۰opsｰapp /= right_id //.
  Qed.

  #[local] Lemma readerｰvalid γ snaps g hist vₛ idx mode past prophs n g' 𝑣 :
    length snaps = S (length (prophecies۰forwards past)) →
    hist !! g = Some (vₛ, idx) →
    snaps۰auth γ snaps -∗
    generation۰auth γ g -∗
    doom۰auth γ (mode۰doomed mode) -∗
    hist۰auth γ hist -∗
    prophet۰model γ past prophs -∗
    reader γ n g' 𝑣 -∗
    ⌜n = length snaps → head (prophecies۰forwards prophs) = Some (𝑣, g') → g' = g → mode = Good → vₛ = 𝑣⌝.
  Proof.
    iIntros "%Hforwards %Hhist_lookup Hsnaps_auth Hgeneration_auth Hdoom_auth Hhist_auth Hprophet_model Hreader".
    iIntros "%Hn %Hhead %Hg %Hmode". subst g' n.
    iDestruct "Hreader" as "[(%snaps' & #Hsnaps_lb & %Hsnaps') | [#Hg | [#Hdoom | (%past' & %prophs' & #Hprophet_snapshot & %Hforwards' & #Hhist)]]]".
    - iDestruct (snaps۰lbｰvalid with "Hsnaps_auth Hsnaps_lb") as %?%prefix_length. lia.
    - iDestruct (generation۰lbｰvalid with "Hgeneration_auth Hg") as %?. lia.
    - iDestruct (doom۰lbｰvalid with "Hdoom_auth Hdoom") as %?. done.
    - iDestruct (prophet_wise۰snapshotｰvalid with "Hprophet_model Hprophet_snapshot") as %(past3 & -> & ->).
      rewrite prophecies۰forwardsｰapp length_app in Hforwards.
      assert (prophecies۰forwards past3 = []) as Hpast3.
      { apply nil_length_inv. lia. }
      iDestruct ("Hhist" with "[]") as "(%idx' & Hhist_at)".
      { rewrite prophecies۰forwardsｰapp Hpast3 //. }
      iDestruct (hist۰atｰvalid with "Hhist_auth Hhist_at") as %?.
      naive.
  Qed.

  #[local] Lemma casｰspec γ ι snaps snap g 𝑣 :
    {{{
      svar۰inv γ ι ∗
      snaps۰lb γ snaps ∗
      ⌜last snaps = Some snap⌝ ∗
      ⌜snap.(snap۰gen) < g⌝ ∗
      ⌜snap.(snap۰inst) ≤ g⌝ ∗
      generation۰lb γ g ∗
      reader γ (length snaps) g 𝑣
    }}}
      𝗿𝗲𝘀𝗼𝗹𝘃𝗲
        (𝗰𝗮𝘀 (#γ.(svar۰name۰self)).[snapshot] (snap۰to_val snap) ‘Snapshot@[ 𝑣, #g ])
        (#γ.(svar۰name۰self)).{proph}
        (‘Forward( 𝑣, #g ))%V
    {{{
      b
    , RET #b;
      if b then
        snapshot۰lb γ g
      else
        ∃ snaps',
        snaps۰lb γ snaps' ∗
        ⌜snaps `prefix_of` snaps'⌝ ∗
        ⌜length snaps < length snaps'⌝ ∗
        snapshot۰lb γ snap.(snap۰inst)
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & #Hsnaps_lb & %Hlast & %Hgen & %Hinst & #Hg & #Hreader) HΦ".
    wp۰pures.
    wp۰load.
    wp۰block۰generative bid.
    wp۰pures.
    iInv "Hinv" as "(:inv۰inner =1)".
    iDestruct (snaps۰lbｰvalid with "Hsnaps_auth Hsnaps_lb") as %Hsnaps.
    iDestruct (generation۰lbｰvalid with "Hgeneration_auth Hg") as %Hg.
    pose proof (inv۰pure۰snaps_last _ _ _ _ _ _ _ _ _ _ _ _ Hinv1) as Hlast1.
    opose proof* inv۰pure۰hist_last as (idx & Hhist_last); first done.
    iDestruct (readerｰvalid with "Hsnaps_auth Hgeneration_auth Hdoom_auth Hhist_auth Hprophet_model Hreader") as %Hvₛ.
    { apply (inv۰pure۰forwards _ _ _ _ _ _ _ _ _ _ _ _ Hinv1). }
    { done. }
    pose proof Hlast as Hlast'%snapsｰlookup_last.
    pose proof Hlast' as Hlast''. eapply prefix_lookup_Some in Hlast''; last done.
    pose proof Hlast1 as Hlast1'%snapsｰlookup_last.
    wp۰apply (prophet_wiseｰwpｰresolve with "Hprophet_model"); [done.. |].
    wp۰cas as Hcas | Hcas.
    - iExists None. iSplitR; first done. iIntros "!> Hprophet_model".
      assert (length snaps < length snaps1) as Hlen.
      { pose proof Hsnaps as Hlen%prefix_length.
        destruct (decide (length snaps = length snaps1)) as [Heq |]; last lia.
        apply prefix_length_eq in Hsnaps as <-; last lia.
        exfalso.
        assert (snap1 = snap) as -> by congruence.
        apply (snap۰to_valｰnonsimilar snap). done.
      }
      destruct (snaps1 !! length snaps) as [snap' |] eqn:Hlookup'; last first.
      { apply lookup_ge_None in Hlookup'. lia. }
      opose proof* (inv۰pure۰snaps_sorted _ _ _ _ _ _ _ _ _ _ _ _ Hinv1 (pred (length snaps)) snap snap') as (_ & Hsorted).
      { done. }
      { replace (S (pred (length snaps))) with (length snaps); first done.
        apply lookup_lt_Some in Hlast'. lia.
      }
      opose proof* (inv۰pureｰsnaps_le_last (length snaps) snap' Hinv1); first done.
      iDestruct (snapshot۰lbｰget with "Hsnapshot_auth") as "#Hsnapshot_lb".
      iDestruct (snaps۰lbｰget with "Hsnaps_auth") as "#Hsnaps_lb1".
      iSplitR "HΦ". { iFrameSteps. }
      iModIntro. iApply "HΦ".
      iExists snaps1. iFrame "#". iSplitR; first done. iSplitR; first done.
      iApply (auth_nat_max۰lbｰle with "Hsnapshot_lb"). lia.
    - iExists (Some (ProphecyForward 𝑣 g)). iSplitR.
      { iPureIntro. rewrite /= Nat2Z.id //. }
      iIntros "!> %prophs' -> Hprophet_model".
      apply snap۰to_valｰsimilar in Hcas.
      assert (snaps1 = snaps) as ->.
      { opose proof* (inv۰pureｰsnaps_gen_inj _ _ _ _ Hinv1 Hlast1' Hlast''); first done.
        apply lookup_lt_Some in Hlast'.
        symmetry. apply prefix_length_eq; first done. lia.
      }
      assert (snap1 = snap) as -> by congruence.
      iMod (snapsｰupdate (Snap bid 𝑣 g g1) with "Hsnaps_auth") as "Hsnaps_auth".
      iMod (snapshotｰupdate g with "Hsnapshot_auth") as "Hsnapshot_auth"; first lia.
      iDestruct (snapshot۰lbｰget with "Hsnapshot_auth") as "#Hsnapshot_lb".
      iSplitR "HΦ".
      { iExists 𝑣1, g1, v1, vₛ1, (snaps ++ [Snap bid 𝑣 g g1]), (Snap bid 𝑣 g g1), hist1, waiters1, helped1, (past1 ++ [ProphecyForward 𝑣 g]), prophs', mode1.
        rewrite waiters۰statusesｰforward.
        iFrame. iPureIntro.
        apply (inv۰pureｰforward 𝑣 g bid Hinv1); [lia | lia | lia |].
        intros. eapply Hvₛ; done.
      }
      iSteps.
  Qed.

  Lemma svar٠forwardｰspec γ ι g0 :
    {{{
      svar۰inv γ ι ∗
      generation۰lb γ g0
    }}}
      svar٠forward #γ.(svar۰name۰self)
    {{{
      RET ();
      snapshot۰lb γ g0
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & #Hg0) HΦ".
    wp۰rec.
    iMod (invｰinit with "Hinv") as "(#Hsnaps_lb0 & %vh0 & %idx0 & #Hhist_at0)".
    wp۰apply (snapshotｰspec with "[$Hinv $Hg0 $Hsnaps_lb0 $Hhist_at0]") as (snaps1 snap1) "(#Hsnaps_lb1 & _ & %Hlast1 & %Hinst1 & #Hinst1_lb & #Hsnapshot_lb1 & _ & %gc1 & %vh1 & %idx1 & #Hhist_at1 & %Hgc1 & %Hidx1)".
    wp۰pures.
    iDestruct (auth_nat_max۰lbｰmax with "Hg0 Hinst1_lb") as "#Hlb1".
    wp۰apply (genｰspec with "[$Hinv $Hlb1]") as (g1) "(%Hg1 & #Hg1_lb)".
    wp۰pures.
    case_bool_decide as Hsnap1; wp۰pures.
    { iApply "HΦ". iApply (auth_nat_max۰lbｰle with "Hsnapshot_lb1"). lia. }
    wp۰apply (valueｰspec _ _ snaps1 snap1 g1 with "[]") as (𝑣1) "#Hreader1".
    { iFrame "#". iPureIntro. split; [done | lia]. }
    wp۰pures.
    wp۰apply (casｰspec _ _ snaps1 snap1 g1 𝑣1 with "[]") as ([]) "H".
    { iFrame "#". iPureIntro. split_and!; [done | lia | lia]. }
    { wp۰pures. iApply "HΦ". iApply (auth_nat_max۰lbｰle with "H"). lia. }
    iDestruct "H" as "(%snaps1' & #Hsnaps_lb1' & %Hpre1 & %Hlen1 & _)".
    wp۰pures.
    wp۰apply (snapshotｰspec with "[$Hinv $Hg0 $Hsnaps_lb1' $Hhist_at1]") as (snaps2 snap2) "(#Hsnaps_lb2 & %Hpre2 & %Hlast2 & %Hinst2 & #Hinst2_lb & #Hsnapshot_lb2 & %Hhist2 & _)".
    assert (gc1 ≤ snap2.(snap۰inst)) as Hgc2.
    { apply Hhist2. apply prefix_length in Hpre2. lia. }
    wp۰pures.
    iDestruct (auth_nat_max۰lbｰmax with "Hg0 Hinst2_lb") as "#Hlb2".
    wp۰apply (genｰspec with "[$Hinv $Hlb2]") as (g2) "(%Hg2 & #Hg2_lb)".
    wp۰pures.
    case_bool_decide as Hsnap2; wp۰pures.
    { iApply "HΦ". iApply (auth_nat_max۰lbｰle with "Hsnapshot_lb2"). lia. }
    wp۰apply (valueｰspec _ _ snaps2 snap2 g2 with "[]") as (𝑣2) "#Hreader2".
    { iFrame "#". iPureIntro. split; [done | lia]. }
    wp۰pures.
    wp۰apply (casｰspec _ _ snaps2 snap2 g2 𝑣2 with "[]") as ([]) "H".
    { iFrame "#". iPureIntro. split_and!; [done | lia | lia]. }
    - wp۰pures. iApply "HΦ". iApply (auth_nat_max۰lbｰle with "H"). lia.
    - iDestruct "H" as "(%snaps2' & _ & _ & _ & #Hinst_lb)".
      wp۰pures. iApply "HΦ". iApply (auth_nat_max۰lbｰle with "Hinst_lb"). lia.
  Qed.

  #[local] Lemma inv۰pureｰfresh {𝑣 g v vₛ snaps snap hist waiters helped past prophs mode} id :
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

  #[local] Lemma waiters۰statusesｰinsert γ ι waiters 𝑣 helped past id waiter Ψ :
    id ∉ operations۰ids (prophecies۰ops past) →
    id ∉ operations۰ids helped →
    waiters !! id = None →
    waiters۰statuses γ ι waiters 𝑣 helped past -∗
    saved_pred waiter.(waiter۰post) Ψ -∗
    waiter۰au γ ι waiter Ψ -∗
    waiters۰statuses γ ι (<[id := waiter]> waiters) 𝑣 helped past.
  Proof.
    iIntros "%Hpast %Hhelped %Hlookup Hwaiters #Hpost Hau".
    iApply (big_sepM_insert with "[- $Hwaiters]"); first done.
    rewrite !bool_decide_eq_false_2 //.
    iSteps.
  Qed.

  #[local] Lemma waiters۰statusesｰwrite γ ι waiters 𝑣 𝑣' helped helped' past id (w : option val) waiter :
    waiters !! id = Some waiter →
    id ∉ operations۰ids (prophecies۰ops past) →
    (∀ id', id' ≠ id → (id' ∈ operations۰ids helped' ↔ id' ∈ operations۰ids helped)) →
    (∀ id', id' ≠ id → id' ∈ operations۰ids helped → helped۰result 𝑣' helped' id' = helped۰result 𝑣 helped id') →
    waiters۰statuses γ ι waiters 𝑣 helped past -∗
    waiters۰elem γ id waiter -∗
      waiters۰statuses γ ι waiters 𝑣' helped' (past ++ [ProphecyOp id w]) ∗
      ∃ Ψ,
      saved_pred waiter.(waiter۰post) Ψ ∗
      if bool_decide (id ∈ operations۰ids helped) then
        Ψ (helped۰result 𝑣 helped id)
      else
        waiter۰au γ ι waiter Ψ.
  Proof.
    iIntros "%Hlookup %Hid %Hhelped %Hresult Hwaiters Helem".
    iDestruct (big_sepM_delete with "Hwaiters") as "(Hwaiter & Hwaiters)"; first done.
    rewrite bool_decide_eq_false_2 //.
    iSplitR "Hwaiter"; last done.
    iApply (big_sepM_delete _ _ id); first done.
    rewrite bool_decide_eq_true_2.
    { rewrite prophecies۰opsｰapp /operations۰ids fmap_app. set_solver. }
    iFrame.
    iApply (big_sepM_impl with "Hwaiters").
    iIntros "!> %id' %waiter' %Hlookup' H".
    apply lookup_delete_Some in Hlookup' as (Hne & _).
    rewrite (bool_decide_ext (id' ∈ operations۰ids (prophecies۰ops (past ++ [ProphecyOp id w]))) (id' ∈ operations۰ids (prophecies۰ops past))).
    { rewrite prophecies۰opsｰapp /operations۰ids fmap_app. set_solver. }
    rewrite (bool_decide_ext (id' ∈ operations۰ids helped') (id' ∈ operations۰ids helped)); first auto.
    destruct (bool_decide (id' ∈ operations۰ids (prophecies۰ops past))); first done.
    destruct (bool_decide_reflect (id' ∈ operations۰ids helped)) as [Hid' | Hid']; last done.
    rewrite Hresult //.
  Qed.

  #[local] Lemma waiters۰statusesｰhelp γ ι waiters 𝑣 past helped help v :
    v = default 𝑣 (last (omap operation۰val helped)) →
    helpable waiters past helped help →
    waiters۰statuses γ ι waiters 𝑣 helped past -∗
    model₂ γ v ={⊤ ∖ ↑ι}=∗
      waiters۰statuses γ ι waiters 𝑣 (helped ++ help) past ∗
      model₂ γ (default v (last (omap operation۰val help))).
  Proof.
    iInduction help as [| op help] "IH" forall (helped v).
    - iIntros "_ _ Hwaiters Hmodel₂". rewrite right_id. iFrame. done.
    - iIntros "%Hv %Hhelpable Hwaiters Hmodel₂".
      destruct Hhelpable as ((waiter & Hlookup & Hval) & Hdone & Hhelped & Hhelpable).
      iDestruct (big_sepM_delete with "Hwaiters") as "(Hwaiter & Hwaiters)"; first done.
      rewrite bool_decide_eq_false_2 // bool_decide_eq_false_2 //.
      iDestruct "Hwaiter" as "(%Ψ & #Hpost & Hau)".
      iMod "Hau" as "(%v' & Hmodel₁ & _ & HΨ)".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod (modelｰupdate (default v waiter.(waiter۰val)) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΨ" with "Hmodel₁") as "HΨ".
      iAssert (waiters۰statuses γ ι waiters 𝑣 (helped ++ [op]) past) with "[HΨ Hwaiters]" as "Hwaiters".
      { iApply (big_sepM_delete _ _ op.(operation۰id)); first done.
        rewrite bool_decide_eq_false_2 // bool_decide_eq_true_2.
        { rewrite /operations۰ids fmap_app. set_solver. }
        rewrite helped۰resultｰapp_not_in // /= decide_True // -Hv.
        iFrame "#∗".
        iApply (big_sepM_impl with "Hwaiters").
        iIntros "!> %id' %waiter' %Hlookup' H".
        apply lookup_delete_Some in Hlookup' as (Hne & _).
        rewrite (bool_decide_ext (id' ∈ operations۰ids (helped ++ [op])) (id' ∈ operations۰ids helped)).
        { rewrite /operations۰ids fmap_app. set_solver. }
        destruct (bool_decide (id' ∈ operations۰ids (prophecies۰ops past))); first done.
        destruct (bool_decide_reflect (id' ∈ operations۰ids helped)) as [Hid' | Hid']; last done.
        rewrite helped۰resultｰapp_in //.
      }
      assert (default v waiter.(waiter۰val) = default 𝑣 (last (omap operation۰val (helped ++ [op])))) as Hv'.
      { rewrite omap_app last_app Hval Hv.
        destruct op as [id_op [x |]]; done.
      }
      iMod ("IH" with "[//] [//] Hwaiters Hmodel₂") as "(Hwaiters & Hmodel₂)".
      rewrite -assoc /= last_omap_cons Hval.
      iFrame.
      destruct (last (omap operation۰val help)), (operation۰val op); done.
  Qed.

  #[local] Lemma waiterｰregister γ ι id (w : option val) Ψ :
    inv' γ ι -∗
    identifier۰model id -∗
    AU <{
      ∃∃ v',
      model₁ γ v'
    }> @ ⊤ ∖ ↑ι, ∅ <{
      model₁ γ (default v' w)
    , COMM
      Ψ v'
    }> ={⊤}=∗
      ∃ waiter,
      ⌜waiter.(waiter۰val) = w⌝ ∗
      waiters۰elem γ id waiter ∗
      saved_pred waiter.(waiter۰post) Ψ ∗
      generation۰lb γ waiter.(waiter۰gen).
  Proof.
    iIntros "#Hinv Hid Hau".
    iMod (saved_predｰalloc Ψ) as "(%γ_post & #Hpost)".
    iInv "Hinv" as "(:inv۰inner =1)".
    pose waiter :=
      {|waiter۰val := w
      ; waiter۰post := γ_post
      ; waiter۰gen := g1
      |}.
    iMod (waitersｰinsert id waiter with "Hwaiters_auth Hid") as "(%Hlookup & Hwaiters_auth & Helem)".
    iDestruct (generation۰lbｰget with "Hgeneration_auth") as "#Hgen".
    destruct (inv۰pureｰfresh id Hinv1) as (Hpast & Hhelped); first done.
    iSplitR "Helem".
    { iModIntro. iNext.
      iExists 𝑣1, g1, v1, vₛ1, snaps1, snap1, hist1, (<[id := waiter]> waiters1), helped1, past1, prophs1, mode1.
      iFrame.
      iSplitL.
      - iApply (waiters۰statusesｰinsert _ _ _ _ _ _ id waiter Ψ Hpast Hhelped Hlookup with "Hwaiters Hpost Hau").
      - iPureIntro. apply inv۰pureｰregister; done.
    }
    iModIntro. iExists waiter. iFrame "#∗". done.
  Qed.

  (* The common linearization step of [get] and [set]: consuming the prophesied operation [id]. *)
  #[local] Lemma waiterｰconsume γ ι 𝑣 g v vₛ snaps snap hist waiters helped past prophs mode id (w : option val) waiter Ψ :
    inv۰pure 𝑣 g v vₛ snaps snap hist waiters helped past (ProphecyOp id w :: prophs) mode →
    waiter.(waiter۰val) = w →
    waiter.(waiter۰gen) ≤ snap.(snap۰gen) →
    waiters۰auth γ waiters -∗
    waiters۰elem γ id waiter -∗
    saved_pred waiter.(waiter۰post) Ψ -∗
    waiters۰statuses γ ι waiters 𝑣 helped past -∗
    model₂ γ v ={⊤ ∖ ↑ι}=∗
      waiters۰auth γ waiters ∗
      waiters۰statuses γ ι waiters (default 𝑣 w) (tail helped) (past ++ [ProphecyOp id w]) ∗
      model₂ γ (if helped is [] then default v w else v) ∗
      ⌜inv۰pure (default 𝑣 w) g (if helped is [] then default v w else v) vₛ snaps snap hist waiters (tail helped) (past ++ [ProphecyOp id w]) prophs mode⌝ ∗
      ▷ Ψ 𝑣.
  Proof.
    iIntros "%Hinv %Hval %Hgen Hwaiters_auth Helem #Hpost Hwaiters Hmodel₂".
    iDestruct (waiters۰elemｰvalid with "Hwaiters_auth Helem") as %Hlookup.
    destruct (decide (id ∈ operations۰ids (prophecies۰ops past))) as [Hdone | Hdone].
    { iDestruct (big_sepM_lookup with "Hwaiters") as "Hwaiter"; first done.
      rewrite bool_decide_eq_true_2 //.
      iDestruct (waiters۰elemｰexclusive with "Helem Hwaiter") as %[].
    }
    destruct (inv۰pureｰwrite id w waiter Hinv Hlookup Hval Hdone Hgen) as (Hhelped & Hinv').
    iDestruct (waiters۰statusesｰwrite _ _ _ 𝑣 (default 𝑣 w) helped (tail helped) _ _ w with "Hwaiters Helem") as "(Hwaiters & %Ψ' & #Hpost' & HΨ)".
    { done. }
    { done. }
    { intros id' Hid'.
      destruct Hhelped as [-> | Hhead]; first done.
      destruct helped as [| op helped]; first done.
      injection Hhead as ->.
      rewrite /operations۰ids /= elem_of_cons. naive.
    }
    { intros id' Hid' Hhelped'.
      destruct Hhelped as [-> | Hhead]; first set_solver.
      destruct helped as [| op helped]; first done.
      injection Hhead as ->.
      rewrite /= decide_False //.
    }
    iFrame.
    iAssert (|={⊤ ∖ ↑ι}=> Ψ' 𝑣 ∗ model₂ γ (if helped is [] then default v w else v))%I with "[HΨ Hmodel₂]" as ">(HΨ & $)".
    { destruct Hhelped as [-> | Hhead].
      - assert (bool_decide (id ∈ operations۰ids []) = false) as -> by (apply bool_decide_eq_false_2, not_elem_of_nil).
        pose proof (inv۰pure۰model _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as ->.
        iMod "HΨ" as "(%v' & Hmodel₁ & _ & HΨ)".
        iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
        iMod (modelｰupdate (default 𝑣 w) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        rewrite Hval.
        iMod ("HΨ" with "Hmodel₁") as "$". done.
      - destruct helped as [| op helped]; first done.
        injection Hhead as ->.
        rewrite bool_decide_eq_true_2.
        { rewrite /operations۰ids /=. set_solver. }
        rewrite /= decide_True //.
        iFrame. done.
    }
    iDestruct (saved_predｰagree 𝑣 with "Hpost Hpost'") as "Heq".
    iModIntro. iSplitR; first done.
    iNext. iRewrite "Heq". done.
  Qed.

  Lemma svar٠getｰspec γ ι :
    <<<
      svar۰inv γ ι
    | ∀∀ v,
      svar۰model γ v
    >>>
      svar٠get #γ.(svar۰name۰self) @ ↑ι
    <<<
      svar۰model γ v
    | RET v;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".
    wp۰rec credit:"H£".
    wp۰apply+ (wpｰid with "[//]") as (id) "Hid".
    iMod (waiterｰregister _ _ id None (λ v, True -∗ Φ v)%I with "Hinv Hid HΦ") as "(%waiter & %Hval & Helem & #Hpost & #Hgen)".
    wp۰pures.
    wp۰apply (svar٠forwardｰspec with "[$Ht_proph $Hinv $Hgen]") as "#Hsnapshot_lb".
    wp۰pures.
    wp۰load.
    wp۰pures.
    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰apply (prophet_wiseｰwpｰresolve with "Hprophet_model"); [done.. |].
    wp۰load.
    iExists (Some (ProphecyOp id None)). iSplitR; first done.
    iIntros "!> %prophs' -> Hprophet_model".
    iDestruct (snapshot۰lbｰvalid with "Hsnapshot_auth Hsnapshot_lb") as %Hgen.
    iMod (waiterｰconsume with "Hwaiters_auth Helem Hpost Hwaiters Hmodel₂") as "(Hwaiters_auth & Hwaiters & Hmodel₂ & %Hinv' & HΨ)"; [done.. |].
    iSplitR "H£ HΨ".
    { iModIntro. iNext. iFrameSteps. }
    iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
    iModIntro. iApply "HΨ". done.
  Qed.

  Lemma svar٠setｰspec γ ι v :
    <<<
      svar۰inv γ ι
    | ∀∀ v',
      svar۰model γ v'
    >>>
      svar٠set #γ.(svar۰name۰self) v @ ↑ι
    <<<
      svar۰model γ v
    | RET ();
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".
    wp۰rec credit:"H£".
    wp۰apply+ (wpｰid with "[//]") as (id) "Hid".
    iMod (waiterｰregister _ _ id (Some v) (λ _, True -∗ Φ ()%V)%I with "Hinv Hid HΦ") as "(%waiter & %Hval & Helem & #Hpost & #Hgen)".
    wp۰pures.
    wp۰apply (svar٠forwardｰspec with "[$Ht_proph $Hinv $Hgen]") as "#Hsnapshot_lb".
    wp۰pures.
    wp۰load.
    wp۰pures.
    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰apply (prophet_wiseｰwpｰresolve with "Hprophet_model"); [done.. |].
    wp۰store.
    iExists (Some (ProphecyOp id (Some v))). iSplitR; first done.
    iIntros "!> %prophs' -> Hprophet_model".
    iDestruct (snapshot۰lbｰvalid with "Hsnapshot_auth Hsnapshot_lb") as %Hgen.
    iMod (waiterｰconsume with "Hwaiters_auth Helem Hpost Hwaiters Hmodel₂") as "(Hwaiters_auth & Hwaiters & Hmodel₂ & %Hinv' & HΨ)"; [done.. |].
    iSplitR "H£ HΨ".
    { iModIntro. iNext. iFrameSteps. }
    iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
    iModIntro. iApply "HΨ". done.
  Qed.

  Lemma svar٠clickｰspec γ ι vₛ :
    <<<
      svar۰inv γ ι ∗
      svar۰scanner γ Own vₛ
    | ∀∀ v,
      svar۰model γ v
    >>>
      svar٠click #γ.(svar۰name۰self) @ ↑ι
    <<<
      svar۰model γ v
    | RET ();
      svar۰scanner γ Own v
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:scanner)) HΦ".
    wp۰rec.
    wp۰apply (genｰspecｰscanner with "[$Hinv $Hscanner₁]") as "Hscanner₁".
    wp۰pures.
    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰store.
    iDestruct (scannerｰagree with "Hscanner₁ Hscanner₂") as %(<- & <-).
    destruct (inv۰pureｰclick Hinv1) as (help & mode' & Hhelpable & Hmode' & Hinv').
    iMod (waiters۰statusesｰhelp with "Hwaiters Hmodel₂") as "(Hwaiters & Hmodel₂)".
    { apply (inv۰pure۰model _ _ _ _ _ _ _ _ _ _ _ _ Hinv1). }
    { done. }
    set v' := default v1 (last (omap operation۰val help)).
    iMod "HΦ" as "(%v_ & Hmodel₁ & _ & HΦ)".
    iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
    iMod ("HΦ" with "Hmodel₁") as "HΦ".
    iMod (scannerｰupdate v' (S g) with "Hscanner₁ Hscanner₂") as "(Hscanner₁ & Hscanner₂)".
    iMod (generationｰupdate with "Hgeneration_auth") as "Hgeneration_auth".
    iMod (histｰupdate v' (pred (length snaps1)) with "Hhist_auth") as "Hhist_auth".
    iMod (doomｰupdate mode' with "Hdoom_auth") as "Hdoom_auth"; first done.
    iSplitR "Hscanner₁ HΦ".
    { iModIntro. iNext.
      iExists 𝑣1, (S g), v', v', snaps1, snap1, (hist1 ++ [(v', pred (length snaps1))]), waiters1, (helped1 ++ help), past1, prophs1, mode'.
      replace (⁺g + 1)%Z with (⁺(S g)) by lia.
      iFrame. done.
    }
    iModIntro. iApply "HΦ". iExists (S g). done.
  Qed.

  Lemma svar٠observeｰspec γ ι dq vₛ :
    {{{
      svar۰inv γ ι ∗
      svar۰scanner γ dq vₛ
    }}}
      svar٠observe #γ.(svar۰name۰self)
    {{{
      RET vₛ;
      svar۰scanner γ dq vₛ
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:scanner)) HΦ".
    wp۰rec.
    iAssert (|={⊤}=> generation۰lb γ g ∗ scanner₁ γ dq vₛ g)%I with "[Hscanner₁]" as ">(#Hg & Hscanner₁)".
    { iInv "Hinv" as "(:inv۰inner =1)".
      iDestruct (scannerｰagree with "Hscanner₁ Hscanner₂") as %(<- & <-).
      iDestruct (generation۰lbｰget with "Hgeneration_auth") as "#Hg".
      iSplitR "Hscanner₁". { iFrameSteps. }
      iFrameSteps.
    }
    wp۰apply (svar٠forwardｰspec with "[$Ht_proph $Hinv $Hg]") as "#Hsnapshot_lb".
    wp۰pures.
    wp۰bind (_.{snapshot})%E.
    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰load.
    iDestruct (scannerｰagree with "Hscanner₁ Hscanner₂") as %(<- & <-).
    iDestruct (snapshot۰lbｰvalid with "Hsnapshot_auth Hsnapshot_lb") as %Hgen.
    destruct (inv۰pureｰstable Hinv1 Hgen) as (_ & Hval).
    iSplitR "Hscanner₁ HΦ". { iFrameSteps. }
    iModIntro. wp۰pures.
    rewrite Hval. iApply "HΦ". iFrameSteps.
  Qed.
End svar_G.

Require zoo_saturn.svar__opaque.

Please opacify.
