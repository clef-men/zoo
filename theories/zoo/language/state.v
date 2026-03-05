From stdpp Require Import
  gmap.

From iris.algebra Require Import
  ofe.

From zoo Require Import
  prelude.
From zoo.language Require Export
  syntax.
From zoo Require Import
  options.

Implicit Types l : location.
Implicit Types v w : val.
Implicit Types vs : list val.

Record header := Header {
  header_tag : nat ;
  header_size : nat ;
}.
Add Printing Constructor header.

Record state := {
  state_headers : gmap location header ;
  state_heap : gmap location val ;
  state_locals : list val ;
  state_prophets : gset prophet_id ;
}.
Implicit Types σ : state.

Canonical state_O {SI : sidx} :=
  leibnizO state.

#[global] Instance state_inhabited : Inhabited state :=
  populate
    {|state_headers := inhabitant ;
      state_heap := inhabitant ;
      state_locals := inhabitant ;
      state_prophets := inhabitant ;
    |}.

Definition state_update_heap f σ :=
  {|state_headers := σ.(state_headers) ;
    state_heap := f σ.(state_heap) ;
    state_locals := σ.(state_locals) ;
    state_prophets := σ.(state_prophets) ;
  |}.
Definition state_update_headers f σ :=
  {|state_headers := f σ.(state_headers) ;
    state_heap := σ.(state_heap) ;
    state_locals := σ.(state_locals) ;
    state_prophets := σ.(state_prophets) ;
  |}.
Definition state_update_locals f σ :=
  {|state_headers := σ.(state_headers) ;
    state_heap := σ.(state_heap) ;
    state_locals := f σ.(state_locals) ;
    state_prophets := σ.(state_prophets) ;
  |}.
Definition state_update_prophets f σ :=
  {|state_headers := σ.(state_headers) ;
    state_heap := σ.(state_heap) ;
    state_locals := σ.(state_locals) ;
    state_prophets := f σ.(state_prophets) ;
  |}.

Definition state_set_location l v :=
  state_update_heap $ insert l v.
Definition state_set_header l hdr :=
  state_update_headers $ insert l hdr.
Definition state_set_local tid v :=
  state_update_locals $ insert tid v.
Definition state_add_local v :=
  state_update_locals $ (.++ [v]).
Definition state_add_prophet pid :=
  state_update_prophets $ ({[pid]} ∪.).

Fixpoint heap_array l vs : gmap location val :=
  match vs with
  | [] =>
      ∅
  | v :: vs =>
      <[l := v]> (heap_array (l +ₗ 1) vs)
  end.
#[global] Arguments heap_array _ !_ / : assert.

Lemma heap_array_singleton l v :
  heap_array l [v] = {[l := v]}.
Proof.
  rewrite /heap_array insert_empty //.
Qed.
Lemma heap_array_lookup l vs w k :
  heap_array l vs !! k = Some w ↔
    ∃ j,
    (0 ≤ j)%Z ∧
    k = l +ₗ j ∧
    vs !! ₊j = Some w.
Proof.
  revert k l; induction vs as [|v' vs IH]=> l' l /=.
  { rewrite lookup_empty. naive_solver lia. }
  rewrite lookup_insert_Some IH. split.
  - intros [[-> ?] | (Hl & j & ? & -> & ?)].
    { eexists 0. rewrite location_add_0. naive_solver lia. }
    eexists (1 + j)%Z. rewrite location_add_assoc !Z.add_1_l Z2Nat.inj_succ; auto with lia.
  - intros (j & ? & -> & Hil). destruct_decide (j = 0); simplify_eq/=.
    { rewrite location_add_0; eauto. }
    right. split.
    { rewrite -{1}(location_add_0 l). intros ?%(inj (location_add _)); lia. }
    assert (₊j = S ₊(j - 1)) as Hj.
    { rewrite -Z2Nat.inj_succ; last lia. f_equal; lia. }
    rewrite Hj /= in Hil.
    eexists (j - 1)%Z. rewrite location_add_assoc Z.add_sub_assoc Z.add_simpl_l. auto with lia.
Qed.
Lemma heap_array_map_disjoint heap l vs :
  ( ∀ i,
    i < length vs →
    heap !! (l +ₗ i) = None
  ) →
  heap_array l vs ##ₘ heap.
Proof.
  intros Hdisj. apply map_disjoint_spec=> l' v1 v2.
  intros (j & ? & -> & ?%lookup_lt_Some%inj_lt)%heap_array_lookup ?.
  ospecialize* (Hdisj ₊j); first lia.
  rewrite Z2Nat.id // in Hdisj. naive_solver.
Qed.

Definition state_alloc l hdr vs σ :=
  {|state_headers := <[l := hdr]> σ.(state_headers) ;
    state_heap := heap_array l vs ∪ σ.(state_heap) ;
    state_locals := σ.(state_locals) ;
    state_prophets := σ.(state_prophets) ;
  |}.
