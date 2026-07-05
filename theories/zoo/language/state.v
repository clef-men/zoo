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
Implicit Types h : gmap location val.

Record header := Header
  { header_tag : nat
  ; header_size : nat
  }.
Add Printing Constructor header.

Record state :=
  { state_headers : gmap location header
  ; state_heap : gmap location val
  ; state_locals : list val
  ; state_prophets : gset prophet_id
  }.
Implicit Types σ : state.

Canonical state_O {SI : sidx} :=
  leibnizO state.

#[global] Instance state_inhabited : Inhabited state :=
  populate
    {|state_headers := inhabitant
    ; state_heap := inhabitant
    ; state_locals := inhabitant
    ; state_prophets := inhabitant
    |}.

Definition state_update_heap f σ :=
  {|state_headers := σ.(state_headers)
  ; state_heap := f σ.(state_heap)
  ; state_locals := σ.(state_locals)
  ; state_prophets := σ.(state_prophets)
  |}.
Definition state_update_headers f σ :=
  {|state_headers := f σ.(state_headers)
  ; state_heap := σ.(state_heap)
  ; state_locals := σ.(state_locals)
  ; state_prophets := σ.(state_prophets)
  |}.
Definition state_update_locals f σ :=
  {|state_headers := σ.(state_headers)
  ; state_heap := σ.(state_heap)
  ; state_locals := f σ.(state_locals)
  ; state_prophets := σ.(state_prophets)
  |}.
Definition state_update_prophets f σ :=
  {|state_headers := σ.(state_headers)
  ; state_heap := σ.(state_heap)
  ; state_locals := σ.(state_locals)
  ; state_prophets := f σ.(state_prophets)
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

Section chunk.
  Context {A : Type}.

  Implicit Types x y : A.
  Implicit Types xs : list A.
  Implicit Types m : gmap location A.

  Fixpoint chunk l xs : gmap location A :=
    match xs with
    | [] =>
        ∅
    | x :: xs =>
        <[l := x]> (chunk (l +ₗ 1) xs)
    end.
  #[global] Arguments chunk _ !_ / : assert.

  Lemma chunk_singleton l x :
    chunk l [x] = {[l := x]}.
  Proof.
    rewrite /chunk insert_empty //.
  Qed.
  Lemma chunk_lookup l xs 𝑙 y :
    chunk l xs !! 𝑙 = Some y ↔
      ∃ i,
      (0 ≤ i)%Z ∧
      𝑙 = l +ₗ i ∧
      xs !! ₊i = Some y.
  Proof.
    move: l 𝑙. induction xs as [| x xs IH] => l 𝑙 /=.
    - naive_solver.
    - rewrite lookup_insert_Some IH.
      split.
      + intros [(<- & <-) | (Hl & i & Hi & -> & Hlookup)].
        * exists 0.
          rewrite location_add_0.
          naive_solver.
        * exists (1 + i)%Z.
          rewrite location_add_assoc Z.add_1_l Z2Nat.inj_succ //.
          auto with lia.
      + intros (i & ? & -> & Hlookup).
        destruct_decide (i = 0); simplify.
        { rewrite location_add_0. auto. }
        right. split.
        * rewrite -{1}(location_add_0 l).
          naive_solver.
        * assert (₊i = ˖₊(i - 1)) as Hi.
          { rewrite -Z2Nat.inj_succ; lia. }
          rewrite Hi /= in Hlookup.
          exists (i - 1)%Z.
          rewrite location_add_assoc Z.add_sub_assoc Z.add_simpl_l.
          auto with lia.
  Qed.
  Lemma chunk_map_disjoint m l xs :
    ( ∀ i,
      i < length xs →
      m !! (l +ₗ i) = None
    ) →
    chunk l xs ##ₘ m.
  Proof.
    intros Hm.
    apply map_disjoint_spec. intros 𝑙 x1 x2 (i & ? & -> & ?%lookup_lt_Some%inj_lt)%chunk_lookup Hlookup.
    ospecialize* (Hm ₊i). 1: lia.
    rewrite Z2Nat.id // in Hm.
    naive_solver.
  Qed.
End chunk.

Definition state_alloc l hdr vs σ :=
  {|state_headers := <[l := hdr]> σ.(state_headers)
  ; state_heap := chunk l vs ∪ σ.(state_heap)
  ; state_locals := σ.(state_locals)
  ; state_prophets := σ.(state_prophets)
  |}.

Definition state_alloc_condition l sz σ :=
  σ.(state_headers) !! l = None ∧
  σ.(state_heap) !! l = None ∧
    ∀ i,
    i < sz →
      σ.(state_headers) !! (l +ₗ i) = None ∧
      σ.(state_heap) !! (l +ₗ i) = None.

Definition state_fresh_dom σ :=
  dom σ.(state_headers) ∪
  dom σ.(state_heap).
Definition state_fresh σ :=
  location_fresh $ state_fresh_dom σ.

Lemma state_alloc_condition_fresh sz σ :
  state_alloc_condition (state_fresh σ) sz σ.
Proof.
  pose proof (location_fresh_fresh $ state_fresh_dom σ) as Hfresh.
  repeat setoid_rewrite not_elem_of_union in Hfresh.
  split_and!.
  - rewrite /state_fresh -(location_add_0 (location_fresh _)) //.
    apply not_elem_of_dom, Hfresh => //.
  - rewrite /state_fresh -(location_add_0 (location_fresh _)) //.
    apply not_elem_of_dom, Hfresh => //.
  - intros i Hi.
    split_and!.
    all: apply not_elem_of_dom, Hfresh; lia.
Qed.
