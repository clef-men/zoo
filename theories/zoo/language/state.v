Require Import stdpp.gmap.

Require Import iris.algebra.ofe.

Require Import zoo.prelude.
Require Export zoo.language.syntax.
Require Import zoo.options.

Implicit Type l : location.
Implicit Type v w : val.
Implicit Type vs : list val.
Implicit Type h : gmap location val.

Record header := Header
  { header۰tag : tag
  ; header۰size : nat
  }.
Add Printing Constructor header.

Record state :=
  { state۰headers : gmap location header
  ; state۰heap : gmap location val
  ; state۰locals : list val
  ; state۰prophets : gset prophet_id
  }.
Implicit Type σ : state.

Canonical state۰O {SI : sidx} :=
  leibnizO state.

#[global] Instance stateｰinhabited : Inhabited state :=
  populate
    {|state۰headers := inhabitant
    ; state۰heap := inhabitant
    ; state۰locals := inhabitant
    ; state۰prophets := inhabitant
    |}.

Definition state۰update_heap f σ :=
  {|state۰headers := σ.(state۰headers)
  ; state۰heap := f σ.(state۰heap)
  ; state۰locals := σ.(state۰locals)
  ; state۰prophets := σ.(state۰prophets)
  |}.
Definition state۰update_headers f σ :=
  {|state۰headers := f σ.(state۰headers)
  ; state۰heap := σ.(state۰heap)
  ; state۰locals := σ.(state۰locals)
  ; state۰prophets := σ.(state۰prophets)
  |}.
Definition state۰update_locals f σ :=
  {|state۰headers := σ.(state۰headers)
  ; state۰heap := σ.(state۰heap)
  ; state۰locals := f σ.(state۰locals)
  ; state۰prophets := σ.(state۰prophets)
  |}.
Definition state۰update_prophets f σ :=
  {|state۰headers := σ.(state۰headers)
  ; state۰heap := σ.(state۰heap)
  ; state۰locals := σ.(state۰locals)
  ; state۰prophets := f σ.(state۰prophets)
  |}.

Definition state۰set_location l v :=
  state۰update_heap $ insert l v.
Definition state۰set_header l hdr :=
  state۰update_headers $ insert l hdr.
Definition state۰set_local tid v :=
  state۰update_locals $ insert tid v.
Definition state۰add_local v :=
  state۰update_locals $ (.++ [v]).
Definition state۰add_prophet pid :=
  state۰update_prophets $ ({[pid]} ∪.).

Section chunk.
  Context {A : Type}.

  Implicit Type x y : A.
  Implicit Type xs : list A.
  Implicit Type m : gmap location A.

  Fixpoint chunk l xs : gmap location A :=
    match xs with
    | [] =>
        ∅
    | x :: xs =>
        <[l := x]> (chunk (l +ₗ 1) xs)
    end.
  #[global] Arguments chunk _ !_ / : assert.

  Lemma chunkｰsingleton l x :
    chunk l [x] = {[l := x]}.
  Proof.
    rewrite /chunk insert_empty //.
  Qed.
  Lemma chunkｰlookup l xs 𝑙 y :
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
          rewrite location۰addｰ0.
          naive_solver.
        * exists (1 + i)%Z.
          rewrite location۰addｰassoc Z.add_1_l Z2Nat.inj_succ //.
          auto with lia.
      + intros (i & ? & -> & Hlookup).
        destruct_decide (i = 0); simp.
        { rewrite location۰addｰ0. auto. }
        right. split.
        * rewrite -{1}(location۰addｰ0 l).
          naive_solver.
        * assert (₊i = ˖₊(i - 1)) as Hi.
          { rewrite -Z2Nat.inj_succ; lia. }
          rewrite Hi /= in Hlookup.
          exists (i - 1)%Z.
          rewrite location۰addｰassoc Z.add_sub_assoc Z.add_simpl_l.
          auto with lia.
  Qed.
  Lemma chunkｰmapｰdisjoint m l xs :
    ( ∀ i,
      i < length xs →
      m !! (l +ₗ i) = None
    ) →
    chunk l xs ##ₘ m.
  Proof.
    intros Hm.
    apply map_disjoint_spec. intros 𝑙 x1 x2 (i & ? & -> & ?%lookup_lt_Some%inj_lt)%chunkｰlookup Hlookup.
    ospecialize* (Hm ₊i). 1: lia.
    rewrite Z2Nat.id // in Hm.
    naive_solver.
  Qed.
End chunk.

Definition state۰alloc l hdr vs σ :=
  {|state۰headers := <[l := hdr]> σ.(state۰headers)
  ; state۰heap := chunk l vs ∪ σ.(state۰heap)
  ; state۰locals := σ.(state۰locals)
  ; state۰prophets := σ.(state۰prophets)
  |}.

Definition state۰alloc_condition l sz σ :=
  σ.(state۰headers) !! l = None ∧
  σ.(state۰heap) !! l = None ∧
    ∀ i,
    i < sz →
      σ.(state۰headers) !! (l +ₗ i) = None ∧
      σ.(state۰heap) !! (l +ₗ i) = None.

Definition state۰fresh۰dom σ :=
  dom σ.(state۰headers) ∪
  dom σ.(state۰heap).
Definition state۰fresh σ :=
  location۰fresh $ state۰fresh۰dom σ.

Lemma state۰alloc_conditionｰfresh sz σ :
  state۰alloc_condition (state۰fresh σ) sz σ.
Proof.
  pose proof (location۰freshｰfresh $ state۰fresh۰dom σ) as Hfresh.
  repeat setoid_rewrite not_elem_of_union in Hfresh.
  split_and!.
  - rewrite /state۰fresh -(location۰addｰ0 (location۰fresh _)) //.
    apply not_elem_of_dom, Hfresh => //.
  - rewrite /state۰fresh -(location۰addｰ0 (location۰fresh _)) //.
    apply not_elem_of_dom, Hfresh => //.
  - intros i Hi.
    split_and!.
    all: apply not_elem_of_dom, Hfresh; lia.
Qed.
