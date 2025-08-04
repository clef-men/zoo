From stdpp Require Import
  gmap.

From iris.algebra Require Import
  ofe.

From zoo Require Import
  prelude.
From zoo.common Require Import
  countable.
From zoo Require Import
  options.

#[local] Open Scope Z_scope.

Record location := Loc {
  location_car : Z ;
}.
Add Printing Constructor location.

Canonical location_O {SI : sidx} :=
  leibnizO location.

Lemma location_eq_spec l1 l2 :
  l1 = l2 ↔
  location_car l1 = location_car l2.
Proof.
  destruct l1, l2; naive_solver.
Qed.

#[global] Instance location_inhabited : Inhabited location :=
  populate {| location_car := 0 |}.
#[global] Instance location_eq_dec : EqDecision location :=
  ltac:(solve_decision).
#[global] Instance location_countable :
  Countable location.
Proof.
  solve_countable.
Qed.

#[global] Program Instance location_infinite : Infinite location :=
  inj_infinite (λ p, {| location_car := p |}) (λ l, Some (location_car l)) _.
Next Obligation.
  done.
Qed.

Definition location_add l i :=
  {| location_car := location_car l + i |}.

Notation "l +ₗ i" := (
  location_add l i
)(at level 50,
  left associativity
) : stdpp_scope.

#[global] Instance location_add_inj_1 l :
  Inj (=) (=) (location_add l).
Proof.
  intros ?*. rewrite location_eq_spec /=. lia.
Qed.
#[global] Instance location_add_inj_2 i :
  Inj (=) (=) (λ l, location_add l i).
Proof.
  intros ?*. rewrite location_eq_spec Z.add_cancel_r location_eq_spec //.
Qed.
Lemma location_add_assoc l i j :
  l +ₗ i +ₗ j = l +ₗ (i + j).
Proof.
  rewrite location_eq_spec /=. lia.
Qed.
Lemma location_add_0 l :
  l +ₗ 0 = l.
Proof.
  rewrite location_eq_spec /=; lia.
Qed.

Definition location_fresh (ls : gset location) :=
  {| location_car := set_fold (λ k r, (1 + location_car k) `max` r) 1 ls |}.

Lemma location_fresh_fresh ls i :
  0 ≤ i →
  location_fresh ls +ₗ i ∉ ls.
Proof.
  intros Hi.
  enough (∀ l, l ∈ ls → location_car l < location_car (location_fresh ls) + i).
  { naive_solver lia. }
  apply (set_fold_ind_L (λ r ls, ∀ l, l ∈ ls → (location_car l < r + i))).
  all: set_solver by eauto with lia.
Qed.

#[global] Opaque location_fresh.
