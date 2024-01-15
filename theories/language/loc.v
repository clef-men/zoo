From stdpp Require Import
  gmap.

From iris.algebra Require Import
  ofe.

From zebra Require Import
  prelude.
From zebra Require Import
  options.

#[local] Open Scope Z_scope.

Record loc := Loc {
  loc_car : Z ;
}.
Add Printing Constructor loc.

Canonical loc_O :=
  leibnizO loc.

Lemma loc_eq_spec l1 l2 :
  l1 = l2 ↔
  loc_car l1 = loc_car l2.
Proof.
  destruct l1, l2; naive_solver.
Qed.

#[global] Instance loc_inhabited : Inhabited loc :=
  populate {| loc_car := 0 |}.
#[global] Instance loc_eq_dec : EqDecision loc :=
  ltac:(solve_decision).
#[global] Instance loc_countable :
  Countable loc.
Proof.
  apply (inj_countable' loc_car Loc); intros []; done.
Qed.

#[global] Program Instance loc_infinite : Infinite loc :=
  inj_infinite (λ p, {| loc_car := p |}) (λ l, Some (loc_car l)) _.
Next Obligation.
  done.
Qed.

Definition loc_add l i :=
  {| loc_car := loc_car l + i |}.

Notation "l +ₗ i" := (
  loc_add l i
)(at level 50,
  left associativity
) : stdpp_scope.
Notation "l .[ i ]" := (
  loc_add l i
)(at level 2,
  i at level 200,
  left associativity,
  format "l .[ i ]"
) : stdpp_scope.

#[global] Instance loc_add_inj l :
  Inj eq eq (loc_add l).
Proof.
  intros ?*. rewrite loc_eq_spec /=. lia.
Qed.
Lemma loc_add_assoc l i j :
  l +ₗ i +ₗ j = l +ₗ (i + j).
Proof.
  rewrite loc_eq_spec /=. lia.
Qed.
Lemma loc_add_0 l :
  l +ₗ 0 = l.
Proof.
  rewrite loc_eq_spec /=; lia.
Qed.

Definition loc_fresh (ls : gset loc) :=
  {| loc_car := set_fold (λ k r, (1 + loc_car k) `max` r) 1 ls |}.

Lemma loc_fresh_fresh ls i :
  0 ≤ i →
  loc_fresh ls +ₗ i ∉ ls.
Proof.
  intros Hi.
  cut (∀ l, l ∈ ls → loc_car l < loc_car (loc_fresh ls) + i).
  { intros help Hf%help. simpl in *. lia. }
  apply (set_fold_ind_L (λ r ls, ∀ l, l ∈ ls → (loc_car l < r + i)));
    set_solver by eauto with lia.
Qed.

#[global] Opaque loc_fresh.
