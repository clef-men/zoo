Require Import stdpp.gmap.

Require Import iris.algebra.ofe.

Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.options.

#[local] Open Scope Z_scope.

Record location := Loc
  { location۰car : Z
  }.
Add Printing Constructor location.

Canonical location۰O {SI : sidx} :=
  leibnizO location.

Lemma locationｰeqｰspec l1 l2 :
  l1 = l2 ↔
  location۰car l1 = location۰car l2.
Proof.
  destruct l1, l2; naive_solver.
Qed.

#[global] Instance locationｰinhabited : Inhabited location :=
  populate {| location۰car := 0 |}.
#[global] Instance locationｰeq_dec : EqDecision location :=
  ltac:(solve_decision).
#[global] Instance locationｰcountable :
  Countable location.
Proof.
  solve_countable.
Qed.

#[global] Program Instance locationｰinfinite : Infinite location :=
  inj_infinite (λ p, {| location۰car := p |}) (λ l, Some (location۰car l)) _.
Next Obligation.
  done.
Qed.

Definition location۰add l i :=
  {| location۰car := location۰car l + i |}.

Notation "l +ₗ i" := (
  location۰add l i
)(at level 50,
  left associativity
) : stdpp_scope.

#[global] Instance location۰addｰinj₁ l :
  Inj (=) (=) (location۰add l).
Proof.
  intros ?*. rewrite locationｰeqｰspec /=. lia.
Qed.
#[global] Instance location۰addｰinj₂ i :
  Inj (=) (=) (λ l, location۰add l i).
Proof.
  intros ?*. rewrite locationｰeqｰspec Z.add_cancel_r locationｰeqｰspec //.
Qed.
Lemma location۰addｰassoc l i j :
  l +ₗ i +ₗ j = l +ₗ (i + j).
Proof.
  rewrite locationｰeqｰspec /=. lia.
Qed.
Lemma location۰addｰ0 l :
  l +ₗ 0 = l.
Proof.
  rewrite locationｰeqｰspec /=; lia.
Qed.

Definition location۰fresh (ls : gset location) :=
  {| location۰car := set_fold (λ k r, (1 + location۰car k) `max` r) 1 ls |}.

Lemma location۰freshｰfresh ls i :
  0 ≤ i →
  location۰fresh ls +ₗ i ∉ ls.
Proof.
  intros Hi.
  enough (∀ l, l ∈ ls → location۰car l < location۰car (location۰fresh ls) + i).
  { naive_solver lia. }
  apply (set_fold_ind_L (λ r ls, ∀ l, l ∈ ls → (location۰car l < r + i))).
  all: set_solver by eauto with lia.
Qed.

#[global] Opaque location۰fresh.
