Require Export iris.algebra.frac.
Require Export iris.algebra.dfrac.
Require Export iris.bi.lib.fractional.
Require Export iris.base_logic.lib.own.

Require Import zoo.prelude.
Require Import zoo.options.

Ltac solve_inG :=
  intros;
  lazymatch goal with
  | H: subG (?xΣ _ _ _ _) _ |- _ =>
      try unfold xΣ in H
  | H: subG (?xΣ _ _ _) _ |- _ =>
      try unfold xΣ in H
  | H: subG (?xΣ _ _) _ |- _ =>
      try unfold xΣ in H
  | H: subG (?xΣ _) _ |- _ =>
      try unfold xΣ in H
  | H: subG ?xΣ _ |- _ =>
      try unfold xΣ in H
  end;
  repeat match goal with
  | H: subG (gFunctors.app _ _) _ |- _ =>
      apply subG_inv in H; destruct H
  end;
  repeat match goal with
  | H: subG _ _ |- _ =>
      move: (H);
      (apply subG_inG in H || clear H)
  end;
  intros;
  simpl in *;
  try assumption;
  esplit;
  (assumption || by apply _).
