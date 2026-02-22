From iris.algebra Require Export
  frac
  dfrac.
From iris.bi Require Export
  lib.fractional.
From iris.base_logic Require Export
  lib.own.

From zoo Require Import
  prelude.
From zoo Require Import
  options.

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
