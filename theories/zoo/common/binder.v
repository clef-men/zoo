From stdpp Require Export
  binders.

From zoo Require Import
  prelude.
From zoo.common Require Export
  string.
From zoo Require Import
  options.

#[global] Program Instance binder_beq : Beq binder := {|
  beq bdr1 bdr2 :=
    match bdr1, bdr2 with
    | BAnon, BAnon =>
        true
    | BNamed str1, BNamed str2 =>
        str1 ≟ str2
    | _, _ =>
        false
    end ;
|}.
Next Obligation.
  naive_solver.
Qed.
Next Obligation.
  naive_solver.
Qed.
Next Obligation.
  intros [] [] => //=.
  rewrite beq_spec. naive_solver.
Qed.
