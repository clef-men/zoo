Require Export stdpp.binders.

Require Import zoo.prelude.
Require Export zoo.common.string.
Require Import zoo.options.

Notation "⎽" :=
  BAnon
: binder_scope.

#[global] Program Instance binderｰbeq : Beq binder :=
  {|beq bdr1 bdr2 :=
      match bdr1, bdr2 with
      | BAnon, BAnon =>
          true
      | BNamed str1, BNamed str2 =>
          str1 ≟ str2
      | _, _ =>
          false
      end
  |}.
Next Obligation.
  naive_solver.
Qed.
Next Obligation.
  naive_solver.
Qed.
Next Obligation.
  intros [] [] => //=.
  rewrite beqｰspec. naive_solver.
Qed.
