From stdpp Require Export
  binders.

From zoo Require Import
  prelude.
From zoo Require Import
  options.

Definition binder_eqb bdr1 bdr2 :=
  match bdr1, bdr2 with
  | BAnon, BAnon =>
      true
  | BNamed str1, BNamed str2 =>
      String.eqb str1 str2
  | _, _ =>
      false
  end.
#[global] Arguments binder_eqb !_ !_ / : assert.

Definition binder_neqb bdr1 bdr2 :=
  negb (binder_eqb bdr1 bdr2).
