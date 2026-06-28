From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.program_logic Require Export
  prophet_typed.
From zoo Require Import
  options.

Definition prophet_nat :=
  {|prophet_typed_type :=
      nat
  ; prophet_typed_of_val _ v :=
      match v with
      | ValInt i =>
          Some $ Some $ Z.to_nat i
      | _ =>
          None
      end
  |}.

Definition prophet_nat_1 :=
  {|prophet_typed_1_type :=
      nat
  ; prophet_typed_1_of_val _ v :=
      match v with
      | ValInt i =>
          Some $ Some $ Z.to_nat i
      | _ =>
          None
      end
  |}.
