Require Import zoo.prelude.
Require Import zoo.language.notations.
Require Export zoo.program_logic.prophet_typed.
Require Import zoo.options.

Definition prophet_nat :=
  {|prophet_typed۰type :=
      nat
  ; prophet_typed۰of_val _ v :=
      match v with
      | ValInt i =>
          Some $ Some $ Z.to_nat i
      | _ =>
          None
      end
  |}.

Definition prophet_nat₁ :=
  {|prophet_typed₁۰type :=
      nat
  ; prophet_typed₁۰of_val _ v :=
      match v with
      | ValInt i =>
          Some $ Some $ Z.to_nat i
      | _ =>
          None
      end
  |}.
