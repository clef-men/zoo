Require Import zoo.prelude.
Require Import zoo.language.notations.
Require Export zoo.program_logic.identifier.
Require Export zoo.program_logic.prophet_typed.
Require Import zoo.options.

Definition prophet_identifier :=
  {|prophet_typed۰type :=
      identifier
  ; prophet_typed۰of_val _ v :=
      match v with
      | ValId id =>
          Some $ Some id
      | _ =>
          None
      end
  |}.

Definition prophet_identifier₁ :=
  {|prophet_typed₁۰type :=
      identifier
  ; prophet_typed₁۰of_val _ v :=
      match v with
      | ValId id =>
          Some $ Some id
      | _ =>
          None
      end
  |}.
