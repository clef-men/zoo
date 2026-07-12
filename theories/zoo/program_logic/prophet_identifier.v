Require Import zoo.prelude.
Require Import zoo.language.notations.
Require Export zoo.program_logic.identifier.
Require Export zoo.program_logic.prophet_typed.
Require Import zoo.options.

Definition prophet_identifier :=
  {|prophet_typed_type :=
      identifier
  ; prophet_typed_of_val _ v :=
      match v with
      | ValId id =>
          Some $ Some id
      | _ =>
          None
      end
  |}.

Definition prophet_identifier_1 :=
  {|prophet_typed_1_type :=
      identifier
  ; prophet_typed_1_of_val _ v :=
      match v with
      | ValId id =>
          Some $ Some id
      | _ =>
          None
      end
  |}.
