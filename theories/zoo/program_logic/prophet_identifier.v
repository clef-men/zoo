From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.program_logic Require Export
  identifier
  prophet_typed.
From zoo Require Import
  options.

Definition prophet_identifier :=
  {|prophet_typed_type :=
      identifier
  ; prophet_typed_of_val _ v :=
      match v with
      | ValId id =>
          Some id
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
          Some id
      | _ =>
          None
      end
  |}.
