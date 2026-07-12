Require Import zoo.prelude.
Require Import zoo.language.notations.
Require Export zoo.program_logic.prophet_typed.
Require Import zoo.options.

Definition prophet_bool :=
  {|prophet_typed_type :=
      bool
  ; prophet_typed_of_val _ v :=
      match v with
      | ValBool b =>
          Some $ Some b
      | _ =>
          None
      end
  |}.

Definition prophet_bool_1 :=
  {|prophet_typed_1_type :=
      bool
  ; prophet_typed_1_of_val _ v :=
      match v with
      | ValBool b =>
          Some $ Some b
      | _ =>
          None
      end
  |}.
