Require Import zoo.prelude.
Require Import zoo.language.notations.
Require Export zoo.program_logic.prophet_typed.
Require Import zoo.options.

Definition prophet_bool :=
  {|prophet_typed۰type :=
      bool
  ; prophet_typed۰of_val _ v :=
      match v with
      | ValBool b =>
          Some $ Some b
      | _ =>
          None
      end
  |}.

Definition prophet_bool₁ :=
  {|prophet_typed₁۰type :=
      bool
  ; prophet_typed₁۰of_val _ v :=
      match v with
      | ValBool b =>
          Some $ Some b
      | _ =>
          None
      end
  |}.
