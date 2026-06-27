From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.program_logic Require Export
  prophet_typed.
From zoo Require Import
  options.

Definition prophet_bool :=
  {|prophet_typed_type :=
      bool
  ; prophet_typed_of_val _ v :=
      match v with
      | ValBool b =>
          Some b
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
          Some b
      | _ =>
          None
      end
  |}.
