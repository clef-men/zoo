From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.program_logic Require Export
  identifier
  prophet_typed.
From zoo Require Import
  options.

Program Definition prophet_identifier := {|
  prophet_typed_type :=
    identifier ;
  prophet_typed_of_val v :=
    match v with
    | ValId id =>
        Some id
    | _ =>
        None
    end ;
  prophet_typed_to_val id :=
    #id ;
|}.
Solve Obligations of prophet_identifier with
  try done.
Next Obligation.
  naive_solver.
Qed.

Program Definition prophet_identifier_1 := {|
  prophet_typed_1_type :=
    identifier ;
  prophet_typed_1_of_val v :=
    match v with
    | ValId id =>
        Some id
    | _ =>
        None
    end ;
  prophet_typed_1_to_val id :=
    #id ;
|}.
Solve Obligations of prophet_identifier_1 with
  try done.
Next Obligation.
  naive_solver.
Qed.
