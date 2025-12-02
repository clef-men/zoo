From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.program_logic Require Export
  prophet_typed.
From zoo Require Import
  options.

Program Definition prophet_bool := {|
  prophet_typed_type :=
    bool ;
  prophet_typed_of_val v :=
    match v with
    | ValBool b =>
        Some b
    | _ =>
        None
    end ;
  prophet_typed_to_val b :=
    #b ;
|}.
Solve Obligations of prophet_bool with
  try done.
Next Obligation.
  naive_solver.
Qed.

Program Definition prophet_bool_1 := {|
  prophet_typed_1_type :=
    bool ;
  prophet_typed_1_of_val v :=
    match v with
    | ValBool b =>
        Some b
    | _ =>
        None
    end ;
  prophet_typed_1_to_val b :=
    #b ;
|}.
Solve Obligations of prophet_bool_1 with
  try done.
Next Obligation.
  naive_solver.
Qed.
