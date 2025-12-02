From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.program_logic Require Export
  prophet_typed.
From zoo Require Import
  options.

Program Definition prophet_nat := {|
  prophet_typed_type :=
    nat ;
  prophet_typed_of_val v :=
    match v with
    | ValInt i =>
        Some (Z.to_nat i)
    | _ =>
        None
    end ;
  prophet_typed_to_val i :=
    #i ;
|}.
Solve Obligations of prophet_nat with
  try done.
Next Obligation.
  intros i v ->. rewrite /= Nat2Z.id //.
Qed.

Program Definition prophet_nat_1 := {|
  prophet_typed_1_type :=
    nat ;
  prophet_typed_1_of_val v :=
    match v with
    | ValInt i =>
        Some (Z.to_nat i)
    | _ =>
        None
    end ;
  prophet_typed_1_to_val i :=
    #i ;
|}.
Solve Obligations of prophet_nat_1 with
  try done.
Next Obligation.
  intros i v ->. rewrite /= Nat2Z.id //.
Qed.
