From stdpp Require Export
  strings.

From zoo Require Import
  prelude.
From zoo.common Require Export
  typeclasses.
From zoo Require Import
  options.

#[local] Fixpoint split_on_go chr str acc :=
  match str with
  | "" =>
      (String.rev acc, None)
  | String chr' str =>
      if Ascii.eqb chr chr' then
        (String.rev acc, Some str)
      else
        split_on_go chr str (String chr' acc)
  end.
Definition split_on chr str :=
  split_on_go chr str "".

#[global] Program Instance string_beq : Beq string := {|
  beq := String.eqb ;
|}.
Next Obligation.
  apply String.eqb_eq.
Qed.
