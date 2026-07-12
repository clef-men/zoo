Require Export stdpp.strings.

Require Import zoo.prelude.
Require Export zoo.common.typeclasses.
Require Import zoo.options.

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

#[global] Program Instance string_beq : Beq string :=
  {|beq := String.eqb
  |}.
Next Obligation.
  apply String.eqb_eq.
Qed.
