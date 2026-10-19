Require Export stdpp.strings.

Require Import zoo.prelude.
Require Export zoo.common.typeclasses.
Require Import zoo.options.

Fixpoint string۰repeat n chr :=
  if n is ˖n then
    String chr (string۰repeat n chr)
  else
    "".

Lemma string۰repeatｰlength n chr :
  String.length (string۰repeat n chr) = n.
Proof.
  induction n; naive.
Qed.

Fixpoint string۰set' i chr str acc :=
  match str with
  | "" =>
      None
  | String chr' str =>
      if i is ˖i then
        string۰set' i chr str (String chr' acc)
      else
        Some $ String.rev_app acc (String chr str)
  end.
Definition string۰set i chr str :=
  string۰set' i chr str "".

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

#[global] Program Instance stringｰbeq : Beq string :=
  {|beq := String.eqb
  |}.
Next Obligation.
  apply String.eqb_eq.
Qed.
