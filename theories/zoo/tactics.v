Require Import Stdlib.Program.Tactics.

Require Import zoo.prelude.

Ltac done :=
  stdpp.tactics.done.

Tactic Notation "simp" :=
  repeat (destruct_conjs; destruct_or?);
  simplify_eq/=.

Tactic Notation "inv" "/=" ident(H) "as" simple_intropattern(pat) :=
  inversion H as pat; clear H; simplify_eq/=.
Tactic Notation "inv" "/=" ident(H) :=
  inv/= H as [].

Tactic Notation "solve_proper+" :=
  solve_proper_core ltac:(fun _ => f_equiv || solve_proper_prepare).

Tactic Notation "Z_to_nat" ident(x) :=
  let y := fresh x in
  rename x into y;
  destruct (Z_of_nat_complete y) as (x & ->); first lia;
  try clear y.
Tactic Notation "Z_to_nat" ident(x) "as" ident(y) :=
  Z_to_nat x;
  rename x into y.

Tactic Notation "destruct_decide" constr(P) "as" simple_intropattern(pat1) "|" simple_intropattern(pat2) :=
  destruct (decide P) as [pat1 | pat2].
Tactic Notation "destruct_decide" constr(P) "as" simple_intropattern(pat) :=
  destruct_decide P as pat | pat.
Tactic Notation "destruct_decide" constr(P) :=
  let H := fresh "H" in
  destruct_decide P as H | H.

Tactic Notation "case_decide" "as" "[" simple_intropattern(pat1) "|" simple_intropattern(pat2) "]" :=
  let H := fresh in
  case_decide as H;
  move: H;
  [ intros pat1
  | intros pat2
  ].
