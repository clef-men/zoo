From Coq.Program Require Import
  Tactics.

From zoo Require Import
  prelude.

Ltac done :=
  stdpp.tactics.done.

Ltac goal_is_false :=
  lazymatch goal with
  | |- False => idtac
  | _ => fail
  end.

Tactic Notation "protect" ident(x) :=
  rewrite -> (lock x) in *.
Tactic Notation "protect" ident(x1) ident(x2) :=
  protect x1; protect x2.
Tactic Notation "protect" ident(x1) ident(x2) ident(x3) :=
  protect x1 x2; protect x3.
Tactic Notation "protect" ident(x1) ident(x2) ident(x3) ident(x4) :=
  protect x1 x2 x3; protect x4.
Tactic Notation "protect" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) :=
  protect x1 x2 x3 x4; protect x5.
Tactic Notation "protect" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6) :=
  protect x1 x2 x3 x4 x5; protect x6.
Tactic Notation "protect" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) :=
  protect x1 x2 x3 x4 x5 x6; protect x7.
Tactic Notation "protect" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) ident(x8) :=
  protect x1 x2 x3 x4 x5 x6 x7; protect x8.

Tactic Notation "unprotect" ident(x) :=
  rewrite <- (lock x) in *.
Tactic Notation "unprotect" ident(x1) ident(x2) :=
  unprotect x1; unprotect x2.
Tactic Notation "unprotect" ident(x1) ident(x2) ident(x3) :=
  unprotect x1 x2; unprotect x3.
Tactic Notation "unprotect" ident(x1) ident(x2) ident(x3) ident(x4) :=
  unprotect x1 x2 x3; unprotect x4.
Tactic Notation "unprotect" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) :=
  unprotect x1 x2 x3 x4; unprotect x5.
Tactic Notation "unprotect" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6) :=
  unprotect x1 x2 x3 x4 x5; unprotect x6.
Tactic Notation "unprotect" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) :=
  unprotect x1 x2 x3 x4 x5 x6; unprotect x7.
Tactic Notation "unprotect" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) ident(x8) :=
  unprotect x1 x2 x3 x4 x5 x6 x7; unprotect x8.

Tactic Notation "simplify" :=
  repeat (destruct_conjs; destruct_or?);
  simplify_eq/=.
Tactic Notation "simplify" "-" ident(x1) :=
  protect x1; simplify; unprotect x1.
Tactic Notation "simplify" "-" ident(x1) ident(x2) :=
  protect x2; simplify- x1; unprotect x2.
Tactic Notation "simplify" "-" ident(x1) ident(x2) ident(x3) :=
  protect x3; simplify- x1 x2; unprotect x3.
Tactic Notation "simplify" "-" ident(x1) ident(x2) ident(x3) ident(x4) :=
  protect x4; simplify- x1 x2 x3; unprotect x4.
Tactic Notation "simplify" "-" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) :=
  protect x5; simplify- x1 x2 x3 x4; unprotect x5.
Tactic Notation "simplify" "-" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6) :=
  protect x6; simplify- x1 x2 x3 x4 x5; unprotect x6.
Tactic Notation "simplify" "-" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) :=
  protect x7; simplify- x1 x2 x3 x4 x5; unprotect x7.
Tactic Notation "simplify" "-" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) ident(x6) ident(x7) ident(x8) :=
  protect x8; simplify- x1 x2 x3 x4 x5; unprotect x8.

Tactic Notation "invert" ident(H) "as" simple_intropattern(pat) :=
  inversion H as pat; clear H; simplify_eq/=.
Tactic Notation "invert" ident(H) :=
  invert H as [].

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
