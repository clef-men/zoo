From Ltac2 Require Export
  Init
  Message.

From zoo Require Import
  prelude.
From zoo Require Import
  options.

Ltac2 print_string str :=
  print (of_string str).
Ltac2 print_constr constr :=
  print (of_constr constr).
Ltac2 print_ident id :=
  print (of_ident id).
