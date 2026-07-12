Require Export Ltac2.Init.
Require Export Ltac2.Message.

Require Import zoo.prelude.
Require Import zoo.options.

Ltac2 print_string str :=
  print (of_string str).
Ltac2 print_constr constr :=
  print (of_constr constr).
Ltac2 print_ident id :=
  print (of_ident id).
