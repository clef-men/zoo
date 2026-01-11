From Ltac2 Require Export
  Ident
  Init.
From Ltac2 Require Import
  Notations.

From iris.proofmode Require Import
  string_ident.

From zoo Require Import
  prelude.
From zoo Require Import
  options.

Ltac2 of_coq_string :=
  StringToIdent.coq_string_to_ident.
Ltac2 rec of_coq_strings idents :=
  lazy_match! idents with
  | nil =>
      []
  | cons ?ident ?idents =>
      let t := of_coq_string ident in
      let ts := of_coq_strings idents in
      t :: ts
  end.
