Require Export Ltac2.Ident.
Require Export Ltac2.Init.
Require Import Ltac2.Notations.

Require Import iris.proofmode.string_ident.

Require Import zoo.prelude.
Require Import zoo.options.

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
