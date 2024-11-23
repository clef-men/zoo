From Coq.Strings Require Export
  Ascii.

From iris.bi Require Export
  lib.fractional.

From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo Require Import
  options.

Parameter unix_close : val.

Parameter unix_fd_model : ∀ `{zoo_G : !ZooG Σ}, val → dfrac → list ascii → iProp Σ.

Axiom unix_fd_model_fractional : ∀ `{zoo_G : !ZooG Σ} fd chars,
  Fractional (λ q, unix_fd_model fd (DfracOwn q) chars).
#[global] Existing Instance unix_fd_model_fractional.
#[global] Instance unix_fd_model_as_fractional : ∀ `{zoo_G : !ZooG Σ} fd q chars,
  AsFractional (unix_fd_model fd (DfracOwn q) chars) (λ q, unix_fd_model fd (DfracOwn q) chars) q.
Proof.
  split; [done | apply _].
Qed.

Axiom unix_close_spec : ∀ `{zoo_G : !ZooG Σ} fd chars,
  {{{
    unix_fd_model fd (DfracOwn 1) chars
  }}}
    unix_close fd
  {{{
    RET ();
    True
  }}}.
