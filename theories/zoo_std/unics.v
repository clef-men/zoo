From Coq.Strings Require Export
  Ascii.

From zoo Require Import
  prelude.
From zoo.language Require Import
  notations
  diaframe.
From zoo_std Require Export
  base.
From zoo Require Import
  options.

Parameter unics_close : val.

Parameter unics_fd_model : ∀ `{zoo_G : !ZooG Σ}, val → dfrac → list ascii → iProp Σ.

Axiom unics_fd_model_fractional : ∀ `{zoo_G : !ZooG Σ} fd chars,
  Fractional (λ q, unics_fd_model fd (DfracOwn q) chars).
#[global] Existing Instance unics_fd_model_fractional.
#[global] Instance unics_fd_model_as_fractional : ∀ `{zoo_G : !ZooG Σ} fd q chars,
  AsFractional (unics_fd_model fd (DfracOwn q) chars) (λ q, unics_fd_model fd (DfracOwn q) chars) q.
Proof.
  split; [done | apply _].
Qed.

Axiom unics_close_spec : ∀ `{zoo_G : !ZooG Σ} fd chars,
  {{{
    unics_fd_model fd (DfracOwn 1) chars
  }}}
    unics_close fd
  {{{
    RET ();
    True
  }}}.
