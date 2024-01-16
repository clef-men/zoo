From Coq.Strings Require Export
  Ascii.

From zebra Require Import
  prelude.
From zebra.language Require Import
  notations
  diaframe.
From zebra.std Require Export
  base.
From zebra Require Import
  options.

Parameter unix_close : val.

Parameter unix_fd_model : ∀ `{zebra_G : !ZebraG Σ}, val → dfrac → list ascii → iProp Σ.

Axiom unix_fd_model_fractional : ∀ `{zebra_G : !ZebraG Σ} fd chars,
  Fractional (λ q, unix_fd_model fd (DfracOwn q) chars).
#[global] Existing Instance unix_fd_model_fractional.
#[global] Instance unix_fd_model_as_fractional : ∀ `{zebra_G : !ZebraG Σ} fd q chars,
  AsFractional (unix_fd_model fd (DfracOwn q) chars) (λ q, unix_fd_model fd (DfracOwn q) chars) q.
Proof.
  split; [done | apply _].
Qed.

Axiom unix_close_spec : ∀ `{zebra_G : !ZebraG Σ} fd chars,
  {{{
    unix_fd_model fd (DfracOwn 1) chars
  }}}
    unix_close fd
  {{{
    RET #(); True
  }}}.
