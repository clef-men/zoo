From Coq.Strings Require Export
  Ascii.

From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Export
  base.
From zebre Require Import
  options.

Parameter unix_close : val.

Parameter unix_fd_model : ∀ `{zebre_G : !ZebreG Σ}, val → dfrac → list ascii → iProp Σ.

Axiom unix_fd_model_fractional : ∀ `{zebre_G : !ZebreG Σ} fd chars,
  Fractional (λ q, unix_fd_model fd (DfracOwn q) chars).
#[global] Existing Instance unix_fd_model_fractional.
#[global] Instance unix_fd_model_as_fractional : ∀ `{zebre_G : !ZebreG Σ} fd q chars,
  AsFractional (unix_fd_model fd (DfracOwn q) chars) (λ q, unix_fd_model fd (DfracOwn q) chars) q.
Proof.
  split; [done | apply _].
Qed.

Axiom unix_close_spec : ∀ `{zebre_G : !ZebreG Σ} fd chars,
  {{{
    unix_fd_model fd (DfracOwn 1) chars
  }}}
    unix_close fd
  {{{
    RET #(); True
  }}}.
