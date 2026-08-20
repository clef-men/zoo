Require Import zoo.prelude.
Require Export zoo.common.ascii.
Require Import zoo.base.
Require Import zoo.options.

Parameter unix٠close : val.

Parameter unix۰fd_model : ∀ `{zoo۰G : !ZooG Σ}, val → dfrac → list ascii → iProp Σ.

Axiom unix۰fd_modelｰfractional : ∀ `{zoo۰G : !ZooG Σ} fd chars,
  Fractional (λ q, unix۰fd_model fd (DfracOwn q) chars).
#[global] Existing Instance unix۰fd_modelｰfractional.
#[global] Instance unix۰fd_modelｰas_fractional : ∀ `{zoo۰G : !ZooG Σ} fd q chars,
  AsFractional (unix۰fd_model fd (DfracOwn q) chars) (λ q, unix۰fd_model fd (DfracOwn q) chars) q.
Proof.
  split; [done | apply _].
Qed.

Axiom unix٠closeｰspec : ∀ `{zoo۰G : !ZooG Σ} fd chars,
  {{{
    unix۰fd_model fd (DfracOwn 1) chars
  }}}
    unix٠close fd
  {{{
    RET ();
    True
  }}}.
#[global] Instance unix٠closeｰdiaspec `{zoo۰G : !ZooG Σ} fd chars :
  DIASPEC
  {{
    unix۰fd_model fd (DfracOwn 1) chars
  }}
    unix٠close fd
  {{
    RET ();
    True
  }}.
Proof.
  iSteps as (Φ) "Hfd HΦ".
  wp۰apply (unix٠closeｰspec with "Hfd HΦ").
Qed.
