Require Export Stdlib.Strings.Ascii.

Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo.options.

Parameter unix٠close : val.

Parameter unix۰fd_model : ∀ `{zoo۰G : !ZooG Σ}, val → dfrac → list ascii → iProp Σ.

Axiom unix۰fd_model𑁒fractional : ∀ `{zoo۰G : !ZooG Σ} fd chars,
  Fractional (λ q, unix۰fd_model fd (DfracOwn q) chars).
#[global] Existing Instance unix۰fd_model𑁒fractional.
#[global] Instance unix۰fd_model𑁒as_fractional : ∀ `{zoo۰G : !ZooG Σ} fd q chars,
  AsFractional (unix۰fd_model fd (DfracOwn q) chars) (λ q, unix۰fd_model fd (DfracOwn q) chars) q.
Proof.
  split; [done | apply _].
Qed.

Axiom unix٠close𑁒spec : ∀ `{zoo۰G : !ZooG Σ} fd chars,
  {{{
    unix۰fd_model fd (DfracOwn 1) chars
  }}}
    unix٠close fd
  {{{
    RET ();
    True
  }}}.
#[global] Instance unix٠close𑁒diaspec `{zoo۰G : !ZooG Σ} fd chars :
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
  wp۰apply (unix٠close𑁒spec with "Hfd HΦ").
Qed.
