Require Export Stdlib.Strings.Ascii.

Require Import zoo.prelude.
Require Import zoo.language.notations.
Require Export zoo.program_logic.wp.
Require Import zoo.diaframe.
Require Import zoo.options.

Parameter unix٠close : val.

Parameter unix_fd_model : ∀ `{zoo_G : !ZooG Σ}, val → dfrac → list ascii → iProp Σ.

Axiom unix_fd_model_fractional : ∀ `{zoo_G : !ZooG Σ} fd chars,
  Fractional (λ q, unix_fd_model fd (DfracOwn q) chars).
#[global] Existing Instance unix_fd_model_fractional.
#[global] Instance unix_fd_model_as_fractional : ∀ `{zoo_G : !ZooG Σ} fd q chars,
  AsFractional (unix_fd_model fd (DfracOwn q) chars) (λ q, unix_fd_model fd (DfracOwn q) chars) q.
Proof.
  split; [done | apply _].
Qed.

Axiom unix٠close𑁒spec : ∀ `{zoo_G : !ZooG Σ} fd chars,
  {{{
    unix_fd_model fd (DfracOwn 1) chars
  }}}
    unix٠close fd
  {{{
    RET ();
    True
  }}}.
#[global] Instance unix٠close𑁒diaspec `{zoo_G : !ZooG Σ} fd chars :
  DIASPEC
  {{
    unix_fd_model fd (DfracOwn 1) chars
  }}
    unix٠close fd
  {{
    RET ();
    True
  }}.
Proof.
  iSteps as (Φ) "Hfd HΦ".
  wp_apply (unix٠close𑁒spec with "Hfd HΦ").
Qed.
