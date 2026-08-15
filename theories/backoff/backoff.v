Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo.options.

Parameter backoff٠default : val.
Parameter backoff٠once : val.

Parameter backoff۰model : ∀ `{zoo۰G : !ZooG Σ}, val → iProp Σ.

Axiom backoff٠defaultｰspec : ∀ `{zoo۰G : !ZooG Σ},
  ⊢ backoff۰model backoff٠default.
#[global] Instance diahintｰbackoff٠default `{zoo۰G : !ZooG Σ} :
  HINT ε₀ ✱ [- ;
    emp
  ] ⊫ [id];
    backoff۰model backoff٠default
  ✱ [
    emp
  ].
Proof.
  rewrite -backoff٠defaultｰspec. iSteps.
Qed.

Axiom backoff٠onceｰspec : ∀ `{zoo۰G : !ZooG Σ} t,
  {{{
    backoff۰model t
  }}}
    backoff٠once t
  {{{
    t
  , RET t;
    backoff۰model t
  }}}.
#[global] Instance backoff٠onceｰdiaspec `{zoo۰G : !ZooG Σ} t :
  DIASPEC
  {{
    backoff۰model t
  }}
    backoff٠once t
  {{
    t
  , RET t;
    backoff۰model t
  }}.
Proof.
  iSteps as (Φ) "Ht HΦ".
  wp۰apply (backoff٠onceｰspec with "Ht HΦ").
Qed.
