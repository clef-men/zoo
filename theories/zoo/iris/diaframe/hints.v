Require Import diaframe.proofmode_base.

Require Import zoo.prelude.
Require Export zoo.iris.diaframe.base.
Require Import zoo.options.

Section big_sepM.
  Context {PROP : bi}.
  Context `{Countable K}.
  Context {V : Type}.

  Implicit Type Φ : K → V → PROP.

  #[global] Instance diahintｰbig_sepMｰempty Φ :
    HINT ε₀ ✱ [- ;
      emp
    ] ⊫ [id];
      [∗ map] k ↦ v ∈ ∅, Φ k v
    ✱ [
      emp
    ].
  Proof.
    iSteps. rewrite big_sepM_empty. iSteps.
  Qed.
End big_sepM.

Section big_sepS.
  Context {PROP : bi}.
  Context `{Countable K}.

  Implicit Type Φ : K → PROP.

  #[global] Instance diahintｰbig_sepSｰempty Φ :
    HINT ε₀ ✱ [- ;
      emp
    ] ⊫ [id];
      [∗ set] k ∈ ∅, Φ k
    ✱ [
      emp
    ].
  Proof.
    iSteps. rewrite big_sepS_empty. iSteps.
  Qed.
End big_sepS.
