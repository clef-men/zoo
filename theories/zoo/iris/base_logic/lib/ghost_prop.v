Require Import zoo.prelude.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.base_logic.lib.ghost_var.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Class GhostPropG Σ :=
  { #[local] ghost_prop۰G۰ghost_var۰G :: GhostVarG Σ (▶ ∙)
  }.

Definition ghost_prop۰Σ :=
  #[ghost_var۰Σ (▶ ∙)
  ].
#[global] Instance subG𑁒ghost_prop۰Σ Σ :
  subG ghost_prop۰Σ Σ →
  GhostPropG Σ.
Proof.
  solve_inG.
Qed.

Section ghost_prop۰G.
  Context `{ghost_prop۰G : !GhostPropG Σ}.

  Implicit Types P : iProp Σ.

  Definition ghost_prop γ dq P :=
    ghost_var γ dq (Next P).

  #[global] Instance ghost_prop𑁒contractive γ dq :
    Contractive (ghost_prop γ dq).
  Proof.
    solve_contractive.
  Qed.
  #[global] Instance ghost_prop𑁒proper γ dq :
    Proper ((≡) ==> (≡)) (ghost_prop γ dq).
  Proof.
    apply _.
  Qed.

  #[global] Instance ghost_prop𑁒persistent γ P :
    Persistent (ghost_prop γ DfracDiscarded P).
  Proof.
    apply _.
  Qed.

  #[global] Instance ghost_prop𑁒fractional γ P :
    Fractional (λ q, ghost_prop γ (DfracOwn q) P).
  Proof.
    apply _.
  Qed.
  #[global] Instance ghost_prop𑁒as_fractional γ P q :
    AsFractional (ghost_prop γ (DfracOwn q) P) (λ q, ghost_prop γ (DfracOwn q) P) q.
  Proof.
    apply _.
  Qed.

  Lemma ghost_prop𑁒alloc P :
    ⊢ |==>
      ∃ γ,
      ghost_prop γ (DfracOwn 1) P.
  Proof.
    apply ghost_var𑁒alloc.
  Qed.
  Lemma ghost_prop𑁒alloc𑁒cofinite (γs : gset gname) P :
    ⊢ |==>
      ∃ γ,
      ⌜γ ∉ γs⌝ ∗
      ghost_prop γ (DfracOwn 1) P.
  Proof.
    apply ghost_var𑁒alloc𑁒cofinite.
  Qed.

  Lemma ghost_prop𑁒valid γ dq P :
    ghost_prop γ dq P ⊢
    ⌜✓ dq⌝.
  Proof.
    apply ghost_var𑁒valid.
  Qed.
  Lemma ghost_prop𑁒combine γ dq1 P1 dq2 P2 :
    ghost_prop γ dq1 P1 -∗
    ghost_prop γ dq2 P2 -∗
      ▷ (P1 ≡ P2) ∗
      ghost_prop γ (dq1 ⋅ dq2) P1.
  Proof.
    rewrite -later_equivI.
    apply: ghost_var𑁒combine.
  Qed.
  Lemma ghost_prop𑁒valid𑁒2 γ dq1 P1 dq2 P2 :
    ghost_prop γ dq1 P1 -∗
    ghost_prop γ dq2 P2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ▷ (P1 ≡ P2).
  Proof.
    rewrite -later_equivI.
    apply: ghost_var𑁒valid𑁒2.
  Qed.
  Lemma ghost_prop𑁒agree γ dq1 P1 dq2 P2 :
    ghost_prop γ dq1 P1 -∗
    ghost_prop γ dq2 P2 -∗
    ▷ (P1 ≡ P2).
  Proof.
    rewrite -later_equivI.
    apply: ghost_var𑁒agree.
  Qed.
  Lemma ghost_prop𑁒dfrac𑁒ne γ1 dq1 P1 γ2 dq2 P2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    ghost_prop γ1 dq1 P1 -∗
    ghost_prop γ2 dq2 P2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply ghost_var𑁒dfrac𑁒ne.
  Qed.
  Lemma ghost_prop𑁒ne γ1 P1 γ2 dq2 P2 :
    ghost_prop γ1 (DfracOwn 1) P1 -∗
    ghost_prop γ2 dq2 P2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply ghost_var𑁒ne.
  Qed.
  Lemma ghost_prop𑁒exclusive γ P1 dq2 P2 :
    ghost_prop γ (DfracOwn 1) P1 -∗
    ghost_prop γ dq2 P2 -∗
    False.
  Proof.
    apply ghost_var𑁒exclusive.
  Qed.
  Lemma ghost_prop𑁒persist γ dq P :
    ghost_prop γ dq P ⊢ |==>
    ghost_prop γ DfracDiscarded P.
  Proof.
    apply ghost_var𑁒persist.
  Qed.

  Lemma ghost_prop𑁒update {γ P} P' :
    ghost_prop γ (DfracOwn 1) P ⊢ |==>
    ghost_prop γ (DfracOwn 1) P'.
  Proof.
    apply ghost_var𑁒update.
  Qed.
End ghost_prop۰G.

#[global] Opaque ghost_prop.
