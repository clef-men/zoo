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
#[global] Instance subGｰghost_prop۰Σ Σ :
  subG ghost_prop۰Σ Σ →
  GhostPropG Σ.
Proof.
  solve_inG.
Qed.

Section ghost_prop۰G.
  Context `{ghost_prop۰G : !GhostPropG Σ}.

  Implicit Type P : iProp Σ.

  Definition ghost_prop γ dq P :=
    ghost_var γ dq (Next P).

  #[global] Instance ghost_propｰcontractive γ dq :
    Contractive (ghost_prop γ dq).
  Proof.
    solve_contractive.
  Qed.
  #[global] Instance ghost_propｰproper γ dq :
    Proper ((≡) ==> (≡)) (ghost_prop γ dq).
  Proof.
    apply _.
  Qed.

  #[global] Instance ghost_propｰpersistent γ P :
    Persistent (ghost_prop γ DfracDiscarded P).
  Proof.
    apply _.
  Qed.

  #[global] Instance ghost_propｰfractional γ P :
    Fractional (λ q, ghost_prop γ (DfracOwn q) P).
  Proof.
    apply _.
  Qed.
  #[global] Instance ghost_propｰas_fractional γ P q :
    AsFractional (ghost_prop γ (DfracOwn q) P) (λ q, ghost_prop γ (DfracOwn q) P) q.
  Proof.
    apply _.
  Qed.

  Lemma ghost_propｰalloc P :
    ⊢ |==>
      ∃ γ,
      ghost_prop γ (DfracOwn 1) P.
  Proof.
    apply ghost_varｰalloc.
  Qed.
  Lemma ghost_propｰallocｰcofinite (γs : gset gname) P :
    ⊢ |==>
      ∃ γ,
      ⌜γ ∉ γs⌝ ∗
      ghost_prop γ (DfracOwn 1) P.
  Proof.
    apply ghost_varｰallocｰcofinite.
  Qed.

  Lemma ghost_propｰvalid γ dq P :
    ghost_prop γ dq P ⊢
    ⌜✓ dq⌝.
  Proof.
    apply ghost_varｰvalid.
  Qed.
  Lemma ghost_propｰcombine γ dq1 P1 dq2 P2 :
    ghost_prop γ dq1 P1 -∗
    ghost_prop γ dq2 P2 -∗
      ▷ (P1 ≡ P2) ∗
      ghost_prop γ (dq1 ⋅ dq2) P1.
  Proof.
    rewrite -later_equivI.
    apply: ghost_varｰcombine.
  Qed.
  Lemma ghost_propｰvalidｰ2 γ dq1 P1 dq2 P2 :
    ghost_prop γ dq1 P1 -∗
    ghost_prop γ dq2 P2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ▷ (P1 ≡ P2).
  Proof.
    rewrite -later_equivI.
    apply: ghost_varｰvalidｰ2.
  Qed.
  Lemma ghost_propｰagree γ dq1 P1 dq2 P2 :
    ghost_prop γ dq1 P1 -∗
    ghost_prop γ dq2 P2 -∗
    ▷ (P1 ≡ P2).
  Proof.
    rewrite -later_equivI.
    apply: ghost_varｰagree.
  Qed.
  Lemma ghost_propｰdfracｰne γ1 dq1 P1 γ2 dq2 P2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    ghost_prop γ1 dq1 P1 -∗
    ghost_prop γ2 dq2 P2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply ghost_varｰdfracｰne.
  Qed.
  Lemma ghost_propｰne γ1 P1 γ2 dq2 P2 :
    ghost_prop γ1 (DfracOwn 1) P1 -∗
    ghost_prop γ2 dq2 P2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply ghost_varｰne.
  Qed.
  Lemma ghost_propｰexclusive γ P1 dq2 P2 :
    ghost_prop γ (DfracOwn 1) P1 -∗
    ghost_prop γ dq2 P2 -∗
    False.
  Proof.
    apply ghost_varｰexclusive.
  Qed.
  Lemma ghost_propｰpersist γ dq P :
    ghost_prop γ dq P ⊢ |==>
    ghost_prop γ DfracDiscarded P.
  Proof.
    apply ghost_varｰpersist.
  Qed.

  Lemma ghost_propｰupdate {γ P} P' :
    ghost_prop γ (DfracOwn 1) P ⊢ |==>
    ghost_prop γ (DfracOwn 1) P'.
  Proof.
    apply ghost_varｰupdate.
  Qed.
End ghost_prop۰G.

#[global] Opaque ghost_prop.
