Require Import zoo.prelude.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.base_logic.lib.ghost_var.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Class GhostPredG Σ A :=
  { #[local] ghost_pred۰G۰ghost_var۰G :: GhostVarG Σ (A -d> ▶ ∙)
  }.

Definition ghost_pred۰Σ A :=
  #[ghost_var۰Σ (A -d> ▶ ∙)
  ].
#[global] Instance subGｰghost_pred۰Σ Σ A :
  subG (ghost_pred۰Σ A) Σ →
  GhostPredG Σ A.
Proof.
  solve_inG.
Qed.

Section ghost_pred۰G.
  Context `{ghost_pred۰G : !GhostPredG Σ A}.

  Implicit Type Ψ : A → iProp Σ.

  Definition ghost_pred γ dq Ψ :=
    ghost_var γ dq (Next ∘ Ψ).

  #[global] Instance ghost_predｰcontractive γ dq n :
    Proper ((pointwise_relation _ (dist_later n)) ==> (≡{n}≡)) (ghost_pred γ dq).
  Proof.
    solve_contractive.
  Qed.
  #[global] Instance ghost_predｰproper γ dq :
    Proper ((≡) ==> (≡)) (ghost_pred γ dq : (A -d> iProp Σ) → _).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance ghost_predｰpersistent γ Ψ :
    Persistent (ghost_pred γ DfracDiscarded Ψ).
  Proof.
    apply _.
  Qed.

  #[global] Instance ghost_predｰfractional γ Ψ :
    Fractional (λ q, ghost_pred γ (DfracOwn q) Ψ).
  Proof.
    apply _.
  Qed.
  #[global] Instance ghost_predｰas_fractional γ Ψ q :
    AsFractional (ghost_pred γ (DfracOwn q) Ψ) (λ q, ghost_pred γ (DfracOwn q) Ψ) q.
  Proof.
    apply _.
  Qed.

  Lemma ghost_predｰalloc Ψ :
    ⊢ |==>
      ∃ γ,
      ghost_pred γ (DfracOwn 1) Ψ.
  Proof.
    apply ghost_varｰalloc.
  Qed.
  Lemma ghost_predｰallocｰcofinite (γs : gset gname) Ψ :
    ⊢ |==>
      ∃ γ,
      ⌜γ ∉ γs⌝ ∗
      ghost_pred γ (DfracOwn 1) Ψ.
  Proof.
    apply ghost_varｰallocｰcofinite.
  Qed.

  Lemma ghost_predｰvalid γ dq Ψ :
    ghost_pred γ dq Ψ ⊢
    ⌜✓ dq⌝.
  Proof.
    apply ghost_varｰvalid.
  Qed.
  Lemma ghost_predｰcombine {γ dq1 Ψ1 dq2 Ψ2} x :
    ghost_pred γ dq1 Ψ1 -∗
    ghost_pred γ dq2 Ψ2 -∗
      ▷ (Ψ1 x ≡ Ψ2 x) ∗
      ghost_pred γ (dq1 ⋅ dq2) Ψ1.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_varｰcombine with "H1 H2") as "(? & $)".
    rewrite -later_equivI discrete_fun_equivI //.
  Qed.
  Lemma ghost_predｰvalidｰ2 {γ dq1 Ψ1 dq2 Ψ2} x :
    ghost_pred γ dq1 Ψ1 -∗
    ghost_pred γ dq2 Ψ2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ▷ (Ψ1 x ≡ Ψ2 x).
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_predｰcombine with "H1 H2") as "($ & H)".
    iApply (ghost_varｰvalid with "H").
  Qed.
  Lemma ghost_predｰagree {γ dq1 Ψ1 dq2 Ψ2} x :
    ghost_pred γ dq1 Ψ1 -∗
    ghost_pred γ dq2 Ψ2 -∗
    ▷ (Ψ1 x ≡ Ψ2 x).
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_predｰvalidｰ2 with "H1 H2") as "(_ & $)".
  Qed.
  Lemma ghost_predｰdfracｰne γ1 dq1 Ψ1 γ2 dq2 Ψ2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    ghost_pred γ1 dq1 Ψ1 -∗
    ghost_pred γ2 dq2 Ψ2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply ghost_varｰdfracｰne.
  Qed.
  Lemma ghost_predｰne γ1 Ψ1 γ2 dq2 Ψ2 :
    ghost_pred γ1 (DfracOwn 1) Ψ1 -∗
    ghost_pred γ2 dq2 Ψ2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply ghost_varｰne.
  Qed.
  Lemma ghost_predｰexclusive γ Ψ1 dq2 Ψ2 :
    ghost_pred γ (DfracOwn 1) Ψ1 -∗
    ghost_pred γ dq2 Ψ2 -∗
    False.
  Proof.
    apply ghost_varｰexclusive.
  Qed.
  Lemma ghost_predｰpersist γ dq Ψ :
    ghost_pred γ dq Ψ ⊢ |==>
    ghost_pred γ DfracDiscarded Ψ.
  Proof.
    apply ghost_varｰpersist.
  Qed.

  Lemma ghost_predｰupdate {γ Ψ} Ψ' :
    ghost_pred γ (DfracOwn 1) Ψ ⊢ |==>
    ghost_pred γ (DfracOwn 1) Ψ'.
  Proof.
    apply ghost_varｰupdate.
  Qed.
End ghost_pred۰G.

#[global] Opaque ghost_pred.
