Require Import zoo.prelude.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.base_logic.lib.agree.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Class SavedPredG Σ A :=
  { #[local] saved_pred۰G :: AgreeG Σ (A -d> ▶ ∙)
  }.

Definition saved_pred۰Σ A :=
  #[agree۰Σ (A -d> ▶ ∙)
  ].
#[global] Instance subG𑁒saved_pred۰Σ Σ A :
  subG (saved_pred۰Σ A) Σ →
  SavedPredG Σ A.
Proof.
  solve_inG.
Qed.

Section saved_pred۰G.
  Context `{saved_pred۰G : !SavedPredG Σ A}.

  Implicit Type Ψ : A → iProp Σ.

  Definition saved_pred γ Ψ :=
    agree۰on γ (Next ∘ Ψ).

  #[global] Instance saved_pred𑁒contractive γ n :
    Proper ((pointwise_relation _ (dist_later n)) ==> (≡{n}≡)) (saved_pred γ).
  Proof.
    solve_contractive.
  Qed.
  #[global] Instance saved_pred𑁒proper γ :
    Proper ((≡) ==> (≡)) (saved_pred γ : (A -d> iProp Σ) → _).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance saved_pred𑁒persistent γ Ψ :
    Persistent (saved_pred γ Ψ).
  Proof.
    apply _.
  Qed.

  Lemma saved_pred𑁒alloc Ψ :
    ⊢ |==>
      ∃ γ,
      saved_pred γ Ψ.
  Proof.
    apply agree𑁒alloc.
  Qed.
  Lemma saved_pred𑁒alloc𑁒cofinite (γs : gset gname) Ψ :
    ⊢ |==>
      ∃ γ,
      ⌜γ ∉ γs⌝ ∗
      saved_pred γ Ψ.
  Proof.
    apply agree𑁒alloc𑁒cofinite.
  Qed.

  Lemma saved_pred𑁒agree {γ Ψ1 Ψ2} x :
    saved_pred γ Ψ1 -∗
    saved_pred γ Ψ2 -∗
    ▷ (Ψ1 x ≡ Ψ2 x).
  Proof.
    iIntros "H1 H2".
    iDestruct (agree۰on𑁒agree with "H1 H2") as "H".
    rewrite discrete_fun_equivI -later_equivI //.
  Qed.
End saved_pred۰G.

#[global] Opaque saved_pred.
