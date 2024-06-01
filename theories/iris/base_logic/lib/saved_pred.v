From zoo Require Import
  prelude.
From zoo.iris.base_logic Require Export
  lib.base.
From zoo.iris.base_logic Require Import
  lib.agree.
From zoo.iris Require Import
  diaframe.
From zoo Require Import
  options.

Class SavedPredG Σ A := {
  #[local] saved_pred_G :: AgreeG Σ (A -d> ▶ ∙) ;
}.

Definition saved_pred_Σ A := #[
  agree_Σ (A -d> ▶ ∙)
].
#[global] Instance subG_saved_pred_Σ Σ A :
  subG (saved_pred_Σ A) Σ →
  SavedPredG Σ A.
Proof.
  solve_inG.
Qed.

Section saved_pred_G.
  Context `{saved_pred_G : !SavedPredG Σ A}.

  Implicit Types Ψ : A → iProp Σ.

  Definition saved_pred γ Ψ :=
    agree_on γ (Next ∘ Ψ).

  #[global] Instance saved_pred_proper γ :
    Proper ((≡) ==> (≡)) (saved_pred γ : (A -d> iProp Σ) → _).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance saved_pred_persistent γ Ψ :
    Persistent (saved_pred γ Ψ).
  Proof.
    apply _.
  Qed.

  Lemma saved_pred_alloc Ψ :
    ⊢ |==>
      ∃ γ,
      saved_pred γ Ψ.
  Proof.
    apply agree_alloc.
  Qed.
  Lemma saved_pred_alloc_cofinite (γs : gset gname) Ψ :
    ⊢ |==>
      ∃ γ,
      ⌜γ ∉ γs⌝ ∗
      saved_pred γ Ψ.
  Proof.
    apply agree_alloc_cofinite.
  Qed.

  Lemma saved_pred_agree {γ Ψ1 Ψ2} x :
    saved_pred γ Ψ1 -∗
    saved_pred γ Ψ2 -∗
    ▷ (Ψ1 x ≡ Ψ2 x).
  Proof.
    iIntros "H1 H2".
    iDestruct (agree_on_agree with "H1 H2") as "H".
    rewrite discrete_fun_equivI -later_equivI //.
  Qed.
End saved_pred_G.

#[global] Opaque saved_pred.
