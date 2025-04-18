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

Class SavedPropG Σ := {
  #[local] saved_prop_G :: AgreeG Σ (▶ ∙) ;
}.

Definition saved_prop_Σ := #[
  agree_Σ (▶ ∙)
].
#[global] Instance subG_saved_prop_Σ Σ :
  subG saved_prop_Σ Σ →
  SavedPropG Σ.
Proof.
  solve_inG.
Qed.

Section saved_prop_G.
  Context `{saved_prop_G : !SavedPropG Σ}.

  Implicit Types P : iProp Σ.

  Definition saved_prop γ P :=
    agree_on γ (Next P).

  #[global] Instance saved_prop_contractive γ :
    Contractive (saved_prop γ).
  Proof.
    solve_contractive.
  Qed.
  #[global] Instance saved_prop_proper γ :
    Proper ((≡) ==> (≡)) (saved_prop γ).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance saved_prop_persistent γ P :
    Persistent (saved_prop γ P).
  Proof.
    apply _.
  Qed.

  Lemma saved_prop_alloc P :
    ⊢ |==>
      ∃ γ,
      saved_prop γ P.
  Proof.
    apply agree_alloc.
  Qed.
  Lemma saved_prop_alloc_cofinite (γs : gset gname) P :
    ⊢ |==>
      ∃ γ,
      ⌜γ ∉ γs⌝ ∗
      saved_prop γ P.
  Proof.
    apply agree_alloc_cofinite.
  Qed.

  Lemma saved_prop_agree γ P1 P2 :
    saved_prop γ P1 -∗
    saved_prop γ P2 -∗
    ▷ (P1 ≡ P2).
  Proof.
    rewrite -later_equivI. apply: agree_on_agree.
  Qed.
End saved_prop_G.

#[global] Opaque saved_prop.
