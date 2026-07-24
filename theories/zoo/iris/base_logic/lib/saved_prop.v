Require Import zoo.prelude.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.base_logic.lib.agree.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Class SavedPropG Σ :=
  { #[local] saved_prop۰G :: AgreeG Σ (▶ ∙)
  }.

Definition saved_prop۰Σ :=
  #[agree۰Σ (▶ ∙)
  ].
#[global] Instance subG𑁒saved_prop۰Σ Σ :
  subG saved_prop۰Σ Σ →
  SavedPropG Σ.
Proof.
  solve_inG.
Qed.

Section saved_prop۰G.
  Context `{saved_prop۰G : !SavedPropG Σ}.

  Implicit Type P : iProp Σ.

  Definition saved_prop γ P :=
    agree۰on γ (Next P).

  #[global] Instance saved_prop𑁒contractive γ :
    Contractive (saved_prop γ).
  Proof.
    solve_contractive.
  Qed.
  #[global] Instance saved_prop𑁒proper γ :
    Proper ((≡) ==> (≡)) (saved_prop γ).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance saved_prop𑁒persistent γ P :
    Persistent (saved_prop γ P).
  Proof.
    apply _.
  Qed.

  Lemma saved_prop𑁒alloc P :
    ⊢ |==>
      ∃ γ,
      saved_prop γ P.
  Proof.
    apply agree𑁒alloc.
  Qed.
  Lemma saved_prop𑁒alloc𑁒cofinite (γs : gset gname) P :
    ⊢ |==>
      ∃ γ,
      ⌜γ ∉ γs⌝ ∗
      saved_prop γ P.
  Proof.
    apply agree𑁒alloc𑁒cofinite.
  Qed.

  Lemma saved_prop𑁒agree γ P1 P2 :
    saved_prop γ P1 -∗
    saved_prop γ P2 -∗
    ▷ (P1 ≡ P2).
  Proof.
    rewrite -later_equivI. apply: agree۰on𑁒agree.
  Qed.
End saved_prop۰G.

#[global] Opaque saved_prop.
