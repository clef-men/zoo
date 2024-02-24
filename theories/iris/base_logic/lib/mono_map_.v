From zebre Require Import
  prelude.
From zebre.iris.base_logic Require Export
  lib.base.
From zebre.iris Require Import
  diaframe.
From zebre Require Import
  options.

Class MonoMapG (Σ : gFunctors) (K V : Type) `{Countable K} := {
}.

Definition mono_map_Σ (K V : Type) `{Countable K} := #[
].
#[global] Instance subG_mono_map_Σ Σ K V `{Countable K} :
  subG (mono_map_Σ K V) Σ →
  MonoMapG Σ K V.
Proof.
Qed.

Section mono_map_G.
  Context `{mono_map_G : MonoMapG Σ K V}.

  Implicit Types γ : gname.
  Implicit Types m : gmap K V.

  Definition mono_map_auth γ m : iProp Σ.
  Proof. Admitted.
  Definition mono_map_lb γ m : iProp Σ.
  Proof. Admitted.

  #[global] Instance mono_map_lb_persistent γ m :
    Persistent (mono_map_lb γ m).
  Proof.
  Admitted.

  Lemma mono_map_alloc m :
    ⊢ |==>
      ∃ γ,
      mono_map_auth γ m.
  Proof.
  Admitted.

  Lemma mono_map_insert {γ m} i v :
    m !! i = None →
    mono_map_auth γ m ⊢ |==>
    mono_map_auth γ (<[i := v]> m).
  Proof.
  Admitted.

  Lemma mono_map_lb_get γ m :
    mono_map_auth γ m ⊢
    mono_map_lb γ m.
  Proof.
  Admitted.

  Lemma mono_map_valid γ m1 m2 :
    mono_map_auth γ m1 -∗
    mono_map_lb γ m2 -∗
    ⌜m2 ⊆ m1⌝.
  Proof.
  Admitted.
End mono_map_G.

#[global] Opaque mono_map_auth.
#[global] Opaque mono_map_lb.
