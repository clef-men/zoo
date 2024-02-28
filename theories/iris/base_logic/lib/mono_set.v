From iris.algebra Require Import
  auth
  gset.

From zebre Require Import
  prelude.
From zebre.iris.base_logic Require Export
  lib.base.
From zebre.iris Require Import
  diaframe.
From zebre Require Import
  options.

#[local] Definition mono_set_UR (V:Type) `{Countable V} :=
  authUR $ gsetUR V.

Class MonoSetG Σ V `{Countable V} := {
  #[local] mono_set_G_inG :: inG Σ (mono_set_UR V) ;
}.

Definition mono_set_Σ V `{Countable V} := #[
  GFunctor (mono_set_UR V)
].
#[global] Instance subG_mono_set_Σ Σ V `{Countable V} :
  subG (mono_set_Σ V) Σ →
  MonoSetG Σ V.
Proof.
  solve_inG.
Qed.

Section mono_set_G.
  Context `{mono_set_G : MonoSetG Σ V}.

  Implicit Types m : gset V.

  Definition mono_set_auth γ m :=
    @own _ _ mono_set_G_inG γ (● m).
  Definition mono_set_lb γ m :=
    @own _ _ mono_set_G_inG γ (◯ m).
  Definition mono_set_elem γ v :=
    mono_set_lb γ {[v]}.

  #[global] Instance mono_set_auth_timeless γ m :
    Timeless (mono_set_auth γ m).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_set_lb_timeless γ m :
    Timeless (mono_set_lb γ m).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_set_lb_persistent γ m :
    Persistent (mono_set_lb γ m).
  Proof.
    apply _.
  Qed.

  Lemma mono_set_alloc m :
    ⊢ |==>
      ∃ γ,
      mono_set_auth γ m.
  Proof.
    iApply own_alloc. by apply auth_auth_valid.
  Qed.

  Lemma mono_set_lb_valid γ m1 m2 :
    mono_set_auth γ m1 -∗
    mono_set_lb γ m2 -∗
    ⌜m2 ⊆ m1⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as "%Hv".
    iPureIntro.
    apply auth_both_valid_discrete in Hv. destruct Hv as (Hv&_).
    by eapply gset_included.
  Qed.

  Lemma mono_set_elem_valid γ m v :
    mono_set_auth γ m -∗
    mono_set_elem γ v -∗
    ⌜v ∈ m⌝.
  Proof.
    iIntros "Hauth Helem".
    iDestruct (mono_set_lb_valid with "Hauth Helem") as %?.
    set_solver.
  Qed.

  Lemma mono_set_lb_get' {γ m} m' :
    m' ⊆ m →
    mono_set_auth γ m ⊢ |==>
      mono_set_auth γ m ∗
      mono_set_lb γ m'.
  Proof.
    intros Hm'. rewrite -own_op.
    apply own_update, auth_update_alloc.
    apply local_update_unital. intros n z Hv Hz.
    rewrite mixin_ucmra_unit_left_id in Hz; first apply gset_ucmra_mixin.
    split; eauto.
    rewrite -Hz.
    intros ?. rewrite gset_op. set_solver.
  Qed.

  Lemma mono_set_lb_get γ m :
    mono_set_auth γ m ⊢ |==>
      mono_set_auth γ m ∗
      mono_set_lb γ m.
  Proof.
    apply mono_set_lb_get'. done.
  Qed.

  Lemma mono_set_elem_get {γ m} v :
    v ∈ m ->
    mono_set_auth γ m ⊢ |==>
      mono_set_auth γ m ∗
      mono_set_elem γ v.
  Proof.
    intros. apply mono_set_lb_get'. set_solver.
  Qed.

  Lemma mono_set_insert {γ m} m' :
    mono_set_auth γ m ⊢ |==>
    mono_set_auth γ (m' ∪ m).
  Proof.
    iIntros "?". iApply (own_update with "[$]").
    apply auth_update_auth with (b':=m' ∪ m).
    apply gset_local_update. set_solver.
  Qed.

  Lemma mono_set_insert' {γ m} v :
    mono_set_auth γ m ⊢ |==>
      mono_set_auth γ ({[v]} ∪ m) ∗
      mono_set_elem γ  v.
  Proof.
    iIntros "Hauth".
    iMod (mono_set_insert {[v]} with "Hauth") as "Hauth".
    iApply (mono_set_elem_get with "Hauth"). set_solver.
  Qed.
End mono_set_G.

#[global] Opaque mono_set_auth.
#[global] Opaque mono_set_lb.
