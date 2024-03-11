From zebre Require Import
  prelude.
From zebre.common Require Import
  relations.
From zebre.iris.base_logic Require Export
  lib.base.
From zebre.iris.base_logic Require Import
  lib.auth_mono.
From zebre.iris Require Import
  diaframe.
From zebre Require Import
  options.

Class MonoSetG Σ A `{Countable A} := {
  #[local] mono_set_G_mono_G :: AuthMonoG Σ (A := leibnizO (gset A)) subseteq ;
}.

Definition mono_set_Σ A `{Countable A} := #[
  auth_mono_Σ (A := leibnizO (gset A)) subseteq
].
#[global] Instance subG_mono_set_Σ Σ V `{Countable V} :
  subG (mono_set_Σ V) Σ →
  MonoSetG Σ V.
Proof.
  solve_inG.
Qed.

Section mono_set_G.
  Context `{mono_set_G : MonoSetG Σ A}.

  Implicit Types a : A.
  Implicit Types s : gset A.

  Definition mono_set_auth γ dq s :=
    auth_mono_auth subseteq γ dq s.
  Definition mono_set_lb γ s :=
    auth_mono_lb subseteq γ s.
  Definition mono_set_elem γ a :=
    mono_set_lb γ {[a]}.

  #[global] Instance mono_set_auth_timeless γ dq s :
    Timeless (mono_set_auth γ dq s).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_set_auth_persistent γ s :
    Persistent (mono_set_auth γ DfracDiscarded s).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_set_lb_timeless γ s :
    Timeless (mono_set_lb γ s).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_set_lb_persistent γ s :
    Persistent (mono_set_lb γ s).
  Proof.
    apply _.
  Qed.

  #[global] Instance mono_set_auth_fractional γ s :
    Fractional (λ q, mono_set_auth γ (DfracOwn q) s).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_set_auth_as_fractional γ q s :
    AsFractional (mono_set_auth γ (DfracOwn q) s) (λ q, mono_set_auth γ (DfracOwn q) s) q.
  Proof.
    apply _.
  Qed.

  Lemma mono_set_alloc s :
    ⊢ |==>
      ∃ γ,
      mono_set_auth γ (DfracOwn 1) s.
  Proof.
    apply auth_mono_alloc.
  Qed.

  Lemma mono_set_auth_valid γ dq s :
    mono_set_auth γ dq s ⊢
    ⌜✓ dq⌝.
  Proof.
    apply auth_mono_auth_valid.
  Qed.
  Lemma mono_set_auth_combine γ dq1 s1 dq2 s2 :
    mono_set_auth γ dq1 s1 -∗
    mono_set_auth γ dq2 s2 -∗
      mono_set_auth γ (dq1 ⋅ dq2) s1 ∗
      ⌜s1 = s2⌝.
  Proof.
    apply: auth_mono_auth_combine.
  Qed.
  Lemma mono_set_auth_valid_2 γ dq1 s1 dq2 s2 :
    mono_set_auth γ dq1 s1 -∗
    mono_set_auth γ dq2 s2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ s1 = s2⌝.
  Proof.
    apply: auth_mono_auth_valid_2.
  Qed.
  Lemma mono_set_auth_agree γ dq1 s1 dq2 s2 :
    mono_set_auth γ dq1 s1 -∗
    mono_set_auth γ dq2 s2 -∗
    ⌜s1 = s2⌝.
  Proof.
    apply: auth_mono_auth_agree.
  Qed.
  Lemma mono_set_auth_dfrac_ne γ1 dq1 s1 γ2 dq2 s2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    mono_set_auth γ1 dq1 s1 -∗
    mono_set_auth γ2 dq2 s2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply: auth_mono_auth_dfrac_ne.
  Qed.
  Lemma mono_set_auth_ne γ1 s1 γ2 dq2 s2 :
    mono_set_auth γ1 (DfracOwn 1) s1 -∗
    mono_set_auth γ2 dq2 s2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply: auth_mono_auth_ne.
  Qed.
  Lemma mono_set_auth_exclusive γ s1 s2 :
    mono_set_auth γ (DfracOwn 1) s1 -∗
    mono_set_auth γ (DfracOwn 1) s2 -∗
    False.
  Proof.
    apply: auth_mono_auth_exclusive.
  Qed.
  Lemma mono_set_auth_persist γ dq s :
    mono_set_auth γ dq s ⊢ |==>
    mono_set_auth γ DfracDiscarded s.
  Proof.
    apply auth_mono_auth_persist.
  Qed.

  Lemma mono_set_lb_get γ dq s :
    mono_set_auth γ dq s ⊢
    mono_set_lb γ s.
  Proof.
    apply auth_mono_lb_get.
  Qed.
  Lemma mono_set_lb_mono {γ s} s' :
    s' ⊆ s →
    mono_set_lb γ s ⊢
    mono_set_lb γ s'.
  Proof.
    apply auth_mono_lb_mono'.
  Qed.
  Lemma mono_set_elem_get {γ dq s} a :
    a ∈ s →
    mono_set_auth γ dq s ⊢
    mono_set_elem γ a.
  Proof.
    iIntros "%Ha Hauth".
    iDestruct (mono_set_lb_get with "Hauth") as "Hlb".
    iApply (mono_set_lb_mono with "Hlb").
    set_solver.
  Qed.

  Lemma mono_set_lb_valid γ dq s1 s2 :
    mono_set_auth γ dq s1 -∗
    mono_set_lb γ s2 -∗
    ⌜s2 ⊆ s1⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (auth_mono_lb_valid with "Hauth Hlb") as %Hs2.
    rewrite preorder_rtc in Hs2. iSteps.
  Qed.
  Lemma mono_set_elem_valid γ dq s a :
    mono_set_auth γ dq s -∗
    mono_set_elem γ a -∗
    ⌜a ∈ s⌝.
  Proof.
    iIntros "Hauth Helem".
    iDestruct (mono_set_lb_valid with "Hauth Helem") as %?%singleton_subseteq_l.
    iSteps.
  Qed.

  Lemma mono_set_update {γ s} s' :
    s ⊆ s' →
    mono_set_auth γ (DfracOwn 1) s ⊢ |==>
    mono_set_auth γ (DfracOwn 1) s'.
  Proof.
    apply auth_mono_update'.
  Qed.
  Lemma mono_set_insert {γ s} a :
    mono_set_auth γ (DfracOwn 1) s ⊢ |==>
    mono_set_auth γ (DfracOwn 1) ({[a]} ∪ s).
  Proof.
    apply mono_set_update. set_solver.
  Qed.
  Lemma mono_set_insert' {γ s} a :
    mono_set_auth γ (DfracOwn 1) s ⊢ |==>
      mono_set_auth γ (DfracOwn 1) ({[a]} ∪ s) ∗
      mono_set_elem γ a.
  Proof.
    iIntros "Hauth".
    iMod (mono_set_insert a with "Hauth") as "Hauth".
    iDestruct (mono_set_elem_get a with "Hauth") as "#Helem"; first set_solver.
    iSteps.
  Qed.
End mono_set_G.

#[global] Opaque mono_set_auth.
#[global] Opaque mono_set_lb.
