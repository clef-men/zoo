From zoo Require Import
  prelude.
From zoo.common Require Import
  relations.
From zoo.iris.base_logic Require Export
  lib.base.
From zoo.iris.base_logic Require Import
  lib.auth_mono.
From zoo.iris Require Import
  diaframe.
From zoo Require Import
  options.

Class MonoGmultisetG Σ A `{Countable A} := {
  #[local] mono_gmultiset_G_mono_G :: AuthMonoG Σ (A := leibnizO (gmultiset A)) subseteq ;
}.

Definition mono_gmultiset_Σ A `{Countable A} := #[
  auth_mono_Σ (A := leibnizO (gmultiset A)) subseteq
].
#[global] Instance subG_mono_gmultiset_Σ Σ V `{Countable V} :
  subG (mono_gmultiset_Σ V) Σ →
  MonoGmultisetG Σ V.
Proof.
  solve_inG.
Qed.

Section mono_gmultiset_G.
  Context `{mono_gmultiset_G : MonoGmultisetG Σ A}.

  Implicit Types a : A.
  Implicit Types s : gmultiset A.

  Definition mono_gmultiset_auth γ dq s :=
    auth_mono_auth subseteq γ dq s.
  Definition mono_gmultiset_lb γ s :=
    auth_mono_lb subseteq γ s.
  Definition mono_gmultiset_elem γ a :=
    mono_gmultiset_lb γ {[+a+]}.

  #[global] Instance mono_gmultiset_auth_proper γ dq :
    Proper ((≡) ==> (≡)) (mono_gmultiset_auth γ dq).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance mono_gmultiset_lb_proper γ :
    Proper ((≡) ==> (≡)) (mono_gmultiset_lb γ).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance mono_gmultiset_auth_timeless γ dq s :
    Timeless (mono_gmultiset_auth γ dq s).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_gmultiset_lb_timeless γ s :
    Timeless (mono_gmultiset_lb γ s).
  Proof.
    apply _.
  Qed.

  #[global] Instance mono_gmultiset_auth_persistent γ s :
    Persistent (mono_gmultiset_auth γ DfracDiscarded s).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_gmultiset_lb_persistent γ s :
    Persistent (mono_gmultiset_lb γ s).
  Proof.
    apply _.
  Qed.

  #[global] Instance mono_gmultiset_auth_fractional γ s :
    Fractional (λ q, mono_gmultiset_auth γ (DfracOwn q) s).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_gmultiset_auth_as_fractional γ q s :
    AsFractional (mono_gmultiset_auth γ (DfracOwn q) s) (λ q, mono_gmultiset_auth γ (DfracOwn q) s) q.
  Proof.
    apply _.
  Qed.

  Lemma mono_gmultiset_alloc s :
    ⊢ |==>
      ∃ γ,
      mono_gmultiset_auth γ (DfracOwn 1) s.
  Proof.
    apply auth_mono_alloc.
  Qed.

  Lemma mono_gmultiset_auth_valid γ dq s :
    mono_gmultiset_auth γ dq s ⊢
    ⌜✓ dq⌝.
  Proof.
    apply auth_mono_auth_valid.
  Qed.
  Lemma mono_gmultiset_auth_combine γ dq1 s1 dq2 s2 :
    mono_gmultiset_auth γ dq1 s1 -∗
    mono_gmultiset_auth γ dq2 s2 -∗
      ⌜s1 = s2⌝ ∗
      mono_gmultiset_auth γ (dq1 ⋅ dq2) s1.
  Proof.
    apply: auth_mono_auth_combine.
  Qed.
  Lemma mono_gmultiset_auth_valid_2 γ dq1 s1 dq2 s2 :
    mono_gmultiset_auth γ dq1 s1 -∗
    mono_gmultiset_auth γ dq2 s2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜s1 = s2⌝.
  Proof.
    apply: auth_mono_auth_valid_2.
  Qed.
  Lemma mono_gmultiset_auth_agree γ dq1 s1 dq2 s2 :
    mono_gmultiset_auth γ dq1 s1 -∗
    mono_gmultiset_auth γ dq2 s2 -∗
    ⌜s1 = s2⌝.
  Proof.
    apply: auth_mono_auth_agree.
  Qed.
  Lemma mono_gmultiset_auth_dfrac_ne γ1 dq1 s1 γ2 dq2 s2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    mono_gmultiset_auth γ1 dq1 s1 -∗
    mono_gmultiset_auth γ2 dq2 s2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply: auth_mono_auth_dfrac_ne.
  Qed.
  Lemma mono_gmultiset_auth_ne γ1 s1 γ2 dq2 s2 :
    mono_gmultiset_auth γ1 (DfracOwn 1) s1 -∗
    mono_gmultiset_auth γ2 dq2 s2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply: auth_mono_auth_ne.
  Qed.
  Lemma mono_gmultiset_auth_exclusive γ s1 dq2 s2 :
    mono_gmultiset_auth γ (DfracOwn 1) s1 -∗
    mono_gmultiset_auth γ dq2 s2 -∗
    False.
  Proof.
    apply: auth_mono_auth_exclusive.
  Qed.
  Lemma mono_gmultiset_auth_persist γ dq s :
    mono_gmultiset_auth γ dq s ⊢ |==>
    mono_gmultiset_auth γ DfracDiscarded s.
  Proof.
    apply auth_mono_auth_persist.
  Qed.

  Lemma mono_gmultiset_lb_get γ dq s :
    mono_gmultiset_auth γ dq s ⊢
    mono_gmultiset_lb γ s.
  Proof.
    apply auth_mono_lb_get.
  Qed.
  Lemma mono_gmultiset_lb_mono {γ s} s' :
    s' ⊆ s →
    mono_gmultiset_lb γ s ⊢
    mono_gmultiset_lb γ s'.
  Proof.
    apply auth_mono_lb_mono'.
  Qed.
  Lemma mono_gmultiset_elem_get {γ dq s} a :
    a ∈ s →
    mono_gmultiset_auth γ dq s ⊢
    mono_gmultiset_elem γ a.
  Proof.
    iIntros "%Ha Hauth".
    iDestruct (mono_gmultiset_lb_get with "Hauth") as "Hlb".
    iApply (mono_gmultiset_lb_mono with "Hlb").
    multiset_solver.
  Qed.

  Lemma mono_gmultiset_lb_valid γ dq s1 s2 :
    mono_gmultiset_auth γ dq s1 -∗
    mono_gmultiset_lb γ s2 -∗
    ⌜s2 ⊆ s1⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (auth_mono_lb_valid with "Hauth Hlb") as %Hs2.
    rewrite preorder_rtc in Hs2. iSteps.
  Qed.
  Lemma mono_gmultiset_elem_valid γ dq s a :
    mono_gmultiset_auth γ dq s -∗
    mono_gmultiset_elem γ a -∗
    ⌜a ∈ s⌝.
  Proof.
    iIntros "Hauth Helem".
    iDestruct (mono_gmultiset_lb_valid with "Hauth Helem") as %?%gmultiset_singleton_subseteq_l.
    iSteps.
  Qed.

  Lemma mono_gmultiset_update {γ s} s' :
    s ⊆ s' →
    mono_gmultiset_auth γ (DfracOwn 1) s ⊢ |==>
    mono_gmultiset_auth γ (DfracOwn 1) s'.
  Proof.
    apply auth_mono_update'.
  Qed.
  Lemma mono_gmultiset_insert {γ s} a :
    mono_gmultiset_auth γ (DfracOwn 1) s ⊢ |==>
    mono_gmultiset_auth γ (DfracOwn 1) ({[+a+]} ⊎ s).
  Proof.
    apply mono_gmultiset_update, gmultiset_disj_union_subseteq_r.
  Qed.
  Lemma mono_gmultiset_insert' {γ s} a :
    mono_gmultiset_auth γ (DfracOwn 1) s ⊢ |==>
      mono_gmultiset_auth γ (DfracOwn 1) ({[+a+]} ⊎ s) ∗
      mono_gmultiset_elem γ a.
  Proof.
    iIntros "Hauth".
    iMod (mono_gmultiset_insert a with "Hauth") as "Hauth".
    iDestruct (mono_gmultiset_elem_get a with "Hauth") as "#Helem"; first multiset_solver.
    iSteps.
  Qed.
End mono_gmultiset_G.

#[global] Opaque mono_gmultiset_auth.
#[global] Opaque mono_gmultiset_lb.
