Require Import zoo.prelude.
Require Import zoo.common.relations.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.base_logic.lib.auth_mono.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Class MonoGmultisetG Σ A `{Countable A} :=
  { #[local] mono_gmultiset۰G۰mono۰G :: AuthMonoG Σ (A := leibnizO (gmultiset A)) subseteq
  }.

Definition mono_gmultiset۰Σ A `{Countable A} :=
  #[auth_mono۰Σ (A := leibnizO (gmultiset A)) subseteq
  ].
#[global] Instance subGｰmono_gmultiset۰Σ Σ V `{Countable V} :
  subG (mono_gmultiset۰Σ V) Σ →
  MonoGmultisetG Σ V.
Proof.
  solve_inG.
Qed.

Section mono_gmultiset۰G.
  Context `{mono_gmultiset۰G : MonoGmultisetG Σ A}.

  Implicit Type a : A.
  Implicit Type s : gmultiset A.

  Definition mono_gmultiset۰auth γ dq s :=
    auth_mono۰auth subseteq γ dq s.
  Definition mono_gmultiset۰lb γ s :=
    auth_mono۰lb subseteq γ s.
  Definition mono_gmultiset۰elem γ a :=
    mono_gmultiset۰lb γ {[+a+]}.

  #[global] Instance mono_gmultiset۰authｰproper γ dq :
    Proper ((≡) ==> (≡)) (mono_gmultiset۰auth γ dq).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance mono_gmultiset۰lbｰproper γ :
    Proper ((≡) ==> (≡)) (mono_gmultiset۰lb γ).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance mono_gmultiset۰authｰtimeless γ dq s :
    Timeless (mono_gmultiset۰auth γ dq s).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_gmultiset۰lbｰtimeless γ s :
    Timeless (mono_gmultiset۰lb γ s).
  Proof.
    apply _.
  Qed.

  #[global] Instance mono_gmultiset۰authｰpersistent γ s :
    Persistent (mono_gmultiset۰auth γ DfracDiscarded s).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_gmultiset۰lbｰpersistent γ s :
    Persistent (mono_gmultiset۰lb γ s).
  Proof.
    apply _.
  Qed.

  #[global] Instance mono_gmultiset۰authｰfractional γ s :
    Fractional (λ q, mono_gmultiset۰auth γ (DfracOwn q) s).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_gmultiset۰authｰas_fractional γ q s :
    AsFractional (mono_gmultiset۰auth γ (DfracOwn q) s) (λ q, mono_gmultiset۰auth γ (DfracOwn q) s) q.
  Proof.
    apply _.
  Qed.

  Lemma mono_gmultisetｰalloc s :
    ⊢ |==>
      ∃ γ,
      mono_gmultiset۰auth γ (DfracOwn 1) s.
  Proof.
    apply auth_monoｰalloc.
  Qed.

  Lemma mono_gmultiset۰authｰvalid γ dq s :
    mono_gmultiset۰auth γ dq s ⊢
    ⌜✓ dq⌝.
  Proof.
    apply auth_mono۰authｰvalid.
  Qed.
  Lemma mono_gmultiset۰authｰcombine γ dq1 s1 dq2 s2 :
    mono_gmultiset۰auth γ dq1 s1 -∗
    mono_gmultiset۰auth γ dq2 s2 -∗
      ⌜s1 = s2⌝ ∗
      mono_gmultiset۰auth γ (dq1 ⋅ dq2) s1.
  Proof.
    apply: auth_mono۰authｰcombine.
  Qed.
  Lemma mono_gmultiset۰authｰvalidｰ2 γ dq1 s1 dq2 s2 :
    mono_gmultiset۰auth γ dq1 s1 -∗
    mono_gmultiset۰auth γ dq2 s2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜s1 = s2⌝.
  Proof.
    apply: auth_mono۰authｰvalidｰ2.
  Qed.
  Lemma mono_gmultiset۰authｰagree γ dq1 s1 dq2 s2 :
    mono_gmultiset۰auth γ dq1 s1 -∗
    mono_gmultiset۰auth γ dq2 s2 -∗
    ⌜s1 = s2⌝.
  Proof.
    apply: auth_mono۰authｰagree.
  Qed.
  Lemma mono_gmultiset۰authｰdfracｰne γ1 dq1 s1 γ2 dq2 s2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    mono_gmultiset۰auth γ1 dq1 s1 -∗
    mono_gmultiset۰auth γ2 dq2 s2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply: auth_mono۰authｰdfracｰne.
  Qed.
  Lemma mono_gmultiset۰authｰne γ1 s1 γ2 dq2 s2 :
    mono_gmultiset۰auth γ1 (DfracOwn 1) s1 -∗
    mono_gmultiset۰auth γ2 dq2 s2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply: auth_mono۰authｰne.
  Qed.
  Lemma mono_gmultiset۰authｰexclusive γ s1 dq2 s2 :
    mono_gmultiset۰auth γ (DfracOwn 1) s1 -∗
    mono_gmultiset۰auth γ dq2 s2 -∗
    False.
  Proof.
    apply: auth_mono۰authｰexclusive.
  Qed.
  Lemma mono_gmultiset۰authｰpersist γ dq s :
    mono_gmultiset۰auth γ dq s ⊢ |==>
    mono_gmultiset۰auth γ DfracDiscarded s.
  Proof.
    apply auth_mono۰authｰpersist.
  Qed.

  Lemma mono_gmultiset۰lbｰget γ dq s :
    mono_gmultiset۰auth γ dq s ⊢
    mono_gmultiset۰lb γ s.
  Proof.
    apply auth_mono۰lbｰget.
  Qed.
  Lemma mono_gmultiset۰lbｰmono {γ s} s' :
    s' ⊆ s →
    mono_gmultiset۰lb γ s ⊢
    mono_gmultiset۰lb γ s'.
  Proof.
    apply auth_mono۰lbｰmono'.
  Qed.
  Lemma mono_gmultiset۰elemｰget {γ dq s} a :
    a ∈ s →
    mono_gmultiset۰auth γ dq s ⊢
    mono_gmultiset۰elem γ a.
  Proof.
    iIntros "%Ha Hauth".
    iDestruct (mono_gmultiset۰lbｰget with "Hauth") as "Hlb".
    iApply (mono_gmultiset۰lbｰmono with "Hlb").
    multiset_solver.
  Qed.

  Lemma mono_gmultiset۰lbｰvalid γ dq s1 s2 :
    mono_gmultiset۰auth γ dq s1 -∗
    mono_gmultiset۰lb γ s2 -∗
    ⌜s2 ⊆ s1⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (auth_mono۰lbｰvalid with "Hauth Hlb") as %Hs2.
    rewrite preorderｰrtc in Hs2. iSteps.
  Qed.
  Lemma mono_gmultiset۰elemｰvalid γ dq s a :
    mono_gmultiset۰auth γ dq s -∗
    mono_gmultiset۰elem γ a -∗
    ⌜a ∈ s⌝.
  Proof.
    iIntros "Hauth Helem".
    iDestruct (mono_gmultiset۰lbｰvalid with "Hauth Helem") as %?%gmultiset_singleton_subseteq_l.
    iSteps.
  Qed.

  Lemma mono_gmultisetｰupdate {γ s} s' :
    s ⊆ s' →
    mono_gmultiset۰auth γ (DfracOwn 1) s ⊢ |==>
    mono_gmultiset۰auth γ (DfracOwn 1) s'.
  Proof.
    apply auth_monoｰupdate'.
  Qed.
  Lemma mono_gmultisetｰinsert {γ s} a :
    mono_gmultiset۰auth γ (DfracOwn 1) s ⊢ |==>
    mono_gmultiset۰auth γ (DfracOwn 1) ({[+a+]} ⊎ s).
  Proof.
    apply mono_gmultisetｰupdate, gmultiset_disj_union_subseteq_r.
  Qed.
  Lemma mono_gmultisetｰinsert' {γ s} a :
    mono_gmultiset۰auth γ (DfracOwn 1) s ⊢ |==>
      mono_gmultiset۰auth γ (DfracOwn 1) ({[+a+]} ⊎ s) ∗
      mono_gmultiset۰elem γ a.
  Proof.
    iIntros "Hauth".
    iMod (mono_gmultisetｰinsert a with "Hauth") as "Hauth".
    iDestruct (mono_gmultiset۰elemｰget a with "Hauth") as "#Helem"; first multiset_solver.
    iSteps.
  Qed.
End mono_gmultiset۰G.

#[global] Opaque mono_gmultiset۰auth.
#[global] Opaque mono_gmultiset۰lb.
