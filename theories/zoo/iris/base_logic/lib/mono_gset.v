Require Import zoo.prelude.
Require Import zoo.common.relations.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.base_logic.lib.auth_mono.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Class MonoGsetG Σ A `{Countable A} :=
  { #[local] mono_gset۰G۰mono۰G :: AuthMonoG Σ (A := leibnizO (gset A)) subseteq
  }.

Definition mono_gset۰Σ A `{Countable A} :=
  #[auth_mono۰Σ (A := leibnizO (gset A)) subseteq
  ].
#[global] Instance subGｰmono_gset۰Σ Σ V `{Countable V} :
  subG (mono_gset۰Σ V) Σ →
  MonoGsetG Σ V.
Proof.
  solve_inG.
Qed.

Section mono_gset۰G.
  Context `{mono_gset۰G : MonoGsetG Σ A}.

  Implicit Type a : A.
  Implicit Type s : gset A.

  Definition mono_gset۰auth γ dq s :=
    auth_mono۰auth subseteq γ dq s.
  Definition mono_gset۰lb γ s :=
    auth_mono۰lb subseteq γ s.
  Definition mono_gset۰elem γ a :=
    mono_gset۰lb γ {[a]}.

  #[global] Instance mono_gset۰authｰproper γ dq :
    Proper ((≡) ==> (≡)) (mono_gset۰auth γ dq).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance mono_gset۰lbｰproper γ :
    Proper ((≡) ==> (≡)) (mono_gset۰lb γ).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance mono_gset۰authｰtimeless γ dq s :
    Timeless (mono_gset۰auth γ dq s).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_gset۰lbｰtimeless γ s :
    Timeless (mono_gset۰lb γ s).
  Proof.
    apply _.
  Qed.

  #[global] Instance mono_gset۰authｰpersistent γ s :
    Persistent (mono_gset۰auth γ DfracDiscarded s).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_gset۰lbｰpersistent γ s :
    Persistent (mono_gset۰lb γ s).
  Proof.
    apply _.
  Qed.

  #[global] Instance mono_gset۰authｰfractional γ s :
    Fractional (λ q, mono_gset۰auth γ (DfracOwn q) s).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_gset۰authｰas_fractional γ q s :
    AsFractional (mono_gset۰auth γ (DfracOwn q) s) (λ q, mono_gset۰auth γ (DfracOwn q) s) q.
  Proof.
    apply _.
  Qed.

  Lemma mono_gsetｰalloc s :
    ⊢ |==>
      ∃ γ,
      mono_gset۰auth γ (DfracOwn 1) s.
  Proof.
    apply auth_monoｰalloc.
  Qed.

  Lemma mono_gset۰authｰvalid γ dq s :
    mono_gset۰auth γ dq s ⊢
    ⌜✓ dq⌝.
  Proof.
    apply auth_mono۰authｰvalid.
  Qed.
  Lemma mono_gset۰authｰcombine γ dq1 s1 dq2 s2 :
    mono_gset۰auth γ dq1 s1 -∗
    mono_gset۰auth γ dq2 s2 -∗
      ⌜s1 = s2⌝ ∗
      mono_gset۰auth γ (dq1 ⋅ dq2) s1.
  Proof.
    apply: auth_mono۰authｰcombine.
  Qed.
  Lemma mono_gset۰authｰvalidｰ2 γ dq1 s1 dq2 s2 :
    mono_gset۰auth γ dq1 s1 -∗
    mono_gset۰auth γ dq2 s2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜s1 = s2⌝.
  Proof.
    apply: auth_mono۰authｰvalidｰ2.
  Qed.
  Lemma mono_gset۰authｰagree γ dq1 s1 dq2 s2 :
    mono_gset۰auth γ dq1 s1 -∗
    mono_gset۰auth γ dq2 s2 -∗
    ⌜s1 = s2⌝.
  Proof.
    apply: auth_mono۰authｰagree.
  Qed.
  Lemma mono_gset۰authｰdfracｰne γ1 dq1 s1 γ2 dq2 s2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    mono_gset۰auth γ1 dq1 s1 -∗
    mono_gset۰auth γ2 dq2 s2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply: auth_mono۰authｰdfracｰne.
  Qed.
  Lemma mono_gset۰authｰne γ1 s1 γ2 dq2 s2 :
    mono_gset۰auth γ1 (DfracOwn 1) s1 -∗
    mono_gset۰auth γ2 dq2 s2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply: auth_mono۰authｰne.
  Qed.
  Lemma mono_gset۰authｰexclusive γ s1 dq2 s2 :
    mono_gset۰auth γ (DfracOwn 1) s1 -∗
    mono_gset۰auth γ dq2 s2 -∗
    False.
  Proof.
    apply: auth_mono۰authｰexclusive.
  Qed.
  Lemma mono_gset۰authｰpersist γ dq s :
    mono_gset۰auth γ dq s ⊢ |==>
    mono_gset۰auth γ DfracDiscarded s.
  Proof.
    apply auth_mono۰authｰpersist.
  Qed.

  Lemma mono_gset۰lbｰget γ dq s :
    mono_gset۰auth γ dq s ⊢
    mono_gset۰lb γ s.
  Proof.
    apply auth_mono۰lbｰget.
  Qed.
  Lemma mono_gset۰lbｰmono {γ s} s' :
    s' ⊆ s →
    mono_gset۰lb γ s ⊢
    mono_gset۰lb γ s'.
  Proof.
    apply auth_mono۰lbｰmono'.
  Qed.
  Lemma mono_gset۰elemｰget {γ dq s} a :
    a ∈ s →
    mono_gset۰auth γ dq s ⊢
    mono_gset۰elem γ a.
  Proof.
    iIntros "%Ha Hauth".
    iDestruct (mono_gset۰lbｰget with "Hauth") as "Hlb".
    iApply (mono_gset۰lbｰmono with "Hlb").
    set_solver.
  Qed.

  Lemma mono_gset۰lbｰvalid γ dq s1 s2 :
    mono_gset۰auth γ dq s1 -∗
    mono_gset۰lb γ s2 -∗
    ⌜s2 ⊆ s1⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (auth_mono۰lbｰvalid with "Hauth Hlb") as %Hs2.
    rewrite preorderｰrtc in Hs2. iSteps.
  Qed.
  Lemma mono_gset۰elemｰvalid γ dq s a :
    mono_gset۰auth γ dq s -∗
    mono_gset۰elem γ a -∗
    ⌜a ∈ s⌝.
  Proof.
    iIntros "Hauth Helem".
    iDestruct (mono_gset۰lbｰvalid with "Hauth Helem") as %?%singleton_subseteq_l.
    iSteps.
  Qed.

  Lemma mono_gsetｰupdate {γ s} s' :
    s ⊆ s' →
    mono_gset۰auth γ (DfracOwn 1) s ⊢ |==>
    mono_gset۰auth γ (DfracOwn 1) s'.
  Proof.
    apply auth_monoｰupdate'.
  Qed.
  Lemma mono_gsetｰinsert {γ s} a :
    mono_gset۰auth γ (DfracOwn 1) s ⊢ |==>
    mono_gset۰auth γ (DfracOwn 1) ({[a]} ∪ s).
  Proof.
    apply mono_gsetｰupdate. set_solver.
  Qed.
  Lemma mono_gsetｰinsert' {γ s} a :
    mono_gset۰auth γ (DfracOwn 1) s ⊢ |==>
      mono_gset۰auth γ (DfracOwn 1) ({[a]} ∪ s) ∗
      mono_gset۰elem γ a.
  Proof.
    iIntros "Hauth".
    iMod (mono_gsetｰinsert a with "Hauth") as "Hauth".
    iDestruct (mono_gset۰elemｰget a with "Hauth") as "#Helem"; first set_solver.
    iSteps.
  Qed.
End mono_gset۰G.

#[global] Opaque mono_gset۰auth.
#[global] Opaque mono_gset۰lb.
