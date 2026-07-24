Require Import zoo.prelude.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.base_logic.lib.ghost_var.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Class OneshotG Σ A B :=
  { #[local] oneshot۰G۰var۰G :: GhostVarG Σ (leibnizO (A + B))
  }.

Definition oneshot۰Σ A B :=
  #[ghost_var۰Σ (leibnizO (A + B))
  ].
#[global] Instance subG𑁒oneshot۰Σ Σ A B :
  subG (oneshot۰Σ A B) Σ →
  OneshotG Σ A B.
Proof.
  solve_inG.
Qed.

Section oneshot۰G.
  Context `{oneshot۰G : !OneshotG Σ A B}.

  Implicit Type a : A.
  Implicit Type b : B.

  Definition oneshot۰pending γ dq a :=
    ghost_var γ dq (inl a).
  Definition oneshot۰shot γ b :=
    ghost_var γ DfracDiscarded (inr b).

  #[global] Instance oneshot۰pending𑁒timeless γ dq a :
    Timeless (oneshot۰pending γ dq a).
  Proof.
    apply _.
  Qed.
  #[global] Instance oneshot۰shot𑁒timeless γ b :
    Timeless (oneshot۰shot γ b).
  Proof.
    apply _.
  Qed.

  #[global] Instance oneshot۰shot𑁒persistent γ b :
    Persistent (oneshot۰shot γ b).
  Proof.
    apply _.
  Qed.

  #[global] Instance oneshot۰pending𑁒fractional γ a :
    Fractional (λ q, oneshot۰pending γ (DfracOwn q) a).
  Proof.
    apply _.
  Qed.
  #[global] Instance oneshot۰pending𑁒as_fractional γ q a :
    AsFractional (oneshot۰pending γ (DfracOwn q) a) (λ q, oneshot۰pending γ (DfracOwn q) a) q.
  Proof.
    apply _.
  Qed.

  Lemma oneshot𑁒alloc a :
    ⊢ |==>
      ∃ γ,
      oneshot۰pending γ (DfracOwn 1) a.
  Proof.
    apply ghost_var𑁒alloc.
  Qed.

  Lemma oneshot۰pending𑁒valid γ dq a :
    oneshot۰pending γ dq a ⊢
    ⌜✓ dq⌝.
  Proof.
    apply ghost_var𑁒valid.
  Qed.
  Lemma oneshot۰pending𑁒combine γ dq1 a1 dq2 a2 :
    oneshot۰pending γ dq1 a1 -∗
    oneshot۰pending γ dq2 a2 -∗
      ⌜a1 = a2⌝ ∗
      oneshot۰pending γ (dq1 ⋅ dq2) a1.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_var𑁒combine𑁒L with "H1 H2") as "(%Heq & $)". injection Heq as ->.
    iSteps.
  Qed.
  Lemma oneshot۰pending𑁒valid𑁒2 γ dq1 a1 dq2 a2 :
    oneshot۰pending γ dq1 a1 -∗
    oneshot۰pending γ dq2 a2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜a1 = a2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (oneshot۰pending𑁒combine with "H1 H2") as "(-> & H)".
    iDestruct (oneshot۰pending𑁒valid with "H") as "$".
    iSteps.
  Qed.
  Lemma oneshot۰pending𑁒agree γ dq1 a1 dq2 a2 :
    oneshot۰pending γ dq1 a1 -∗
    oneshot۰pending γ dq2 a2 -∗
    ⌜a1 = a2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (oneshot۰pending𑁒valid𑁒2 with "H1 H2") as "(_ & $)".
  Qed.
  Lemma oneshot۰pending𑁒dfrac𑁒ne γ1 dq1 a1 γ2 dq2 a2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    oneshot۰pending γ1 dq1 a1 -∗
    oneshot۰pending γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply ghost_var𑁒dfrac𑁒ne.
  Qed.
  Lemma oneshot۰pending𑁒ne γ1 a1 γ2 dq2 a2 :
    oneshot۰pending γ1 (DfracOwn 1) a1 -∗
    oneshot۰pending γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply ghost_var𑁒ne.
  Qed.
  Lemma oneshot۰pending𑁒exclusive γ a1 dq2 a2 :
    oneshot۰pending γ (DfracOwn 1) a1 -∗
    oneshot۰pending γ dq2 a2 -∗
    False.
  Proof.
    apply ghost_var𑁒exclusive.
  Qed.
  Lemma oneshot۰pending𑁒persist γ dq a :
    oneshot۰pending γ dq a ⊢ |==>
    oneshot۰pending γ DfracDiscarded a.
  Proof.
    apply ghost_var𑁒persist.
  Qed.

  Lemma oneshot۰shot𑁒agree γ b1 b2 :
    oneshot۰shot γ b1 -∗
    oneshot۰shot γ b2 -∗
    ⌜b1 = b2⌝.
  Proof.
    iIntros "Hshot1 Hshot2".
    iDestruct (ghost_var𑁒agree𑁒L with "Hshot1 Hshot2") as %[= <-].
    iSteps.
  Qed.

  Lemma oneshot𑁒pending𑁒shot γ dq a b :
    oneshot۰pending γ dq a -∗
    oneshot۰shot γ b -∗
    False.
  Proof.
    iIntros "Hpending Hshot".
    iDestruct (ghost_var𑁒valid𑁒2𑁒L with "Hpending Hshot") as %(_ & [=]).
  Qed.

  Lemma oneshot𑁒update𑁒pending γ a a' :
    oneshot۰pending γ (DfracOwn 1) a ⊢ |==>
    oneshot۰pending γ (DfracOwn 1) a'.
  Proof.
    apply ghost_var𑁒update.
  Qed.
  Lemma oneshot𑁒update𑁒shot {γ a} b :
    oneshot۰pending γ (DfracOwn 1) a ⊢ |==>
    oneshot۰shot γ b.
  Proof.
    iIntros "Hpending".
    iMod (ghost_var𑁒update with "Hpending") as "Hshot".
    iApply (ghost_var𑁒persist with "Hshot").
  Qed.
End oneshot۰G.

#[global] Opaque oneshot۰pending.
#[global] Opaque oneshot۰shot.
