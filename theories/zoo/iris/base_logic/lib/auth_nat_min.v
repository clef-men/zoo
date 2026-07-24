Require Import zoo.prelude.
Require Import zoo.common.math.
Require Import zoo.common.relations.
Require Import zoo.iris.base_logic.lib.auth_mono.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Class AuthNatMinG Σ :=
  { #[local] auth_nat_min۰G۰mono۰G :: AuthMonoG Σ ge
  }.

Definition auth_nat_min۰Σ :=
  #[auth_mono۰Σ ge
  ].
#[global] Instance subG𑁒auth_nat_min۰Σ Σ :
  subG auth_nat_min۰Σ Σ →
  AuthNatMinG Σ.
Proof.
  solve_inG.
Qed.

Section auth_nat_min۰G.
  Context `{auth_nat_min۰G : !AuthNatMinG Σ}.

  Implicit Type n m p : nat.

  Definition auth_nat_min۰auth γ dq n :=
    auth_mono۰auth ge γ dq n.
  Definition auth_nat_min۰ub γ n :=
    auth_mono۰lb ge γ n.

  #[global] Instance auth_nat_min۰auth𑁒timeless γ dq n :
    Timeless (auth_nat_min۰auth γ dq n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_nat_min۰ub𑁒timeless γ n :
    Timeless (auth_nat_min۰ub γ n).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_nat_min۰auth𑁒persistent γ n :
    Persistent (auth_nat_min۰auth γ DfracDiscarded n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_nat_min۰ub𑁒persistent γ n :
    Persistent (auth_nat_min۰ub γ n).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_nat_min۰auth𑁒fractional γ n :
    Fractional (λ q, auth_nat_min۰auth γ (DfracOwn q) n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_nat_min۰auth𑁒as_fractional γ q n :
    AsFractional (auth_nat_min۰auth γ (DfracOwn q) n) (λ q, auth_nat_min۰auth γ (DfracOwn q) n) q.
  Proof.
    apply _.
  Qed.

  Lemma auth_nat_min𑁒alloc n :
    ⊢ |==>
      ∃ γ,
      auth_nat_min۰auth γ (DfracOwn 1) n.
  Proof.
    apply auth_mono𑁒alloc.
  Qed.

  Lemma auth_nat_min۰auth𑁒valid γ dq a :
    auth_nat_min۰auth γ dq a ⊢
    ⌜✓ dq⌝.
  Proof.
    apply auth_mono۰auth𑁒valid.
  Qed.
  Lemma auth_nat_min۰auth𑁒combine γ dq1 n1 dq2 n2 :
    auth_nat_min۰auth γ dq1 n1 -∗
    auth_nat_min۰auth γ dq2 n2 -∗
      ⌜n1 = n2⌝ ∗
      auth_nat_min۰auth γ (dq1 ⋅ dq2) n1.
  Proof.
    apply: auth_mono۰auth𑁒combine.
  Qed.
  Lemma auth_nat_min۰auth𑁒valid𑁒2 γ dq1 n1 dq2 n2 :
    auth_nat_min۰auth γ dq1 n1 -∗
    auth_nat_min۰auth γ dq2 n2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜n1 = n2⌝.
  Proof.
    apply: auth_mono۰auth𑁒valid𑁒2.
  Qed.
  Lemma auth_nat_min۰auth𑁒agree γ dq1 n1 dq2 n2 :
    auth_nat_min۰auth γ dq1 n1 -∗
    auth_nat_min۰auth γ dq2 n2 -∗
    ⌜n1 = n2⌝.
  Proof.
    apply: auth_mono۰auth𑁒agree.
  Qed.
  Lemma auth_nat_min۰auth𑁒dfrac𑁒ne γ1 dq1 n1 γ2 dq2 n2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    auth_nat_min۰auth γ1 dq1 n1 -∗
    auth_nat_min۰auth γ2 dq2 n2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply: auth_mono۰auth𑁒dfrac𑁒ne.
  Qed.
  Lemma auth_nat_min۰auth𑁒ne γ1 n1 γ2 dq2 n2 :
    auth_nat_min۰auth γ1 (DfracOwn 1) n1 -∗
    auth_nat_min۰auth γ2 dq2 n2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply: auth_mono۰auth𑁒ne.
  Qed.
  Lemma auth_nat_min۰auth𑁒exclusive γ n1 dq2 n2 :
    auth_nat_min۰auth γ (DfracOwn 1) n1 -∗
    auth_nat_min۰auth γ dq2 n2 -∗
    False.
  Proof.
    apply: auth_mono۰auth𑁒exclusive.
  Qed.
  Lemma auth_nat_min۰auth𑁒persist γ dq n :
    auth_nat_min۰auth γ dq n ⊢ |==>
    auth_nat_min۰auth γ DfracDiscarded n.
  Proof.
    apply auth_mono۰auth𑁒persist.
  Qed.

  Lemma auth_nat_min۰ub𑁒get γ q n :
    auth_nat_min۰auth γ q n ⊢
    auth_nat_min۰ub γ n.
  Proof.
    apply auth_mono۰lb𑁒get.
  Qed.
  Lemma auth_nat_min۰ub𑁒le {γ n} n' :
    n ≤ n' →
    auth_nat_min۰ub γ n ⊢
    auth_nat_min۰ub γ n'.
  Proof.
    intros. apply auth_mono۰lb𑁒mono'. lia.
  Qed.

  Lemma auth_nat_min۰ub𑁒valid γ dq n m :
    auth_nat_min۰auth γ dq n -∗
    auth_nat_min۰ub γ m -∗
    ⌜n ≤ m⌝.
  Proof.
    iIntros "Hauth Hub".
    iDestruct (auth_mono۰lb𑁒valid with "Hauth Hub") as %Hrtc.
    rewrite preorder𑁒rtc in Hrtc. iSteps.
  Qed.

  Lemma auth_nat_min𑁒update {γ n} n' :
    n' ≤ n →
    auth_nat_min۰auth γ (DfracOwn 1) n ⊢ |==>
    auth_nat_min۰auth γ (DfracOwn 1) n'.
  Proof.
    intros. apply auth_mono𑁒update'. lia.
  Qed.
End auth_nat_min۰G.

#[global] Opaque auth_nat_min۰auth.
#[global] Opaque auth_nat_min۰ub.
