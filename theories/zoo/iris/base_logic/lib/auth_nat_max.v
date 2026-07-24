Require Import zoo.prelude.
Require Import zoo.common.math.
Require Import zoo.iris.base_logic.lib.auth_monoi.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Class AuthNatMaxG Σ :=
  { #[local] auth_nat_max۰G۰mono۰G :: AuthMonoiG Σ (≤)
  }.

Definition auth_nat_max۰Σ :=
  #[auth_monoi۰Σ (≤)
  ].
#[global] Instance subG𑁒auth_nat_max۰Σ Σ :
  subG auth_nat_max۰Σ Σ →
  AuthNatMaxG Σ.
Proof.
  solve_inG.
Qed.

Section auth_nat_max۰G.
  Context `{auth_nat_max۰G : !AuthNatMaxG Σ}.

  Implicit Type n m p : nat.

  Definition auth_nat_max۰auth γ dq n :=
    auth_monoi۰auth (≤) γ dq n.
  Definition auth_nat_max۰lb γ n :=
    auth_monoi۰lb (≤) γ n.

  #[global] Instance auth_nat_max۰auth𑁒timeless γ dq n :
    Timeless (auth_nat_max۰auth γ dq n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_nat_max۰lb𑁒timeless γ n :
    Timeless (auth_nat_max۰lb γ n).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_nat_max۰auth𑁒persistent γ n :
    Persistent (auth_nat_max۰auth γ DfracDiscarded n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_nat_max۰lb𑁒persistent γ n :
    Persistent (auth_nat_max۰lb γ n).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_nat_max۰auth𑁒fractional γ n :
    Fractional (λ q, auth_nat_max۰auth γ (DfracOwn q) n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_nat_max۰auth𑁒as_fractional γ q n :
    AsFractional (auth_nat_max۰auth γ (DfracOwn q) n) (λ q, auth_nat_max۰auth γ (DfracOwn q) n) q.
  Proof.
    apply _.
  Qed.

  Lemma auth_nat_max𑁒alloc n :
    ⊢ |==>
      ∃ γ,
      auth_nat_max۰auth γ (DfracOwn 1) n.
  Proof.
    apply auth_monoi𑁒alloc.
  Qed.

  Lemma auth_nat_max۰auth𑁒valid γ dq a :
    auth_nat_max۰auth γ dq a ⊢
    ⌜✓ dq⌝.
  Proof.
    apply auth_monoi۰auth𑁒valid.
  Qed.
  Lemma auth_nat_max۰auth𑁒combine γ dq1 n1 dq2 n2 :
    auth_nat_max۰auth γ dq1 n1 -∗
    auth_nat_max۰auth γ dq2 n2 -∗
      ⌜n1 = n2⌝ ∗
      auth_nat_max۰auth γ (dq1 ⋅ dq2) n1.
  Proof.
    apply: auth_monoi۰auth𑁒combine.
  Qed.
  Lemma auth_nat_max۰auth𑁒valid𑁒2 γ dq1 n1 dq2 n2 :
    auth_nat_max۰auth γ dq1 n1 -∗
    auth_nat_max۰auth γ dq2 n2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜n1 = n2⌝.
  Proof.
    apply: auth_monoi۰auth𑁒valid𑁒2.
  Qed.
  Lemma auth_nat_max۰auth𑁒agree γ dq1 n1 dq2 n2 :
    auth_nat_max۰auth γ dq1 n1 -∗
    auth_nat_max۰auth γ dq2 n2 -∗
    ⌜n1 = n2⌝.
  Proof.
    apply: auth_monoi۰auth𑁒agree.
  Qed.
  Lemma auth_nat_max۰auth𑁒dfrac𑁒ne γ1 dq1 n1 γ2 dq2 n2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    auth_nat_max۰auth γ1 dq1 n1 -∗
    auth_nat_max۰auth γ2 dq2 n2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply: auth_monoi۰auth𑁒dfrac𑁒ne.
  Qed.
  Lemma auth_nat_max۰auth𑁒ne γ1 n1 γ2 dq2 n2 :
    auth_nat_max۰auth γ1 (DfracOwn 1) n1 -∗
    auth_nat_max۰auth γ2 dq2 n2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    apply: auth_monoi۰auth𑁒ne.
  Qed.
  Lemma auth_nat_max۰auth𑁒exclusive γ n1 dq2 n2 :
    auth_nat_max۰auth γ (DfracOwn 1) n1 -∗
    auth_nat_max۰auth γ dq2 n2 -∗
    False.
  Proof.
    apply: auth_monoi۰auth𑁒exclusive.
  Qed.
  Lemma auth_nat_max۰auth𑁒persist γ dq n :
    auth_nat_max۰auth γ dq n ⊢ |==>
    auth_nat_max۰auth γ DfracDiscarded n.
  Proof.
    apply auth_monoi۰auth𑁒persist.
  Qed.

  Lemma auth_nat_max۰lb𑁒0 γ :
    ⊢ |==>
      auth_nat_max۰lb γ 0.
  Proof.
    apply auth_monoi۰lb𑁒initial.
  Qed.
  Lemma auth_nat_max۰lb𑁒get γ q n :
    auth_nat_max۰auth γ q n ⊢
    auth_nat_max۰lb γ n.
  Proof.
    apply auth_monoi۰lb𑁒get.
  Qed.
  Lemma auth_nat_max۰lb𑁒le {γ n} n' :
    n' ≤ n →
    auth_nat_max۰lb γ n ⊢
    auth_nat_max۰lb γ n'.
  Proof.
    apply auth_monoi۰lb𑁒mono'.
  Qed.
  Lemma auth_nat_max۰lb𑁒max γ n1 n2 :
    auth_nat_max۰lb γ n1 -∗
    auth_nat_max۰lb γ n2 -∗
    auth_nat_max۰lb γ (n1 `max` n2).
  Proof.
    iIntros "Hlb_1 Hlb_2".
    destruct (Nat.max_spec n1 n2) as [(_ & ->) | (_ & ->)] => //.
  Qed.

  Lemma auth_nat_max۰lb𑁒valid γ dq n m :
    auth_nat_max۰auth γ dq n -∗
    auth_nat_max۰lb γ m -∗
    ⌜m ≤ n⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (auth_monoi۰lb𑁒valid with "Hauth Hlb") as %Hrtc.
    rewrite preorder𑁒rtc in Hrtc. iSteps.
  Qed.

  Lemma auth_nat_max𑁒update {γ n} n' :
    n ≤ n' →
    auth_nat_max۰auth γ (DfracOwn 1) n ⊢ |==>
    auth_nat_max۰auth γ (DfracOwn 1) n'.
  Proof.
    apply auth_monoi𑁒update'.
  Qed.
End auth_nat_max۰G.

#[global] Opaque auth_nat_max۰auth.
#[global] Opaque auth_nat_max۰lb.
