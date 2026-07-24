Require Import iris.algebra.gmultiset.

Require Import zoo.prelude.
Require Import zoo.iris.algebra.auth.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Class AuthGmultisetG Σ A `{Countable A} :=
  { #[local] auth_gmultiset۰G۰inG :: inG Σ (authR (gmultisetUR A))
  }.

Definition auth_gmultiset۰Σ A `{Countable A} :=
  #[GFunctor (authR (gmultisetUR  A))
  ].
#[global] Instance subG𑁒auth_gmultiset۰Σ Σ A `{Countable A} :
  subG (auth_gmultiset۰Σ A) Σ →
  AuthGmultisetG Σ A.
Proof.
  solve_inG.
Qed.

Section auth_gmultiset۰G.
  Context `{auth_gmultiset۰G : AuthGmultisetG Σ A}.

  Implicit Type x y : gmultiset A.

  Definition auth_gmultiset۰auth γ dq x :=
    own γ (●{dq} x).
  Definition auth_gmultiset۰frag γ y :=
    own γ (◯ y).

  #[global] Instance auth_gmultiset۰auth𑁒proper γ dq :
    Proper ((≡) ==> (≡)) (auth_gmultiset۰auth γ dq).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance auth_gmultiset۰frag𑁒proper γ :
    Proper ((≡) ==> (≡)) (auth_gmultiset۰frag γ).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance auth_gmultiset۰auth𑁒timeless γ dq x :
    Timeless (auth_gmultiset۰auth γ dq x).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_gmultiset۰frag𑁒timeless γ y :
    Timeless (auth_gmultiset۰frag γ y).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_gmultiset۰auth𑁒persistent γ x :
    Persistent (auth_gmultiset۰auth γ DfracDiscarded x).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_gmultiset۰auth𑁒fractional γ x :
    Fractional (λ q, auth_gmultiset۰auth γ (DfracOwn q) x).
  Proof.
    intros ?*. rewrite -own_op -auth_auth_dfrac_op //.
  Qed.
  #[global] Instance auth_gmultiset۰auth𑁒as_fractional γ q x :
    AsFractional (auth_gmultiset۰auth γ (DfracOwn q) x) (λ q, auth_gmultiset۰auth γ (DfracOwn q) x) q.
  Proof.
    split; [done | apply _].
  Qed.

  Lemma auth_gmultiset𑁒alloc :
    ⊢ |==>
      ∃ γ,
      auth_gmultiset۰auth γ (DfracOwn 1) ∅.
  Proof.
    apply own_alloc, auth_auth_valid. done.
  Qed.

  Lemma auth_gmultiset۰auth𑁒valid γ dq x :
    auth_gmultiset۰auth γ dq x ⊢
    ⌜✓ dq⌝.
  Proof.
    iIntros "H●".
    iDestruct (own_valid with "H●") as %(? & _)%auth_auth_dfrac_valid.
    iSteps.
  Qed.
  Lemma auth_gmultiset۰auth𑁒combine γ dq1 x1 dq2 x2 :
    auth_gmultiset۰auth γ dq1 x1 -∗
    auth_gmultiset۰auth γ dq2 x2 -∗
      ⌜x1 = x2⌝ ∗
      auth_gmultiset۰auth γ (dq1 ⋅ dq2) x1.
  Proof.
    iIntros "H●1 H●2". iCombine "H●1 H●2" as "H●".
    iDestruct (own_valid with "H●") as %(_ & [= ->]%leibniz_equiv & _)%auth_auth_dfrac_op_valid.
    rewrite -auth_auth_dfrac_op. iSteps.
  Qed.
  Lemma auth_gmultiset۰auth𑁒valid𑁒2 γ dq1 x1 dq2 x2 :
    auth_gmultiset۰auth γ dq1 x1 -∗
    auth_gmultiset۰auth γ dq2 x2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜x1 = x2⌝.
  Proof.
    iIntros "H●1 H●2".
    iDestruct (auth_gmultiset۰auth𑁒combine with "H●1 H●2") as "(-> & H●)".
    iDestruct (auth_gmultiset۰auth𑁒valid with "H●") as "$".
    iSteps.
  Qed.
  Lemma auth_gmultiset۰auth𑁒agree γ dq1 x1 dq2 x2 :
    auth_gmultiset۰auth γ dq1 x1 -∗
    auth_gmultiset۰auth γ dq2 x2 -∗
    ⌜x1 = x2⌝.
  Proof.
    iIntros "H●1 H●2".
    iDestruct (auth_gmultiset۰auth𑁒valid𑁒2 with "H●1 H●2") as "(_ & $)".
  Qed.
  Lemma auth_gmultiset۰auth𑁒dfrac𑁒ne γ1 dq1 x1 γ2 dq2 x2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    auth_gmultiset۰auth γ1 dq1 x1 -∗
    auth_gmultiset۰auth γ2 dq2 x2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iIntros "% H●1 H●2 ->".
    iDestruct (auth_gmultiset۰auth𑁒valid𑁒2 with "H●1 H●2") as "(% & _)". done.
  Qed.
  Lemma auth_gmultiset۰auth𑁒ne γ1 x1 γ2 dq2 x2 :
    auth_gmultiset۰auth γ1 (DfracOwn 1) x1 -∗
    auth_gmultiset۰auth γ2 dq2 x2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iApply auth_gmultiset۰auth𑁒dfrac𑁒ne; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma auth_gmultiset۰auth𑁒exclusive γ x1 dq2 x2 :
    auth_gmultiset۰auth γ (DfracOwn 1) x1 -∗
    auth_gmultiset۰auth γ dq2 x2 -∗
    False.
  Proof.
    iIntros "H●1 H●2".
    iDestruct (auth_gmultiset۰auth𑁒ne with "H●1 H●2") as %?. done.
  Qed.
  Lemma auth_gmultiset۰auth𑁒persist γ dq x :
    auth_gmultiset۰auth γ dq x ⊢ |==>
    auth_gmultiset۰auth γ DfracDiscarded x.
  Proof.
    apply own_update, auth_update_auth_persist.
  Qed.

  Lemma auth_gmultiset۰frag𑁒combine γ y1 y2 :
    auth_gmultiset۰frag γ y1 -∗
    auth_gmultiset۰frag γ y2 -∗
    auth_gmultiset۰frag γ (y1 ⊎ y2).
  Proof.
    iIntros "H◯1 H◯2".
    iCombine "H◯1 H◯2" as "H◯". rewrite gmultiset_op //.
  Qed.

  Lemma auth_gmultiset𑁒subseteq γ dq x y :
    auth_gmultiset۰auth γ dq x -∗
    auth_gmultiset۰frag γ y -∗
    ⌜y ⊆ x⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as %(_ & ?%gmultiset_included & _)%auth_both_dfrac_valid_discrete.
    iSteps.
  Qed.
  Lemma auth_gmultiset𑁒elem_of γ dq x b :
    auth_gmultiset۰auth γ dq x -∗
    auth_gmultiset۰frag γ {[+b+]} -∗
    ⌜b ∈ x⌝.
  Proof.
    rewrite -gmultiset_singleton_subseteq_l. apply auth_gmultiset𑁒subseteq.
  Qed.

  Lemma auth_gmultiset𑁒update𑁒alloc {γ x} y :
    auth_gmultiset۰auth γ (DfracOwn 1) x ⊢ |==>
      auth_gmultiset۰auth γ (DfracOwn 1) (y ⊎ x) ∗
      auth_gmultiset۰frag γ y.
  Proof.
    iIntros "H●".
    iMod (own_update with "H●") as "(H● & H◯)".
    { apply auth_update_alloc, gmultiset_local_update_alloc. }
    rewrite left_id comm. iSteps.
  Qed.
  Lemma auth_gmultiset𑁒update𑁒alloc𑁒singleton {γ x} a :
    auth_gmultiset۰auth γ (DfracOwn 1) x ⊢ |==>
      auth_gmultiset۰auth γ (DfracOwn 1) ({[+a+]} ⊎ x) ∗
      auth_gmultiset۰frag γ {[+a+]}.
  Proof.
    apply auth_gmultiset𑁒update𑁒alloc.
  Qed.

  Lemma auth_gmultiset𑁒update𑁒dealloc {γ x} y :
    auth_gmultiset۰auth γ (DfracOwn 1) x -∗
    auth_gmultiset۰frag γ y ==∗
    auth_gmultiset۰auth γ (DfracOwn 1) (x ∖ y).
  Proof.
    apply own_update_2, auth_update_dealloc.
    rewrite /ε /= /gmultiset_unit_instance -(gmultiset_difference_diag y).
    apply gmultiset_local_update_dealloc. done.
  Qed.
End auth_gmultiset۰G.

#[global] Opaque auth_gmultiset۰auth.
#[global] Opaque auth_gmultiset۰frag.
