Require Import iris.algebra.gset.

Require Import zoo.prelude.
Require Import zoo.iris.algebra.auth.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Class AuthDgsetG Σ A `{Countable A} :=
  { #[local] auth_dgset۰G۰inG :: inG Σ (authR (gset_disjUR A))
  }.

Definition auth_dgset۰Σ A `{Countable A} :=
  #[GFunctor (authR (gset_disjUR A))
  ].
#[global] Instance subGｰauth_dgset۰Σ Σ A `{Countable A} :
  subG (auth_dgset۰Σ A) Σ →
  AuthDgsetG Σ A.
Proof.
  solve_inG.
Qed.

Section auth_dgset۰G.
  Context `{auth_dgset۰G : AuthDgsetG Σ A}.

  Implicit Type x y : gset A.

  Definition auth_dgset۰auth γ dq x :=
    own γ (●{dq} GSet x).
  Definition auth_dgset۰frag γ y :=
    own γ (◯ GSet y).

  #[global] Instance auth_dgset۰authｰproper γ dq :
    Proper ((≡) ==> (≡)) (auth_dgset۰auth γ dq).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance auth_dgset۰fragｰproper γ :
    Proper ((≡) ==> (≡)) (auth_dgset۰frag γ).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance auth_dgset۰authｰtimeless γ dq x :
    Timeless (auth_dgset۰auth γ dq x).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_dgset۰fragｰtimeless γ y :
    Timeless (auth_dgset۰frag γ y).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_dgset۰authｰpersistent γ x :
    Persistent (auth_dgset۰auth γ DfracDiscarded x).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_dgset۰authｰfractional γ x :
    Fractional (λ q, auth_dgset۰auth γ (DfracOwn q) x).
  Proof.
    intros ?*. rewrite -own_op -auth_auth_dfrac_op //.
  Qed.
  #[global] Instance auth_dgset۰authｰas_fractional γ q x :
    AsFractional (auth_dgset۰auth γ (DfracOwn q) x) (λ q, auth_dgset۰auth γ (DfracOwn q) x) q.
  Proof.
    split; [done | apply _].
  Qed.

  Lemma auth_dgsetｰalloc x :
    ⊢ |==>
      ∃ γ,
      auth_dgset۰auth γ (DfracOwn 1) x ∗
      auth_dgset۰frag γ x.
  Proof.
     iMod (own_alloc (● GSet x ⋅ ◯ GSet x)) as "(%γ & $ & $)"; last iSteps.
     apply auth_both_valid_2; done.
  Qed.
  Lemma auth_dgsetｰallocｰempty :
    ⊢ |==>
      ∃ γ,
      auth_dgset۰auth γ (DfracOwn 1) ∅.
  Proof.
    apply own_alloc, auth_auth_valid. done.
  Qed.

  Lemma auth_dgset۰authｰvalid γ dq x :
    auth_dgset۰auth γ dq x ⊢
    ⌜✓ dq⌝.
  Proof.
    iIntros "H●".
    iDestruct (own_valid with "H●") as %(? & _)%auth_auth_dfrac_valid.
    iSteps.
  Qed.
  Lemma auth_dgset۰authｰcombine γ dq1 x1 dq2 x2 :
    auth_dgset۰auth γ dq1 x1 -∗
    auth_dgset۰auth γ dq2 x2 -∗
      ⌜x1 = x2⌝ ∗
      auth_dgset۰auth γ (dq1 ⋅ dq2) x1.
  Proof.
    iIntros "H●1 H●2". iCombine "H●1 H●2" as "H●".
    iDestruct (own_valid with "H●") as %(_ & [= ->]%leibniz_equiv & _)%auth_auth_dfrac_op_valid.
    rewrite -auth_auth_dfrac_op. iSteps.
  Qed.
  Lemma auth_dgset۰authｰvalidｰ2 γ dq1 x1 dq2 x2 :
    auth_dgset۰auth γ dq1 x1 -∗
    auth_dgset۰auth γ dq2 x2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜x1 = x2⌝.
  Proof.
    iIntros "H●1 H●2".
    iDestruct (auth_dgset۰authｰcombine with "H●1 H●2") as "(-> & H●)".
    iDestruct (auth_dgset۰authｰvalid with "H●") as "$".
    iSteps.
  Qed.
  Lemma auth_dgset۰authｰagree γ dq1 x1 dq2 x2 :
    auth_dgset۰auth γ dq1 x1 -∗
    auth_dgset۰auth γ dq2 x2 -∗
    ⌜x1 = x2⌝.
  Proof.
    iIntros "H●1 H●2".
    iDestruct (auth_dgset۰authｰvalidｰ2 with "H●1 H●2") as "(_ & $)".
  Qed.
  Lemma auth_dgset۰authｰdfracｰne γ1 dq1 x1 γ2 dq2 x2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    auth_dgset۰auth γ1 dq1 x1 -∗
    auth_dgset۰auth γ2 dq2 x2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iIntros "% H●1 H●2 ->".
    iDestruct (auth_dgset۰authｰvalidｰ2 with "H●1 H●2") as "(% & _)". done.
  Qed.
  Lemma auth_dgset۰authｰne γ1 x1 γ2 dq2 x2 :
    auth_dgset۰auth γ1 (DfracOwn 1) x1 -∗
    auth_dgset۰auth γ2 dq2 x2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iApply auth_dgset۰authｰdfracｰne; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma auth_dgset۰authｰexclusive γ x1 dq2 x2 :
    auth_dgset۰auth γ (DfracOwn 1) x1 -∗
    auth_dgset۰auth γ dq2 x2 -∗
    False.
  Proof.
    iIntros "H●1 H●2".
    iDestruct (auth_dgset۰authｰne with "H●1 H●2") as %?. done.
  Qed.
  Lemma auth_dgset۰authｰpersist γ dq x :
    auth_dgset۰auth γ dq x ⊢ |==>
    auth_dgset۰auth γ DfracDiscarded x.
  Proof.
    apply own_update, auth_update_auth_persist.
  Qed.

  Lemma auth_dgset۰fragｰdisjoint γ y1 y2 :
    auth_dgset۰frag γ y1 -∗
    auth_dgset۰frag γ y2 -∗
    ⌜y1 ## y2⌝.
  Proof.
    iIntros "H◯1 H◯2".
    iDestruct (own_valid_2 with "H◯1 H◯2") as %?%auth_frag_op_valid%gset_disj_valid_op.
    iSteps.
  Qed.
  Lemma auth_dgset۰fragｰsingletonｰne γ b1 b2 :
    auth_dgset۰frag γ {[b1]} -∗
    auth_dgset۰frag γ {[b2]} -∗
    ⌜b1 ≠ b2⌝.
  Proof.
    iIntros "H◯1 H◯2".
    iDestruct (auth_dgset۰fragｰdisjoint with "H◯1 H◯2") as %Hdisjoint%disjoint_singleton_l.
    rewrite not_elem_of_singleton in Hdisjoint. iSteps.
  Qed.
  Lemma auth_dgset۰fragｰexclusive γ y :
    y ≠ ∅ →
    auth_dgset۰frag γ y -∗
    auth_dgset۰frag γ y -∗
    False.
  Proof.
    iIntros "%Hy H◯1 H◯2".
    iDestruct (auth_dgset۰fragｰdisjoint with "H◯1 H◯2") as %?. set_solver.
  Qed.
  Lemma auth_dgset۰fragｰsingletonｰexclusive γ b :
    auth_dgset۰frag γ {[b]} -∗
    auth_dgset۰frag γ {[b]} -∗
    False.
  Proof.
    apply auth_dgset۰fragｰexclusive. done.
  Qed.

  Lemma auth_dgset۰fragｰcombine γ y1 y2 :
    auth_dgset۰frag γ y1 -∗
    auth_dgset۰frag γ y2 -∗
    auth_dgset۰frag γ (y1 ∪ y2).
  Proof.
    iIntros "H◯1 H◯2".
    iDestruct (auth_dgset۰fragｰdisjoint with "H◯1 H◯2") as %Hdisjoint.
    iCombine "H◯1 H◯2" as "H◯". rewrite gset_disj_union //.
  Qed.

  Lemma auth_dgsetｰsubseteq γ dq x y :
    auth_dgset۰auth γ dq x -∗
    auth_dgset۰frag γ y -∗
    ⌜y ⊆ x⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as %(_ & ?%gset_disj_included & _)%auth_both_dfrac_valid_discrete.
    iSteps.
  Qed.
  Lemma auth_dgsetｰelem_of γ dq x b :
    auth_dgset۰auth γ dq x -∗
    auth_dgset۰frag γ {[b]} -∗
    ⌜b ∈ x⌝.
  Proof.
    rewrite elem_of_subseteq_singleton. apply auth_dgsetｰsubseteq.
  Qed.

  Lemma auth_dgsetｰupdateｰalloc {γ x} y :
    x ## y →
    auth_dgset۰auth γ (DfracOwn 1) x ⊢ |==>
      auth_dgset۰auth γ (DfracOwn 1) (y ∪ x) ∗
      auth_dgset۰frag γ y.
  Proof.
    iIntros "% H●".
    iMod (own_update with "H●") as "(H● & H◯)".
    { apply auth_update_alloc, gset_disj_alloc_empty_local_update. done. }
    iSteps.
  Qed.
  Lemma auth_dgsetｰupdateｰallocｰsingleton {γ x} a :
    a ∉ x →
    auth_dgset۰auth γ (DfracOwn 1) x ⊢ |==>
      auth_dgset۰auth γ (DfracOwn 1) ({[a]} ∪ x) ∗
      auth_dgset۰frag γ {[a]}.
  Proof.
    intros. apply auth_dgsetｰupdateｰalloc. set_solver.
  Qed.

  Lemma auth_dgsetｰupdateｰdealloc {γ x} y :
    auth_dgset۰auth γ (DfracOwn 1) x -∗
    auth_dgset۰frag γ y ==∗
    auth_dgset۰auth γ (DfracOwn 1) (x ∖ y).
  Proof.
    apply own_update_2, auth_update_dealloc, gset_disj_dealloc_local_update.
  Qed.
End auth_dgset۰G.

#[global] Opaque auth_dgset۰auth.
#[global] Opaque auth_dgset۰frag.
