From iris.algebra Require Import
  lib.frac_auth.

From zoo Require Import
  prelude.
From zoo.common Require Import
  math.
From zoo.iris.base_logic Require Export
  lib.base.
From zoo.iris Require Import
  diaframe.
From zoo Require Import
  options.

Class AuthFracG Σ A :=
  { #[local] auth_frac_G_inG :: inG Σ (frac_authUR A)
  }.

Definition auth_frac_Σ A :=
  #[GFunctor (frac_authUR A)
  ].
#[global] Instance subG_auth_frac_Σ Σ A :
  subG (auth_frac_Σ A) Σ →
  AuthFracG Σ A.
Proof.
  solve_inG.
Qed.

Section auth_frac_G.
  Context `{auth_frac_G : !AuthFracG Σ A}.

  Implicit Types q : frac.
  Implicit Types x y : A.

  Definition auth_frac_auth γ x :=
    own γ (frac_auth_auth (DfracOwn 1) x).
  Definition auth_frac_frag γ q y :=
    own γ (frac_auth_frag q y).

  #[global] Instance auth_frac_auth_proper γ :
    Proper ((≡) ==> (≡)) (auth_frac_auth γ).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance auth_frac_frag_proper γ q :
    Proper ((≡) ==> (≡)) (auth_frac_frag γ q).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance auth_frac_auth_timeless γ x :
    Discrete x →
    Timeless (auth_frac_auth γ x).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_frac_frag_timeless γ q y :
    Discrete y →
    Timeless (auth_frac_frag γ q y).
  Proof.
    apply _.
  Qed.

  Lemma auth_frac_alloc x :
    ✓ x →
    ⊢ |==>
      ∃ γ,
      auth_frac_auth γ x ∗
      auth_frac_frag γ 1 x.
  Proof.
    intros Hx.
    iMod (own_alloc (●F x ⋅ ◯F x)) as "(%γ & $ & $)" => //.
    apply auth_both_valid_2 => //.
  Qed.

  Lemma auth_frac_auth_valid `{!CmraDiscrete A} γ x :
    auth_frac_auth γ x ⊢
    ⌜✓ x⌝.
  Proof.
    iIntros "H●".
    iDestruct (own_valid with "H●") as %Hvalid.
    rewrite frac_auth_auth_valid in Hvalid.
    iSteps.
  Qed.

  Lemma auth_frac_frag_valid `{!CmraDiscrete A} γ q y :
    auth_frac_frag γ q y ⊢
      ⌜q ≤ 1⌝%Qp ∗
      ⌜✓ y⌝.
  Proof.
    iIntros "H◯".
    iDestruct (own_valid with "H◯") as %?%frac_auth_frag_valid => //.
  Qed.
  Lemma auth_frac_frag_split {γ q y} q1 y1 q2 y2 :
    q = (q1 + q2)%Qp →
    y = y1 ⋅ y2 →
    auth_frac_frag γ q y ⊢
      auth_frac_frag γ q1 y1 ∗
      auth_frac_frag γ q2 y2.
  Proof.
    iIntros (-> ->) "($ & $)".
  Qed.
  Lemma auth_frac_frag_combine γ q1 y1 q2 y2 :
    auth_frac_frag γ q1 y1 -∗
    auth_frac_frag γ q2 y2 -∗
    auth_frac_frag γ (q1 ⋅ q2) (y1 ⋅ y2).
  Proof.
    iIntros "H◯1 H◯2".
    iCombine "H◯1 H◯2" as "$".
  Qed.
  Lemma auth_frac_frag_valid_2 `{!CmraDiscrete A} γ q1 y1 q2 y2 :
    auth_frac_frag γ q1 y1 -∗
    auth_frac_frag γ q2 y2 -∗
      ⌜q1 ⋅ q2 ≤ 1⌝%Qp ∗
      ⌜✓ (y1 ⋅ y2)⌝.
  Proof.
    iIntros "H◯1 H◯2".
    iDestruct (auth_frac_frag_combine with "H◯1 H◯2") as "H◯".
    iDestruct (auth_frac_frag_valid with "H◯") as "$".
  Qed.
  Lemma auth_frac_frag_frac_ne `{!CmraDiscrete A} γ1 q1 y1 γ2 q2 y2 :
    ¬ (q1 + q2 ≤ 1)%Qp →
    auth_frac_frag γ1 q1 y1 -∗
    auth_frac_frag γ2 q2 y2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iIntros "% H◯1 H◯2 ->".
    iDestruct (auth_frac_frag_valid_2 with "H◯1 H◯2") as "(% & _)" => //.
  Qed.
  Lemma auth_frac_frag_ne `{!CmraDiscrete A} γ1 y1 γ2 q2 y2 :
    auth_frac_frag γ1 1 y1 -∗
    auth_frac_frag γ2 q2 y2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iApply auth_frac_frag_frac_ne.
    { intros []%(exclusive_l 1%Qp). }
  Qed.
  Lemma auth_frac_frag_exclusive `{!CmraDiscrete A} γ y1 q2 y2 :
    auth_frac_frag γ 1 y1 -∗
    auth_frac_frag γ q2 y2 -∗
    False.
  Proof.
    iIntros "H◯1 H◯2".
    iDestruct (auth_frac_frag_ne with "H◯1 H◯2") as %? => //.
  Qed.

  Lemma auth_frac_auth_frag_agree `{!CmraDiscrete A} γ x y :
    auth_frac_auth γ x -∗
    auth_frac_frag γ 1 y -∗
    ⌜x ≡ y⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as %?%frac_auth_agree => //.
  Qed.
  Lemma auth_frac_auth_frag_agree_L `{!CmraDiscrete A, !LeibnizEquiv A} γ x y :
    auth_frac_auth γ x -∗
    auth_frac_frag γ 1 y -∗
    ⌜x = y⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (auth_frac_auth_frag_agree with "H● H◯") as %?%leibniz_equiv => //.
  Qed.

  Lemma auth_frac_auth_frag_included `{!CmraDiscrete A, !CmraTotal A} γ x q y :
    auth_frac_auth γ x -∗
    auth_frac_frag γ q y -∗
    ⌜y ≼ x⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as %?%frac_auth_included_total => //.
  Qed.

  Lemma auth_frac_update {γ x q y} x' y' :
    (x, y) ~l~> (x', y') →
    auth_frac_auth γ x -∗
    auth_frac_frag γ q y ==∗
      auth_frac_auth γ x' ∗
      auth_frac_frag γ q y'.
  Proof.
    iIntros "% H● H◯".
    iMod (own_update_2 with "H● H◯") as "($ & $)" => //.
    { apply frac_auth_update => //. }
  Qed.
  Lemma auth_frac_update_1 {γ x y} x' :
    ✓ x' →
    auth_frac_auth γ x -∗
    auth_frac_frag γ 1 y ==∗
      auth_frac_auth γ x' ∗
      auth_frac_frag γ 1 x'.
  Proof.
    iIntros "% H● H◯".
    iMod (own_update_2 with "H● H◯") as "($ & $)" => //.
    { apply frac_auth_update_1 => //. }
  Qed.
End auth_frac_G.

#[global] Opaque auth_frac_auth.
#[global] Opaque auth_frac_frag.

Section auth_frac_G.
  Context {A : ucmra}.
  Context `{auth_frac_G : !AuthFracG Σ A}.

  Implicit Types q : frac.
  Implicit Types x y : A.

  Lemma auth_frac_frag_divide {γ q y} ys :
    y = foldr (⋅) ε ys →
    auth_frac_frag γ q y ⊢
    [∗ list] y ∈ ys, auth_frac_frag γ (q / Qp_of_nat (length ys)) y.
  Proof.
    iInduction ys as [| y0 ys IH] forall (q y).
    all: iIntros (->) "H◯ /=".
    - iSteps.
    - destruct_decide (length ys = 0) as ->%nil_length_inv | Hys.
      + iEval (rewrite right_id) in "H◯".
        iEval (rewrite Qp_of_nat_1 Qp.div_1).
        iSteps.
      + assert (q = q / (1 + Qp_of_nat (length ys)) + (q * Qp_of_nat (length ys) / (1 + Qp_of_nat (length ys))))%Qp as Heq.
        { rewrite -Qp.div_add_distr -{2}(Qp.mul_1_r q) -Qp.mul_add_distr_l.
          rewrite -{2}(Qp.mul_1_l (1 + _)).
          rewrite Qp.div_mul_cancel_r Qp.div_1 //.
        }
        iEval (setoid_rewrite Heq) in "H◯". clear Heq.
        iEval (rewrite Qp_of_nat_S //).
        iDestruct (auth_frac_frag_split with "H◯") as "($ & H◯)". 1,2: done.
        iDestruct ("IH" with "[//] H◯") as "H◯s".
        iEval (rewrite Qp.div_div Qp.div_mul_cancel_r) in "H◯s".
        iFrame.
  Qed.
  Lemma auth_frac_frag_divide' {γ q y} q' ys :
    q = (Qp_of_nat (length ys) * q')%Qp →
    y = foldr (⋅) ε ys →
    auth_frac_frag γ q y ⊢
    [∗ list] y ∈ ys, auth_frac_frag γ q' y.
  Proof.
    iIntros (-> ->) "H◯".
    iDestruct (auth_frac_frag_divide with "H◯") as "H◯s". 1: done.
    iEval (rewrite -{2}(Qp.mul_1_r (Qp_of_nat _)) Qp.div_mul_cancel_l Qp.div_1) in "H◯s".
    iFrame.
  Qed.
  Lemma auth_frac_frag_gather γ q ys :
    0 < length ys →
    ([∗ list] y ∈ ys, auth_frac_frag γ q y) ⊢
    auth_frac_frag γ (Qp_of_nat (length ys) * q) (foldr (⋅) ε ys).
  Proof.
    iInduction ys as [| y ys IH] forall (q).
    all: iIntros "/= %Hys H◯s".
    - lia.
    - iDestruct "H◯s" as "(H◯ & H◯s)".
      clear Hys. destruct_decide (length ys = 0) as ->%nil_length_inv | Hys.
      + iEval (rewrite Qp_of_nat_1 Qp.mul_1_l right_id).
        iFrame.
      + iEval (rewrite Qp_of_nat_S //).
        iEval (rewrite Qp.mul_add_distr_r Qp.mul_1_l).
        iApply (auth_frac_frag_combine with "H◯").
        iApply ("IH" with "[%] H◯s"). 1: lia.
  Qed.
End auth_frac_G.
