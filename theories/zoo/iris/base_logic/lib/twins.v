Require Import zoo.prelude.
Require Import zoo.iris.algebra.lib.twins.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.base_logic.algebra.twins.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Class TwinsG Σ F :=
  { #[local] twins۰G۰inG :: inG Σ (twins۰R $ oFunctor_apply F $ iPropO Σ)
  }.

Definition twins۰Σ F `{!oFunctorContractive F} :=
  #[GFunctor (twins۰RF F)
  ].
#[global] Instance subGｰtwins۰Σ Σ F `{!oFunctorContractive F} :
  subG (twins۰Σ F) Σ →
  TwinsG Σ F.
Proof.
  solve_inG.
Qed.

Section twins۰G.
  Context `{twins۰G : !TwinsG Σ F}.

  Definition twins۰twin₁ γ dq a :=
    own γ (twins۰twin₁ dq a).
  Definition twins۰twin₂ γ a :=
    own γ (twins۰twin₂ a).

  #[global] Instance twins۰twin₁ｰproper γ dq :
    Proper ((≡) ==> (≡)) (twins۰twin₁ γ dq).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance twins۰twin₂ｰproper γ :
    Proper ((≡) ==> (≡)) (twins۰twin₂ γ).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance twins۰twin₁ｰtimeless γ dq a :
    Discrete a →
    Timeless (twins۰twin₁ γ dq a).
  Proof.
    apply _.
  Qed.
  #[global] Instance twins۰twin₂ｰtimeless γ a :
    Discrete a →
    Timeless (twins۰twin₂ γ a).
  Proof.
    apply _.
  Qed.

  #[global] Instance twins۰twin₁ｰpersistent γ a :
    Persistent (twins۰twin₁ γ DfracDiscarded a).
  Proof.
    apply _.
  Qed.

  #[global] Instance twins۰twin₁ｰfractional γ a :
    Fractional (λ q, twins۰twin₁ γ (DfracOwn q) a).
  Proof.
    intros ?*. rewrite -own_op -twins۰twin₁ｰdfracｰop //.
  Qed.
  #[global] Instance twins۰twin₁ｰas_fractional γ q a :
    AsFractional (twins۰twin₁ γ (DfracOwn q) a) (λ q, twins۰twin₁ γ (DfracOwn q) a) q.
  Proof.
    split; [done | apply _].
  Qed.

  Lemma twinsｰalloc a b :
    a ≡ b →
    ⊢ |==>
      ∃ γ,
      twins۰twin₁ γ (DfracOwn 1) a ∗
      twins۰twin₂ γ b.
  Proof.
    iIntros.
    iMod (own_alloc (twins.twins۰twin₁ (DfracOwn 1) a ⋅ twins.twins۰twin₂ b)) as "(% & ? & ?)"; first by apply twinsｰbothｰvalid.
    iSteps.
  Qed.
  Lemma twinsｰalloc' a :
    ⊢ |==>
      ∃ γ,
      twins۰twin₁ γ (DfracOwn 1) a ∗ twins۰twin₂ γ a.
  Proof.
    iApply twinsｰalloc. done.
  Qed.

  Lemma twins۰twin₁ｰvalid γ dq a :
    twins۰twin₁ γ dq a ⊢
    ⌜✓ dq⌝.
  Proof.
    iIntros "Htwin₁".
    iApply twins۰twin₁ｰdfracｰvalidI.
    iApply (own_valid with "Htwin₁").
  Qed.
  Lemma twins۰twin₁ｰcombine γ dq1 a1 dq2 a2 :
    twins۰twin₁ γ dq1 a1 -∗
    twins۰twin₁ γ dq2 a2 -∗
      a1 ≡ a2 ∗
      twins۰twin₁ γ (dq1 ⋅ dq2) a1.
  Proof.
    iIntros "Htwin₁1 Htwin₁2". iCombine "Htwin₁1 Htwin₁2" as "Htwin₁".
    iDestruct (own_valid with "Htwin₁") as "#Hvalid".
    iDestruct (twins۰twin₁ｰdfracｰopｰvalidI with "Hvalid") as "(% & Hequiv)".
    iRewrite -"Hequiv" in "Htwin₁". rewrite -twins۰twin₁ｰdfracｰop.
    auto.
  Qed.
  Lemma twins۰twin₁ｰvalidｰ2 γ dq1 a1 dq2 a2 :
    twins۰twin₁ γ dq1 a1 -∗
    twins۰twin₁ γ dq2 a2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      a1 ≡ a2.
  Proof.
    iIntros "Htwin₁1 Htwin₁2".
    iDestruct (twins۰twin₁ｰcombine with "Htwin₁1 Htwin₁2") as "($ & Htwin₁)".
    iDestruct (twins۰twin₁ｰvalid with "Htwin₁") as "$".
  Qed.
  Lemma twins۰twin₁ｰagree γ dq1 a1 dq2 a2 :
    twins۰twin₁ γ dq1 a1 -∗
    twins۰twin₁ γ dq2 a2 -∗
    a1 ≡ a2.
  Proof.
    iIntros "Htwin₁1 Htwin₁2".
    iDestruct (twins۰twin₁ｰvalidｰ2 with "Htwin₁1 Htwin₁2") as "(_ & $)".
  Qed.
  Lemma twins۰twin₁ｰdfracｰne γ1 dq1 a1 γ2 dq2 a2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    twins۰twin₁ γ1 dq1 a1 -∗
    twins۰twin₁ γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iIntros "% Htwin₁1 Htwin₁2 ->".
    iDestruct (twins۰twin₁ｰvalidｰ2 with "Htwin₁1 Htwin₁2") as "(% & _)". done.
  Qed.
  Lemma twins۰twin₁ｰne γ1 a1 γ2 dq2 a2 :
    twins۰twin₁ γ1 (DfracOwn 1) a1 -∗
    twins۰twin₁ γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iApply twins۰twin₁ｰdfracｰne; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma twins۰twin₁ｰexclusive γ a1 dq2 a2 :
    twins۰twin₁ γ (DfracOwn 1) a1 -∗
    twins۰twin₁ γ dq2 a2 -∗
    False.
  Proof.
    iIntros "Htwin₁1 Htwin₁2".
    iDestruct (twins۰twin₁ｰne with "Htwin₁1 Htwin₁2") as %?. done.
  Qed.
  Lemma twins۰twin₁ｰpersist γ dq a :
    twins۰twin₁ γ dq a ⊢ |==>
    twins۰twin₁ γ DfracDiscarded a.
  Proof.
    apply own_update, twins۰twin₁ｰpersist.
  Qed.

  Lemma twins۰twin₂ｰexclusive γ a1 a2 :
    twins۰twin₂ γ a1 -∗
    twins۰twin₂ γ a2 -∗
    False.
  Proof.
    iIntros "Htwin₂1 Htwin₂2".
    iApply twins۰twin₂ｰopｰvalidI.
    iApply (own_valid_2 with "Htwin₂1 Htwin₂2").
  Qed.

  Lemma twinsｰagree γ dq a b :
    twins۰twin₁ γ dq a -∗
    twins۰twin₂ γ b -∗
    a ≡ b.
  Proof.
    iIntros "Htwin₁ Htwin₂".
    iDestruct (own_valid_2 with "Htwin₁ Htwin₂") as "Hvalid".
    iDestruct (twinsｰbothｰdfracｰvalidI with "Hvalid") as "(_ & $)".
  Qed.

  Section ofe_discrete.
    Context `{!OfeDiscrete $ oFunctor_apply F $ iPropO Σ}.

    Lemma twins۰twin₁ｰcombineｰdiscrete γ dq1 a1 dq2 a2 :
      twins۰twin₁ γ dq1 a1 -∗
      twins۰twin₁ γ dq2 a2 -∗
        ⌜a1 ≡ a2⌝ ∗
        twins۰twin₁ γ (dq1 ⋅ dq2) a1.
    Proof.
      rewrite -discrete_eq -twins۰twin₁ｰcombine //.
    Qed.
    Lemma twins۰twin₁ｰvalidｰ2ｰdiscrete γ dq1 a1 dq2 a2 :
      twins۰twin₁ γ dq1 a1 -∗
      twins۰twin₁ γ dq2 a2 -∗
        ⌜✓ (dq1 ⋅ dq2)⌝ ∗
        ⌜a1 ≡ a2⌝.
    Proof.
      rewrite -discrete_eq -twins۰twin₁ｰvalidｰ2 //.
    Qed.
    Lemma twins۰twin₁ｰagreeｰdiscrete γ dq1 a1 dq2 a2 :
      twins۰twin₁ γ dq1 a1 -∗
      twins۰twin₁ γ dq2 a2 -∗
      ⌜a1 ≡ a2⌝.
    Proof.
      rewrite -discrete_eq -twins۰twin₁ｰagree //.
    Qed.

    Lemma twinsｰagreeｰdiscrete γ dq a b :
      twins۰twin₁ γ dq a -∗
      twins۰twin₂ γ b -∗
      ⌜a ≡ b⌝.
    Proof.
      rewrite -discrete_eq -twinsｰagree //.
    Qed.

    Section leibniz_equiv.
      Context `{!LeibnizEquiv $ oFunctor_apply F $ iPropO Σ}.

      Lemma twins۰twin₁ｰcombineｰL γ dq1 a1 dq2 a2 :
        twins۰twin₁ γ dq1 a1 -∗
        twins۰twin₁ γ dq2 a2 -∗
          ⌜a1 = a2⌝ ∗
          twins۰twin₁ γ (dq1 ⋅ dq2) a1.
      Proof.
        rewrite -leibniz_equiv_iff -twins۰twin₁ｰcombineｰdiscrete //.
      Qed.
      Lemma twins۰twin₁ｰvalidｰ2ｰL γ dq1 a1 dq2 a2 :
        twins۰twin₁ γ dq1 a1 -∗
        twins۰twin₁ γ dq2 a2 -∗
          ⌜✓ (dq1 ⋅ dq2)⌝ ∗
          ⌜a1 = a2⌝.
      Proof.
        rewrite -leibniz_equiv_iff -twins۰twin₁ｰvalidｰ2ｰdiscrete //.
      Qed.
      Lemma twins۰twin₁ｰagreeｰL γ dq1 a1 dq2 a2 :
        twins۰twin₁ γ dq1 a1 -∗
        twins۰twin₁ γ dq2 a2 -∗
        ⌜a1 = a2⌝.
      Proof.
        rewrite -leibniz_equiv_iff -twins۰twin₁ｰagreeｰdiscrete //.
      Qed.

      Lemma twinsｰagreeｰL γ dq a b :
        twins۰twin₁ γ dq a -∗
        twins۰twin₂ γ b -∗
        ⌜a = b⌝.
      Proof.
        rewrite -leibniz_equiv_iff -twinsｰagreeｰdiscrete //.
      Qed.
    End leibniz_equiv.
  End ofe_discrete.

  Lemma twinsｰupdateｰequivI {γ a1 b1} a2 b2 :
    twins۰twin₁ γ (DfracOwn 1) a1 -∗
    twins۰twin₂ γ b1 -∗
    a2 ≡ b2 ==∗
      twins۰twin₁ γ (DfracOwn 1) a2 ∗
      twins۰twin₂ γ b2.
  Proof.
    iIntros "Htwin₁ Htwin₂ Heq".
    iMod (own_update_2 with "Htwin₁ Htwin₂") as "($ & Htwin₂)"; first by apply twinsｰbothｰupdate.
    iRewrite "Heq" in "Htwin₂" => //.
  Qed.
  Lemma twinsｰupdateｰequiv {γ a1 b1} a2 b2 :
    a2 ≡ b2 →
    twins۰twin₁ γ (DfracOwn 1) a1 -∗
    twins۰twin₂ γ b1 ==∗
      twins۰twin₁ γ (DfracOwn 1) a2 ∗
      twins۰twin₂ γ b2.
  Proof.
    iIntros "% Htwin₁ Htwin₂".
    iApply (twinsｰupdateｰequivI with "Htwin₁ Htwin₂").
    iSteps.
  Qed.
  Lemma twinsｰupdate {γ a b} a' :
    twins۰twin₁ γ (DfracOwn 1) a -∗
    twins۰twin₂ γ b ==∗
      twins۰twin₁ γ (DfracOwn 1) a' ∗
      twins۰twin₂ γ a'.
  Proof.
    iApply twinsｰupdateｰequiv. done.
  Qed.
End twins۰G.

#[global] Opaque twins۰twin₁.
#[global] Opaque twins۰twin₂.
