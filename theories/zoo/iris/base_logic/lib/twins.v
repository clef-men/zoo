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
#[global] Instance subG𑁒twins۰Σ Σ F `{!oFunctorContractive F} :
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

  #[global] Instance twins۰twin₁𑁒proper γ dq :
    Proper ((≡) ==> (≡)) (twins۰twin₁ γ dq).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance twins۰twin₂𑁒proper γ :
    Proper ((≡) ==> (≡)) (twins۰twin₂ γ).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance twins۰twin₁𑁒timeless γ dq a :
    Discrete a →
    Timeless (twins۰twin₁ γ dq a).
  Proof.
    apply _.
  Qed.
  #[global] Instance twins۰twin₂𑁒timeless γ a :
    Discrete a →
    Timeless (twins۰twin₂ γ a).
  Proof.
    apply _.
  Qed.

  #[global] Instance twins۰twin₁𑁒persistent γ a :
    Persistent (twins۰twin₁ γ DfracDiscarded a).
  Proof.
    apply _.
  Qed.

  #[global] Instance twins۰twin₁𑁒fractional γ a :
    Fractional (λ q, twins۰twin₁ γ (DfracOwn q) a).
  Proof.
    intros ?*. rewrite -own_op -twins۰twin₁𑁒dfrac𑁒op //.
  Qed.
  #[global] Instance twins۰twin₁𑁒as_fractional γ q a :
    AsFractional (twins۰twin₁ γ (DfracOwn q) a) (λ q, twins۰twin₁ γ (DfracOwn q) a) q.
  Proof.
    split; [done | apply _].
  Qed.

  Lemma twins𑁒alloc a b :
    a ≡ b →
    ⊢ |==>
      ∃ γ,
      twins۰twin₁ γ (DfracOwn 1) a ∗
      twins۰twin₂ γ b.
  Proof.
    iIntros.
    iMod (own_alloc (twins.twins۰twin₁ (DfracOwn 1) a ⋅ twins.twins۰twin₂ b)) as "(% & ? & ?)"; first by apply twins𑁒both𑁒valid.
    iSteps.
  Qed.
  Lemma twins𑁒alloc' a :
    ⊢ |==>
      ∃ γ,
      twins۰twin₁ γ (DfracOwn 1) a ∗ twins۰twin₂ γ a.
  Proof.
    iApply twins𑁒alloc. done.
  Qed.

  Lemma twins۰twin₁𑁒valid γ dq a :
    twins۰twin₁ γ dq a ⊢
    ⌜✓ dq⌝.
  Proof.
    iIntros "Htwin₁".
    iApply twins۰twin₁𑁒dfrac𑁒validI.
    iApply (own_valid with "Htwin₁").
  Qed.
  Lemma twins۰twin₁𑁒combine γ dq1 a1 dq2 a2 :
    twins۰twin₁ γ dq1 a1 -∗
    twins۰twin₁ γ dq2 a2 -∗
      a1 ≡ a2 ∗
      twins۰twin₁ γ (dq1 ⋅ dq2) a1.
  Proof.
    iIntros "Htwin₁1 Htwin₁2". iCombine "Htwin₁1 Htwin₁2" as "Htwin₁".
    iDestruct (own_valid with "Htwin₁") as "#Hvalid".
    iDestruct (twins۰twin₁𑁒dfrac𑁒op𑁒validI with "Hvalid") as "(% & Hequiv)".
    iRewrite -"Hequiv" in "Htwin₁". rewrite -twins۰twin₁𑁒dfrac𑁒op.
    auto.
  Qed.
  Lemma twins۰twin₁𑁒valid𑁒2 γ dq1 a1 dq2 a2 :
    twins۰twin₁ γ dq1 a1 -∗
    twins۰twin₁ γ dq2 a2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      a1 ≡ a2.
  Proof.
    iIntros "Htwin₁1 Htwin₁2".
    iDestruct (twins۰twin₁𑁒combine with "Htwin₁1 Htwin₁2") as "($ & Htwin₁)".
    iDestruct (twins۰twin₁𑁒valid with "Htwin₁") as "$".
  Qed.
  Lemma twins۰twin₁𑁒agree γ dq1 a1 dq2 a2 :
    twins۰twin₁ γ dq1 a1 -∗
    twins۰twin₁ γ dq2 a2 -∗
    a1 ≡ a2.
  Proof.
    iIntros "Htwin₁1 Htwin₁2".
    iDestruct (twins۰twin₁𑁒valid𑁒2 with "Htwin₁1 Htwin₁2") as "(_ & $)".
  Qed.
  Lemma twins۰twin₁𑁒dfrac𑁒ne γ1 dq1 a1 γ2 dq2 a2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    twins۰twin₁ γ1 dq1 a1 -∗
    twins۰twin₁ γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iIntros "% Htwin₁1 Htwin₁2 ->".
    iDestruct (twins۰twin₁𑁒valid𑁒2 with "Htwin₁1 Htwin₁2") as "(% & _)". done.
  Qed.
  Lemma twins۰twin₁𑁒ne γ1 a1 γ2 dq2 a2 :
    twins۰twin₁ γ1 (DfracOwn 1) a1 -∗
    twins۰twin₁ γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iApply twins۰twin₁𑁒dfrac𑁒ne; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma twins۰twin₁𑁒exclusive γ a1 dq2 a2 :
    twins۰twin₁ γ (DfracOwn 1) a1 -∗
    twins۰twin₁ γ dq2 a2 -∗
    False.
  Proof.
    iIntros "Htwin₁1 Htwin₁2".
    iDestruct (twins۰twin₁𑁒ne with "Htwin₁1 Htwin₁2") as %?. done.
  Qed.
  Lemma twins۰twin₁𑁒persist γ dq a :
    twins۰twin₁ γ dq a ⊢ |==>
    twins۰twin₁ γ DfracDiscarded a.
  Proof.
    apply own_update, twins۰twin₁𑁒persist.
  Qed.

  Lemma twins۰twin₂𑁒exclusive γ a1 a2 :
    twins۰twin₂ γ a1 -∗
    twins۰twin₂ γ a2 -∗
    False.
  Proof.
    iIntros "Htwin₂1 Htwin₂2".
    iApply twins۰twin₂𑁒op𑁒validI.
    iApply (own_valid_2 with "Htwin₂1 Htwin₂2").
  Qed.

  Lemma twins𑁒agree γ dq a b :
    twins۰twin₁ γ dq a -∗
    twins۰twin₂ γ b -∗
    a ≡ b.
  Proof.
    iIntros "Htwin₁ Htwin₂".
    iDestruct (own_valid_2 with "Htwin₁ Htwin₂") as "Hvalid".
    iDestruct (twins𑁒both𑁒dfrac𑁒validI with "Hvalid") as "(_ & $)".
  Qed.

  Section ofe_discrete.
    Context `{!OfeDiscrete $ oFunctor_apply F $ iPropO Σ}.

    Lemma twins۰twin₁𑁒combine𑁒discrete γ dq1 a1 dq2 a2 :
      twins۰twin₁ γ dq1 a1 -∗
      twins۰twin₁ γ dq2 a2 -∗
        ⌜a1 ≡ a2⌝ ∗
        twins۰twin₁ γ (dq1 ⋅ dq2) a1.
    Proof.
      rewrite -discrete_eq -twins۰twin₁𑁒combine //.
    Qed.
    Lemma twins۰twin₁𑁒valid𑁒2𑁒discrete γ dq1 a1 dq2 a2 :
      twins۰twin₁ γ dq1 a1 -∗
      twins۰twin₁ γ dq2 a2 -∗
        ⌜✓ (dq1 ⋅ dq2)⌝ ∗
        ⌜a1 ≡ a2⌝.
    Proof.
      rewrite -discrete_eq -twins۰twin₁𑁒valid𑁒2 //.
    Qed.
    Lemma twins۰twin₁𑁒agree𑁒discrete γ dq1 a1 dq2 a2 :
      twins۰twin₁ γ dq1 a1 -∗
      twins۰twin₁ γ dq2 a2 -∗
      ⌜a1 ≡ a2⌝.
    Proof.
      rewrite -discrete_eq -twins۰twin₁𑁒agree //.
    Qed.

    Lemma twins𑁒agree𑁒discrete γ dq a b :
      twins۰twin₁ γ dq a -∗
      twins۰twin₂ γ b -∗
      ⌜a ≡ b⌝.
    Proof.
      rewrite -discrete_eq -twins𑁒agree //.
    Qed.

    Section leibniz_equiv.
      Context `{!LeibnizEquiv $ oFunctor_apply F $ iPropO Σ}.

      Lemma twins۰twin₁𑁒combine𑁒L γ dq1 a1 dq2 a2 :
        twins۰twin₁ γ dq1 a1 -∗
        twins۰twin₁ γ dq2 a2 -∗
          ⌜a1 = a2⌝ ∗
          twins۰twin₁ γ (dq1 ⋅ dq2) a1.
      Proof.
        rewrite -leibniz_equiv_iff -twins۰twin₁𑁒combine𑁒discrete //.
      Qed.
      Lemma twins۰twin₁𑁒valid𑁒2𑁒L γ dq1 a1 dq2 a2 :
        twins۰twin₁ γ dq1 a1 -∗
        twins۰twin₁ γ dq2 a2 -∗
          ⌜✓ (dq1 ⋅ dq2)⌝ ∗
          ⌜a1 = a2⌝.
      Proof.
        rewrite -leibniz_equiv_iff -twins۰twin₁𑁒valid𑁒2𑁒discrete //.
      Qed.
      Lemma twins۰twin₁𑁒agree𑁒L γ dq1 a1 dq2 a2 :
        twins۰twin₁ γ dq1 a1 -∗
        twins۰twin₁ γ dq2 a2 -∗
        ⌜a1 = a2⌝.
      Proof.
        rewrite -leibniz_equiv_iff -twins۰twin₁𑁒agree𑁒discrete //.
      Qed.

      Lemma twins𑁒agree𑁒L γ dq a b :
        twins۰twin₁ γ dq a -∗
        twins۰twin₂ γ b -∗
        ⌜a = b⌝.
      Proof.
        rewrite -leibniz_equiv_iff -twins𑁒agree𑁒discrete //.
      Qed.
    End leibniz_equiv.
  End ofe_discrete.

  Lemma twins𑁒update𑁒equivI {γ a1 b1} a2 b2 :
    twins۰twin₁ γ (DfracOwn 1) a1 -∗
    twins۰twin₂ γ b1 -∗
    a2 ≡ b2 ==∗
      twins۰twin₁ γ (DfracOwn 1) a2 ∗
      twins۰twin₂ γ b2.
  Proof.
    iIntros "Htwin₁ Htwin₂ Heq".
    iMod (own_update_2 with "Htwin₁ Htwin₂") as "($ & Htwin₂)"; first by apply twins𑁒both𑁒update.
    iRewrite "Heq" in "Htwin₂" => //.
  Qed.
  Lemma twins𑁒update𑁒equiv {γ a1 b1} a2 b2 :
    a2 ≡ b2 →
    twins۰twin₁ γ (DfracOwn 1) a1 -∗
    twins۰twin₂ γ b1 ==∗
      twins۰twin₁ γ (DfracOwn 1) a2 ∗
      twins۰twin₂ γ b2.
  Proof.
    iIntros "% Htwin₁ Htwin₂".
    iApply (twins𑁒update𑁒equivI with "Htwin₁ Htwin₂").
    iSteps.
  Qed.
  Lemma twins𑁒update {γ a b} a' :
    twins۰twin₁ γ (DfracOwn 1) a -∗
    twins۰twin₂ γ b ==∗
      twins۰twin₁ γ (DfracOwn 1) a' ∗
      twins۰twin₂ γ a'.
  Proof.
    iApply twins𑁒update𑁒equiv. done.
  Qed.
End twins۰G.

#[global] Opaque twins۰twin₁.
#[global] Opaque twins۰twin₂.
