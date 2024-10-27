From zoo Require Import
  prelude.
From zoo.iris.algebra Require Import
  lib.twins.
From zoo.iris.base_logic Require Export
  lib.base.
From zoo.iris.base_logic Require Import
  algebra.twins.
From zoo.iris Require Import
  diaframe.
From zoo Require Import
  options.

Class TwinsG Σ F := {
  #[local] twins_G_inG :: inG Σ (twins_R $ oFunctor_apply F $ iPropO Σ) ;
}.

Definition twins_Σ F `{!oFunctorContractive F} := #[
  GFunctor (twins_RF F)
].
#[global] Instance subG_twins_Σ Σ F `{!oFunctorContractive F} :
  subG (twins_Σ F) Σ →
  TwinsG Σ F.
Proof.
  solve_inG.
Qed.

Section twins_G.
  Context `{twins_G : !TwinsG Σ F}.

  Definition twins_twin1 γ dq a :=
    own γ (twins_twin1 dq a).
  Definition twins_twin2 γ a :=
    own γ (twins_twin2 a).

  #[global] Instance twins_twin1_proper γ dq :
    Proper ((≡) ==> (≡)) (twins_twin1 γ dq).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance twins_twin2_proper γ :
    Proper ((≡) ==> (≡)) (twins_twin2 γ).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance twins_twin1_timeless γ dq a :
    Discrete a →
    Timeless (twins_twin1 γ dq a).
  Proof.
    apply _.
  Qed.
  #[global] Instance twins_twin1_persistent γ a :
    Persistent (twins_twin1 γ DfracDiscarded a).
  Proof.
    apply _.
  Qed.
  #[global] Instance twins_twin2_timeless γ a :
    Discrete a →
    Timeless (twins_twin2 γ a).
  Proof.
    apply _.
  Qed.

  #[global] Instance twins_twin1_fractional γ a :
    Fractional (λ q, twins_twin1 γ (DfracOwn q) a).
  Proof.
    intros ?*. rewrite -own_op -twins_twin1_dfrac_op //.
  Qed.
  #[global] Instance twins_twin1_as_fractional γ q a :
    AsFractional (twins_twin1 γ (DfracOwn q) a) (λ q, twins_twin1 γ (DfracOwn q) a) q.
  Proof.
    split; [done | apply _].
  Qed.

  Lemma twins_alloc a b :
    a ≡ b →
    ⊢ |==>
      ∃ γ,
      twins_twin1 γ (DfracOwn 1) a ∗
      twins_twin2 γ b.
  Proof.
    iIntros.
    iMod (own_alloc (twins.twins_twin1 (DfracOwn 1) a ⋅ twins.twins_twin2 b)) as "(% & ? & ?)"; first by apply twins_both_valid.
    iSteps.
  Qed.
  Lemma twins_alloc' a :
    ⊢ |==>
      ∃ γ,
      twins_twin1 γ (DfracOwn 1) a ∗ twins_twin2 γ a.
  Proof.
    iApply twins_alloc. done.
  Qed.

  Lemma twins_twin1_valid γ dq a :
    twins_twin1 γ dq a ⊢
    ⌜✓ dq⌝.
  Proof.
    iIntros "Htwin1".
    iApply twins_twin1_dfrac_validI.
    iApply (own_valid with "Htwin1").
  Qed.
  Lemma twins_twin1_combine γ dq1 a1 dq2 a2 :
    twins_twin1 γ dq1 a1 -∗
    twins_twin1 γ dq2 a2 -∗
      twins_twin1 γ (dq1 ⋅ dq2) a1 ∗
      a1 ≡ a2.
  Proof.
    iIntros "Htwin11 Htwin12". iCombine "Htwin11 Htwin12" as "Htwin1".
    iDestruct (own_valid with "Htwin1") as "#Hvalid".
    iDestruct (twins_twin1_dfrac_op_validI with "Hvalid") as "(% & Hequiv)".
    iRewrite -"Hequiv" in "Htwin1". rewrite -twins_twin1_dfrac_op.
    auto with iFrame.
  Qed.
  Lemma twins_twin1_valid_2 γ dq1 a1 dq2 a2 :
    twins_twin1 γ dq1 a1 -∗
    twins_twin1 γ dq2 a2 -∗
    ⌜✓ (dq1 ⋅ dq2)⌝ ∧ a1 ≡ a2.
  Proof.
    iIntros "Htwin11 Htwin12".
    iDestruct (twins_twin1_combine with "Htwin11 Htwin12") as "(Htwin1 & $)".
    iDestruct (twins_twin1_valid with "Htwin1") as "$".
  Qed.
  Lemma twins_twin1_agree γ dq1 a1 dq2 a2 :
    twins_twin1 γ dq1 a1 -∗
    twins_twin1 γ dq2 a2 -∗
    a1 ≡ a2.
  Proof.
    iIntros "Htwin11 Htwin12".
    iDestruct (twins_twin1_valid_2 with "Htwin11 Htwin12") as "(_ & $)".
  Qed.
  Lemma twins_twin1_dfrac_ne γ1 dq1 a1 γ2 dq2 a2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    twins_twin1 γ1 dq1 a1 -∗
    twins_twin1 γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iIntros "% Htwin11 Htwin12 ->".
    iDestruct (twins_twin1_valid_2 with "Htwin11 Htwin12") as "(% & _)".
    iSmash.
  Qed.
  Lemma twins_twin1_ne γ1 a1 γ2 dq2 a2 :
    twins_twin1 γ1 (DfracOwn 1) a1 -∗
    twins_twin1 γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    intros.
    iApply twins_twin1_dfrac_ne; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma twins_twin1_exclusive γ a1 a2 :
    twins_twin1 γ (DfracOwn 1) a1 -∗
    twins_twin1 γ (DfracOwn 1) a2 -∗
    False.
  Proof.
    iIntros "Htwin11 Htwin12".
    iDestruct (twins_twin1_valid_2 with "Htwin11 Htwin12") as "(% & _)".
    iSmash.
  Qed.
  Lemma twins_twin1_persist γ dq a :
    twins_twin1 γ dq a ⊢ |==>
    twins_twin1 γ DfracDiscarded a.
  Proof.
    apply own_update, twins_twin1_persist.
  Qed.

  Lemma twins_twin2_exclusive γ a1 a2 :
    twins_twin2 γ a1 -∗
    twins_twin2 γ a2 -∗
    False.
  Proof.
    iIntros "Htwin21 Htwin22".
    iApply twins_twin2_op_validI.
    iApply (own_valid_2 with "Htwin21 Htwin22").
  Qed.

  Lemma twins_agree γ dq a b :
    twins_twin1 γ dq a -∗
    twins_twin2 γ b -∗
    a ≡ b.
  Proof.
    iIntros "Htwin1 Htwin2".
    iDestruct (own_valid_2 with "Htwin1 Htwin2") as "Hvalid".
    iDestruct (twins_both_dfrac_validI with "Hvalid") as "(_ & $)".
  Qed.

  Section ofe_discrete.
    Context `{!OfeDiscrete $ oFunctor_apply F $ iPropO Σ}.

    Lemma twins_twin1_combine_discrete γ dq1 a1 dq2 a2 :
      twins_twin1 γ dq1 a1 -∗
      twins_twin1 γ dq2 a2 -∗
        twins_twin1 γ (dq1 ⋅ dq2) a1 ∗
        ⌜a1 ≡ a2⌝.
    Proof.
      rewrite -discrete_eq -twins_twin1_combine //.
    Qed.
    Lemma twins_twin1_valid_2_discrete γ dq1 a1 dq2 a2 :
      twins_twin1 γ dq1 a1 -∗
      twins_twin1 γ dq2 a2 -∗
      ⌜✓ (dq1 ⋅ dq2) ∧ a1 ≡ a2⌝.
    Proof.
      rewrite bi.pure_and -discrete_eq -twins_twin1_valid_2 //.
    Qed.
    Lemma twins_twin1_agree_discrete γ dq1 a1 dq2 a2 :
      twins_twin1 γ dq1 a1 -∗
      twins_twin1 γ dq2 a2 -∗
      ⌜a1 ≡ a2⌝.
    Proof.
      rewrite -discrete_eq -twins_twin1_agree //.
    Qed.

    Lemma twins_agree_discrete γ dq a b :
      twins_twin1 γ dq a -∗
      twins_twin2 γ b -∗
      ⌜a ≡ b⌝.
    Proof.
      rewrite -discrete_eq -twins_agree //.
    Qed.

    Section leibniz_equiv.
      Context `{!LeibnizEquiv $ oFunctor_apply F $ iPropO Σ}.

      Lemma twins_twin1_combine_L γ dq1 a1 dq2 a2 :
        twins_twin1 γ dq1 a1 -∗
        twins_twin1 γ dq2 a2 -∗
          twins_twin1 γ (dq1 ⋅ dq2) a1 ∗
          ⌜a1 = a2⌝.
      Proof.
        rewrite -leibniz_equiv_iff -twins_twin1_combine_discrete //.
      Qed.
      Lemma twins_twin1_valid_2_L γ dq1 a1 dq2 a2 :
        twins_twin1 γ dq1 a1 -∗
        twins_twin1 γ dq2 a2 -∗
        ⌜✓ (dq1 ⋅ dq2) ∧ a1 = a2⌝.
      Proof.
        rewrite -leibniz_equiv_iff -twins_twin1_valid_2_discrete //.
      Qed.
      Lemma twins_twin1_agree_L γ dq1 a1 dq2 a2 :
        twins_twin1 γ dq1 a1 -∗
        twins_twin1 γ dq2 a2 -∗
        ⌜a1 = a2⌝.
      Proof.
        rewrite -leibniz_equiv_iff -twins_twin1_agree_discrete //.
      Qed.

      Lemma twins_agree_L γ dq a b :
        twins_twin1 γ dq a -∗
        twins_twin2 γ b -∗
        ⌜a = b⌝.
      Proof.
        rewrite -leibniz_equiv_iff -twins_agree_discrete //.
      Qed.
    End leibniz_equiv.
  End ofe_discrete.

  Lemma twins_update {γ a b} a' b' :
    a' ≡ b' →
    twins_twin1 γ (DfracOwn 1) a -∗
    twins_twin2 γ b ==∗
      twins_twin1 γ (DfracOwn 1) a' ∗
      twins_twin2 γ b'.
  Proof.
    iIntros "% Htwin1 Htwin2".
    iMod (own_update_2 with "Htwin1 Htwin2") as "(? & ?)"; first by apply twins_both_update.
    iSteps.
  Qed.
  Lemma twins_update' {γ a b} a' :
    twins_twin1 γ (DfracOwn 1) a -∗
    twins_twin2 γ b ==∗
      twins_twin1 γ (DfracOwn 1) a' ∗
      twins_twin2 γ a'.
  Proof.
    iApply twins_update. done.
  Qed.
End twins_G.

#[global] Opaque twins_twin1.
#[global] Opaque twins_twin2.
