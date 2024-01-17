From zebre Require Import
  prelude.
From zebre.iris.algebra Require Import
  lib.auth_excl.
From zebre.iris.base_logic Require Export
  lib.base.
From zebre.iris.base_logic Require Import
  algebra.auth_excl.
From zebre.iris Require Import
  diaframe.
From zebre Require Import
  options.

Class AuthExclG Σ F := {
  #[local] auth_excl_G_inG :: inG Σ (auth_excl_R $ oFunctor_apply F $ iPropO Σ) ;
}.

Definition auth_excl_Σ F `{!oFunctorContractive F} := #[
  GFunctor (auth_excl_RF F)
].
#[global] Instance subG_auth_excl_Σ Σ F `{!oFunctorContractive F} :
  subG (auth_excl_Σ F) Σ →
  AuthExclG Σ F.
Proof.
  solve_inG.
Qed.

Section auth_excl_G.
  Context `{auth_excl_G : !AuthExclG Σ F}.

  Definition auth_excl_auth γ dq a :=
    own γ (●E{dq} a).
  Definition auth_excl_frag γ a :=
    own γ (◯E a).

  #[global] Instance auth_excl_auth_timeless γ dq a :
    Discrete a →
    Timeless (auth_excl_auth γ dq a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_excl_auth_persistent γ a :
    Persistent (auth_excl_auth γ DfracDiscarded a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_excl_frag_timeless γ a :
    Discrete a →
    Timeless (auth_excl_frag γ a).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_excl_auth_fractional γ a :
    Fractional (λ q, auth_excl_auth γ (DfracOwn q) a).
  Proof.
    intros ?*. rewrite -own_op -auth_excl_auth_dfrac_op //.
  Qed.
  #[global] Instance auth_excl_auth_as_fractional γ q a :
    AsFractional (auth_excl_auth γ (DfracOwn q) a) (λ q, auth_excl_auth γ (DfracOwn q) a) q.
  Proof.
    split; [done | apply _].
  Qed.

  Lemma auth_excl_alloc a b :
    a ≡ b →
    ⊢ |==>
      ∃ γ,
      auth_excl_auth γ (DfracOwn 1) a ∗
      auth_excl_frag γ b.
  Proof.
    iIntros.
    iMod (own_alloc (●E a ⋅ ◯E b)) as "(% & ? & ?)"; first by apply auth_excl_both_valid.
    iSteps.
  Qed.
  Lemma auth_excl_alloc' a :
    ⊢ |==>
      ∃ γ,
      auth_excl_auth γ (DfracOwn 1) a ∗ auth_excl_frag γ a.
  Proof.
    iApply auth_excl_alloc. done.
  Qed.

  Lemma auth_excl_auth_valid γ dq a :
    auth_excl_auth γ dq a ⊢
    ⌜✓ dq⌝.
  Proof.
    iIntros "H●".
    iApply auth_excl_auth_dfrac_validI.
    iApply (own_valid with "H●").
  Qed.
  Lemma auth_excl_auth_combine γ dq1 a1 dq2 a2 :
    auth_excl_auth γ dq1 a1 -∗
    auth_excl_auth γ dq2 a2 -∗
      auth_excl_auth γ (dq1 ⋅ dq2) a1 ∗
      a1 ≡ a2.
  Proof.
    iIntros "H●1 H●2". iCombine "H●1 H●2" as "H●".
    iDestruct (own_valid with "H●") as "#Hvalid".
    iDestruct (auth_excl_auth_dfrac_op_validI with "Hvalid") as "(% & Hequiv)".
    iRewrite -"Hequiv" in "H●". rewrite -auth_excl_auth_dfrac_op.
    auto with iFrame.
  Qed.
  Lemma auth_excl_auth_valid_2 γ dq1 a1 dq2 a2 :
    auth_excl_auth γ dq1 a1 -∗
    auth_excl_auth γ dq2 a2 -∗
    ⌜✓ (dq1 ⋅ dq2)⌝ ∧ a1 ≡ a2.
  Proof.
    iIntros "H●1 H●2".
    iDestruct (auth_excl_auth_combine with "H●1 H●2") as "(H● & $)".
    iDestruct (auth_excl_auth_valid with "H●") as "$".
  Qed.
  Lemma auth_excl_auth_agree γ dq1 a1 dq2 a2 :
    auth_excl_auth γ dq1 a1 -∗
    auth_excl_auth γ dq2 a2 -∗
    a1 ≡ a2.
  Proof.
    iIntros "H●1 H●2".
    iDestruct (auth_excl_auth_valid_2 with "H●1 H●2") as "(_ & $)".
  Qed.
  Lemma auth_excl_auth_dfrac_ne γ1 dq1 a1 γ2 dq2 a2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    auth_excl_auth γ1 dq1 a1 -∗
    auth_excl_auth γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iIntros "% H●1 H●2 ->".
    iDestruct (auth_excl_auth_valid_2 with "H●1 H●2") as "(% & _)".
    iSmash.
  Qed.
  Lemma auth_excl_auth_ne γ1 a1 γ2 dq2 a2 :
    auth_excl_auth γ1 (DfracOwn 1) a1 -∗
    auth_excl_auth γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    intros.
    iApply auth_excl_auth_dfrac_ne; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma auth_excl_auth_exclusive γ a1 a2 :
    auth_excl_auth γ (DfracOwn 1) a1 -∗
    auth_excl_auth γ (DfracOwn 1) a2 -∗
    False.
  Proof.
    iIntros "H●1 H●2".
    iDestruct (auth_excl_auth_valid_2 with "H●1 H●2") as "(% & _)".
    iSmash.
  Qed.
  Lemma auth_excl_auth_persist γ dq a :
    auth_excl_auth γ dq a ⊢ |==>
    auth_excl_auth γ DfracDiscarded a.
  Proof.
    apply own_update, auth_excl_auth_persist.
  Qed.

  Lemma auth_excl_frag_exclusive γ a1 a2 :
    auth_excl_frag γ a1 -∗
    auth_excl_frag γ a2 -∗
    False.
  Proof.
    iIntros "H◯1 H◯2".
    iApply auth_excl_frag_op_validI.
    iApply (own_valid_2 with "H◯1 H◯2").
  Qed.

  Lemma auth_excl_agree γ dq a b :
    auth_excl_auth γ dq a -∗
    auth_excl_frag γ b -∗
    a ≡ b.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as "Hvalid".
    iDestruct (auth_excl_both_dfrac_validI with "Hvalid") as "(_ & $)".
  Qed.

  Section ofe_discrete.
    Context `{!OfeDiscrete $ oFunctor_apply F $ iPropO Σ}.

    Lemma auth_excl_auth_combine_discrete γ dq1 a1 dq2 a2 :
      auth_excl_auth γ dq1 a1 -∗
      auth_excl_auth γ dq2 a2 -∗
        auth_excl_auth γ (dq1 ⋅ dq2) a1 ∗
        ⌜a1 ≡ a2⌝.
    Proof.
      rewrite -discrete_eq -auth_excl_auth_combine //.
    Qed.
    Lemma auth_excl_auth_valid_2_discrete γ dq1 a1 dq2 a2 :
      auth_excl_auth γ dq1 a1 -∗
      auth_excl_auth γ dq2 a2 -∗
      ⌜✓ (dq1 ⋅ dq2) ∧ a1 ≡ a2⌝.
    Proof.
      rewrite bi.pure_and -discrete_eq -auth_excl_auth_valid_2 //.
    Qed.
    Lemma auth_excl_auth_agree_discrete γ dq1 a1 dq2 a2 :
      auth_excl_auth γ dq1 a1 -∗
      auth_excl_auth γ dq2 a2 -∗
      ⌜a1 ≡ a2⌝.
    Proof.
      rewrite -discrete_eq -auth_excl_auth_agree //.
    Qed.

    Lemma auth_excl_agree_discrete γ dq a b :
      auth_excl_auth γ dq a -∗
      auth_excl_frag γ b -∗
      ⌜a ≡ b⌝.
    Proof.
      rewrite -discrete_eq -auth_excl_agree //.
    Qed.

    Section leibniz_equiv.
      Context `{!LeibnizEquiv $ oFunctor_apply F $ iPropO Σ}.

      Lemma auth_excl_auth_combine_L γ dq1 a1 dq2 a2 :
        auth_excl_auth γ dq1 a1 -∗
        auth_excl_auth γ dq2 a2 -∗
          auth_excl_auth γ (dq1 ⋅ dq2) a1 ∗
          ⌜a1 = a2⌝.
      Proof.
        rewrite -leibniz_equiv_iff -auth_excl_auth_combine_discrete //.
      Qed.
      Lemma auth_excl_auth_valid_2_L γ dq1 a1 dq2 a2 :
        auth_excl_auth γ dq1 a1 -∗
        auth_excl_auth γ dq2 a2 -∗
        ⌜✓ (dq1 ⋅ dq2) ∧ a1 = a2⌝.
      Proof.
        rewrite -leibniz_equiv_iff -auth_excl_auth_valid_2_discrete //.
      Qed.
      Lemma auth_excl_auth_agree_L γ dq1 a1 dq2 a2 :
        auth_excl_auth γ dq1 a1 -∗
        auth_excl_auth γ dq2 a2 -∗
        ⌜a1 = a2⌝.
      Proof.
        rewrite -leibniz_equiv_iff -auth_excl_auth_agree_discrete //.
      Qed.

      Lemma auth_excl_agree_L γ dq a b :
        auth_excl_auth γ dq a -∗
        auth_excl_frag γ b -∗
        ⌜a = b⌝.
      Proof.
        rewrite -leibniz_equiv_iff -auth_excl_agree_discrete //.
      Qed.
    End leibniz_equiv.
  End ofe_discrete.

  Lemma auth_excl_update {γ a b} a' b' :
    a' ≡ b' →
    auth_excl_auth γ (DfracOwn 1) a -∗
    auth_excl_frag γ b ==∗
      auth_excl_auth γ (DfracOwn 1) a' ∗
      auth_excl_frag γ b'.
  Proof.
    iIntros "% H● H◯".
    iMod (own_update_2 with "H● H◯") as "(? & ?)"; first by apply auth_excl_both_update.
    iSteps.
  Qed.
  Lemma auth_excl_update' {γ a b} a' :
    auth_excl_auth γ (DfracOwn 1) a -∗
    auth_excl_frag γ b ==∗
      auth_excl_auth γ (DfracOwn 1) a' ∗
      auth_excl_frag γ a'.
  Proof.
    iApply auth_excl_update. done.
  Qed.
End auth_excl_G.

#[global] Opaque auth_excl_auth.
#[global] Opaque auth_excl_frag.
