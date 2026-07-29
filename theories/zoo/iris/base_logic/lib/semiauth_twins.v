Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.iris.base_logic.lib.auth_twins.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Class SemiauthTwinsG Σ (A : ofe) (R : relation A) F :=
  { #[local] semiauth_twins۰G۰left_twins۰G :: AuthTwinsG Σ A R
  ; #[local] semiauth_twins۰G۰right_twins۰G :: TwinsG Σ F
  }.

Definition semiauth_twins۰Σ (A : ofe) (R : relation A) F `{!oFunctorContractive F} :=
  #[auth_twins۰Σ A R
  ; twins۰Σ F
  ].
#[global] Instance subGｰsemiauth_twins۰Σ Σ (A : ofe) (R : relation A) F `{!oFunctorContractive F} :
  subG (semiauth_twins۰Σ A R F) Σ →
  SemiauthTwinsG Σ A R F.
Proof.
  solve_inG.
Qed.

Section semiauth_twins۰G.
  Context {A : ofe} (R : relation A) (F : oFunctor).
  Context `{semiauth_twins۰G : !SemiauthTwinsG Σ A R F}.

  Notation Rs := (
    rtc R
  ).

  Implicit Type a b : A.
  Implicit Type 𝑎 𝑏 : oFunctor_apply F $ iProp Σ.

  Record semiauth_twins۰name :=
    { semiauth_twins۰name۰left_twins : auth_twins۰name
    ; semiauth_twins۰name۰right_twins : gname
    }.
  Implicit Type γ : semiauth_twins۰name.

  #[global] Instance semiauth_twins۰nameｰeq_dec : EqDecision semiauth_twins۰name :=
    ltac:(solve_decision).
  #[global] Instance semiauth_twins۰nameｰcountable :
    Countable semiauth_twins۰name.
  Proof.
    solve_countable.
  Qed.

  Definition semiauth_twins۰auth γ :=
    auth_twins۰auth R γ.(semiauth_twins۰name۰left_twins).
  Definition semiauth_twins۰twin₁ γ a 𝑎 : iProp Σ :=
    auth_twins۰twin₁ R γ.(semiauth_twins۰name۰left_twins) a ∗
    twins۰twin₁ γ.(semiauth_twins۰name۰right_twins) (DfracOwn 1) 𝑎.
  #[local] Instance : CustomIpat "twin₁" :=
    " ( Hltwin₁{_{}}
      & Hrtwin₁{_{}}
      )
    ".
  Definition semiauth_twins۰twin₂ γ a 𝑎 : iProp Σ :=
    auth_twins۰twin₂ R γ.(semiauth_twins۰name۰left_twins) a ∗
    twins۰twin₂ γ.(semiauth_twins۰name۰right_twins) 𝑎.
  #[local] Instance : CustomIpat "twin₂" :=
    " ( Hltwin₂{_{}}
      & Hrtwin₂{_{}}
      )
    ".

  #[global] Instance semiauth_twins۰authｰtimeless γ a :
    Timeless (semiauth_twins۰auth γ a).
  Proof.
    apply _.
  Qed.
  #[global] Instance semiauth_twins۰twin₁ｰtimeless γ a 𝑎 :
    Discrete a →
    Discrete 𝑎 →
    Timeless (semiauth_twins۰twin₁ γ a 𝑎).
  Proof.
    apply _.
  Qed.
  #[global] Instance semiauth_twins۰twin₂ｰtimeless γ a 𝑎 :
    Discrete a →
    Discrete 𝑎 →
    Timeless (semiauth_twins۰twin₂ γ a 𝑎).
  Proof.
    apply _.
  Qed.

  Lemma semiauth_twinsｰalloc a 𝑎 :
    ⊢ |==>
      ∃ γ,
      semiauth_twins۰auth γ a ∗
      semiauth_twins۰twin₁ γ a 𝑎 ∗
      semiauth_twins۰twin₂ γ a 𝑎.
  Proof.
    iMod auth_twinsｰalloc as "(%γ_left_twins & Hauth & Hltwin₁ & Hltwin₂)".
    iMod twinsｰalloc' as "(%γ_right_twins & Hrtwin₁ & Hrtwin₂)".
    pose γ :=
      {|semiauth_twins۰name۰left_twins := γ_left_twins
      ; semiauth_twins۰name۰right_twins := γ_right_twins
      |}.
    iExists γ. iSteps.
  Qed.

  Lemma semiauth_twins۰authｰexclusive `{!AntiSymm (≡) Rs} γ a1 a2 :
    semiauth_twins۰auth γ a1 -∗
    semiauth_twins۰auth γ a2 -∗
    False.
  Proof.
    apply: auth_twins۰authｰexclusive.
  Qed.
  Lemma semiauth_twins۰authｰexclusiveｰL `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ a1 a2 :
    semiauth_twins۰auth γ a1 -∗
    semiauth_twins۰auth γ a2 -∗
    False.
  Proof.
    apply: auth_twins۰authｰexclusiveｰL.
  Qed.

  Lemma semiauth_twins۰twin₁ｰexclusive γ a1 𝑎1 a2 𝑎2 :
    semiauth_twins۰twin₁ γ a1 𝑎1 -∗
    semiauth_twins۰twin₁ γ a2 𝑎2 -∗
    False.
  Proof.
    iIntros "(:twin₁ =1) (:twin₁ =2)".
    iApply (twins۰twin₁ｰexclusive with "Hrtwin₁_1 Hrtwin₁_2").
  Qed.

  Lemma semiauth_twins۰twin₂ｰexclusive γ a1 𝑎1 a2 𝑎2 :
    semiauth_twins۰twin₂ γ a1 𝑎1 -∗
    semiauth_twins۰twin₂ γ a2 𝑎2 -∗
    False.
  Proof.
    iIntros "(:twin₂ =1) (:twin₂ =2)".
    iApply (twins۰twin₂ｰexclusive with "Hrtwin₂_1 Hrtwin₂_2").
  Qed.

  Lemma semiauth_twinsｰvalid₁ γ a b 𝑎 :
    semiauth_twins۰auth γ a -∗
    semiauth_twins۰twin₁ γ b 𝑎 -∗
    ⌜Rs b a⌝.
  Proof.
    iIntros "Hauth (:twin₁)".
    iApply (auth_twinsｰvalid₁ with "Hauth Hltwin₁").
  Qed.
  Lemma semiauth_twinsｰvalid₂ γ a b 𝑎 :
    semiauth_twins۰auth γ a -∗
    semiauth_twins۰twin₂ γ b 𝑎 -∗
    ⌜Rs b a⌝.
  Proof.
    iIntros "Hauth (:twin₂)".
    iApply (auth_twinsｰvalid₂ with "Hauth Hltwin₂").
  Qed.

  Lemma semiauth_twinsｰagree γ a1 𝑎1 a2 𝑎2 :
    semiauth_twins۰twin₁ γ a1 𝑎1 -∗
    semiauth_twins۰twin₂ γ a2 𝑎2 -∗
      a1 ≡ a2 ∗
      𝑎1 ≡ 𝑎2.
  Proof.
    iIntros "(:twin₁) (:twin₂)".
    iDestruct (auth_twinsｰagree with "Hltwin₁ Hltwin₂") as "$".
    iDestruct (twinsｰagree with "Hrtwin₁ Hrtwin₂") as "$".
  Qed.
  Lemma semiauth_twinsｰagreeｰdiscrete `{!OfeDiscrete A} `{!OfeDiscrete $ oFunctor_apply F $ iPropO Σ} γ a1 𝑎1 a2 𝑎2 :
    semiauth_twins۰twin₁ γ a1 𝑎1 -∗
    semiauth_twins۰twin₂ γ a2 𝑎2 -∗
      ⌜a1 ≡ a2⌝ ∗
      ⌜𝑎1 ≡ 𝑎2⌝.
  Proof.
    rewrite -!discrete_eq -semiauth_twinsｰagree //.
  Qed.
  Lemma semiauth_twinsｰagreeｰL `{!OfeDiscrete A} `{!LeibnizEquiv A} `{!OfeDiscrete $ oFunctor_apply F $ iPropO Σ} `{!LeibnizEquiv $ oFunctor_apply F $ iPropO Σ} γ a1 𝑎1 a2 𝑎2 :
    semiauth_twins۰twin₁ γ a1 𝑎1 -∗
    semiauth_twins۰twin₂ γ a2 𝑎2 -∗
      ⌜a1 = a2⌝ ∗
      ⌜𝑎1 = 𝑎2⌝.
  Proof.
    rewrite -!leibniz_equiv_iff -semiauth_twinsｰagreeｰdiscrete //.
  Qed.

  Lemma semiauth_twinsｰupdateｰauth {γ a b1 𝑎1 b2 𝑎2} a' :
    semiauth_twins۰auth γ a -∗
    semiauth_twins۰twin₁ γ b1 𝑎1 -∗
    semiauth_twins۰twin₂ γ b2 𝑎2 ==∗
      semiauth_twins۰auth γ a' ∗
      semiauth_twins۰twin₁ γ a' 𝑎1 ∗
      semiauth_twins۰twin₂ γ a' 𝑎2.
  Proof.
    iIntros "Hauth (:twin₁) (:twin₂)".
    iMod (auth_twinsｰupdateｰauth with "Hauth Hltwin₁ Hltwin₂") as "(Hauth & Hltwin₁ & Hltwin₂)".
    iSteps.
  Qed.
  Lemma semiauth_twinsｰupdateｰtwins {γ a1 𝑎1 a2 𝑎2} a 𝑎 :
    Rs a a1 →
    Rs a a2 →
    semiauth_twins۰twin₁ γ a1 𝑎1 -∗
    semiauth_twins۰twin₂ γ a2 𝑎2 ==∗
      semiauth_twins۰twin₁ γ a 𝑎 ∗
      semiauth_twins۰twin₂ γ a 𝑎.
  Proof.
    iIntros "% % (:twin₁) (:twin₂)".
    iMod (auth_twinsｰupdateｰtwins with "Hltwin₁ Hltwin₂") as "($ & $)"; [done.. |].
    iMod (twinsｰupdate with "Hrtwin₁ Hrtwin₂") as "($ & $)".
    iSteps.
  Qed.
  Lemma semiauth_twinsｰupdateｰtwinsｰL `{!OfeDiscrete A} `{!LeibnizEquiv A} {γ a1 𝑎1 a2 𝑎2} a 𝑎 :
    Rs a a1 →
    semiauth_twins۰twin₁ γ a1 𝑎1 -∗
    semiauth_twins۰twin₂ γ a2 𝑎2 ==∗
      semiauth_twins۰twin₁ γ a 𝑎 ∗
      semiauth_twins۰twin₂ γ a 𝑎.
  Proof.
    iIntros "%Ha Htwin₁ Htwin₂".
    iDestruct (semiauth_twinsｰagree with "Htwin₁ Htwin₂") as "#(<- & _)".
    iApply (semiauth_twinsｰupdateｰtwins with "Htwin₁ Htwin₂"); done.
  Qed.
  Lemma semiauth_twinsｰupdateｰleft_twins {γ a1 𝑎1 a2 𝑎2} a :
    Rs a a1 →
    Rs a a2 →
    semiauth_twins۰twin₁ γ a1 𝑎1 -∗
    semiauth_twins۰twin₂ γ a2 𝑎2 ==∗
      semiauth_twins۰twin₁ γ a 𝑎1 ∗
      semiauth_twins۰twin₂ γ a 𝑎2.
  Proof.
    iIntros "% % (:twin₁) (:twin₂)".
    iMod (auth_twinsｰupdateｰtwins with "Hltwin₁ Hltwin₂") as "($ & $)"; [done.. |].
    iSteps.
  Qed.
  Lemma semiauth_twinsｰupdateｰleft_twinsｰL `{!OfeDiscrete A} `{!LeibnizEquiv A} {γ a1 𝑎1 a2 𝑎2} a :
    Rs a a1 →
    semiauth_twins۰twin₁ γ a1 𝑎1 -∗
    semiauth_twins۰twin₂ γ a2 𝑎2 ==∗
      semiauth_twins۰twin₁ γ a 𝑎1 ∗
      semiauth_twins۰twin₂ γ a 𝑎2.
  Proof.
    iIntros "%Ha Htwin₁ Htwin₂".
    iDestruct (semiauth_twinsｰagree with "Htwin₁ Htwin₂") as "#(<- & _)".
    iApply (semiauth_twinsｰupdateｰleft_twins with "Htwin₁ Htwin₂"); done.
  Qed.
  Lemma semiauth_twinsｰupdateｰright_twins {γ a1 𝑎1 a2 𝑎2} 𝑎 :
    semiauth_twins۰twin₁ γ a1 𝑎1 -∗
    semiauth_twins۰twin₂ γ a2 𝑎2 ==∗
      semiauth_twins۰twin₁ γ a1 𝑎 ∗
      semiauth_twins۰twin₂ γ a2 𝑎.
  Proof.
    iIntros "(:twin₁) (:twin₂)".
    iMod (twinsｰupdate with "Hrtwin₁ Hrtwin₂") as "($ & $)".
    iSteps.
  Qed.
End semiauth_twins۰G.

#[global] Opaque semiauth_twins۰auth.
#[global] Opaque semiauth_twins۰twin₁.
#[global] Opaque semiauth_twins۰twin₂.
