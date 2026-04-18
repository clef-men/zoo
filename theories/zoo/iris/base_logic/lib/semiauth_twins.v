From zoo Require Import
  prelude.
From zoo.common Require Import
  countable.
From zoo.iris.base_logic Require Export
  lib.base.
From zoo.iris.base_logic Require Import
  lib.twins
  lib.auth_twins.
From zoo.iris Require Import
  diaframe.
From zoo Require Import
  options.

Class SemiauthTwinsG Σ (A : ofe) (R : relation A) F :=
  { #[local] semiauth_twins_G_left_twins_G :: AuthTwinsG Σ A R
  ; #[local] semiauth_twins_G_right_twins_G :: TwinsG Σ F
  }.

Definition semiauth_twins_Σ (A : ofe) (R : relation A) F `{!oFunctorContractive F} := #[
  auth_twins_Σ A R ;
  twins_Σ F
].
#[global] Instance subG_semiauth_twins_Σ Σ (A : ofe) (R : relation A) F `{!oFunctorContractive F} :
  subG (semiauth_twins_Σ A R F) Σ →
  SemiauthTwinsG Σ A R F.
Proof.
  solve_inG.
Qed.

Section semiauth_twins_G.
  Context {A : ofe} (R : relation A) (F : oFunctor).
  Context `{semiauth_twins_G : !SemiauthTwinsG Σ A R F}.

  Notation Rs := (
    rtc R
  ).

  Implicit Types a b : A.
  Implicit Types 𝑎 𝑏 : oFunctor_apply F $ iProp Σ.

  Record semiauth_twins_name :=
    { semiauth_twins_name_left_twins : auth_twins_name
    ; semiauth_twins_name_right_twins : gname
    }.
  Implicit Types γ : semiauth_twins_name.

  #[global] Instance semiauth_twins_name_eq_dec : EqDecision semiauth_twins_name :=
    ltac:(solve_decision).
  #[global] Instance semiauth_twins_name_countable :
    Countable semiauth_twins_name.
  Proof.
    solve_countable.
  Qed.

  Definition semiauth_twins_auth γ :=
    auth_twins_auth R γ.(semiauth_twins_name_left_twins).
  Definition semiauth_twins_twin1 γ a 𝑎 : iProp Σ :=
    auth_twins_twin1 R γ.(semiauth_twins_name_left_twins) a ∗
    twins_twin1 γ.(semiauth_twins_name_right_twins) (DfracOwn 1) 𝑎.
  #[local] Instance : CustomIpat "twin1" :=
    " ( Hltwin1{_{}}
      & Hrtwin1{_{}}
      )
    ".
  Definition semiauth_twins_twin2 γ a 𝑎 : iProp Σ :=
    auth_twins_twin2 R γ.(semiauth_twins_name_left_twins) a ∗
    twins_twin2 γ.(semiauth_twins_name_right_twins) 𝑎.
  #[local] Instance : CustomIpat "twin2" :=
    " ( Hltwin2{_{}}
      & Hrtwin2{_{}}
      )
    ".

  #[global] Instance semiauth_twins_auth_timeless γ a :
    Timeless (semiauth_twins_auth γ a).
  Proof.
    apply _.
  Qed.
  #[global] Instance semiauth_twins_twin1_timeless γ a 𝑎 :
    Discrete a →
    Discrete 𝑎 →
    Timeless (semiauth_twins_twin1 γ a 𝑎).
  Proof.
    apply _.
  Qed.
  #[global] Instance semiauth_twins_twin2_timeless γ a 𝑎 :
    Discrete a →
    Discrete 𝑎 →
    Timeless (semiauth_twins_twin2 γ a 𝑎).
  Proof.
    apply _.
  Qed.

  Lemma semiauth_twins_alloc a 𝑎 :
    ⊢ |==>
      ∃ γ,
      semiauth_twins_auth γ a ∗
      semiauth_twins_twin1 γ a 𝑎 ∗
      semiauth_twins_twin2 γ a 𝑎.
  Proof.
    iMod auth_twins_alloc as "(%γ_left_twins & Hauth & Hltwin1 & Hltwin2)".
    iMod twins_alloc' as "(%γ_right_twins & Hrtwin1 & Hrtwin2)".
    pose γ :=
      {|semiauth_twins_name_left_twins := γ_left_twins
      ; semiauth_twins_name_right_twins := γ_right_twins
      |}.
    iExists γ. iSteps.
  Qed.

  Lemma semiauth_twins_auth_exclusive `{!AntiSymm (≡) Rs} γ a1 a2 :
    semiauth_twins_auth γ a1 -∗
    semiauth_twins_auth γ a2 -∗
    False.
  Proof.
    apply: auth_twins_auth_exclusive.
  Qed.
  Lemma semiauth_twins_auth_exclusive_L `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ a1 a2 :
    semiauth_twins_auth γ a1 -∗
    semiauth_twins_auth γ a2 -∗
    False.
  Proof.
    apply: auth_twins_auth_exclusive_L.
  Qed.

  Lemma semiauth_twins_twin1_exclusive γ a1 𝑎1 a2 𝑎2 :
    semiauth_twins_twin1 γ a1 𝑎1 -∗
    semiauth_twins_twin1 γ a2 𝑎2 -∗
    False.
  Proof.
    iIntros "(:twin1 =1) (:twin1 =2)".
    iApply (twins_twin1_exclusive with "Hrtwin1_1 Hrtwin1_2").
  Qed.

  Lemma semiauth_twins_twin2_exclusive γ a1 𝑎1 a2 𝑎2 :
    semiauth_twins_twin2 γ a1 𝑎1 -∗
    semiauth_twins_twin2 γ a2 𝑎2 -∗
    False.
  Proof.
    iIntros "(:twin2 =1) (:twin2 =2)".
    iApply (twins_twin2_exclusive with "Hrtwin2_1 Hrtwin2_2").
  Qed.

  Lemma semiauth_twins_valid_1 γ a b 𝑎 :
    semiauth_twins_auth γ a -∗
    semiauth_twins_twin1 γ b 𝑎 -∗
    ⌜Rs b a⌝.
  Proof.
    iIntros "Hauth (:twin1)".
    iApply (auth_twins_valid_1 with "Hauth Hltwin1").
  Qed.
  Lemma semiauth_twins_valid_2 γ a b 𝑎 :
    semiauth_twins_auth γ a -∗
    semiauth_twins_twin2 γ b 𝑎 -∗
    ⌜Rs b a⌝.
  Proof.
    iIntros "Hauth (:twin2)".
    iApply (auth_twins_valid_2 with "Hauth Hltwin2").
  Qed.

  Lemma semiauth_twins_agree γ a1 𝑎1 a2 𝑎2 :
    semiauth_twins_twin1 γ a1 𝑎1 -∗
    semiauth_twins_twin2 γ a2 𝑎2 -∗
      a1 ≡ a2 ∗
      𝑎1 ≡ 𝑎2.
  Proof.
    iIntros "(:twin1) (:twin2)".
    iDestruct (auth_twins_agree with "Hltwin1 Hltwin2") as "$".
    iDestruct (twins_agree with "Hrtwin1 Hrtwin2") as "$".
  Qed.
  Lemma semiauth_twins_agree_discrete `{!OfeDiscrete A} `{!OfeDiscrete $ oFunctor_apply F $ iPropO Σ} γ a1 𝑎1 a2 𝑎2 :
    semiauth_twins_twin1 γ a1 𝑎1 -∗
    semiauth_twins_twin2 γ a2 𝑎2 -∗
      ⌜a1 ≡ a2⌝ ∗
      ⌜𝑎1 ≡ 𝑎2⌝.
  Proof.
    rewrite -!discrete_eq -semiauth_twins_agree //.
  Qed.
  Lemma semiauth_twins_agree_L `{!OfeDiscrete A} `{!LeibnizEquiv A} `{!OfeDiscrete $ oFunctor_apply F $ iPropO Σ} `{!LeibnizEquiv $ oFunctor_apply F $ iPropO Σ} γ a1 𝑎1 a2 𝑎2 :
    semiauth_twins_twin1 γ a1 𝑎1 -∗
    semiauth_twins_twin2 γ a2 𝑎2 -∗
      ⌜a1 = a2⌝ ∗
      ⌜𝑎1 = 𝑎2⌝.
  Proof.
    rewrite -!leibniz_equiv_iff -semiauth_twins_agree_discrete //.
  Qed.

  Lemma semiauth_twins_update_auth {γ a b1 𝑎1 b2 𝑎2} a' :
    semiauth_twins_auth γ a -∗
    semiauth_twins_twin1 γ b1 𝑎1 -∗
    semiauth_twins_twin2 γ b2 𝑎2 ==∗
      semiauth_twins_auth γ a' ∗
      semiauth_twins_twin1 γ a' 𝑎1 ∗
      semiauth_twins_twin2 γ a' 𝑎2.
  Proof.
    iIntros "Hauth (:twin1) (:twin2)".
    iMod (auth_twins_update_auth with "Hauth Hltwin1 Hltwin2") as "(Hauth & Hltwin1 & Hltwin2)".
    iSteps.
  Qed.
  Lemma semiauth_twins_update_twins {γ a1 𝑎1 a2 𝑎2} a 𝑎 :
    Rs a a1 →
    Rs a a2 →
    semiauth_twins_twin1 γ a1 𝑎1 -∗
    semiauth_twins_twin2 γ a2 𝑎2 ==∗
      semiauth_twins_twin1 γ a 𝑎 ∗
      semiauth_twins_twin2 γ a 𝑎.
  Proof.
    iIntros "% % (:twin1) (:twin2)".
    iMod (auth_twins_update_twins with "Hltwin1 Hltwin2") as "($ & $)"; [done.. |].
    iMod (twins_update with "Hrtwin1 Hrtwin2") as "($ & $)".
    iSteps.
  Qed.
  Lemma semiauth_twins_update_twins_L `{!OfeDiscrete A} `{!LeibnizEquiv A} {γ a1 𝑎1 a2 𝑎2} a 𝑎 :
    Rs a a1 →
    semiauth_twins_twin1 γ a1 𝑎1 -∗
    semiauth_twins_twin2 γ a2 𝑎2 ==∗
      semiauth_twins_twin1 γ a 𝑎 ∗
      semiauth_twins_twin2 γ a 𝑎.
  Proof.
    iIntros "%Ha Htwin1 Htwin2".
    iDestruct (semiauth_twins_agree with "Htwin1 Htwin2") as "#(<- & _)".
    iApply (semiauth_twins_update_twins with "Htwin1 Htwin2"); done.
  Qed.
  Lemma semiauth_twins_update_left_twins {γ a1 𝑎1 a2 𝑎2} a :
    Rs a a1 →
    Rs a a2 →
    semiauth_twins_twin1 γ a1 𝑎1 -∗
    semiauth_twins_twin2 γ a2 𝑎2 ==∗
      semiauth_twins_twin1 γ a 𝑎1 ∗
      semiauth_twins_twin2 γ a 𝑎2.
  Proof.
    iIntros "% % (:twin1) (:twin2)".
    iMod (auth_twins_update_twins with "Hltwin1 Hltwin2") as "($ & $)"; [done.. |].
    iSteps.
  Qed.
  Lemma semiauth_twins_update_left_twins_L `{!OfeDiscrete A} `{!LeibnizEquiv A} {γ a1 𝑎1 a2 𝑎2} a :
    Rs a a1 →
    semiauth_twins_twin1 γ a1 𝑎1 -∗
    semiauth_twins_twin2 γ a2 𝑎2 ==∗
      semiauth_twins_twin1 γ a 𝑎1 ∗
      semiauth_twins_twin2 γ a 𝑎2.
  Proof.
    iIntros "%Ha Htwin1 Htwin2".
    iDestruct (semiauth_twins_agree with "Htwin1 Htwin2") as "#(<- & _)".
    iApply (semiauth_twins_update_left_twins with "Htwin1 Htwin2"); done.
  Qed.
  Lemma semiauth_twins_update_right_twins {γ a1 𝑎1 a2 𝑎2} 𝑎 :
    semiauth_twins_twin1 γ a1 𝑎1 -∗
    semiauth_twins_twin2 γ a2 𝑎2 ==∗
      semiauth_twins_twin1 γ a1 𝑎 ∗
      semiauth_twins_twin2 γ a2 𝑎.
  Proof.
    iIntros "(:twin1) (:twin2)".
    iMod (twins_update with "Hrtwin1 Hrtwin2") as "($ & $)".
    iSteps.
  Qed.
End semiauth_twins_G.

#[global] Opaque semiauth_twins_auth.
#[global] Opaque semiauth_twins_twin1.
#[global] Opaque semiauth_twins_twin2.
