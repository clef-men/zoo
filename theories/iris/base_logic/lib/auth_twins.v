From zebre Require Import
  prelude.
From zebre.iris.base_logic Require Export
  lib.base.
From zebre.iris.base_logic Require Import
  lib.semiauth_twins.
From zebre.iris Require Import
  diaframe.
From zebre Require Import
  options.

Class AuthTwinsG Σ {A : ofe} (R : relation A) := {
  #[local] auth_twins_G_semiauth_twins_G :: SemiauthTwinsG Σ R unitO ;
}.

Definition auth_twins_Σ {A : ofe} (R : relation A) := #[
  semiauth_twins_Σ R unitO
].
#[global] Instance subG_auth_twins_Σ Σ {A : ofe} (R : relation A) :
  subG (auth_twins_Σ R) Σ →
  AuthTwinsG Σ R.
Proof.
  solve_inG.
Qed.

Section auth_twins_G.
  Context {A : ofe} (R : relation A) `{auth_twins_G : !AuthTwinsG Σ R}.

  Notation Rs := (
    rtc R
  ).

  Implicit Types a b : A.

  Definition auth_twins_name :=
    semiauth_twins_name.
  Implicit Types γ : auth_twins_name.

  #[global] Instance auth_twins_name_eq_dec : EqDecision auth_twins_name :=
    ltac:(solve_decision).
  #[global] Instance auth_twins_name_countable :
    Countable auth_twins_name.
  Proof.
    apply _.
  Qed.

  Definition auth_twins_auth γ a : iProp Σ :=
    semiauth_twins_auth R unitO γ a.
  Definition auth_twins_twin1 γ a : iProp Σ :=
    semiauth_twins_twin1 R unitO γ a ().
  Definition auth_twins_twin2 γ a : iProp Σ :=
    semiauth_twins_twin2 R unitO γ a ().

  #[global] Instance auth_twins_auth_timeless γ a :
    Timeless (auth_twins_auth γ a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_twins_twin1_timeless γ a :
    Discrete a →
    Timeless (auth_twins_twin1 γ a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_twins_twin2_timeless γ a :
    Discrete a →
    Timeless (auth_twins_twin2 γ a).
  Proof.
    apply _.
  Qed.

  Lemma auth_twins_alloc a :
    ⊢ |==>
      ∃ γ,
      auth_twins_auth γ a ∗
      auth_twins_twin1 γ a ∗
      auth_twins_twin2 γ a.
  Proof.
    apply semiauth_twins_alloc.
  Qed.

  Lemma auth_twins_auth_exclusive `{!AntiSymm (≡) Rs} γ a1 a2 :
    auth_twins_auth γ a1 -∗
    auth_twins_auth γ a2 -∗
    False.
  Proof.
    apply: semiauth_twins_auth_exclusive.
  Qed.
  Lemma auth_twins_auth_exclusive_L `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ a1 a2 :
    auth_twins_auth γ a1 -∗
    auth_twins_auth γ a2 -∗
    False.
  Proof.
    apply: semiauth_twins_auth_exclusive_L.
  Qed.

  Lemma auth_twins_twin1_exclusive γ a1 a2 :
    auth_twins_twin1 γ a1 -∗
    auth_twins_twin1 γ a2 -∗
    False.
  Proof.
    apply semiauth_twins_twin1_exclusive.
  Qed.

  Lemma auth_twins_twin2_exclusive γ a1 a2 :
    auth_twins_twin2 γ a1 -∗
    auth_twins_twin2 γ a2 -∗
    False.
  Proof.
    apply semiauth_twins_twin2_exclusive.
  Qed.

  Lemma auth_twins_valid_1 γ a b :
    auth_twins_auth γ a -∗
    auth_twins_twin1 γ b -∗
    ⌜Rs b a⌝.
  Proof.
    apply semiauth_twins_valid_1.
  Qed.
  Lemma auth_twins_valid_2 γ a b :
    auth_twins_auth γ a -∗
    auth_twins_twin2 γ b -∗
    ⌜Rs b a⌝.
  Proof.
    apply semiauth_twins_valid_2.
  Qed.

  Lemma auth_twins_agree γ a1 a2 :
    auth_twins_twin1 γ a1 -∗
    auth_twins_twin2 γ a2 -∗
    a1 ≡ a2.
  Proof.
    iIntros "Htwin1 Htwin2".
    iDestruct (semiauth_twins_agree with "Htwin1 Htwin2") as "($ & _)".
  Qed.
  Lemma auth_twins_agree_discrete `{!OfeDiscrete A} γ a1 a2 :
    auth_twins_twin1 γ a1 -∗
    auth_twins_twin2 γ a2 -∗
    ⌜a1 ≡ a2⌝.
  Proof.
    iIntros "Htwin1 Htwin2".
    iDestruct (semiauth_twins_agree_discrete with "Htwin1 Htwin2") as "($ & _)".
  Qed.
  Lemma auth_twins_agree_L `{!OfeDiscrete A} `{!LeibnizEquiv A} γ a1 a2 :
    auth_twins_twin1 γ a1 -∗
    auth_twins_twin2 γ a2 -∗
    ⌜a1 = a2⌝.
  Proof.
    iIntros "Htwin1 Htwin2".
    iDestruct (semiauth_twins_agree_L with "Htwin1 Htwin2") as "($ & _)".
  Qed.

  Lemma auth_twins_update_auth {γ a b1 b2} a' :
    auth_twins_auth γ a -∗
    auth_twins_twin1 γ b1 -∗
    auth_twins_twin2 γ b2 ==∗
      auth_twins_auth γ a' ∗
      auth_twins_twin1 γ a' ∗
      auth_twins_twin2 γ a'.
  Proof.
    apply semiauth_twins_update_auth.
  Qed.
  Lemma auth_twins_update_twins {γ a1 a2} a :
    Rs a a1 →
    Rs a a2 →
    auth_twins_twin1 γ a1 -∗
    auth_twins_twin2 γ a2 ==∗
      auth_twins_twin1 γ a ∗
      auth_twins_twin2 γ a.
  Proof.
    apply semiauth_twins_update_twins.
  Qed.
  Lemma auth_twins_update_twins_L `{!OfeDiscrete A} `{!LeibnizEquiv A} {γ a1 a2} a :
    Rs a a1 →
    auth_twins_twin1 γ a1 -∗
    auth_twins_twin2 γ a2 ==∗
      auth_twins_twin1 γ a ∗
      auth_twins_twin2 γ a.
  Proof.
    apply: semiauth_twins_update_twins_L.
  Qed.
End auth_twins_G.

#[global] Opaque auth_twins_name.
#[global] Opaque auth_twins_auth.
#[global] Opaque auth_twins_twin1.
#[global] Opaque auth_twins_twin2.
