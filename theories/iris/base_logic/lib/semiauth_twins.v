From zebre Require Import
  prelude.
From zebre.iris.base_logic Require Export
  lib.base.
From zebre.iris.base_logic Require Import
  lib.ghost_var
  lib.auth_mono
  lib.twins.
From zebre.iris Require Import
  diaframe.
From zebre Require Import
  options.

Class SemiauthTwinsG Σ {A : ofe} (R : relation A) F := {
  #[local] semiauth_twins_G_var_G :: GhostVarG Σ gname ;
  #[local] semiauth_twins_G_mono_G :: AuthMonoG Σ R ;
  #[local] semiauth_twins_G_left_twins_G :: TwinsG Σ A ;
  #[local] semiauth_twins_G_right_twins_G :: TwinsG Σ F ;
}.

Definition semiauth_twins_Σ {A : ofe} (R : relation A) F `{!oFunctorContractive F} := #[
  ghost_var_Σ gname ;
  auth_mono_Σ R ;
  twins_Σ A ;
  twins_Σ F
].
#[global] Instance subG_semiauth_twins_Σ Σ {A : ofe} (R : relation A) F `{!oFunctorContractive F} :
  subG (semiauth_twins_Σ R F) Σ →
  SemiauthTwinsG Σ R F.
Proof.
  solve_inG.
Qed.

Section semiauth_twins_G.
  Context {A : ofe} (R : relation A) F `{semiauth_twins_G : !SemiauthTwinsG Σ R F}.

  Notation Rs := (
    rtc R
  ).

  Implicit Types a b : A.
  Implicit Types α β : oFunctor_apply F $ iProp Σ.

  Record semiauth_twins_name := {
    semiauth_twins_name_var : gname ;
    semiauth_twins_name_left_twins : gname ;
    semiauth_twins_name_right_twins : gname ;
  }.
  Implicit Types γ : semiauth_twins_name.

  #[global] Instance semiauth_twins_name_eq_dec : EqDecision semiauth_twins_name :=
    ltac:(solve_decision).
  #[global] Instance semiauth_twins_name_countable :
    Countable semiauth_twins_name.
  Proof.
    pose encode γ := (
      γ.(semiauth_twins_name_var),
      γ.(semiauth_twins_name_left_twins),
      γ.(semiauth_twins_name_right_twins)
    ).
    pose decode := λ '(γ_var, γ_left_twins, γ_right_twins), {|
      semiauth_twins_name_var := γ_var ;
      semiauth_twins_name_left_twins := γ_left_twins ;
      semiauth_twins_name_right_twins := γ_right_twins ;
    |}.
    refine (inj_countable' encode decode _). intros []. done.
  Qed.

  Definition semiauth_twins_auth γ a : iProp Σ :=
    ∃ η,
    ghost_var γ.(semiauth_twins_name_var) (DfracOwn (1/3)) η ∗
    auth_mono_auth R η (DfracOwn 1) a.
  Definition semiauth_twins_twin1 γ a α : iProp Σ :=
    ∃ η,
    ghost_var γ.(semiauth_twins_name_var) (DfracOwn (1/3)) η ∗
    auth_mono_lb R η a ∗
    twins_twin1 (twins_G := semiauth_twins_G_left_twins_G) γ.(semiauth_twins_name_left_twins) (DfracOwn 1) a ∗
    twins_twin1 (twins_G := semiauth_twins_G_right_twins_G) γ.(semiauth_twins_name_right_twins) (DfracOwn 1) α.
  Definition semiauth_twins_twin2 γ a α : iProp Σ :=
    ∃ η,
    ghost_var γ.(semiauth_twins_name_var) (DfracOwn (1/3)) η ∗
    auth_mono_lb R η a ∗
    twins_twin2 (twins_G := semiauth_twins_G_left_twins_G) γ.(semiauth_twins_name_left_twins) a ∗
    twins_twin2 (twins_G := semiauth_twins_G_right_twins_G) γ.(semiauth_twins_name_right_twins) α.

  #[global] Instance semiauth_twins_auth_timeless γ a :
    Timeless (semiauth_twins_auth γ a).
  Proof.
    apply _.
  Qed.
  #[global] Instance semiauth_twins_twin1_timeless γ a α :
    Discrete a →
    Discrete α →
    Timeless (semiauth_twins_twin1 γ a α).
  Proof.
    apply _.
  Qed.
  #[global] Instance semiauth_twins_twin2_timeless γ a α :
    Discrete a →
    Discrete α →
    Timeless (semiauth_twins_twin2 γ a α).
  Proof.
    apply _.
  Qed.

  Lemma semiauth_twins_alloc a α :
    ⊢ |==>
      ∃ γ,
      semiauth_twins_auth γ a ∗
      semiauth_twins_twin1 γ a α ∗
      semiauth_twins_twin2 γ a α.
  Proof.
    iMod (auth_mono_alloc _ a) as "(%η & Hauth)".
    iDestruct (auth_mono_lb_get with "Hauth") as "#Hlb".
    iMod (twins_alloc' (twins_G := semiauth_twins_G_left_twins_G) a) as "(%γ_left_twins & Hltwin1 & Hltwin2)".
    iMod (twins_alloc' (twins_G := semiauth_twins_G_right_twins_G) α) as "(%γ_right_twins & Hrtwin1 & Hrtwin2)".
    iMod (ghost_var_alloc η) as "(%γ_var & Hvar)".
    iEval (assert (1 = 1/3 + (1/3 + 1/3))%Qp as -> by compute_done) in "Hvar".
    iDestruct "Hvar" as "(Hvar1 & (Hvar2 & Hvar3))".
    iExists {|
      semiauth_twins_name_var := γ_var ;
      semiauth_twins_name_left_twins := γ_left_twins ;
      semiauth_twins_name_right_twins := γ_right_twins ;
    |}.
    iSteps.
  Qed.

  Lemma semiauth_twins_auth_exclusive `{!AntiSymm (≡) Rs} γ a1 a2 :
    semiauth_twins_auth γ a1 -∗
    semiauth_twins_auth γ a2 -∗
    False.
  Proof.
    iIntros "(%η & Hvar1 & Hauth1) (%_η & Hvar2 & Hauth2)".
    iDestruct (ghost_var_agree with "Hvar1 Hvar2") as %<-.
    iApply (auth_mono_auth_exclusive with "Hauth1 Hauth2").
  Qed.
  Lemma semiauth_twins_auth_exclusive_L `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ a1 a2 :
    semiauth_twins_auth γ a1 -∗
    semiauth_twins_auth γ a2 -∗
    False.
  Proof.
    iIntros "(%η & Hvar1 & Hauth1) (%_η & Hvar2 & Hauth2)".
    iDestruct (ghost_var_agree with "Hvar1 Hvar2") as %<-.
    iApply (auth_mono_auth_exclusive_L with "Hauth1 Hauth2").
  Qed.

  Lemma semiauth_twins_twin1_exclusive γ a1 α1 a2 α2 :
    semiauth_twins_twin1 γ a1 α1 -∗
    semiauth_twins_twin1 γ a2 α2 -∗
    False.
  Proof.
    iIntros "(%η & Hvar1 & _ & Hltwin1_1 & _) (%_η & Hvar2 & _ & Hltwin1_2 & _)".
    iDestruct (ghost_var_agree with "Hvar1 Hvar2") as %<-.
    iApply (twins_twin1_exclusive with "Hltwin1_1 Hltwin1_2").
  Qed.

  Lemma semiauth_twins_twin2_exclusive γ a1 α1 a2 α2 :
    semiauth_twins_twin2 γ a1 α1 -∗
    semiauth_twins_twin2 γ a2 α2 -∗
    False.
  Proof.
    iIntros "(%η & Hvar1 & _ & Hltwin2_1 & _) (%_η & Hvar2 & _ & Hltwin2_2 & _)".
    iDestruct (ghost_var_agree with "Hvar1 Hvar2") as %<-.
    iApply (twins_twin2_exclusive with "Hltwin2_1 Hltwin2_2").
  Qed.

  Lemma semiauth_twins_valid_1 γ a b α :
    semiauth_twins_auth γ a -∗
    semiauth_twins_twin1 γ b α -∗
    ⌜Rs b a⌝.
  Proof.
    iIntros "(%η & Hvar1 & Hauth) (%_η & Hvar2 & Hlb & _)".
    iDestruct (ghost_var_agree with "Hvar1 Hvar2") as %<-.
    iApply (auth_mono_lb_valid with "Hauth Hlb").
  Qed.
  Lemma semiauth_twins_valid_2 γ a b α :
    semiauth_twins_auth γ a -∗
    semiauth_twins_twin2 γ b α -∗
    ⌜Rs b a⌝.
  Proof.
    iIntros "(%η & Hvar1 & Hauth) (%_η & Hvar2 & Hlb & _)".
    iDestruct (ghost_var_agree with "Hvar1 Hvar2") as %<-.
    iApply (auth_mono_lb_valid with "Hauth Hlb").
  Qed.

  Lemma semiauth_twins_agree γ a1 α1 a2 α2 :
    semiauth_twins_twin1 γ a1 α1 -∗
    semiauth_twins_twin2 γ a2 α2 -∗
      a1 ≡ a2 ∗
      α1 ≡ α2.
  Proof.
    iIntros "(%η & Hvar1 & _ & Hltwin1 & Hrtwin1) (%_η & Hvar2 & _ & Hltwin2 & Hrtwin2)".
    iDestruct (ghost_var_agree with "Hvar1 Hvar2") as %<-.
    iDestruct (twins_agree with "Hltwin1 Hltwin2") as "$".
    iDestruct (twins_agree with "Hrtwin1 Hrtwin2") as "$".
  Qed.
  Lemma semiauth_twins_agree_discrete `{!OfeDiscrete A} `{!OfeDiscrete $ oFunctor_apply F $ iPropO Σ} γ a1 α1 a2 α2 :
    semiauth_twins_twin1 γ a1 α1 -∗
    semiauth_twins_twin2 γ a2 α2 -∗
      ⌜a1 ≡ a2⌝ ∗
      ⌜α1 ≡ α2⌝.
  Proof.
    rewrite -!discrete_eq -semiauth_twins_agree //.
  Qed.
  Lemma semiauth_twins_agree_L `{!OfeDiscrete A} `{!LeibnizEquiv A} `{!OfeDiscrete $ oFunctor_apply F $ iPropO Σ} `{!LeibnizEquiv $ oFunctor_apply F $ iPropO Σ} γ a1 α1 a2 α2 :
    semiauth_twins_twin1 γ a1 α1 -∗
    semiauth_twins_twin2 γ a2 α2 -∗
      ⌜a1 = a2⌝ ∗
      ⌜α1 = α2⌝.
  Proof.
    rewrite -!leibniz_equiv_iff -semiauth_twins_agree_discrete //.
  Qed.

  Lemma semiauth_twins_update_auth {γ a b1 α1 b2 α2} a' :
    semiauth_twins_auth γ a -∗
    semiauth_twins_twin1 γ b1 α1 -∗
    semiauth_twins_twin2 γ b2 α2 ==∗
      semiauth_twins_auth γ a' ∗
      semiauth_twins_twin1 γ a' α1 ∗
      semiauth_twins_twin2 γ a' α2.
  Proof.
    assert (1 = 1/3 + (1/3 + 1/3))%Qp as Heq by compute_done.
    iIntros "(%η & Hvar1 & _) (%_η1 & Hvar2 & _ & Hltwin1 & Hrtwin1) (%_η2 & Hvar3 & _ & Hltwin2 & Hrtwin2)".
    iDestruct (ghost_var_agree with "Hvar1 Hvar2") as %<-.
    iDestruct (ghost_var_agree with "Hvar1 Hvar3") as %<-.
    iCombine "Hvar1 Hvar2 Hvar3" as "Hvar". rewrite -Heq.
    iMod (twins_update (twins_G := semiauth_twins_G_left_twins_G) a' a' with "Hltwin1 Hltwin2") as "(Hltwin1 & Hltwin2)"; first done.
    iMod (auth_mono_alloc _ a') as "(%η' & Hauth)".
    iDestruct (auth_mono_lb_get with "Hauth") as "#Hlb".
    iMod (ghost_var_update η' with "Hvar") as "Hvar".
    iEval (rewrite Heq) in "Hvar". iDestruct "Hvar" as "(Hvar1 & (Hvar2 & Hvar3))".
    iSteps.
  Qed.
  Lemma semiauth_twins_update_twins {γ a1 α1 a2 α2} a α :
    Rs a a1 →
    Rs a a2 →
    semiauth_twins_twin1 γ a1 α1 -∗
    semiauth_twins_twin2 γ a2 α2 ==∗
      semiauth_twins_twin1 γ a α ∗
      semiauth_twins_twin2 γ a α.
  Proof.
    iIntros "%Ha1 %Ha2 (%η & Hvar1 & #Hlb & Hltwin1 & Hrtwin1) (%_η & Hvar2 & _ & Hltwin2 & Hrtwin2)".
    iDestruct (ghost_var_agree with "Hvar1 Hvar2") as %<-.
    iMod (twins_update' (twins_G := semiauth_twins_G_left_twins_G) a with "Hltwin1 Hltwin2") as "(Hltwin1 & Hltwin2)".
    iMod (twins_update' (twins_G := semiauth_twins_G_right_twins_G) α with "Hrtwin1 Hrtwin2") as "(Hrtwin1 & Hrtwin2)".
    iDestruct (auth_mono_lb_mono with "Hlb") as "#Hlb'"; first done.
    iSteps.
  Qed.
  Lemma semiauth_twins_update_twins_L `{!OfeDiscrete A} `{!LeibnizEquiv A} {γ a1 α1 a2 α2} a α :
    Rs a a1 →
    semiauth_twins_twin1 γ a1 α1 -∗
    semiauth_twins_twin2 γ a2 α2 ==∗
      semiauth_twins_twin1 γ a α ∗
      semiauth_twins_twin2 γ a α.
  Proof.
    iIntros "%Ha Htwin1 Htwin2".
    iDestruct (semiauth_twins_agree with "Htwin1 Htwin2") as "#(<- & _)".
    iApply (semiauth_twins_update_twins with "Htwin1 Htwin2"); done.
  Qed.
  Lemma semiauth_twins_update_left_twins {γ a1 α1 a2 α2} a :
    Rs a a1 →
    Rs a a2 →
    semiauth_twins_twin1 γ a1 α1 -∗
    semiauth_twins_twin2 γ a2 α2 ==∗
      semiauth_twins_twin1 γ a α1 ∗
      semiauth_twins_twin2 γ a α2.
  Proof.
    iIntros "%Ha1 %Ha2 (%η & Hvar1 & #Hlb & Hltwin1 & Hrtwin1) (%_η & Hvar2 & _ & Hltwin2 & Hrtwin2)".
    iDestruct (ghost_var_agree with "Hvar1 Hvar2") as %<-.
    iMod (twins_update' (twins_G := semiauth_twins_G_left_twins_G) a with "Hltwin1 Hltwin2") as "(Hltwin1 & Hltwin2)".
    iDestruct (auth_mono_lb_mono with "Hlb") as "#Hlb'"; first done.
    iSteps.
  Qed.
  Lemma semiauth_twins_update_left_twins_L `{!OfeDiscrete A} `{!LeibnizEquiv A} {γ a1 α1 a2 α2} a :
    Rs a a1 →
    semiauth_twins_twin1 γ a1 α1 -∗
    semiauth_twins_twin2 γ a2 α2 ==∗
      semiauth_twins_twin1 γ a α1 ∗
      semiauth_twins_twin2 γ a α2.
  Proof.
    iIntros "%Ha Htwin1 Htwin2".
    iDestruct (semiauth_twins_agree with "Htwin1 Htwin2") as "#(<- & _)".
    iApply (semiauth_twins_update_left_twins with "Htwin1 Htwin2"); done.
  Qed.
  Lemma semiauth_twins_update_right_twins {γ a1 α1 a2 α2} α :
    semiauth_twins_twin1 γ a1 α1 -∗
    semiauth_twins_twin2 γ a2 α2 ==∗
      semiauth_twins_twin1 γ a1 α ∗
      semiauth_twins_twin2 γ a2 α.
  Proof.
    iIntros "(%η & Hvar1 & #Hlb1 & Hltwin1 & Hrtwin1) (%_η & Hvar2 & #Hlb2 & Hltwin2 & Hrtwin2)".
    iDestruct (ghost_var_agree with "Hvar1 Hvar2") as %<-.
    iMod (twins_update' (twins_G := semiauth_twins_G_right_twins_G) α with "Hrtwin1 Hrtwin2") as "(Hrtwin1 & Hrtwin2)".
    iSteps.
  Qed.
End semiauth_twins_G.

#[global] Opaque semiauth_twins_auth.
#[global] Opaque semiauth_twins_twin1.
#[global] Opaque semiauth_twins_twin2.
