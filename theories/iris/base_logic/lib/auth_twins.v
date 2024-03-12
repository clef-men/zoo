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

Class AuthTwinsG Σ {A : ofe} (R : relation A) := {
  #[local] auth_twins_G_var_G :: GhostVarG Σ (gname * gname) ;
  #[local] auth_twins_G_mono_G :: AuthMonoG Σ R ;
  #[local] auth_twins_G_twins_G :: TwinsG Σ A ;
}.

Definition auth_twins_Σ {A : ofe} (R : relation A) := #[
  ghost_var_Σ (gname * gname) ;
  auth_mono_Σ R ;
  twins_Σ A
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

  Definition auth_twins_auth γ a : iProp Σ :=
    ∃ γs,
    ghost_var γ (DfracOwn (1/3)) γs ∗
    auth_mono_auth R γs.1 (DfracOwn 1) a.
  Definition auth_twins_twin1 γ a : iProp Σ :=
    ∃ γs,
    ghost_var γ (DfracOwn (1/3)) γs ∗
    auth_mono_lb R γs.1 a ∗
    twins_twin1 γs.2 (DfracOwn 1) a.
  Definition auth_twins_twin2 γ a : iProp Σ :=
    ∃ γs,
    ghost_var γ (DfracOwn (1/3)) γs ∗
    auth_mono_lb R γs.1 a ∗
    twins_twin2 γs.2 a.

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
    iMod (auth_mono_alloc _ a) as "(%γ_mono & Hauth)".
    iDestruct (auth_mono_lb_get with "Hauth") as "#Hlb".
    iMod (twins_alloc' (twins_G := auth_twins_G_twins_G) a) as "(%γ_twins & Htwin1 & Htwin2)".
    iMod (ghost_var_alloc (γ_mono, γ_twins)) as "(%γ & Hγ)".
    iEval (assert (1 = 1/3 + (1/3 + 1/3))%Qp as -> by compute_done) in "Hγ".
    iDestruct "Hγ" as "(Hγ1 & (Hγ2 & Hγ3))".
    iSteps.
  Qed.

  Lemma auth_twins_auth_exclusive `{!AntiSymm (≡) Rs} γ a1 a2 :
    auth_twins_auth γ a1 -∗
    auth_twins_auth γ a2 -∗
    False.
  Proof.
    iIntros "(%γs & Hγ1 & Hauth1) (%_γs & Hγ2 & Hauth2)".
    iDestruct (ghost_var_agree with "Hγ1 Hγ2") as %<-.
    iApply (auth_mono_auth_exclusive with "Hauth1 Hauth2").
  Qed.
  Lemma auth_twins_auth_exclusive_L `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ a1 a2 :
    auth_twins_auth γ a1 -∗
    auth_twins_auth γ a2 -∗
    False.
  Proof.
    iIntros "(%γs & Hγ1 & Hauth1) (%_γs & Hγ2 & Hauth2)".
    iDestruct (ghost_var_agree with "Hγ1 Hγ2") as %<-.
    iApply (auth_mono_auth_exclusive_L with "Hauth1 Hauth2").
  Qed.

  Lemma auth_twins_twin1_exclusive γ a1 a2 :
    auth_twins_twin1 γ a1 -∗
    auth_twins_twin1 γ a2 -∗
    False.
  Proof.
    iIntros "(%γs & Hγ1 & _ & Htwin1_1) (%_γs & Hγ2 & _ & Htwin1_2)".
    iDestruct (ghost_var_agree with "Hγ1 Hγ2") as %<-.
    iApply (twins_twin1_exclusive with "Htwin1_1 Htwin1_2").
  Qed.

  Lemma auth_twins_twin2_exclusive γ a1 a2 :
    auth_twins_twin2 γ a1 -∗
    auth_twins_twin2 γ a2 -∗
    False.
  Proof.
    iIntros "(%γs & Hγ1 & _ & Htwin2_1) (%_γs & Hγ2 & _ & Htwin2_2)".
    iDestruct (ghost_var_agree with "Hγ1 Hγ2") as %<-.
    iApply (twins_twin2_exclusive with "Htwin2_1 Htwin2_2").
  Qed.

  Lemma auth_twins_auth_twin1_valid γ a b :
    auth_twins_auth γ a -∗
    auth_twins_twin1 γ b -∗
    ⌜Rs b a⌝.
  Proof.
    iIntros "(%γs & Hγ1 & Hauth) (%_γs & Hγ2 & Hlb & _)".
    iDestruct (ghost_var_agree with "Hγ1 Hγ2") as %<-.
    iApply (auth_mono_lb_valid with "Hauth Hlb").
  Qed.
  Lemma auth_twins_auth_twin2_valid γ a b :
    auth_twins_auth γ a -∗
    auth_twins_twin2 γ b -∗
    ⌜Rs b a⌝.
  Proof.
    iIntros "(%γs & Hγ1 & Hauth) (%_γs & Hγ2 & Hlb & _)".
    iDestruct (ghost_var_agree with "Hγ1 Hγ2") as %<-.
    iApply (auth_mono_lb_valid with "Hauth Hlb").
  Qed.

  Lemma auth_twins_frags_agree γ a1 a2 :
    auth_twins_twin1 γ a1 -∗
    auth_twins_twin2 γ a2 -∗
    a1 ≡ a2.
  Proof.
    iIntros "(%γs & Hγ1 & _ & Htwin1) (%_γs & Hγ2 & _ & Htwin2)".
    iDestruct (ghost_var_agree with "Hγ1 Hγ2") as %<-.
    iApply (twins_agree with "Htwin1 Htwin2").
  Qed.
  Lemma auth_twins_frags_agree_discrete `{!OfeDiscrete A} γ a1 a2 :
    auth_twins_twin1 γ a1 -∗
    auth_twins_twin2 γ a2 -∗
    ⌜a1 ≡ a2⌝.
  Proof.
    iIntros "(%γs & Hγ1 & _ & Htwin1) (%_γs & Hγ2 & _ & Htwin2)".
    iDestruct (ghost_var_agree with "Hγ1 Hγ2") as %<-.
    iApply (twins_agree_discrete with "Htwin1 Htwin2").
  Qed.
  Lemma auth_twins_frags_agree_L `{!OfeDiscrete A} `{!LeibnizEquiv A} γ a1 a2 :
    auth_twins_twin1 γ a1 -∗
    auth_twins_twin2 γ a2 -∗
    ⌜a1 = a2⌝.
  Proof.
    iIntros "(%γs & Hγ1 & _ & Htwin1) (%_γs & Hγ2 & _ & Htwin2)".
    iDestruct (ghost_var_agree with "Hγ1 Hγ2") as %<-.
    iApply (twins_agree_L with "Htwin1 Htwin2").
  Qed.

  Lemma auth_twins_update_auth {γ a b1 b2} a' :
    auth_twins_auth γ a -∗
    auth_twins_twin1 γ b1 -∗
    auth_twins_twin2 γ b2 ==∗
      auth_twins_auth γ a' ∗
      auth_twins_twin1 γ a' ∗
      auth_twins_twin2 γ a'.
  Proof.
    assert (1 = 1/3 + (1/3 + 1/3))%Qp as Heq by compute_done.
    iIntros "(%γs & Hγ1 & _) (%_γs & Hγ2 & _ & Htwin1) (%__γs & Hγ3 & _ & Htwin2)".
    iDestruct (ghost_var_agree with "Hγ1 Hγ2") as %<-.
    iDestruct (ghost_var_agree with "Hγ1 Hγ3") as %<-.
    iCombine "Hγ1 Hγ2 Hγ3" as "Hγ". rewrite -Heq.
    iMod (twins_update' (twins_G := auth_twins_G_twins_G) a' with "Htwin1 Htwin2") as "(Htwin1 & Htwin2)".
    iMod (auth_mono_alloc _ a') as "(%γ_mono & Hauth)".
    iDestruct (auth_mono_lb_get with "Hauth") as "#Hlb".
    iMod (ghost_var_update (γ_mono, γs.2) with "Hγ") as "Hγ".
    iEval (rewrite Heq) in "Hγ". iDestruct "Hγ" as "(Hγ1 & (Hγ2 & Hγ3))".
    iSteps.
  Qed.
  Lemma auth_twins_update_twins {γ a1 a2} a :
    Rs a a1 →
    Rs a a2 →
    auth_twins_twin1 γ a1 -∗
    auth_twins_twin2 γ a2 ==∗
      auth_twins_twin1 γ a ∗
      auth_twins_twin2 γ a.
  Proof.
    iIntros "%Ha1 %Ha2 (%γs & Hγ1 & #Hlb1 & Htwin1) (%_γs & Hγ2 & #Hlb2 & Htwin2)".
    iDestruct (ghost_var_agree with "Hγ1 Hγ2") as %<-.
    iMod (twins_update' (twins_G := auth_twins_G_twins_G) a with "Htwin1 Htwin2") as "(Htwin1 & Htwin2)".
    iDestruct (auth_mono_lb_mono with "Hlb1") as "#Hlb1'"; first done.
    iDestruct (auth_mono_lb_mono with "Hlb2") as "#Hlb2'"; first done.
    iSteps.
  Qed.
  Lemma auth_twins_update_twins_L `{!OfeDiscrete A} `{!LeibnizEquiv A} {γ a1 a2} a :
    Rs a a1 →
    auth_twins_twin1 γ a1 -∗
    auth_twins_twin2 γ a2 ==∗
      auth_twins_twin1 γ a ∗
      auth_twins_twin2 γ a.
  Proof.
    iIntros "%Ha (%γs & Hγ1 & #Hlb & Htwin1) (%_γs & Hγ2 & _ & Htwin2)".
    iDestruct (ghost_var_agree with "Hγ1 Hγ2") as %<-.
    iDestruct (twins_agree_L with "Htwin1 Htwin2") as %<-.
    iMod (twins_update' (twins_G := auth_twins_G_twins_G) a with "Htwin1 Htwin2") as "(Htwin1 & Htwin2)".
    iDestruct (auth_mono_lb_mono with "Hlb") as "#Hlb'"; first done.
    iSteps.
  Qed.
End auth_twins_G.

#[global] Opaque auth_twins_auth.
#[global] Opaque auth_twins_twin1.
#[global] Opaque auth_twins_twin2.
