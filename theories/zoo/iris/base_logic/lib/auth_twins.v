From zoo Require Import
  prelude.
From zoo.common Require Import
  countable.
From zoo.iris.base_logic Require Export
  lib.base.
From zoo.iris.base_logic Require Import
  lib.ghost_var
  lib.auth_mono
  lib.twins.
From zoo.iris Require Import
  diaframe.
From zoo Require Import
  options.

Class AuthTwinsG Σ (A : ofe) (R : relation A) := {
  #[local] auth_twins_G_var_G :: GhostVarG Σ (leibnizO gname) ;
  #[local] auth_twins_G_mono_G :: AuthMonoG Σ R ;
  #[local] auth_twins_G_twins_G :: TwinsG Σ A ;
}.

Definition auth_twins_Σ (A : ofe) (R : relation A) := #[
  ghost_var_Σ (leibnizO gname) ;
  auth_mono_Σ R ;
  twins_Σ A
].
#[global] Instance subG_auth_twins_Σ Σ (A : ofe) (R : relation A) :
  subG (auth_twins_Σ A R) Σ →
  AuthTwinsG Σ A R.
Proof.
  solve_inG.
Qed.

Section auth_twins_G.
  Context {A : ofe} (R : relation A).
  Context `{auth_twins_G : !AuthTwinsG Σ A R}.

  Notation Rs := (
    rtc R
  ).

  Implicit Types a b : A.

  Record auth_twins_name := {
    auth_twins_name_var : gname ;
    auth_twins_name_twins : gname ;
  }.
  Implicit Types γ : auth_twins_name.

  #[global] Instance auth_twins_name_eq_dec : EqDecision auth_twins_name :=
    ltac:(solve_decision).
  #[global] Instance auth_twins_name_countable :
    Countable auth_twins_name.
  Proof.
    solve_countable.
  Qed.

  Definition auth_twins_auth γ a : iProp Σ :=
    ∃ η,
    ghost_var γ.(auth_twins_name_var) (DfracOwn (1/3)) η ∗
    auth_mono_auth R η (DfracOwn 1) a.
  #[local] Instance : CustomIpatFormat "auth" :=
    " ( %{{pref}_}η &
        Hvar{} &
        {{pref}_}Hauth
      )
    ".
  Definition auth_twins_twin1 γ a : iProp Σ :=
    ∃ η,
    ghost_var γ.(auth_twins_name_var) (DfracOwn (1/3)) η ∗
    auth_mono_lb R η a ∗
    twins_twin1 γ.(auth_twins_name_twins) (DfracOwn 1) a.
  #[local] Instance : CustomIpatFormat "twin1" :=
    " ( %{{pref}_}η &
        Hvar{} &
        #Hlb{} &
        Htwin1{_{suff}}
      )
    ".
  Definition auth_twins_twin2 γ a : iProp Σ :=
    ∃ η,
    ghost_var γ.(auth_twins_name_var) (DfracOwn (1/3)) η ∗
    auth_mono_lb R η a ∗
    twins_twin2 γ.(auth_twins_name_twins) a.
  #[local] Instance : CustomIpatFormat "twin2" :=
    " ( %{{pref}_}η &
        Hvar{} &
        #Hlb{} &
        Htwin2{_{suff}}
      )
    ".

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
    iMod (auth_mono_alloc _ a) as "(%η & Hauth)".
    iDestruct (auth_mono_lb_get with "Hauth") as "#Hlb".
    iMod (twins_alloc' (twins_G := auth_twins_G_twins_G) a) as "(%γ_twins & Htwin1 & Htwin2)".
    iMod (ghost_var_alloc (ghost_var_G := auth_twins_G_var_G ) η) as "(%γ_var & Hvar)".
    iEval (assert (1 = 1/3 + (1/3 + 1/3))%Qp as -> by compute_done) in "Hvar".
    iDestruct "Hvar" as "(Hvar1 & (Hvar2 & Hvar3))".
    iExists {|
      auth_twins_name_var := γ_var ;
      auth_twins_name_twins := γ_twins ;
    |}.
    iSteps.
  Qed.

  Lemma auth_twins_auth_exclusive `{!AntiSymm (≡) Rs} γ a1 a2 :
    auth_twins_auth γ a1 -∗
    auth_twins_auth γ a2 -∗
    False.
  Proof.
    iIntros "(:auth =1) (:auth =2 pref=)".
    iDestruct (ghost_var_agree_L with "Hvar1 Hvar2") as %<-.
    iApply (auth_mono_auth_exclusive with "Hauth _Hauth").
  Qed.
  Lemma auth_twins_auth_exclusive_L `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ a1 a2 :
    auth_twins_auth γ a1 -∗
    auth_twins_auth γ a2 -∗
    False.
  Proof.
    iIntros "(:auth =1) (:auth =2 pref=)".
    iDestruct (ghost_var_agree_L with "Hvar1 Hvar2") as %<-.
    iApply (auth_mono_auth_exclusive_L with "Hauth _Hauth").
  Qed.

  Lemma auth_twins_twin1_exclusive γ a1 a2 :
    auth_twins_twin1 γ a1 -∗
    auth_twins_twin1 γ a2 -∗
    False.
  Proof.
    iIntros "(:twin1 =1 suff=1) (:twin1 =2 pref= suff=2)".
    iApply (twins_twin1_exclusive with "Htwin1_1 Htwin1_2").
  Qed.

  Lemma auth_twins_twin2_exclusive γ a1 a2 :
    auth_twins_twin2 γ a1 -∗
    auth_twins_twin2 γ a2 -∗
    False.
  Proof.
    iIntros "(:twin2 =1 suff=1) (:twin2 =2 pref= suff=2)".
    iApply (twins_twin2_exclusive with "Htwin2_1 Htwin2_2").
  Qed.

  Lemma auth_twins_valid_1 γ a1 a2 :
    auth_twins_auth γ a1 -∗
    auth_twins_twin1 γ a2 -∗
    ⌜Rs a2 a1⌝.
  Proof.
    iIntros "(:auth =1) (:twin1 =2 pref=)".
    iDestruct (ghost_var_agree_L with "Hvar1 Hvar2") as %<-.
    iApply (auth_mono_lb_valid with "Hauth Hlb2").
  Qed.
  Lemma auth_twins_valid_2 γ a1 a2 :
    auth_twins_auth γ a1 -∗
    auth_twins_twin2 γ a2 -∗
    ⌜Rs a2 a1⌝.
  Proof.
    iIntros "(:auth =1) (:twin2 =2 pref=)".
    iDestruct (ghost_var_agree_L with "Hvar1 Hvar2") as %<-.
    iApply (auth_mono_lb_valid with "Hauth Hlb2").
  Qed.

  Lemma auth_twins_agree γ a1 a2 :
    auth_twins_twin1 γ a1 -∗
    auth_twins_twin2 γ a2 -∗
    a1 ≡ a2.
  Proof.
    iIntros "(:twin1 =1) (:twin2 =2 pref=)".
    iApply (twins_agree with "Htwin1 Htwin2").
  Qed.
  Lemma auth_twins_agree_discrete `{!OfeDiscrete A} γ a1 a2 :
    auth_twins_twin1 γ a1 -∗
    auth_twins_twin2 γ a2 -∗
    ⌜a1 ≡ a2⌝.
  Proof.
    rewrite -!discrete_eq -auth_twins_agree //.
  Qed.
  Lemma auth_twins_agree_L `{!OfeDiscrete A} `{!LeibnizEquiv A}  γ a1 a2 :
    auth_twins_twin1 γ a1 -∗
    auth_twins_twin2 γ a2 -∗
    ⌜a1 = a2⌝.
  Proof.
    rewrite -!leibniz_equiv_iff -auth_twins_agree_discrete //.
  Qed.

  Lemma auth_twins_update_auth {γ a a1 a2} a' :
    auth_twins_auth γ a -∗
    auth_twins_twin1 γ a1 -∗
    auth_twins_twin2 γ a2 ==∗
      auth_twins_auth γ a' ∗
      auth_twins_twin1 γ a' ∗
      auth_twins_twin2 γ a'.
  Proof.
    assert (1 = 1/3 + (1/3 + 1/3))%Qp as Heq by compute_done.
    iIntros "(:auth =1) (:twin1 =2 pref=) (:twin2 =3 pref=_)".
    iDestruct (ghost_var_agree_L with "Hvar1 Hvar2") as %<-.
    iDestruct (ghost_var_agree_L with "Hvar1 Hvar3") as %<-.
    iCombine "Hvar1 Hvar2 Hvar3" as "Hvar". rewrite -Heq.
    iMod (twins_update (twins_G := auth_twins_G_twins_G) a' with "Htwin1 Htwin2") as "(Htwin1 & Htwin2)".
    iMod (auth_mono_alloc _ a') as "(%η' & Hauth')".
    iDestruct (auth_mono_lb_get with "Hauth'") as "#Hlb".
    iMod (ghost_var_update (ghost_var_G := auth_twins_G_var_G ) η' with "Hvar") as "Hvar".
    iEval (rewrite Heq) in "Hvar". iDestruct "Hvar" as "(Hvar1 & (Hvar2 & Hvar3))".
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
    iIntros "%Ha1 %Ha2 (:twin1 =1) (:twin2 =2 pref=)".
    iDestruct (ghost_var_agree_L with "Hvar1 Hvar2") as %<-.
    iMod (twins_update (twins_G := auth_twins_G_twins_G) a with "Htwin1 Htwin2") as "(Htwin1 & Htwin2)".
    iDestruct (auth_mono_lb_mono with "Hlb1") as "#Hlb1'"; first done.
    iSteps.
  Qed.
  Lemma auth_twins_update_twins_L `{!OfeDiscrete A} `{!LeibnizEquiv A} {γ a1 a2} a :
    Rs a a1 →
    auth_twins_twin1 γ a1 -∗
    auth_twins_twin2 γ a2 ==∗
      auth_twins_twin1 γ a ∗
      auth_twins_twin2 γ a.
  Proof.
    iIntros "%Ha Htwin1 Htwin2".
    iDestruct (auth_twins_agree with "Htwin1 Htwin2") as %<-.
    iApply (auth_twins_update_twins with "Htwin1 Htwin2"); done.
  Qed.
End auth_twins_G.

#[global] Opaque auth_twins_auth.
#[global] Opaque auth_twins_twin1.
#[global] Opaque auth_twins_twin2.
