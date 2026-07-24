Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.base_logic.lib.ghost_var.
Require Import zoo.iris.base_logic.lib.auth_mono.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Class AuthTwinsG Σ (A : ofe) (R : relation A) :=
  { #[local] auth_twins۰G۰var۰G :: GhostVarG Σ (leibnizO gname)
  ; #[local] auth_twins۰G۰mono۰G :: AuthMonoG Σ R
  ; #[local] auth_twins۰G۰twins۰G :: TwinsG Σ A
  }.

Definition auth_twins۰Σ (A : ofe) (R : relation A) :=
  #[ghost_var۰Σ (leibnizO gname)
  ; auth_mono۰Σ R
  ; twins۰Σ A
  ].
#[global] Instance subG𑁒auth_twins۰Σ Σ (A : ofe) (R : relation A) :
  subG (auth_twins۰Σ A R) Σ →
  AuthTwinsG Σ A R.
Proof.
  solve_inG.
Qed.

Section auth_twins۰G.
  Context {A : ofe} (R : relation A).
  Context `{auth_twins۰G : !AuthTwinsG Σ A R}.

  Notation Rs := (
    rtc R
  ).

  Implicit Type a b : A.

  Record auth_twins۰name :=
    { auth_twins۰name۰var : gname
    ; auth_twins۰name۰twins : gname
    }.
  Implicit Type γ : auth_twins۰name.

  #[global] Instance auth_twins۰name𑁒eq_dec : EqDecision auth_twins۰name :=
    ltac:(solve_decision).
  #[global] Instance auth_twins۰name𑁒countable :
    Countable auth_twins۰name.
  Proof.
    solve_countable.
  Qed.

  Definition auth_twins۰auth γ a : iProp Σ :=
    ∃ η,
    ghost_var γ.(auth_twins۰name۰var) (DfracOwn (1/3)) η ∗
    auth_mono۰auth R η (DfracOwn 1) a.
  #[local] Instance : CustomIpat "auth" :=
    " ( %{{pref}_}η
      & Hvar{}
      & {{pref}_}Hauth
      )
    ".
  Definition auth_twins۰twin₁ γ a : iProp Σ :=
    ∃ η,
    ghost_var γ.(auth_twins۰name۰var) (DfracOwn (1/3)) η ∗
    auth_mono۰lb R η a ∗
    twins۰twin₁ γ.(auth_twins۰name۰twins) (DfracOwn 1) a.
  #[local] Instance : CustomIpat "twin₁" :=
    " ( %{{pref}_}η
      & Hvar{}
      & #Hlb{}
      & Htwin₁{_{suff}}
      )
    ".
  Definition auth_twins۰twin₂ γ a : iProp Σ :=
    ∃ η,
    ghost_var γ.(auth_twins۰name۰var) (DfracOwn (1/3)) η ∗
    auth_mono۰lb R η a ∗
    twins۰twin₂ γ.(auth_twins۰name۰twins) a.
  #[local] Instance : CustomIpat "twin₂" :=
    " ( %{{pref}_}η
      & Hvar{}
      & #Hlb{}
      & Htwin₂{_{suff}}
      )
    ".

  #[global] Instance auth_twins۰auth𑁒timeless γ a :
    Timeless (auth_twins۰auth γ a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_twins۰twin₁𑁒timeless γ a :
    Discrete a →
    Timeless (auth_twins۰twin₁ γ a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_twins۰twin₂𑁒timeless γ a :
    Discrete a →
    Timeless (auth_twins۰twin₂ γ a).
  Proof.
    apply _.
  Qed.

  Lemma auth_twins𑁒alloc a :
    ⊢ |==>
      ∃ γ,
      auth_twins۰auth γ a ∗
      auth_twins۰twin₁ γ a ∗
      auth_twins۰twin₂ γ a.
  Proof.
    iMod (auth_mono𑁒alloc _ a) as "(%η & Hauth)".
    iDestruct (auth_mono۰lb𑁒get with "Hauth") as "#Hlb".
    iMod (twins𑁒alloc' (twins۰G := auth_twins۰G۰twins۰G) a) as "(%γ_twins & Htwin₁ & Htwin₂)".
    iMod (ghost_var𑁒alloc (ghost_var۰G := auth_twins۰G۰var۰G ) η) as "(%γ_var & Hvar)".
    iEval (assert (1 = 1/3 + (1/3 + 1/3))%Qp as -> by compute_done) in "Hvar".
    iDestruct "Hvar" as "(Hvar1 & (Hvar2 & Hvar3))".
    iExists
      {|auth_twins۰name۰var := γ_var
      ; auth_twins۰name۰twins := γ_twins
      |}.
    iSteps.
  Qed.

  Lemma auth_twins۰auth𑁒exclusive `{!AntiSymm (≡) Rs} γ a1 a2 :
    auth_twins۰auth γ a1 -∗
    auth_twins۰auth γ a2 -∗
    False.
  Proof.
    iIntros "(:auth =1) (:auth =2 pref=)".
    iDestruct (ghost_var𑁒agree𑁒L with "Hvar1 Hvar2") as %<-.
    iApply (auth_mono۰auth𑁒exclusive with "Hauth _Hauth").
  Qed.
  Lemma auth_twins۰auth𑁒exclusive𑁒L `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ a1 a2 :
    auth_twins۰auth γ a1 -∗
    auth_twins۰auth γ a2 -∗
    False.
  Proof.
    iIntros "(:auth =1) (:auth =2 pref=)".
    iDestruct (ghost_var𑁒agree𑁒L with "Hvar1 Hvar2") as %<-.
    iApply (auth_mono۰auth𑁒exclusive𑁒L with "Hauth _Hauth").
  Qed.

  Lemma auth_twins۰twin₁𑁒exclusive γ a1 a2 :
    auth_twins۰twin₁ γ a1 -∗
    auth_twins۰twin₁ γ a2 -∗
    False.
  Proof.
    iIntros "(:twin₁ =1 suff=1) (:twin₁ =2 pref= suff=2)".
    iApply (twins۰twin₁𑁒exclusive with "Htwin₁_1 Htwin₁_2").
  Qed.

  Lemma auth_twins۰twin₂𑁒exclusive γ a1 a2 :
    auth_twins۰twin₂ γ a1 -∗
    auth_twins۰twin₂ γ a2 -∗
    False.
  Proof.
    iIntros "(:twin₂ =1 suff=1) (:twin₂ =2 pref= suff=2)".
    iApply (twins۰twin₂𑁒exclusive with "Htwin₂_1 Htwin₂_2").
  Qed.

  Lemma auth_twins𑁒valid₁ γ a1 a2 :
    auth_twins۰auth γ a1 -∗
    auth_twins۰twin₁ γ a2 -∗
    ⌜Rs a2 a1⌝.
  Proof.
    iIntros "(:auth =1) (:twin₁ =2 pref=)".
    iDestruct (ghost_var𑁒agree𑁒L with "Hvar1 Hvar2") as %<-.
    iApply (auth_mono۰lb𑁒valid with "Hauth Hlb2").
  Qed.
  Lemma auth_twins𑁒valid₂ γ a1 a2 :
    auth_twins۰auth γ a1 -∗
    auth_twins۰twin₂ γ a2 -∗
    ⌜Rs a2 a1⌝.
  Proof.
    iIntros "(:auth =1) (:twin₂ =2 pref=)".
    iDestruct (ghost_var𑁒agree𑁒L with "Hvar1 Hvar2") as %<-.
    iApply (auth_mono۰lb𑁒valid with "Hauth Hlb2").
  Qed.

  Lemma auth_twins𑁒agree γ a1 a2 :
    auth_twins۰twin₁ γ a1 -∗
    auth_twins۰twin₂ γ a2 -∗
    a1 ≡ a2.
  Proof.
    iIntros "(:twin₁ =1) (:twin₂ =2 pref=)".
    iApply (twins𑁒agree with "Htwin₁ Htwin₂").
  Qed.
  Lemma auth_twins𑁒agree𑁒discrete `{!OfeDiscrete A} γ a1 a2 :
    auth_twins۰twin₁ γ a1 -∗
    auth_twins۰twin₂ γ a2 -∗
    ⌜a1 ≡ a2⌝.
  Proof.
    rewrite -!discrete_eq -auth_twins𑁒agree //.
  Qed.
  Lemma auth_twins𑁒agree𑁒L `{!OfeDiscrete A} `{!LeibnizEquiv A}  γ a1 a2 :
    auth_twins۰twin₁ γ a1 -∗
    auth_twins۰twin₂ γ a2 -∗
    ⌜a1 = a2⌝.
  Proof.
    rewrite -!leibniz_equiv_iff -auth_twins𑁒agree𑁒discrete //.
  Qed.

  Lemma auth_twins𑁒update𑁒auth {γ a a1 a2} a' :
    auth_twins۰auth γ a -∗
    auth_twins۰twin₁ γ a1 -∗
    auth_twins۰twin₂ γ a2 ==∗
      auth_twins۰auth γ a' ∗
      auth_twins۰twin₁ γ a' ∗
      auth_twins۰twin₂ γ a'.
  Proof.
    assert (1 = 1/3 + (1/3 + 1/3))%Qp as Heq by compute_done.
    iIntros "(:auth =1) (:twin₁ =2 pref=) (:twin₂ =3 pref=_)".
    iDestruct (ghost_var𑁒agree𑁒L with "Hvar1 Hvar2") as %<-.
    iDestruct (ghost_var𑁒agree𑁒L with "Hvar1 Hvar3") as %<-.
    iCombine "Hvar1 Hvar2 Hvar3" as "Hvar". rewrite -Heq.
    iMod (twins𑁒update (twins۰G := auth_twins۰G۰twins۰G) a' with "Htwin₁ Htwin₂") as "(Htwin₁ & Htwin₂)".
    iMod (auth_mono𑁒alloc _ a') as "(%η' & Hauth')".
    iDestruct (auth_mono۰lb𑁒get with "Hauth'") as "#Hlb".
    iMod (ghost_var𑁒update (ghost_var۰G := auth_twins۰G۰var۰G ) η' with "Hvar") as "Hvar".
    iEval (rewrite Heq) in "Hvar". iDestruct "Hvar" as "(Hvar1 & (Hvar2 & Hvar3))".
    iSteps.
  Qed.
  Lemma auth_twins𑁒update𑁒twins {γ a1 a2} a :
    Rs a a1 →
    Rs a a2 →
    auth_twins۰twin₁ γ a1 -∗
    auth_twins۰twin₂ γ a2 ==∗
      auth_twins۰twin₁ γ a ∗
      auth_twins۰twin₂ γ a.
  Proof.
    iIntros "%Ha1 %Ha2 (:twin₁ =1) (:twin₂ =2 pref=)".
    iDestruct (ghost_var𑁒agree𑁒L with "Hvar1 Hvar2") as %<-.
    iMod (twins𑁒update (twins۰G := auth_twins۰G۰twins۰G) a with "Htwin₁ Htwin₂") as "(Htwin₁ & Htwin₂)".
    iDestruct (auth_mono۰lb𑁒mono with "Hlb1") as "#Hlb1'"; first done.
    iSteps.
  Qed.
  Lemma auth_twins𑁒update𑁒twins𑁒L `{!OfeDiscrete A} `{!LeibnizEquiv A} {γ a1 a2} a :
    Rs a a1 →
    auth_twins۰twin₁ γ a1 -∗
    auth_twins۰twin₂ γ a2 ==∗
      auth_twins۰twin₁ γ a ∗
      auth_twins۰twin₂ γ a.
  Proof.
    iIntros "%Ha Htwin₁ Htwin₂".
    iDestruct (auth_twins𑁒agree with "Htwin₁ Htwin₂") as %<-.
    iApply (auth_twins𑁒update𑁒twins with "Htwin₁ Htwin₂"); done.
  Qed.
End auth_twins۰G.

#[global] Opaque auth_twins۰auth.
#[global] Opaque auth_twins۰twin₁.
#[global] Opaque auth_twins۰twin₂.
