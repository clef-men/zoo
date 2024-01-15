From zebra Require Import
  prelude.
From zebra.iris.base_logic Require Export
  lib.base.
From zebra.iris.base_logic Require Import
  lib.ghost_var
  lib.auth_mono.
From zebra.iris Require Import
  diaframe.
From zebra Require Import
  options.

Class AuthMonoAnnotatedG Σ `(R : relation A) B := {
  #[local] auth_mono_annotated_G_auth_mono_G :: AuthMonoG Σ R ;
  #[local] auth_mono_annotated_G_ghost_var_G :: GhostVarG Σ B ;
}.

Definition auth_mono_annotated_Σ `(R : relation A) B := #[
  auth_mono_Σ R ;
  ghost_var_Σ B
].
#[global] Instance subG_auth_mono_annotated_Σ Σ `(R : relation A) B :
  subG (auth_mono_annotated_Σ R B) Σ →
  AuthMonoAnnotatedG Σ R B.
Proof.
  solve_inG.
Qed.

Section auth_mono_annotated_G.
  Context `(R : relation A) `{auth_mono_annotated_G : !AuthMonoAnnotatedG Σ R B}.

  Implicit Types a : A.
  Implicit Types b : B.

  Definition auth_mono_annotated_name : Type :=
    gname * gname.
  Implicit Types γ : auth_mono_annotated_name.

  #[global] Instance auth_mono_annotated_name_eq_dec : EqDecision auth_mono_annotated_name :=
    ltac:(apply _).
  #[global] Instance auth_mono_annotated_name_countable :
    Countable auth_mono_annotated_name.
  Proof.
    apply _.
  Qed.

  Definition auth_mono_annotated_auth γ dq a b : iProp Σ :=
    auth_mono_auth R γ.1 dq a ∗
    ghost_var γ.2 dq b.
  Definition auth_mono_annotated_lb γ a :=
    auth_mono_lb R γ.1 a.

  #[global] Instance auth_mono_annotated_auth_timeless γ dq a b :
    Timeless (auth_mono_annotated_auth γ dq a b).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_mono_annotated_auth_persistent γ a b :
    Persistent (auth_mono_annotated_auth γ DfracDiscarded a b).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_mono_annotated_lb_timeless γ a :
    Timeless (auth_mono_annotated_lb γ a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_mono_annotated_lb_persistent γ a :
    Persistent (auth_mono_annotated_lb γ a).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_mono_annotated_auth_fractional γ a b :
    Fractional (λ q, auth_mono_annotated_auth γ (DfracOwn q) a b).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_mono_annotated_auth_as_fractional γ q a b :
    AsFractional (auth_mono_annotated_auth γ (DfracOwn q) a b) (λ q, auth_mono_annotated_auth γ (DfracOwn q) a b) q.
  Proof.
    split; [done | apply _].
  Qed.

  Lemma auth_mono_annotated_alloc a b :
    ⊢ |==>
      ∃ γ,
      auth_mono_annotated_auth γ (DfracOwn 1) a b.
  Proof.
    iMod auth_mono_alloc as "(%γ_auth_mono & Hauth_mono)".
    iMod ghost_var_alloc as "(%γ_ghost_var & Hghost_var)".
    iExists (_, _). iSteps.
  Qed.

  Lemma auth_mono_annotated_auth_valid γ dq a b :
    auth_mono_annotated_auth γ dq a b ⊢
    ⌜✓ dq⌝.
  Proof.
    iIntros "(Hauth_mono & _)".
    iApply (auth_mono_auth_valid with "Hauth_mono").
  Qed.
  Lemma auth_mono_annotated_auth_combine `{!AntiSymm (=) (rtc R)} γ dq1 a1 b1 dq2 a2 b2 :
    auth_mono_annotated_auth γ dq1 a1 b1 -∗
    auth_mono_annotated_auth γ dq2 a2 b2 -∗
      auth_mono_annotated_auth γ (dq1 ⋅ dq2) a1 b1 ∗
      ⌜a1 = a2 ∧ b1 = b2⌝.
  Proof.
    iIntros "(Hauth_mono_1 & Hghost_var_1) (Hauth_mono_2 & Hghost_var_2)".
    iDestruct (auth_mono_auth_combine with "Hauth_mono_1 Hauth_mono_2") as "($ & ->)".
    iDestruct (ghost_var_combine with "Hghost_var_1 Hghost_var_2") as "($ & ->)".
    iSteps.
  Qed.
  Lemma auth_mono_annotated_auth_valid_2 `{!AntiSymm (=) (rtc R)} γ dq1 a1 b1 dq2 a2 b2 :
    auth_mono_annotated_auth γ dq1 a1 b1 -∗
    auth_mono_annotated_auth γ dq2 a2 b2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ a1 = a2 ∧ b1 = b2⌝.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_mono_annotated_auth_combine with "Hauth1 Hauth2") as "(Hauth & (-> & ->))".
    iDestruct (auth_mono_annotated_auth_valid with "Hauth") as %?.
    iSteps.
  Qed.
  Lemma auth_mono_annotated_auth_agree `{!AntiSymm (=) (rtc R)} γ dq1 a1 b1 dq2 a2 b2 :
    auth_mono_annotated_auth γ dq1 a1 b1 -∗
    auth_mono_annotated_auth γ dq2 a2 b2 -∗
    ⌜a1 = a2 ∧ b1 = b2⌝.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_mono_annotated_auth_valid_2 with "Hauth1 Hauth2") as "(_ & $)".
  Qed.
  Lemma auth_mono_annotated_auth_dfrac_ne `{!AntiSymm (=) (rtc R)} γ1 dq1 a1 b1 γ2 dq2 a2 b2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    auth_mono_annotated_auth γ1 dq1 a1 b1 -∗
    auth_mono_annotated_auth γ2 dq2 a2 b2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iIntros "% Hauth1 Hauth2" (->).
    iDestruct (auth_mono_annotated_auth_valid_2 with "Hauth1 Hauth2") as %?.
    naive_solver.
  Qed.
  Lemma auth_mono_annotated_auth_ne `{!AntiSymm (=) (rtc R)} γ1 a1 b1 γ2 dq2 a2 b2 :
    auth_mono_annotated_auth γ1 (DfracOwn 1) a1 b1 -∗
    auth_mono_annotated_auth γ2 dq2 a2 b2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    intros.
    iApply auth_mono_annotated_auth_dfrac_ne; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma auth_mono_annotated_ghost_varusive `{!AntiSymm (=) (rtc R)} γ a1 b1 a2 b2 :
    auth_mono_annotated_auth γ (DfracOwn 1) a1 b1 -∗
    auth_mono_annotated_auth γ (DfracOwn 1) a2 b2 -∗
    False.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_mono_annotated_auth_valid_2 with "Hauth1 Hauth2") as "(% & _)".
    iSmash.
  Qed.
  Lemma auth_mono_annotated_auth_persist γ dq a b :
    auth_mono_annotated_auth γ dq a b ⊢ |==>
    auth_mono_annotated_auth γ DfracDiscarded a b.
  Proof.
    iIntros "(Hauth_mono & Hghost_var)".
    iMod (auth_mono_auth_persist with "Hauth_mono") as "$".
    iMod (ghost_var_persist with "Hghost_var") as "$".
    iSteps.
  Qed.

  Lemma auth_mono_annotated_lb_get `{!Reflexive R} γ q a b :
    auth_mono_annotated_auth γ q a b ⊢
    auth_mono_annotated_lb γ a.
  Proof.
    iIntros "(Hauth_mono & _)".
    iApply (auth_mono_lb_get with "Hauth_mono").
  Qed.
  Lemma auth_mono_annotated_lb_mono {γ a} a' :
    rtc R a' a →
    auth_mono_annotated_lb γ a ⊢
    auth_mono_annotated_lb γ a'.
  Proof.
    apply auth_mono_lb_mono.
  Qed.
  Lemma auth_mono_annotated_lb_mono' {γ a} a' :
    R a' a →
    auth_mono_annotated_lb γ a ⊢
    auth_mono_annotated_lb γ a'.
  Proof.
    apply auth_mono_lb_mono'.
  Qed.

  Lemma auth_mono_annotated_valid γ dq a b a' :
    auth_mono_annotated_auth γ dq a b -∗
    auth_mono_annotated_lb γ a' -∗
    ⌜rtc R a' a⌝.
  Proof.
    iIntros "(Hauth_mono & _) Hlb".
    iApply (auth_mono_valid with "Hauth_mono Hlb").
  Qed.

  Lemma auth_mono_annotated_update {γ a b} a' b' :
    rtc R a a' →
    auth_mono_annotated_auth γ (DfracOwn 1) a b ⊢ |==>
    auth_mono_annotated_auth γ (DfracOwn 1) a' b'.
  Proof.
    iIntros "%Hrtc (Hauth_mono & Hghost_var)".
    iMod (auth_mono_update with "Hauth_mono") as "$"; first done.
    iMod (ghost_var_update with "Hghost_var") as "$".
    iSteps.
  Qed.
  Lemma auth_mono_annotated_update' {γ a b} a' b' :
    R a a' →
    auth_mono_annotated_auth γ (DfracOwn 1) a b ⊢ |==>
    auth_mono_annotated_auth γ (DfracOwn 1) a' b'.
  Proof.
    intros. apply auth_mono_annotated_update, rtc_once. done.
  Qed.
End auth_mono_annotated_G.

#[global] Opaque auth_mono_annotated_name.
#[global] Opaque auth_mono_annotated_auth.
#[global] Opaque auth_mono_annotated_lb.
