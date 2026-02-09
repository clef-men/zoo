From zoo Require Import
  prelude.
From zoo.common Require Export
  relations.
From zoo.iris.algebra Require Import
  lib.auth_monoi.
From zoo.iris.base_logic Require Export
  lib.base.
From zoo.iris Require Import
  diaframe.
From zoo Require Import
  options.

Class AuthMonoiG Σ {A : ofe} (R : relation A) `{!Initial R} := {
  #[local] auth_monoi_G_inG :: inG Σ (auth_monoi_UR R) ;
}.

Definition auth_monoi_Σ {A : ofe} (R : relation A) `{!Initial R} := #[
  GFunctor (auth_monoi_UR R)
].
#[global] Instance subG_auth_monoi_Σ Σ {A : ofe} (R : relation A) `{!Initial R} :
  subG (auth_monoi_Σ R) Σ →
  AuthMonoiG Σ R.
Proof.
  solve_inG.
Qed.

Section auth_monoi_G.
  Context {A : ofe} (R : relation A) `{!Initial R}.
  Context `{auth_monoi_G : !AuthMonoiG Σ R}.

  Implicit Types a : A.

  Notation Rs := (
    rtc R
  ).

  Definition auth_monoi_auth γ dq a :=
    own γ (auth_monoi_auth R dq a).
  Definition auth_monoi_lb γ a :=
    own γ (auth_monoi_lb R a).

  #[global] Instance auth_monoi_auth_timeless γ dq a :
    Timeless (auth_monoi_auth γ dq a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_monoi_lb_timeless γ a :
    Timeless (auth_monoi_lb γ a).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_monoi_auth_persistent γ a :
    Persistent (auth_monoi_auth γ DfracDiscarded a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_monoi_lb_persistent γ a :
    Persistent (auth_monoi_lb γ a).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_monoi_auth_fractional γ a :
    Fractional (λ q, auth_monoi_auth γ (DfracOwn q) a).
  Proof.
    intros ?*. rewrite -own_op -auth_monoi_auth_dfrac_op //.
  Qed.
  #[global] Instance auth_monoi_auth_as_fractional γ q a :
    AsFractional (auth_monoi_auth γ (DfracOwn q) a) (λ q, auth_monoi_auth γ (DfracOwn q) a) q.
  Proof.
    split; [done | apply _].
  Qed.

  Lemma auth_monoi_alloc a :
    ⊢ |==>
      ∃ γ,
      auth_monoi_auth γ (DfracOwn 1) a.
  Proof.
    apply own_alloc, auth_monoi_auth_valid.
  Qed.

  Lemma auth_monoi_auth_valid γ dq a :
    auth_monoi_auth γ dq a ⊢
    ⌜✓ dq⌝.
  Proof.
    iIntros "Hauth".
    iDestruct (own_valid with "Hauth") as %?%auth_monoi_auth_dfrac_valid.
    iSteps.
  Qed.
  Lemma auth_monoi_auth_combine `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ dq1 a1 dq2 a2 :
    auth_monoi_auth γ dq1 a1 -∗
    auth_monoi_auth γ dq2 a2 -∗
      ⌜a1 = a2⌝ ∗
      auth_monoi_auth γ (dq1 ⋅ dq2) a1.
  Proof.
    iIntros "Hauth1 Hauth2".
    iCombine "Hauth1 Hauth2" as "Hauth".
    iDestruct (own_valid with "Hauth") as %(_ & <-)%auth_monoi_auth_dfrac_op_valid_L.
    rewrite -auth_monoi_auth_dfrac_op. iSteps.
  Qed.
  Lemma auth_monoi_auth_valid_2 `{!AntiSymm (≡) Rs} γ dq1 a1 dq2 a2 :
    auth_monoi_auth γ dq1 a1 -∗
    auth_monoi_auth γ dq2 a2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜a1 ≡ a2⌝.
  Proof.
    iIntros "Hauth1 Hauth2".
    iCombine "Hauth1 Hauth2" as "Hauth".
    iDestruct (own_valid with "Hauth") as %(? & ?)%auth_monoi_auth_dfrac_op_valid.
    iSteps.
  Qed.
  Lemma auth_monoi_auth_valid_2_L `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ dq1 a1 dq2 a2 :
    auth_monoi_auth γ dq1 a1 -∗
    auth_monoi_auth γ dq2 a2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜a1 = a2⌝.
  Proof.
    iIntros "Hauth1 Hauth2".
    iCombine "Hauth1 Hauth2" as "Hauth".
    iDestruct (own_valid with "Hauth") as %(? & <-)%auth_monoi_auth_dfrac_op_valid_L.
    iSteps.
  Qed.
  Lemma auth_monoi_auth_agree `{!AntiSymm (≡) Rs} γ dq1 a1 dq2 a2 :
    auth_monoi_auth γ dq1 a1 -∗
    auth_monoi_auth γ dq2 a2 -∗
    ⌜a1 ≡ a2⌝.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_monoi_auth_valid_2 with "Hauth1 Hauth2") as "(_ & $)".
  Qed.
  Lemma auth_monoi_auth_agree_L `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ dq1 a1 dq2 a2 :
    auth_monoi_auth γ dq1 a1 -∗
    auth_monoi_auth γ dq2 a2 -∗
    ⌜a1 = a2⌝.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_monoi_auth_valid_2_L with "Hauth1 Hauth2") as "(_ & $)".
  Qed.
  Lemma auth_monoi_auth_dfrac_ne `{!AntiSymm (≡) Rs} γ1 dq1 a1 γ2 dq2 a2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    auth_monoi_auth γ1 dq1 a1 -∗
    auth_monoi_auth γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iIntros "% Hauth1 Hauth2" (->).
    iDestruct (auth_monoi_auth_valid_2 with "Hauth1 Hauth2") as %(? & _). done.
  Qed.
  Lemma auth_monoi_auth_dfrac_ne_L `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ1 dq1 a1 γ2 dq2 a2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    auth_monoi_auth γ1 dq1 a1 -∗
    auth_monoi_auth γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iIntros "% Hauth1 Hauth2" (->).
    iDestruct (auth_monoi_auth_valid_2_L with "Hauth1 Hauth2") as %(? & _). done.
  Qed.
  Lemma auth_monoi_auth_ne `{!AntiSymm (≡) Rs} γ1 a1 γ2 dq2 a2 :
    auth_monoi_auth γ1 (DfracOwn 1) a1 -∗
    auth_monoi_auth γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iApply auth_monoi_auth_dfrac_ne; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma auth_monoi_auth_ne_L `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ1 a1 γ2 dq2 a2 :
    auth_monoi_auth γ1 (DfracOwn 1) a1 -∗
    auth_monoi_auth γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iApply auth_monoi_auth_dfrac_ne_L; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma auth_monoi_auth_exclusive `{!AntiSymm (≡) Rs} γ a1 dq2 a2 :
    auth_monoi_auth γ (DfracOwn 1) a1 -∗
    auth_monoi_auth γ dq2 a2 -∗
    False.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_monoi_auth_ne with "Hauth1 Hauth2") as %?. done.
  Qed.
  Lemma auth_monoi_auth_exclusive_L `{!LeibnizEquiv A} `{!AntiSymm (=) Rs} γ a1 dq2 a2 :
    auth_monoi_auth γ (DfracOwn 1) a1 -∗
    auth_monoi_auth γ dq2 a2 -∗
    False.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_monoi_auth_ne_L with "Hauth1 Hauth2") as %?. done.
  Qed.
  Lemma auth_monoi_auth_persist γ dq a :
    auth_monoi_auth γ dq a ⊢ |==>
    auth_monoi_auth γ DfracDiscarded a.
  Proof.
    apply own_update, auth_monoi_auth_persist.
  Qed.

  Lemma auth_monoi_lb_initial γ :
    ⊢ |==>
      auth_monoi_lb γ initial.
  Proof.
    apply own_unit.
  Qed.
  Lemma auth_monoi_lb_mono {γ a} a' :
    Rs a' a →
    auth_monoi_lb γ a ⊢
    auth_monoi_lb γ a'.
  Proof.
    intros. apply own_mono, auth_monoi_lb_mono. done.
  Qed.
  Lemma auth_monoi_lb_mono' {γ a} a' :
    R a' a →
    auth_monoi_lb γ a ⊢
    auth_monoi_lb γ a'.
  Proof.
    intros. apply auth_monoi_lb_mono, rtc_once. done.
  Qed.

  Lemma auth_monoi_lb_get γ q a :
    auth_monoi_auth γ q a ⊢
    auth_monoi_lb γ a.
  Proof.
    apply own_mono, auth_monoi_lb_included'.
  Qed.
  Lemma auth_monoi_lb_get_mono' γ q a a' :
    R a' a →
    auth_monoi_auth γ q a ⊢
    auth_monoi_lb γ a'.
  Proof.
    intros Ha'.
    rewrite -auth_monoi_lb_mono' // auth_monoi_lb_get //.
  Qed.
  Lemma auth_monoi_lb_get_mono γ q a a' :
    Rs a' a →
    auth_monoi_auth γ q a ⊢
    auth_monoi_lb γ a'.
  Proof.
    intros Ha'.
    rewrite -auth_monoi_lb_mono // auth_monoi_lb_get //.
  Qed.

  Lemma auth_monoi_lb_valid γ dq a a' :
    auth_monoi_auth γ dq a -∗
    auth_monoi_lb γ a' -∗
    ⌜Rs a' a⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (own_valid_2 with "Hauth Hlb") as %?%auth_monoi_both_dfrac_valid.
    naive_solver.
  Qed.
  Lemma auth_monoi_lb_agree γ a1 a2 :
    auth_monoi_lb γ a1 -∗
    auth_monoi_lb γ a2 -∗
      ∃ a,
      ⌜Rs a1 a⌝ ∧
      ⌜Rs a2 a⌝.
  Proof.
    iIntros "Hlb1 Hlb2".
    iDestruct (own_valid_2 with "Hlb1 Hlb2") as %?%auth_monoi_lb_op_valid. done.
  Qed.

  Lemma auth_monoi_update {γ a} a' :
    Rs a a' →
    auth_monoi_auth γ (DfracOwn 1) a ⊢ |==>
    auth_monoi_auth γ (DfracOwn 1) a'.
  Proof.
    iIntros "% Hauth".
    iMod (own_update with "Hauth"); first by apply auth_monoi_auth_update.
    iSteps.
  Qed.
  Lemma auth_monoi_update' {γ a} a' :
    R a a' →
    auth_monoi_auth γ (DfracOwn 1) a ⊢ |==>
    auth_monoi_auth γ (DfracOwn 1) a'.
  Proof.
    intros. apply auth_monoi_update, rtc_once. done.
  Qed.
End auth_monoi_G.

#[global] Opaque auth_monoi_auth.
#[global] Opaque auth_monoi_lb.
