From iris.base_logic Require Import
  lib.fancy_updates.

From zoo Require Import
  prelude.
From zoo.iris.base_logic Require Import
  lib.auth_dgset
  lib.saved_pred.
From zoo.iris.base_logic Require Export
  lib.base.
From zoo.iris Require Import
  diaframe.
From zoo Require Import
  options.

Class SubpredsG Σ A := {
  #[local] subpreds_G_auth_dgset_G :: AuthDgsetG Σ gname ;
  #[local] subpreds_G_saved_pred_G :: SavedPredG Σ A ;
}.

Definition subpreds_Σ A := #[
  auth_dgset_Σ gname ;
  saved_pred_Σ A
].
#[global] Instance subG_subpreds_Σ Σ A :
  subG (subpreds_Σ A) Σ →
  SubpredsG Σ A.
Proof.
  solve_inG.
Qed.

Section subpreds_G.
  Context `{subpreds_G : !SubpredsG Σ A}.

  Implicit Types state : option A.
  Implicit Types η : gname.
  Implicit Types Ψ Χ : A → iProp Σ.

  Definition subpreds_auth γ Ψ state : iProp Σ :=
    ∃ ηs,
    auth_dgset_auth γ (DfracOwn 1) ηs ∗
      ∀ x,
      (if state is Some y then ⌜x = y⌝ else Ψ x) -∗
      [∗ set] η ∈ ηs,
        ∃ Χ,
        saved_pred η Χ ∗
        ▷ Χ x.
  #[local] Instance : CustomIpatFormat "auth" :=
    "(
      %ηs &
      {>=}Hauth &
      Hηs
    )".

  Definition subpreds_frag γ Χ : iProp Σ :=
    ∃ η,
    auth_dgset_frag γ {[η]} ∗
    saved_pred η Χ.
  #[local] Instance : CustomIpatFormat "frag" :=
    "(
      %η &
      Hfrag &
      #Hη
    )".

  #[global] Instance subpreds_auth_ne γ n :
    Proper (
      (pointwise_relation _ (≡{n}≡)) ==>
      (=) ==>
      (≡{n}≡)
    ) (subpreds_auth γ).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance subpreds_auth_proper γ :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (=) ==>
      (≡)
    ) (subpreds_auth γ).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance subpreds_frag_contractive γ n :
    Proper (
      (pointwise_relation _ (dist_later n)) ==>
      (≡{n}≡)
    ) (subpreds_frag γ).
  Proof.
    solve_contractive.
  Qed.
  #[global] Instance subpreds_frag_proper γ :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (subpreds_frag γ).
  Proof.
    solve_proper.
  Qed.

  Lemma subpreds_alloc Ψ :
    ⊢ |==>
      ∃ γ,
      subpreds_auth γ Ψ None ∗
      subpreds_frag γ Ψ.
  Proof.
    iMod (saved_pred_alloc Ψ) as "(%η & #Hη)".
    iMod (auth_dgset_alloc {[η]}) as "(%γ & Hauth & Hfrag)".
    iFrame "#∗".
    setoid_rewrite big_sepS_singleton. iSteps.
  Qed.

  Lemma subpreds_split `{inv_G : !invGS Σ} {γ Ψ state Χ} Χ1 Χ2 E :
    ▷ subpreds_auth γ Ψ state -∗
    subpreds_frag γ Χ -∗
    (∀ x, Χ x -∗ Χ1 x ∗ Χ2 x) ={E}=∗
      ▷ subpreds_auth γ Ψ state ∗
      subpreds_frag γ Χ1 ∗
      subpreds_frag γ Χ2.
  Proof.
    iIntros "(:auth >) (:frag) H".
    iDestruct (auth_dgset_elem_of with "Hauth Hfrag") as %Hη.
    iMod (auth_dgset_update_dealloc {[η]} with "Hauth Hfrag") as "Hauth".
    iMod (saved_pred_alloc_cofinite (ηs ∖ {[η]}) Χ1) as "(%η1 & %Hη1 & #Hη1)".
    iMod (auth_dgset_update_alloc_singleton η1 with "Hauth") as "(Hauth & Hfrag1)"; first done.
    iMod (saved_pred_alloc_cofinite ({[η1]} ∪ ηs ∖ {[η]}) Χ2) as "(%η2 & %Hη2 & #Hη2)".
    iMod (auth_dgset_update_alloc_singleton η2 with "Hauth") as "(Hauth & Hfrag2)"; first done.
    iFrame "#∗". iIntros "!> !> %x Hstate".
    iDestruct ("Hηs" with "Hstate") as "Hηs".
    iDestruct (big_sepS_delete with "Hηs") as "((%Χ_ & Hη_ & HΧ) & Hηs)"; first done.
    iDestruct (saved_pred_agree x with "Hη Hη_") as "Heq".
    iAssert (▷ (Χ1 x ∗ Χ2 x))%I with "[H HΧ Heq]" as "(HΧ1 & HΧ2)".
    { iModIntro.
      iApply "H".
      iRewrite "Heq" => //.
    }
    do 2 (rewrite big_sepS_union; first set_solver).
    rewrite !big_sepS_singleton. iFrame "#∗".
  Qed.
  Lemma subpreds_divide `{inv_G : !invGS Σ} {γ Ψ state Χ} Χs E :
    ▷ subpreds_auth γ Ψ state -∗
    subpreds_frag γ Χ -∗
    (∀ x, Χ x -∗ [∗ list] Χ ∈ Χs, Χ x) ={E}=∗
      ▷ subpreds_auth γ Ψ state ∗
      [∗ list] Χ ∈ Χs, subpreds_frag γ Χ.
  Proof.
    iInduction Χs as [| Χ0 Χs] "IH" forall (Χ); first auto.
    iIntros "Hauth Hfrag H".
    iMod (subpreds_split Χ0 (λ x, [∗ list] Χ ∈ Χs, Χ x)%I with "Hauth Hfrag [H]") as "(Hauth & $ & Hfrag)"; first iSteps.
    iApply ("IH" with "Hauth Hfrag").
    iSteps.
  Qed.

  Lemma subpreds_produce {γ Ψ} x :
    subpreds_auth γ Ψ None -∗
    Ψ x -∗
    subpreds_auth γ Ψ (Some x).
  Proof.
    iSteps.
  Qed.

  Lemma subpreds_consume `{inv_G : !invGS Σ} γ Ψ x Χ E :
    ▷ subpreds_auth γ Ψ (Some x) -∗
    subpreds_frag γ Χ ={E}=∗
      ▷ subpreds_auth γ Ψ (Some x) ∗
      ▷^2 Χ x.
  Proof.
    iIntros "(:auth >) (:frag)".
    iDestruct ("Hηs" with "[//]") as "Hηs".
    iDestruct (auth_dgset_elem_of with "Hauth Hfrag") as %Hη.
    iMod (auth_dgset_update_dealloc {[η]} with "Hauth Hfrag") as "Hauth".
    iDestruct (big_sepS_delete with "Hηs") as "((%Χ_ & Hη_ & HΧ) & Hηs)"; first done.
    iDestruct (saved_pred_agree x with "Hη Hη_") as "Heq".
    iFrame "#∗". iSplitL "Hηs"; first iSteps.
    do 3 iModIntro.
    iRewrite "Heq" => //.
  Qed.
End subpreds_G.

#[global] Opaque subpreds_auth.
#[global] Opaque subpreds_frag.
