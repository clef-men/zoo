From zoo Require Import
  prelude.
From zoo.iris.base_logic Require Import
  lib.twins.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  option
  glst.
From zoo_saturn Require Export
  base
  mpmc_stack_1__code.
From zoo Require Import
  options.

Implicit Types l : location.
Implicit Types v t : val.
Implicit Types vs : list val.

Class MpmcStack1G Σ `{zoo_G : !ZooG Σ} := {
  #[local] mpmc_stack_1_G_model_G :: TwinsG Σ (leibnizO (list val)) ;
}.

Definition mpmc_stack_1_Σ := #[
  twins_Σ (leibnizO (list val))
].
#[global] Instance subG_mpmc_stack_1_Σ Σ `{zoo_G : !ZooG Σ} :
  subG mpmc_stack_1_Σ Σ →
  MpmcStack1G Σ.
Proof.
  solve_inG.
Qed.

Section zoo_G.
  Context `{mpmc_stack_1_G : MpmcStack1G Σ}.

  #[local] Definition metadata :=
    gname.
  Implicit Types γ : metadata.

  #[local] Definition model₁ γ vs :=
    twins_twin1 γ (DfracOwn 1) vs.
  #[local] Definition model₂ γ vs :=
    twins_twin2 γ vs.

  #[local] Definition inv_inner l γ : iProp Σ :=
    ∃ vs,
    l ↦ᵣ glst_to_val vs ∗
    model₂ γ vs.
  #[local] Instance : CustomIpatFormat "inv_inner" :=
    "(
      %vs{} &
      Hl &
      Hmodel₂
    )".
  Definition mpmc_stack_1_inv t ι : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    inv ι (inv_inner l γ).
  #[local] Instance : CustomIpatFormat "inv" :=
    "(
      %l &
      %γ &
      -> &
      #Hmeta &
      #Hinv
    )".

  Definition mpmc_stack_1_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    model₁ γ vs.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %l{;_} &
      %γ{;_} &
      %Heq{} &
      Hmeta_{} &
      Hmodel₁{_{}}
    )".

  #[global] Instance mpmc_stack_1_model_timeless t vs :
    Timeless (mpmc_stack_1_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpmc_stack_1_inv_persistent t ι :
    Persistent (mpmc_stack_1_inv t ι).
  Proof.
    apply _.
  Qed.

  #[local] Lemma model_alloc :
    ⊢ |==>
      ∃ γ,
      model₁ γ [] ∗
      model₂ γ [].
  Proof.
    apply twins_alloc'.
  Qed.
  #[local] Lemma model₁_exclusive γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₁ γ vs2 -∗
    False.
  Proof.
    apply twins_twin1_exclusive.
  Qed.
  #[local] Lemma model_agree γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₂ γ vs2 -∗
    ⌜vs1 = vs2⌝.
  Proof.
    apply: twins_agree_L.
  Qed.
  #[local] Lemma model_update {γ vs1 vs2} vs :
    model₁ γ vs1 -∗
    model₂ γ vs2 ==∗
      model₁ γ vs ∗
      model₂ γ vs.
  Proof.
    apply twins_update'.
  Qed.

  Lemma mpmc_stack_1_model_exclusive t vs1 vs2 :
    mpmc_stack_1_model t vs1 -∗
    mpmc_stack_1_model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (model₁_exclusive with "Hmodel₁_1 Hmodel₁_2").
  Qed.

  Lemma mpmc_stack_1_create_spec ι :
    {{{
      True
    }}}
      mpmc_stack_1_create ()
    {{{ t,
      RET t;
      mpmc_stack_1_inv t ι ∗
      mpmc_stack_1_model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.
    wp_ref l as "Hmeta" "Hl".

    iMod model_alloc as "(%γ & Hmodel₁ & Hmodel₂)".

    iMod (meta_set with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ". iSplitR "Hmodel₁"; last iSteps.
    iStep 2. iApply inv_alloc. iExists []. iSteps.
  Qed.

  Lemma mpmc_stack_1_push_spec t ι v :
    <<<
      mpmc_stack_1_inv t ι
    | ∀∀ vs,
      mpmc_stack_1_model t vs
    >>>
      mpmc_stack_1_push t v @ ↑ι
    <<<
      mpmc_stack_1_model t (v :: vs)
    | RET ();
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    iLöb as "HLöb".

    wp_rec. wp_pures.

    wp_bind (!_)%E.
    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    iSplitR "HΦ"; first iSteps.
    iModIntro.

    wp_pures.

    wp_bind (CAS _ _ _).
    iInv "Hinv" as "(:inv_inner =')".
    wp_cas as _ | ->%(inj _); first iSteps.
    iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
    iMod (model_update (v :: vs) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
    iSplitR "HΦ". { iExists (v :: vs). iSteps. }
    iSteps.
  Qed.

  Lemma mpmc_stack_1_pop_spec t ι :
    <<<
      mpmc_stack_1_inv t ι
    | ∀∀ vs,
      mpmc_stack_1_model t vs
    >>>
      mpmc_stack_1_pop t @ ↑ι
    <<<
      mpmc_stack_1_model t (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    iLöb as "HLöb".

    wp_rec. wp_pures.

    wp_bind (!_)%E.
    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    destruct vs as [| v vs].

    - iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
      iSplitR "HΦ". { iExists []. iSteps. }
      iSteps.

    - iSplitR "HΦ". { iExists (v :: vs). iSteps. }
      iModIntro.

      wp_pures.

      wp_bind (CAS _ _ _).
      iInv "Hinv" as "(:inv_inner =')".
      wp_cas as _ | Hcas; first iSteps.
      destruct vs'; first done. apply (inj glst_to_val _ (_ :: _)) in Hcas as [= -> ->].
      iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod (model_update vs with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
      iSplitR "HΦ"; first iSteps.
      iSteps.
  Qed.

  Lemma mpmc_stack_1_snapshot_spec t ι :
    <<<
      mpmc_stack_1_inv t ι
    | ∀∀ vs,
      mpmc_stack_1_model t vs
    >>>
      mpmc_stack_1_snapshot t @ ↑ι
    <<<
      mpmc_stack_1_model t vs
    | RET glst_to_val vs;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec.

    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
    iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
    iSteps.
  Qed.
End zoo_G.

From zoo_saturn Require
  mpmc_stack_1__opaque.

#[global] Opaque mpmc_stack_1_inv.
#[global] Opaque mpmc_stack_1_model.
