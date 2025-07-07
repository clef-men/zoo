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
  optional
  clst.
From zoo_saturn Require Export
  base
  mpmc_stack_2__code.
From zoo Require Import
  options.

Implicit Types l : location.
Implicit Types v t : val.
Implicit Types ws : list val.

Class MpmcStack2G Σ `{zoo_G : !ZooG Σ} := {
  #[local] mpmc_stack_2_G_model_G :: TwinsG Σ (leibnizO (option $ list val)) ;
}.

Definition mpmc_stack_2_Σ := #[
  twins_Σ (leibnizO (option $ list val))
].
#[global] Instance subG_mpmc_stack_2_Σ Σ `{zoo_G : !ZooG Σ} :
  subG mpmc_stack_2_Σ Σ →
  MpmcStack2G Σ.
Proof.
  solve_inG.
Qed.

Section zoo_G.
  Context `{mpmc_stack_2_G : MpmcStack2G Σ}.

  #[local] Definition metadata :=
    gname.
  Implicit Types γ : metadata.

  #[local] Definition model₁ γ vs :=
    twins_twin1 γ (if vs is None then DfracDiscarded else DfracOwn 1) vs.
  #[local] Definition model₂ γ vs :=
    twins_twin2 γ vs.

  #[local] Definition inv_inner l γ : iProp Σ :=
    ∃ vs,
    l ↦ᵣ from_option (clist_to_val ∘ list_to_clist_open) §ClstClosed vs ∗
    model₂ γ vs.
  #[local] Instance : CustomIpatFormat "inv_inner" :=
    "(
      %vs &
      Hl &
      Hmodel₂
    )".
  Definition mpmc_stack_2_inv t ι : iProp Σ :=
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

  Definition mpmc_stack_2_model t vs : iProp Σ :=
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

  Definition mpmc_stack_2_closed t :=
    mpmc_stack_2_model t None.

  #[global] Instance mpmc_stack_2_model_timeless t vs :
    Timeless (mpmc_stack_2_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpmc_stack_2_inv_persistent t ι :
    Persistent (mpmc_stack_2_inv t ι).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpmc_stack_2_model_persistent t :
    Persistent (mpmc_stack_2_model t None).
  Proof.
    apply _.
  Qed.

  #[local] Lemma model_alloc :
    ⊢ |==>
      ∃ γ,
      model₁ γ (Some []) ∗
      model₂ γ (Some []).
  Proof.
    apply twins_alloc'.
  Qed.
  #[local] Lemma model₁_exclusive γ vs1 vs2 :
    model₁ γ (Some vs1) -∗
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
  #[local] Lemma model_update {γ ws1 ws2} ws :
    model₁ γ (Some ws1) -∗
    model₂ γ (Some ws2) ==∗
      model₁ γ (Some ws) ∗
      model₂ γ (Some ws).
  Proof.
    apply twins_update.
  Qed.
  #[local] Lemma model_close γ ws1 ws2 :
    model₁ γ (Some ws1) -∗
    model₂ γ (Some ws2) ==∗
      model₁ γ None ∗
      model₂ γ None.
  Proof.
    iIntros "Hmodel₁ Hmodel₂".
    iMod (twins_update with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod (twins_twin1_persist with "Hmodel₁") as "Hmodel₁".
    iSteps.
  Qed.

  Lemma mpmc_stack_2_model_exclusive t vs1 vs2 :
    mpmc_stack_2_model t (Some vs1) -∗
    mpmc_stack_2_model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (model₁_exclusive with "Hmodel₁_1 Hmodel₁_2").
  Qed.

  Lemma mpmc_stack_2_create_spec ι :
    {{{
      True
    }}}
      mpmc_stack_2_create ()
    {{{ t,
      RET t;
      mpmc_stack_2_inv t ι ∗
      mpmc_stack_2_model t (Some [])
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.
    wp_ref l as "Hmeta" "Hl".

    iMod model_alloc as "(%γ & Hmodel₁ & Hmodel₂)".

    iMod (meta_set with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁"; last iSteps.
    iStep 2. iApply inv_alloc. iExists (Some []). iSteps.
  Qed.

  Lemma mpmc_stack_2_push_spec t ι v :
    <<<
      mpmc_stack_2_inv t ι
    | ∀∀ vs,
      mpmc_stack_2_model t vs
    >>>
      mpmc_stack_2_push t v @ ↑ι
    <<<
      mpmc_stack_2_model t (cons v <$> vs)
    | RET #(bool_decide (vs = None));
      £ 1
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    iLöb as "HLöb".

    wp_rec credit:"H£". wp_pures.

    wp_bind (!_)%E.
    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    destruct vs as [ws |].

    - iSplitR "H£ HΦ". { iFrameSteps. }
      iIntros "!> {%}".

      wp_smart_apply wp_match_clist_open.
      wp_pures.

      wp_bind (CAS _ _ _).
      iInv "Hinv" as "(:inv_inner)".
      destruct vs as [vs |].

      + simpl.
        wp_cas as _ | ->%(inj _)%(inj _).

        * iSplitR "HΦ". { iFrameSteps. }
          iSteps.

        * iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
          iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
          iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
          pose ws' := v :: ws.
          iMod (model_update ws' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iMod ("HΦ" with "[$Hmodel₁] H£") as "HΦ"; first iSteps.
          iSplitR "HΦ". { iFrameSteps. }
          iSteps.

      + wp_cas as _ | []%(inj clist_to_val ClstClosed)%list_to_clist_open_not_closed'.
        iSplitR "HΦ". { iFrameSteps. }
        iSteps.

    - iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[$Hmodel₁] H£") as "HΦ"; first iSteps.
      iSplitR "HΦ". { iFrameSteps. }
      iSteps.
  Qed.
  Lemma mpmc_stack_2_push_spec_closed t ι v :
    {{{
      mpmc_stack_2_inv t ι ∗
      mpmc_stack_2_closed t
    }}}
      mpmc_stack_2_push t v
    {{{
      RET #true;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosed) HΦ".

    iApply wp_fupd.
    awp_apply (mpmc_stack_2_push_spec with "Hinv").
    iAaccIntro with "Hclosed"; first iSteps. iIntros "_ !> H£".
    iDestruct (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iSteps.
  Qed.

  Lemma mpmc_stack_2_pop_spec t ι :
    <<<
      mpmc_stack_2_inv t ι
    | ∀∀ vs,
      mpmc_stack_2_model t vs
    >>>
      mpmc_stack_2_pop t @ ↑ι
    <<<
      mpmc_stack_2_model t (tail <$> vs)
    | RET default Anything (option_to_optional ∘ head <$> vs);
      £ 1
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    iLöb as "HLöb".

    wp_rec credit:"H£".

    wp_bind (!_)%E.
    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    destruct vs as [[| v ws] |].

    - iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
      iSplitR "H£ HΦ". { iFrameSteps. }
      iSteps.

    - iSplitR "H£ HΦ". { iFrameSteps. }
      iIntros "!> {%}".

      wp_pures.

      wp_bind (CAS _ _ _).
      iInv "Hinv" as "(:inv_inner)".
      destruct vs as [vs |].

      + wp_cas as _ | ->%(inj clist_to_val _ (ClstCons _ _))%(inj list_to_clist_open _ (_ :: _)).

        * iSplitR "HΦ". { iFrameSteps. }
          iSteps.

        * iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
          iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
          iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
          iMod (model_update ws with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
          iSplitR "H£ HΦ". { iFrameSteps. }
          iSteps.

      + wp_cas as _ | [=].
        iSplitR "HΦ". { iFrameSteps. }
        iSteps.

    - iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
      iSplitR "H£ HΦ". { iFrameSteps. }
      iSteps.
  Qed.
  Lemma mpmc_stack_2_pop_spec_closed t ι v :
    {{{
      mpmc_stack_2_inv t ι ∗
      mpmc_stack_2_closed t
    }}}
      mpmc_stack_2_pop t
    {{{
      RET §Anything;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosed) HΦ".

    iApply wp_fupd.
    awp_apply (mpmc_stack_2_pop_spec with "Hinv").
    iAaccIntro with "Hclosed"; first iSteps. iIntros "_ !> H£".
    iDestruct (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iSteps.
  Qed.

  Lemma mpmc_stack_2_is_closed_spec t ι :
    <<<
      mpmc_stack_2_inv t ι
    | ∀∀ vs,
      mpmc_stack_2_model t vs
    >>>
      mpmc_stack_2_is_closed t @ ↑ι
    <<<
      mpmc_stack_2_model t vs
    | RET #(bool_decide (vs = None));
      £ 1
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec credit:"H£".

    wp_bind (!_)%E.
    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
    destruct vs as [vs |].

    - iMod ("HΦ" with "[$Hmodel₁] H£") as "HΦ"; first iSteps.
      iSplitR "HΦ". { iFrameSteps. }
      iIntros "!> {%}".

      wp_equal as _ | []%(inj clist_to_val _ ClstClosed)%list_to_clist_open_not_closed.
      iSteps.

    - iMod ("HΦ" with "[$Hmodel₁] H£") as "HΦ"; first iSteps.
      iSplitR "HΦ". { iFrameSteps. }
      iSteps.
  Qed.
  Lemma mpmc_stack_2_is_closed_spec_closed t ι :
    {{{
      mpmc_stack_2_inv t ι ∗
      mpmc_stack_2_closed t
    }}}
      mpmc_stack_2_is_closed t
    {{{
      RET #true;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosed) HΦ".

    iApply wp_fupd.
    awp_apply (mpmc_stack_2_is_closed_spec with "Hinv").
    iAaccIntro with "Hclosed"; first iSteps. iIntros "_ !> H£".
    iDestruct (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iSteps.
  Qed.

  Lemma mpmc_stack_2_close_spec t ι :
    <<<
      mpmc_stack_2_inv t ι
    | ∀∀ vs,
      mpmc_stack_2_model t vs
    >>>
      mpmc_stack_2_close t @ ↑ι
    <<<
      mpmc_stack_2_model t None
    | RET from_option list_to_clist_open ClstClosed vs;
      £ 1
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec credit:"H£". wp_pures.

    iInv "Hinv" as "(:inv_inner)".
    wp_xchg.
    iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
    destruct vs as [vs |].

    - iMod (model_close with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[$Hmodel₁] H£") as "HΦ"; first iSteps.
      iSplitR "HΦ". { iFrameSteps. }
      iSteps.

    - iMod ("HΦ" with "[$Hmodel₁] H£") as "HΦ"; first iSteps.
      iSplitR "HΦ". { iFrameSteps. }
      iSteps.
  Qed.
  Lemma mpmc_stack_2_closed_spec_closed t ι v :
    {{{
      mpmc_stack_2_inv t ι ∗
      mpmc_stack_2_closed t
    }}}
      mpmc_stack_2_close t
    {{{
      RET §ClstClosed;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosed) HΦ".

    iApply wp_fupd.
    awp_apply (mpmc_stack_2_close_spec with "Hinv").
    iAaccIntro with "Hclosed"; first iSteps. iIntros "_ !> H£".
    iDestruct (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iSteps.
  Qed.
End zoo_G.

From zoo_saturn Require
  mpmc_stack_2__opaque.

#[global] Opaque mpmc_stack_2_inv.
#[global] Opaque mpmc_stack_2_model.
