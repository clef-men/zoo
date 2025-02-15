From zoo Require Import
  prelude.
From zoo.common Require Import
  countable
  list.
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
  mpsc_queue_2__code.
From zoo_saturn Require Import
  mpsc_queue_2__types.
From zoo Require Import
  options.

Implicit Types l : location.
Implicit Types v t : val.
Implicit Types vs front back : list val.
Implicit Types o : option val.

Class MpscQueue2G Σ `{zoo_G : !ZooG Σ} := {
  #[local] mpsc_queue_2_G_twins_G :: TwinsG Σ (leibnizO (list val)) ;
}.

Definition mpsc_queue_2_Σ := #[
  twins_Σ (leibnizO (list val))
].
#[global] Instance subG_mpsc_queue_2_Σ Σ `{zoo_G : !ZooG Σ} :
  subG mpsc_queue_2_Σ Σ →
  MpscQueue2G Σ.
Proof.
  solve_inG.
Qed.

Section mpsc_queue_2_G.
  Context `{mpsc_queue_2_G : MpscQueue2G Σ}.

  Record metadata := {
    metadata_model : gname ;
    metadata_front : gname ;
  }.
  Implicit Types γ : metadata.

  #[local] Instance metadata_eq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[local] Instance metadata_countable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition model₁' γ_model vs :=
    twins_twin1 γ_model (DfracOwn 1) vs.
  #[local] Definition model₁ γ vs :=
    model₁' γ.(metadata_model) vs.
  #[local] Definition model₂' γ_model vs :=
    twins_twin2 γ_model vs.
  #[local] Definition model₂ γ vs :=
    model₂' γ.(metadata_model) vs.

  #[local] Definition front₁' γ_front front :=
    twins_twin1 γ_front (DfracOwn 1) front.
  #[local] Definition front₁ γ front :=
    front₁' γ.(metadata_front) front.
  #[local] Definition front₂' γ_model front :=
    twins_twin2 γ_model front.
  #[local] Definition front₂ γ front :=
    front₂' γ.(metadata_front) front.

  #[local] Definition inv_inner l γ : iProp Σ :=
    ∃ front back,
    front₂ γ front ∗
    l.[back] ↦ glst_to_val back ∗
    model₂ γ (front ++ reverse back).
  #[local] Instance : CustomIpatFormat "inv_inner" :=
    "(
      %front{} &
      %back{} &
      >Hfront₂ &
      >Hl_back &
      >Hmodel₂
    )".
  Definition mpsc_queue_2_inv t ι : iProp Σ :=
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

  Definition mpsc_queue_2_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    model₁ γ vs.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %l_ &
      %γ_ &
      %Heq &
      Hmeta_ &
      Hmodel₁
    )".

  Definition mpsc_queue_2_consumer t : iProp Σ :=
    ∃ l γ front,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[front] ↦ glst_to_val front ∗
    front₁ γ front.
  #[local] Instance : CustomIpatFormat "consumer" :=
    "(
      %l_ &
      %γ_ &
      %front &
      %Heq &
      Hmeta_ &
      Hl_front &
      Hfront₁
    )".

  #[global] Instance mpsc_queue_2_model_timeless t vs :
    Timeless (mpsc_queue_2_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpsc_queue_2_consumer_timeless t :
    Timeless (mpsc_queue_2_consumer t ).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpsc_queue_2_inv_persistent t ι :
    Persistent (mpsc_queue_2_inv t ι).
  Proof.
    apply _.
  Qed.

  #[local] Lemma model_alloc :
    ⊢ |==>
      ∃ γ_model,
      model₁' γ_model [] ∗
      model₂' γ_model [].
  Proof.
    apply twins_alloc'.
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

  #[local] Lemma front_alloc :
    ⊢ |==>
      ∃ γ_front,
      front₁' γ_front [] ∗
      front₂' γ_front [].
  Proof.
    apply twins_alloc'.
  Qed.
  #[local] Lemma front_agree γ front1 front2 :
    front₁ γ front1 -∗
    front₂ γ front2 -∗
    ⌜front1 = front2⌝.
  Proof.
    apply: twins_agree_L.
  Qed.
  #[local] Lemma front_update {γ front1 front2} front :
    front₁ γ front1 -∗
    front₂ γ front2 ==∗
      front₁ γ front ∗
      front₂ γ front.
  Proof.
    apply twins_update'.
  Qed.

  Lemma mpsc_queue_2_consumer_exclusive t :
    mpsc_queue_2_consumer t -∗
    mpsc_queue_2_consumer t -∗
    False.
  Proof.
    iSteps.
  Qed.

  Lemma mpsc_queue_2_create_spec ι :
    {{{
      True
    }}}
      mpsc_queue_2_create ()
    {{{ t,
      RET t;
      mpsc_queue_2_inv t ι ∗
      mpsc_queue_2_model t [] ∗
      mpsc_queue_2_consumer t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.

    wp_block l as "Hmeta" "(Hfront & Hback & _)".

    iMod model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod front_alloc as "(%γ_front & Hfront₁ & Hfront₂)".

    pose γ := {|
      metadata_model := γ_model ;
      metadata_front := γ_front ;
    |}.
    iMod (meta_set _ _ γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁ Hfront Hfront₁".
    - iExists l, γ. iStep 2. iApply inv_alloc. iExists [], []. iSteps.
    - iSplitL "Hmodel₁"; first iSteps. iExists l, γ, []. iSteps.
  Qed.

  Lemma mpsc_queue_2_is_empty_spec t ι :
    <<<
      mpsc_queue_2_inv t ι ∗
      mpsc_queue_2_consumer t
    | ∀∀ vs,
      mpsc_queue_2_model t vs
    >>>
      mpsc_queue_2_is_empty t @ ↑ι
    <<<
      mpsc_queue_2_model t vs
    | RET #(bool_decide (vs = []%list));
      mpsc_queue_2_consumer t
    >>>.
  Proof.
    iIntros "!> %Φ ((:inv) & (:consumer)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec. wp_load.

    destruct front as [| v front]; wp_pures.

    - wp_bind (_.{back})%E.
      iInv "Hinv" as "(:inv_inner)".
      wp_load.
      iDestruct (front_agree with "Hfront₁ Hfront₂") as %<-.
      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      destruct back as [| v back].

      + iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
        iSplitR "Hl_front Hfront₁ HΦ". { iFrameSteps. }
        iSteps. iExists []. iSteps.

      + iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
        iSplitR "Hl_front Hfront₁ HΦ". { iFrameSteps. }
        rewrite reverse_cons bool_decide_eq_false_2 /=; first intros (_ & [=])%app_nil.
        iSteps. iExists []. iSteps.

    - iInv "Hinv" as "(:inv_inner =1)".
      iDestruct (front_agree with "Hfront₁ Hfront₂") as %<-.
      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
      iSteps. iExists (v :: front). iSteps.
  Qed.

  Lemma mpsc_queue_2_push_front_spec t ι v :
    <<<
      mpsc_queue_2_inv t ι ∗
      mpsc_queue_2_consumer t
    | ∀∀ vs,
      mpsc_queue_2_model t vs
    >>>
      mpsc_queue_2_push_front t v @ ↑ι
    <<<
      mpsc_queue_2_model t (v :: vs)
    | RET ();
      mpsc_queue_2_consumer t
    >>>.
  Proof.
    iIntros "!> %Φ ((:inv) & (:consumer)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec. wp_load. wp_store.

    iInv "Hinv" as "(:inv_inner =1)".
    iDestruct (front_agree with "Hfront₁ Hfront₂") as %<-.
    set front' := v :: front.
    iMod (front_update front' with "Hfront₁ Hfront₂") as "(Hfront₁ & Hfront₂)".
    iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
    set vs' := front' ++ reverse back1.
    iMod (model_update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
    iSteps. iExists (v :: front). iSteps.
  Qed.

  Lemma mpsc_queue_2_push_back_spec t ι v :
    <<<
      mpsc_queue_2_inv t ι
    | ∀∀ vs,
      mpsc_queue_2_model t vs
    >>>
      mpsc_queue_2_push_back t v @ ↑ι
    <<<
      mpsc_queue_2_model t (vs ++ [v])
    | RET ();
      True
    >>>.
  Proof.
    iIntros "!> %Φ (:inv) HΦ".

    iLöb as "HLöb".

    wp_rec. wp_pures.

    wp_bind (_.{back})%E.
    iInv "Hinv" as "(:inv_inner =1)".
    wp_load.
    iSplitR "HΦ". { iFrameSteps. }
    iModIntro. clear.

    wp_pures.

    wp_bind (CAS _ _ _).
    iInv "Hinv" as "(:inv_inner =2)".
    wp_cas as _ | ->%(inj _); first iSteps.
    iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %Hvs.
    iMod (model_update (vs ++ [v]) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
    iSplitR "HΦ".
    { iExists _, (v :: back1). iSteps.
      rewrite Hvs reverse_cons assoc //.
    }
    iSteps.
  Qed.

  Lemma mpsc_queue_2_pop_spec t ι :
    <<<
      mpsc_queue_2_inv t ι ∗
      mpsc_queue_2_consumer t
    | ∀∀ vs,
      mpsc_queue_2_model t vs
    >>>
      mpsc_queue_2_pop t @ ↑ι
    <<<
      mpsc_queue_2_model t (tail vs)
    | RET head vs;
      mpsc_queue_2_consumer t
    >>>.
  Proof.
    iIntros "!> %Φ ((:inv) & (:consumer)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec. wp_load.
    destruct front as [| v front]; wp_pures.

    - wp_bind (Xchg _ _).
      iInv "Hinv" as "(:inv_inner)".
      wp_xchg.
      iDestruct (front_agree with "Hfront₁ Hfront₂") as %<-.
      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      destruct (rev_elim back) as [-> | (back' & v & ->)].

      + iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
        iSplitR "Hl_front Hfront₁ HΦ". { iFrameSteps. }
        iModIntro. clear.

        wp_apply (glst_rev_spec with "[//]") as "_"; first done.
        wp_pures.

        iApply "HΦ".
        iExists l, γ, []. iSteps.

      + set front := reverse back'.
        iMod (front_update front with "Hfront₁ Hfront₂") as "(Hfront₁ & Hfront₂)".
        iMod (model_update front with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" with "[Hmodel₁]") as "HΦ".
        { rewrite reverse_snoc. iSteps. }
        iSplitR "Hl_front Hfront₁ HΦ".
        { iExists front, []. iSteps. rewrite right_id //. }
        iModIntro. clear.

        wp_apply (glst_rev_spec with "[//]") as "_"; first done.
        rewrite reverse_snoc. iSteps.

    - wp_store.

      iApply fupd_wp.
      iInv "Hinv" as "(:inv_inner =1)".
      iDestruct (front_agree with "Hfront₁ Hfront₂") as %<-.
      iMod (front_update with "Hfront₁ Hfront₂") as "(Hfront₁ & Hfront₂)".
      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %Hvs.
      set vs' := front ++ reverse back1.
      iMod (model_update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      rewrite Hvs.
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
      iSteps.
  Qed.
End mpsc_queue_2_G.

#[global] Opaque mpsc_queue_2_create.
#[global] Opaque mpsc_queue_2_is_empty.
#[global] Opaque mpsc_queue_2_push_front.
#[global] Opaque mpsc_queue_2_push_back.
#[global] Opaque mpsc_queue_2_pop.

#[global] Opaque mpsc_queue_2_inv.
#[global] Opaque mpsc_queue_2_model.
#[global] Opaque mpsc_queue_2_consumer.
