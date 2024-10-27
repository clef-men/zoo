From iris.algebra Require Import
  list.

From zoo Require Import
  prelude.
From zoo.common Require Import
  list.
From zoo.iris.base_logic Require Import
  lib.twins.
From zoo.language Require Import
  notations
  diaframe.
From zoo_std Require Import
  option
  lst.
From saturn Require Export
  base
  mpsc_queue_2__code.
From saturn Require Import
  mpsc_queue_2__types.
From zoo Require Import
  options.

Implicit Types l : location.
Implicit Types v t : val.
Implicit Types vs front back : list val.
Implicit Types o : option val.

Class MpscQueue2G Σ `{zoo_G : !ZooG Σ} := {
  #[local] mpsc_queue_2_G_twins_G :: TwinsG Σ (listO val) ;
}.

Definition mpsc_queue_2_Σ := #[
  twins_Σ (listO val)
].
#[global] Instance subG_mpsc_queue_2_Σ Σ `{zoo_G : !ZooG Σ} :
  subG mpsc_queue_2_Σ Σ →
  MpscQueue2G Σ.
Proof.
  solve_inG.
Qed.

Section mpsc_queue_2_G.
  Context `{mpsc_queue_2_G : MpscQueue2G Σ}.

  Record mpsc_queue_2_meta := {
    mpsc_queue_2_meta_model : gname ;
    mpsc_queue_2_meta_front : gname ;
  }.
  Implicit Types γ : mpsc_queue_2_meta.

  #[local] Instance mpsc_queue_2_meta_eq_dec : EqDecision mpsc_queue_2_meta :=
    ltac:(solve_decision).
  #[local] Instance mpsc_queue_2_meta_countable :
    Countable mpsc_queue_2_meta.
  Proof.
    pose encode γ := (
      γ.(mpsc_queue_2_meta_model),
      γ.(mpsc_queue_2_meta_front)
    ).
    pose decode := λ '(γ_model, γ_front), {|
      mpsc_queue_2_meta_model := γ_model ;
      mpsc_queue_2_meta_front := γ_front ;
    |}.
    refine (inj_countable' encode decode _). intros []. done.
  Qed.

  #[local] Definition mpsc_queue_2_model₁' γ_model vs :=
    twins_twin1 γ_model (DfracOwn 1) vs.
  #[local] Definition mpsc_queue_2_model₁ γ vs :=
    mpsc_queue_2_model₁' γ.(mpsc_queue_2_meta_model) vs.
  #[local] Definition mpsc_queue_2_model₂' γ_model vs :=
    twins_twin2 γ_model vs.
  #[local] Definition mpsc_queue_2_model₂ γ vs :=
    mpsc_queue_2_model₂' γ.(mpsc_queue_2_meta_model) vs.

  #[local] Definition mpsc_queue_2_front₁' γ_front front :=
    twins_twin1 γ_front (DfracOwn 1) front.
  #[local] Definition mpsc_queue_2_front₁ γ front :=
    mpsc_queue_2_front₁' γ.(mpsc_queue_2_meta_front) front.
  #[local] Definition mpsc_queue_2_front₂' γ_model front :=
    twins_twin2 γ_model front.
  #[local] Definition mpsc_queue_2_front₂ γ front :=
    mpsc_queue_2_front₂' γ.(mpsc_queue_2_meta_front) front.

  #[local] Definition mpsc_queue_2_inv_inner l γ : iProp Σ :=
    ∃ front back,
    mpsc_queue_2_front₂ γ front ∗
    l.[back] ↦ lst_to_val back ∗
    mpsc_queue_2_model₂ γ (front ++ reverse back).
  Definition mpsc_queue_2_inv t ι : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    inv ι (mpsc_queue_2_inv_inner l γ).

  Definition mpsc_queue_2_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    mpsc_queue_2_model₁ γ vs.

  Definition mpsc_queue_2_consumer t : iProp Σ :=
    ∃ l γ front,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[front] ↦ lst_to_val front ∗
    mpsc_queue_2_front₁ γ front.

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

  #[local] Lemma mpsc_queue_2_model_alloc :
    ⊢ |==>
      ∃ γ_model,
      mpsc_queue_2_model₁' γ_model [] ∗
      mpsc_queue_2_model₂' γ_model [].
  Proof.
    apply twins_alloc'.
  Qed.
  #[local] Lemma mpsc_queue_2_model_agree γ vs1 vs2 :
    mpsc_queue_2_model₁ γ vs1 -∗
    mpsc_queue_2_model₂ γ vs2 -∗
    ⌜vs1 = vs2⌝.
  Proof.
    apply: twins_agree_L.
  Qed.
  #[local] Lemma mpsc_queue_2_model_update {γ vs1 vs2} vs :
    mpsc_queue_2_model₁ γ vs1 -∗
    mpsc_queue_2_model₂ γ vs2 ==∗
      mpsc_queue_2_model₁ γ vs ∗
      mpsc_queue_2_model₂ γ vs.
  Proof.
    apply twins_update'.
  Qed.

  #[local] Lemma mpsc_queue_2_front_alloc :
    ⊢ |==>
      ∃ γ_front,
      mpsc_queue_2_front₁' γ_front [] ∗
      mpsc_queue_2_front₂' γ_front [].
  Proof.
    apply twins_alloc'.
  Qed.
  #[local] Lemma mpsc_queue_2_front_agree γ front1 front2 :
    mpsc_queue_2_front₁ γ front1 -∗
    mpsc_queue_2_front₂ γ front2 -∗
    ⌜front1 = front2⌝.
  Proof.
    apply: twins_agree_L.
  Qed.
  #[local] Lemma mpsc_queue_2_front_update {γ front1 front2} front :
    mpsc_queue_2_front₁ γ front1 -∗
    mpsc_queue_2_front₂ γ front2 ==∗
      mpsc_queue_2_front₁ γ front ∗
      mpsc_queue_2_front₂ γ front.
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

    iMod mpsc_queue_2_model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod mpsc_queue_2_front_alloc as "(%γ_front & Hfront₁ & Hfront₂)".

    pose γ := {|
      mpsc_queue_2_meta_model := γ_model ;
      mpsc_queue_2_meta_front := γ_front ;
    |}.
    iMod (meta_set _ _ γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁ Hfront Hfront₁".
    - iExists l, γ. iStep 2. iApply inv_alloc. iExists [], []. iSteps.
    - iSplitL "Hmodel₁"; first iSteps. iExists l, γ, []. iSteps.
  Qed.

  Lemma mpsc_queue_2_push_spec t ι v :
    <<<
      mpsc_queue_2_inv t ι
    | ∀∀ vs,
      mpsc_queue_2_model t vs
    >>>
      mpsc_queue_2_push t v @ ↑ι
    <<<
      mpsc_queue_2_model t (vs ++ [v])
    | RET ();
      True
    >>>.
  Proof.
    iIntros "!> %Φ (%l & %γ & -> & #Hmeta & #Hinv) HΦ".

    iLöb as "HLöb".

    wp_rec. wp_pures.

    wp_bind (Load _ _).
    iInv "Hinv" as "(%front & %back & Hfront₂ & Hback & Hmodel₂)".
    wp_load.
    iSplitR "HΦ"; first iSteps.
    iModIntro. clear.

    wp_pures.

    wp_bind (CAS _ _ _).
    iInv "Hinv" as "(%front & %back' & Hfront₂ & Hback & Hmodel₂)".
    wp_cas as _ | ->%(inj _); first iSteps.
    iMod "HΦ" as "(%vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (mpsc_queue_2_model_agree with "Hmodel₁ Hmodel₂") as %Hvs.
    iMod (mpsc_queue_2_model_update (vs ++ [v]) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
    iSplitR "HΦ".
    { iSteps. iExists (v :: back). iSteps. rewrite Hvs reverse_cons assoc //. }
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
    iIntros "!> %Φ ((%l & %γ & -> & #Hmeta & #Hinv) & (%_l & %_γ & %front & %Heq & _Hmeta & Hfront & Hfront₁)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

    wp_rec. wp_load.
    destruct front as [| v front]; wp_pures.

    - wp_bind (Xchg _ _).
      iInv "Hinv" as "(%_front & %back & Hfront₂ & Hback & Hmodel₂)".
      wp_xchg.
      iDestruct (mpsc_queue_2_front_agree with "Hfront₁ Hfront₂") as %<-.
      iMod "HΦ" as "(%vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (mpsc_queue_2_model_agree with "Hmodel₁ Hmodel₂") as %->.
      destruct (rev_elim back) as [-> | (back' & v & ->)].

      + iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
        iSplitR "Hfront Hfront₁ HΦ". { iExists [], []. iSteps. }
        iModIntro. clear.

        wp_apply (lst_rev_spec _ [] with "[//]") as "%back ->".
        wp_pures.

        iApply "HΦ".
        iExists l, γ, []. iSteps.

      + set front := reverse back'.
        iMod (mpsc_queue_2_front_update front with "Hfront₁ Hfront₂") as "(Hfront₁ & Hfront₂)".
        iMod (mpsc_queue_2_model_update front with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" with "[Hmodel₁]") as "HΦ".
        { rewrite reverse_snoc. iSteps. }
        iSplitR "Hfront Hfront₁ HΦ".
        { iExists front, []. iSteps. rewrite right_id //. }
        iModIntro. clear.

        wp_apply (lst_rev_spec with "[//]") as "%back ->". rewrite reverse_snoc.
        iSteps.

    - wp_store.
      iApply fupd_wp. iInv "Hinv" as "(%_front & %back & >Hfront₂ & Hback & >Hmodel₂)".
      iDestruct (mpsc_queue_2_front_agree with "Hfront₁ Hfront₂") as %<-.
      iMod (mpsc_queue_2_front_update with "Hfront₁ Hfront₂") as "(Hfront₁ & Hfront₂)".
      iMod "HΦ" as "(%vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (mpsc_queue_2_model_agree with "Hmodel₁ Hmodel₂") as %Hvs.
      set vs' := front ++ reverse back.
      iMod (mpsc_queue_2_model_update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      rewrite Hvs.
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
      iSteps.
  Qed.
End mpsc_queue_2_G.

#[global] Opaque mpsc_queue_2_create.
#[global] Opaque mpsc_queue_2_push.
#[global] Opaque mpsc_queue_2_pop.

#[global] Opaque mpsc_queue_2_inv.
#[global] Opaque mpsc_queue_2_model.
#[global] Opaque mpsc_queue_2_consumer.
