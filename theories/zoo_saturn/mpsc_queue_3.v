From zoo Require Import
  prelude.
From zoo.common Require Import
  countable
  list.
From zoo.iris.base_logic Require Import
  lib.twins
  lib.oneshot.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  option
  clst.
From zoo_saturn Require Export
  base
  mpsc_queue_3__code.
From zoo_saturn Require Import
  mpsc_queue_3__types.
From zoo Require Import
  options.

Implicit Types b closed : bool.
Implicit Types l : location.
Implicit Types v t : val.
Implicit Types vs front back : list val.
Implicit Types ws : option (list val).

Class MpscQueue3G Σ `{zoo_G : !ZooG Σ} := {
  #[local] mpsc_queue_3_G_twins_G :: TwinsG Σ (leibnizO (list val)) ;
  #[local] mpsc_queue_3_G_lstate_G :: OneshotG Σ () () ;
}.

Definition mpsc_queue_3_Σ := #[
  twins_Σ (leibnizO (list val)) ;
  oneshot_Σ () ()
].
#[global] Instance subG_mpsc_queue_3_Σ Σ `{zoo_G : !ZooG Σ} :
  subG mpsc_queue_3_Σ Σ →
  MpscQueue3G Σ.
Proof.
  solve_inG.
Qed.

Section mpsc_queue_3_G.
  Context `{mpsc_queue_3_G : MpscQueue3G Σ}.

  Record metadata := {
    metadata_model : gname ;
    metadata_front : gname ;
    metadata_lstate : gname ;
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

  #[local] Definition lstate_open₁' γ_lstate :=
    oneshot_pending γ_lstate (DfracOwn (1/2)) ().
  #[local] Definition lstate_open₁ γ :=
    lstate_open₁' γ.(metadata_lstate).
  #[local] Definition lstate_open₂' γ_lstate :=
    oneshot_pending γ_lstate (DfracOwn (1/2)) ().
  #[local] Definition lstate_open₂ γ :=
    lstate_open₂' γ.(metadata_lstate).
  #[local] Definition lstate_closed γ :=
    oneshot_shot γ.(metadata_lstate) ().

  #[local] Definition inv_inner l γ : iProp Σ :=
    ∃ front v_back,
    front₂ γ front ∗
    l.[back] ↦ v_back ∗
    ((lstate_open₂ γ ∗
      ∃ back,
      ⌜v_back = list_to_clist_open back⌝ ∗
      model₂ γ (front ++ reverse back)
    ) ∨ (
      lstate_closed γ ∗
      ⌜v_back = §ClstClosed%V⌝
    )).
  Definition mpsc_queue_3_inv t ι : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    inv ι (inv_inner l γ).

  Definition mpsc_queue_3_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    model₁ γ vs.

  Definition mpsc_queue_3_consumer t ws : iProp Σ :=
    ∃ l γ v_front front,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[front] ↦ v_front ∗
    front₁ γ front ∗
    ( ⌜ws = None ∧ v_front = list_to_clist_open front⌝ ∗
      lstate_open₁ γ
    ∨ ⌜ws = Some front ∧ v_front = list_to_clist_closed front⌝ ∗
      lstate_closed γ ∗
      model₂ γ front
    ).

  Definition mpsc_queue_3_closed t : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    lstate_closed γ.

  #[global] Instance mpsc_queue_3_model_timeless t vs :
    Timeless (mpsc_queue_3_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpsc_queue_3_consumer_timeless t ws :
    Timeless (mpsc_queue_3_consumer t ws ).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpsc_queue_3_inv_persistent t ι :
    Persistent (mpsc_queue_3_inv t ι).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpsc_queue_3_closed_persistent t :
    Persistent (mpsc_queue_3_closed t).
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

  #[local] Lemma lstate_alloc :
    ⊢ |==>
      ∃ γ_lstate,
      lstate_open₁' γ_lstate ∗
      lstate_open₂' γ_lstate.
  Proof.
    iMod oneshot_alloc as "(%γ_lstate & (Hopen₁ & Hopen₂))".
    iSteps.
  Qed.
  #[local] Lemma lstate_open₁_closed γ :
    lstate_open₁ γ -∗
    lstate_closed γ -∗
    False.
  Proof.
    apply oneshot_pending_shot.
  Qed.
  #[local] Lemma lstate_open₂_closed γ :
    lstate_open₂ γ -∗
    lstate_closed γ -∗
    False.
  Proof.
    apply oneshot_pending_shot.
  Qed.
  #[local] Lemma lstate_update γ :
    lstate_open₁ γ -∗
    lstate_open₂ γ ==∗
    lstate_closed γ.
  Proof.
    iIntros "Hopen₁ Hopen₂".
    iCombine "Hopen₁ Hopen₂" as "Hopen".
    iApply (oneshot_update_shot with "Hopen").
  Qed.

  Lemma mpsc_queue_3_consumer_exclusive t ws1 ws2 :
    mpsc_queue_3_consumer t ws1 -∗
    mpsc_queue_3_consumer t ws2 -∗
    False.
  Proof.
    iSteps.
  Qed.
  Lemma mpsc_queue_3_consumer_closed t vs :
    mpsc_queue_3_consumer t (Some vs) ⊢
    mpsc_queue_3_closed t.
  Proof.
    iSteps.
  Qed.

  Lemma mpsc_queue_3_create_spec ι :
    {{{
      True
    }}}
      mpsc_queue_3_create ()
    {{{ t,
      RET t;
      mpsc_queue_3_inv t ι ∗
      mpsc_queue_3_model t [] ∗
      mpsc_queue_3_consumer t None
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.

    wp_block l as "Hmeta" "(Hfront & Hback & _)".

    iMod model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod front_alloc as "(%γ_front & Hfront₁ & Hfront₂)".
    iMod lstate_alloc as "(%γ_lstate & Hopen₁ & Hopen₂)".

    pose γ := {|
      metadata_model := γ_model ;
      metadata_front := γ_front ;
      metadata_lstate := γ_lstate ;
    |}.
    iMod (meta_set _ _ γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁ Hfront Hfront₁ Hopen₁"; last iSteps.
    iSteps. iExists []. iSteps.
  Qed.

  Lemma mpsc_queue_3_push_front_spec_open t ι v :
    <<<
      mpsc_queue_3_inv t ι ∗
      mpsc_queue_3_consumer t None
    | ∀∀ vs,
      mpsc_queue_3_model t vs
    >>>
      mpsc_queue_3_push_front t v @ ↑ι
    <<<
      mpsc_queue_3_model t (v :: vs)
    | RET #false;
      mpsc_queue_3_consumer t None
    >>>.
  Proof.
    iIntros "!> %Φ ((%l & %γ & -> & #Hmeta & #Hinv) & (%_l & %_γ & %v_front & %front & %Heq & _Hmeta & Hfront & Hfront₁ & Hlstate)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct "Hlstate" as "[((_ & ->) & Hopen₁) | ((% & _) & _)]"; last done.

    wp_rec. wp_load.
    iApply wp_match_clist_open. wp_store. wp_pures.

    iInv "Hinv" as "(%_front & %v_back & >Hfront₂ & Hback & [(Hopen₂ & %back & >-> & >Hmodel₂) | (>Hclosed & _)])"; last first.
    { iDestruct (lstate_open₁_closed with "Hopen₁ Hclosed") as %[]. }
    iDestruct (front_agree with "Hfront₁ Hfront₂") as %<-.
    set front' := v :: front.
    iMod (front_update front' with "Hfront₁ Hfront₂") as "(Hfront₁ & Hfront₂)".
    iMod "HΦ" as "(%vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
    set vs' := front' ++ reverse back.
    iMod (model_update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
    iSteps.
  Qed.
  Lemma mpsc_queue_3_push_front_spec_closed t ι vs v :
    <<<
      mpsc_queue_3_inv t ι ∗
      mpsc_queue_3_consumer t (Some vs)
    | ∀∀ vs',
      mpsc_queue_3_model t vs'
    >>>
      mpsc_queue_3_push_front t v @ ↑ι
    <<<
      ⌜vs' = vs⌝ ∗
      mpsc_queue_3_model t (if vs is [] then [] else v :: vs)
    | RET #(bool_decide (vs = []%list));
      mpsc_queue_3_consumer t (Some $ if vs is [] then [] else v :: vs)
    >>>.
  Proof.
    iIntros "!> %Φ ((%l & %γ & -> & #Hmeta & #Hinv) & (%_l & %_γ & %v_front & %front & %Heq & _Hmeta & Hfront & Hfront₁ & Hlstate)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct "Hlstate" as "[((% & _) & _) | ((%Heq & ->) & Hclosed & Hmodel₂)]"; first done. injection Heq as ->.

    wp_rec. wp_load.

    destruct front as [| v' front]; wp_pures.

    - iMod "HΦ" as "(%vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
      iSteps.

    - wp_store. wp_pures.
      iInv "Hinv" as "(%_front & %v_back & >Hfront₂ & Hback & [(>Hopen₂ & _) | (_ & >->)])".
      { iDestruct (lstate_open₂_closed with "Hopen₂ Hclosed") as %[]. }
      iDestruct (front_agree with "Hfront₁ Hfront₂") as %<-.
      set front' := v :: v' :: front.
      iMod (front_update front' with "Hfront₁ Hfront₂") as "(Hfront₁ & Hfront₂)".
      iMod "HΦ" as "(%vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod (model_update front' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
      iSteps.
  Qed.

  Lemma mpsc_queue_3_push_back_spec_open closed t ι v :
    <<<
      mpsc_queue_3_inv t ι
    | ∀∀ vs,
      mpsc_queue_3_model t vs
    >>>
      mpsc_queue_3_push_back t v @ ↑ι
    <<<
      ∃∃ closed,
      if closed then
        mpsc_queue_3_model t vs
      else
        mpsc_queue_3_model t (vs ++ [v])
    | RET #closed;
      if closed then
        mpsc_queue_3_closed t
      else
        True
    >>>.
  Proof.
    iIntros "!> %Φ (%l & %γ & -> & #Hmeta & #Hinv) HΦ".

    iLöb as "HLöb".

    wp_rec. wp_pures.

    wp_bind (_.{back})%E.
    iInv "Hinv" as "(%front & %v_back & Hfront₂ & Hback & [(>Hopen₂ & %back1 & >-> & Hmodel₂) | (Hclosed & >->)])".

    - wp_load.
      iSplitR "HΦ"; first iSteps.
      iModIntro. clear.

      iApply wp_match_clist_open. wp_pures.

      wp_bind (CAS _ _ _).
      iInv "Hinv" as "(%front & %v_back & Hfront₂ & Hback & [(>Hopen₂ & %back2 & >-> & Hmodel₂) | (Hclosed & >->)])".

      + wp_cas as _ | ->%(inj _)%(inj _); first iSteps.
        iMod "HΦ" as "(%vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
        set back := v :: back1.
        set vs' := front ++ reverse back.
        iMod (model_update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" $! false with "[Hmodel₁]") as "HΦ".
        { iSteps. rewrite -assoc /vs' reverse_cons //. }
        iSplitR "HΦ". { iSteps. iExists back. iSteps. }
        iSteps.

      + wp_cas as _ | []%(inj clist_to_val ClistClosed)%list_to_clist_open_not_closed'.
        iSteps.

    - iMod "HΦ" as "(%vs & Hmodel & _ & HΦ)".
      iMod ("HΦ" $! true with "Hmodel") as "HΦ".
      iSteps.
  Qed.
  Lemma mpsc_queue_3_push_back_spec_closed closed t ι v :
    {{{
      mpsc_queue_3_inv t ι ∗
      mpsc_queue_3_closed t
    }}}
      mpsc_queue_3_push_back t v
    {{{
      RET #true;
      True
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & -> & #Hmeta & #Hinv) & (%_l & %_γ & %Heq & _Hmeta & Hclosed)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

    iLöb as "HLöb".

    wp_rec. wp_pures.

    wp_bind (_.{back})%E.
    iInv "Hinv" as "(%front & %v_back & Hfront₂ & Hback & [(>Hopen₂ & _) | (_ & >->)])".
    { iDestruct (lstate_open₂_closed with "Hopen₂ Hclosed") as %[]. }
    iSteps.
  Qed.

  Lemma mpsc_queue_3_pop_front_spec_open t ι :
    <<<
      mpsc_queue_3_inv t ι ∗
      mpsc_queue_3_consumer t None
    | ∀∀ vs,
      mpsc_queue_3_model t vs
    >>>
      mpsc_queue_3_pop_front t @ ↑ι
    <<<
      mpsc_queue_3_model t (tail vs)
    | RET head vs;
      mpsc_queue_3_consumer t None
    >>>.
  Proof.
    iIntros "!> %Φ ((%l & %γ & -> & #Hmeta & #Hinv) & (%_l & %_γ & %v_front & %front & %Heq & _Hmeta & Hfront & Hfront₁ & Hlstate)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct "Hlstate" as "[((_ & ->) & Hopen₁) | ((% & _) & _)]"; last done.

    wp_rec. wp_load.

    destruct front as [| v front]; wp_pures.

    - wp_bind (Xchg _ _).
      iInv "Hinv" as "(%_front & %v_back & Hfront₂ & Hback & [(Hopen₂ & %back & >-> & Hmodel₂) | (>Hclosed & _)])"; last first.
      { iDestruct (lstate_open₁_closed with "Hopen₁ Hclosed") as %[]. }
      wp_xchg.
      iDestruct (front_agree with "Hfront₁ Hfront₂") as %<-.
      iMod "HΦ" as "(%vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      destruct (rev_elim back) as [-> | (back' & v' & ->)].

      + iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
        iSplitR "Hfront Hfront₁ Hopen₂ HΦ".
        { iSteps. iExists []. iSteps. }
        iSteps.

      + set front := reverse back'.
        iMod (front_update front with "Hfront₁ Hfront₂") as "(Hfront₁ & Hfront₂)".
        iMod (model_update front with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        rewrite reverse_snoc /=.
        iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
        iSplitR "Hfront Hfront₁ Hopen₂ HΦ".
        { iSteps. iExists []. iSteps. rewrite right_id //. }
        iModIntro. clear.

        remember (back' ++ [v']) as back eqn:Hback.
        destruct back as [| v'' back'']; first by eelim app_cons_not_nil.
        wp_smart_apply (clst_rev_app_spec (v'' :: back'') ClistOpen with "[//]") as "_"; [done.. |].
        rewrite clist_app_ClistOpen {}Hback reverse_snoc.
        iSteps.

    - wp_store. wp_pures.

      iInv "Hinv" as "(%_front & %v_back & >Hfront₂ & Hback & [(Hopen₂ & %back & >-> & >Hmodel₂) | (>Hclosed & _)])"; last first.
      { iDestruct (lstate_open₁_closed with "Hopen₁ Hclosed") as %[]. }
      iDestruct (front_agree with "Hfront₁ Hfront₂") as %<-.
      iMod (front_update front with "Hfront₁ Hfront₂") as "(Hfront₁ & Hfront₂)".
      iMod "HΦ" as "(%vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      set vs := front ++ reverse back.
      iMod (model_update vs with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
      iSteps.
  Qed.
  Lemma mpsc_queue_3_pop_front_spec_closed t ι vs :
    <<<
      mpsc_queue_3_inv t ι ∗
      mpsc_queue_3_consumer t (Some vs)
    | ∀∀ vs',
      mpsc_queue_3_model t vs'
    >>>
      mpsc_queue_3_pop_front t @ ↑ι
    <<<
      ⌜vs' = vs⌝ ∗
      mpsc_queue_3_model t (tail vs)
    | RET head vs;
      mpsc_queue_3_consumer t (Some $ tail vs)
    >>>.
  Proof.
    iIntros "!> %Φ ((%l & %γ & -> & #Hmeta & #Hinv) & (%_l & %_γ & %v_front & %front & %Heq & _Hmeta & Hfront & Hfront₁ & Hlstate)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct "Hlstate" as "[((% & _) & _) | ((%Heq & ->) & Hclosed & Hmodel₂)]"; first done. injection Heq as ->.

    wp_rec. wp_load.

    destruct front as [| v front]; wp_pures.

    - iMod "HΦ" as "(%vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
      iSteps.

    - wp_store. wp_pures.
      iInv "Hinv" as "(%_front & %v_back & >Hfront₂ & Hback & [(>Hopen₂ & _) | (_ & >->)])".
      { iDestruct (lstate_open₂_closed with "Hopen₂ Hclosed") as %[]. }
      iDestruct (front_agree with "Hfront₁ Hfront₂") as %<-.
      iMod (front_update front with "Hfront₁ Hfront₂") as "(Hfront₁ & Hfront₂)".
      iMod "HΦ" as "(%vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod (model_update front with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
      iSteps.
  Qed.

  Lemma mpsc_queue_3_close_spec_open t ι :
    <<<
      mpsc_queue_3_inv t ι ∗
      mpsc_queue_3_consumer t None
    | ∀∀ vs,
      mpsc_queue_3_model t vs
    >>>
      mpsc_queue_3_close t @ ↑ι
    <<<
      mpsc_queue_3_model t vs
    | RET #false;
      mpsc_queue_3_consumer t (Some vs)
    >>>.
  Proof.
    iIntros "!> %Φ ((%l & %γ & -> & #Hmeta & #Hinv) & (%_l & %_γ & %v_front & %front & %Heq & _Hmeta & Hfront & Hfront₁ & Hlstate)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct "Hlstate" as "[((_ & ->) & Hopen₁) | ((% & _) & _)]"; last done.

    wp_rec. wp_pures.

    wp_bind (Xchg _ _).
    iInv "Hinv" as "(%_front & %v_back & Hfront₂ & Hback & [(Hopen₂ & %back & >-> & Hmodel₂) | (>Hclosed & _)])"; last first.
    { iDestruct (lstate_open₁_closed with "Hopen₁ Hclosed") as %[]. }
    wp_xchg.
    iDestruct (front_agree with "Hfront₁ Hfront₂") as %<-.
    set front' := front ++ reverse back.
    iMod (front_update front' with "Hfront₁ Hfront₂") as "(Hfront₁ & Hfront₂)".
    iMod (lstate_update with "Hopen₁ Hopen₂") as "#Hclosed".
    iMod "HΦ" as "(%vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
    iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
    iSplitR "Hfront Hfront₁ Hmodel₂ HΦ"; first iSteps.
    iModIntro. clear.

    iApply wp_match_clist_open. simpl.
    wp_apply (clst_rev_app_spec _ ClistClosed with "[//]") as "_"; [done.. |].
    wp_load.
    wp_apply (clst_app_spec with "[//]") as "_"; [done.. |].
    wp_store.

    iSteps. rewrite clist_app_ClistClosed. erewrite clist_app_closed => //.
  Qed.
  Lemma mpsc_queue_3_close_spec_closed t ι vs :
    {{{
      mpsc_queue_3_inv t ι ∗
      mpsc_queue_3_consumer t (Some vs)
    }}}
      mpsc_queue_3_close t
    {{{
      RET #true;
      mpsc_queue_3_consumer t (Some vs)
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & -> & #Hmeta & #Hinv) & (%_l & %_γ & %v_front & %front & %Heq & _Hmeta & Hfront & Hfront₁ & Hlstate)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct "Hlstate" as "[((% & _) & _) | ((%Heq & ->) & Hclosed & Hmodel₂)]"; first done. injection Heq as ->.

    wp_rec. wp_pures.

    wp_bind (Xchg _ _).
    iInv "Hinv" as "(%_front & %v_back & >Hfront₂ & Hback & [(>Hopen₂ & _) | (_ & >->)])".
    { iDestruct (lstate_open₂_closed with "Hopen₂ Hclosed") as %[]. }
    iSteps.
  Qed.

  Lemma mpsc_queue_3_is_empty_spec_open t ι :
    <<<
      mpsc_queue_3_inv t ι ∗
      mpsc_queue_3_consumer t None
    | ∀∀ vs,
      mpsc_queue_3_model t vs
    >>>
      mpsc_queue_3_is_empty t @ ↑ι
    <<<
      mpsc_queue_3_model t vs
    | RET #(bool_decide (vs = []%list));
      mpsc_queue_3_consumer t None
    >>>.
  Proof.
    iIntros "!> %Φ ((%l & %γ & -> & #Hmeta & #Hinv) & (%_l & %_γ & %v_front & %front & %Heq & _Hmeta & Hfront & Hfront₁ & Hlstate)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct "Hlstate" as "[((_ & ->) & Hopen₁) | ((% & _) & _)]"; last done.

    wp_rec. wp_load.

    destruct front as [| v front]; wp_pures.

    - wp_bind (_.{back})%E.
      iInv "Hinv" as "(%_front & %v_back & Hfront₂ & Hback & [(Hopen₂ & %back & >-> & Hmodel₂) | (>Hclosed & _)])"; last first.
      { iDestruct (lstate_open₁_closed with "Hopen₁ Hclosed") as %[]. }
      wp_load.
      iDestruct (front_agree with "Hfront₁ Hfront₂") as %<-.
      iMod "HΦ" as "(%vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      destruct back as [| v back].

      + iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
        iSplitR "Hfront Hfront₁ Hopen₁ HΦ".
        { iSteps. iExists []. iSteps. }
        iSteps.

      + iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
        iSplitR "Hfront Hfront₁ Hopen₁ HΦ".
        { iSteps. iExists (v :: back). iSteps. }
        rewrite reverse_cons bool_decide_eq_false_2 /=; first intros (_ & [=])%app_nil.
        iSteps.

    - iInv "Hinv" as "(%_front & %v_back & >Hfront₂ & Hback & [(Hopen₂ & %back & >-> & >Hmodel₂) | (>Hclosed & _)])"; last first.
      { iDestruct (lstate_open₁_closed with "Hopen₁ Hclosed") as %[]. }
      iDestruct (front_agree with "Hfront₁ Hfront₂") as %<-.
      iMod "HΦ" as "(%vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
      iSteps.
  Qed.
  Lemma mpsc_queue_3_is_empty_spec_closed t ι vs :
    {{{
      mpsc_queue_3_inv t ι ∗
      mpsc_queue_3_consumer t (Some vs)
    }}}
      mpsc_queue_3_is_empty t
    {{{
      RET #(bool_decide (vs = []%list));
      mpsc_queue_3_consumer t (Some vs)
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & -> & #Hmeta & #Hinv) & (%_l & %_γ & %v_front & %front & %Heq & _Hmeta & Hfront & Hfront₁ & Hlstate)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct "Hlstate" as "[((% & _) & _) | ((%Heq & ->) & Hclosed & Hmodel₂)]"; first done. injection Heq as ->.

    wp_rec. wp_load.

    destruct front as [| v front]; iSteps.
  Qed.
End mpsc_queue_3_G.

#[global] Opaque mpsc_queue_3_create.
#[global] Opaque mpsc_queue_3_push_front.
#[global] Opaque mpsc_queue_3_push_back.
#[global] Opaque mpsc_queue_3_pop_front.
#[global] Opaque mpsc_queue_3_close.
#[global] Opaque mpsc_queue_3_is_empty.

#[global] Opaque mpsc_queue_3_inv.
#[global] Opaque mpsc_queue_3_model.
#[global] Opaque mpsc_queue_3_consumer.
#[global] Opaque mpsc_queue_3_closed.
