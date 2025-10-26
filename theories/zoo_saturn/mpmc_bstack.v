From zoo Require Import
  prelude.
From zoo.common Require Import
  countable.
From zoo.iris.base_logic Require Import
  lib.twins.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  option.
From zoo_saturn Require Export
  base
  mpmc_bstack__code.
From zoo_saturn Require Import
  mpmc_bstack__types.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types cap sz : nat.
Implicit Types l : location.
Implicit Types v t front : val.
Implicit Types vs : list val.

Class MpmcBstackG Σ `{zoo_G : !ZooG Σ}:= {
  #[local] mpmc_bstack_G_model_G :: TwinsG Σ (leibnizO (list val)) ;
}.

Definition mpmc_bstack_Σ := #[
  twins_Σ (leibnizO (list val))
].
#[global] Instance subG_mpmc_bstack_Σ Σ `{zoo_G : !ZooG Σ} :
  subG mpmc_bstack_Σ Σ →
  MpmcBstackG Σ.
Proof.
  solve_inG.
Qed.

Section mpmc_bstack_G.
  Context `{mpmc_bstack_G : MpmcBstackG Σ}.

  Record metadata := {
    metadata_capacity : nat ;
    metadata_model : gname ;
  }.
  Implicit Types γ : metadata.

  #[local] Instance metadata_eq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[local] Instance metadata_countable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Fixpoint lst_to_val sz vs :=
    match vs with
    | [] =>
        §Nil%V
    | v :: vs =>
        ‘Cons[ #sz, v, lst_to_val (sz - 1) vs ]%V
    end.

  #[local] Instance lst_to_val_inj_similar sz :
    Inj (=) (≈@{val}) (lst_to_val sz).
  Proof.
    intros vs1. move: sz. induction vs1 as [| v1 vs1 IH]; intros sz [| v2 vs2]; [done.. |].
    intros (_ & _ & [= <- <-%val_similar_refl%IH]). done.
  Qed.
  #[local] Instance lst_to_val_inj sz :
    Inj (=) (=) (lst_to_val sz).
  Proof.
    intros ?* ->%val_similar_refl%(inj _). done.
  Qed.

  Lemma lst_to_val_inj' vs1 vs2 :
    lst_to_val (length vs1) vs1 ≈ lst_to_val (length vs2) vs2 →
    vs1 = vs2.
  Proof.
    destruct vs1, vs2; try done.
    intros (_ & _ & [= ->%(inj _) -> ?%(inj _)]). naive_solver.
  Qed.

  #[local] Definition model₁' γ_model vs :=
    twins_twin1 γ_model (DfracOwn 1) vs.
  #[local] Definition model₁ γ vs :=
    model₁' γ.(metadata_model) vs.
  #[local] Definition model₂' γ_model vs :=
    twins_twin2 γ_model vs.
  #[local] Definition model₂ γ vs :=
    model₂' γ.(metadata_model) vs.

  #[local] Definition inv_inner l γ : iProp Σ :=
    ∃ vs,
    l.[front] ↦ lst_to_val (length vs) vs ∗
    model₂ γ vs.
  #[local] Instance : CustomIpatFormat "inv_inner" :=
    "(
      %vs{} &
      Hl_front &
      Hmodel₂
    )".
  Definition mpmc_bstack_inv t ι cap : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    ⌜cap = γ.(metadata_capacity)⌝ ∗
    ⌜0 < γ.(metadata_capacity)⌝ ∗
    l.[capacity] ↦□ #γ.(metadata_capacity) ∗
    inv ι (inv_inner l γ).
  #[local] Instance : CustomIpatFormat "inv" :=
    "(
      %l &
      %γ &
      -> &
      #Hmeta &
      -> &
      %Hcapacity &
      #Hl_capacity &
      #Hinv
    )".

  Definition mpmc_bstack_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    ⌜length vs ≤ γ.(metadata_capacity)⌝ ∗
    model₁ γ vs.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %l{;_} &
      %γ{;_} &
      %Heq{} &
      Hmeta_{} &
      %Hvs{} &
      Hmodel₁{_{}}
    )".

  #[global] Instance mpmc_bstack_model_timeless t vs :
    Timeless (mpmc_bstack_model t vs).
  Proof.
    apply _.
  Qed.

  #[global] Instance mpmc_bstack_inv_persistent t ι cap :
    Persistent (mpmc_bstack_inv t ι cap).
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
  #[local] Lemma model₁_exclusive γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₁ γ vs2 -∗
    False.
  Proof.
    apply: twins_twin1_exclusive.
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
    apply twins_update.
  Qed.

  Lemma mpmc_bstack_model_valid t ι cap vs :
    mpmc_bstack_inv t ι cap -∗
    mpmc_bstack_model t vs -∗
    ⌜length vs ≤ cap⌝.
  Proof.
    iIntros "(:inv) (:model)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iSteps.
  Qed.
  Lemma mpmc_bstack_model_exclusive t vs1 vs2 :
    mpmc_bstack_model t vs1 -∗
    mpmc_bstack_model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (model₁_exclusive with "Hmodel₁_1 Hmodel₁_2").
  Qed.

  Lemma mpmc_bstack_create_spec ι (cap : Z) :
    (0 < cap)%Z →
    {{{
      True
    }}}
      mpmc_bstack_create #cap
    {{{ t,
      RET t;
      mpmc_bstack_inv t ι ₊cap ∗
      mpmc_bstack_model t []
    }}}.
  Proof.
    iIntros "%Hcap %Φ _ HΦ".

    wp_rec.
    wp_block l as "Hmeta" "(Hl_capacity & Hl_front & _)".
    iMod (pointsto_persist with "Hl_capacity") as "#Hl_capacity".
    rewrite -{1}(Z2Nat.id cap); first lia.

    iMod model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".

    pose γ := {|
      metadata_capacity := ₊cap ;
      metadata_model := γ_model ;
    |}.
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁"; last iSteps.
    iStep 5. iApply inv_alloc. iExists []. iSteps.
  Qed.

  Lemma mpmc_bstack_size_spec t ι cap :
    <<<
      mpmc_bstack_inv t ι cap
    | ∀∀ vs,
      mpmc_bstack_model t vs
    >>>
      mpmc_bstack_size t @ ↑ι
    <<<
      mpmc_bstack_model t vs
    | RET #(length vs);
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec.

    wp_bind (_.{front})%E.
    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
    iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
    iSplitR "HΦ". { iFrameSteps. }
    iIntros "!> {%}".

    destruct vs as [| v vs]; iSteps.
  Qed.

  Lemma mpmc_bstack_is_empty_spec t ι cap :
    <<<
      mpmc_bstack_inv t ι cap
    | ∀∀ vs,
      mpmc_bstack_model t vs
    >>>
      mpmc_bstack_is_empty t @ ↑ι
    <<<
      mpmc_bstack_model t vs
    | RET #(bool_decide (vs = []%list));
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec.

    wp_bind (_.{front})%E.
    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
    iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
    iSplitR "HΦ". { iFrameSteps. }
    iIntros "!> {%}".

    destruct vs as [| v vs]; iSteps.
  Qed.

  #[local] Lemma mpmc_bstack_push_aux_push_spec t ι cap v :
    ⊢ (
      ∀ (sz : Z) front ws,
      <<<
        ⌜sz = length ws⌝ ∗
        ⌜front = lst_to_val (length ws) ws⌝ ∗
        ⌜length ws < cap⌝ ∗
        mpmc_bstack_inv t ι cap
      | ∀∀ vs,
        mpmc_bstack_model t vs
      >>>
        mpmc_bstack_push_aux t #sz v front @ ↑ι
      <<<
        ∃∃ b,
        ⌜b = bool_decide (length vs < cap)⌝ ∗
        mpmc_bstack_model t (if b then v :: vs else vs)
      | RET #b;
        True
      >>>
    ) ∧ (
      <<<
        mpmc_bstack_inv t ι cap
      | ∀∀ vs,
        mpmc_bstack_model t vs
      >>>
        mpmc_bstack_push t v @ ↑ι
      <<<
        ∃∃ b,
        ⌜b = bool_decide (length vs < cap)⌝ ∗
        mpmc_bstack_model t (if b then v :: vs else vs)
      | RET #b;
        True
      >>>
    ).
  Proof.
    iLöb as "HLöb".
    iDestruct "HLöb" as "(IHpush_aux & IHpush)".
    iSplit.

    - iIntros "%sz %front %ws %Φ (-> & -> & %Hws & (:inv)) HΦ".

      wp_rec. wp_pures.

      wp_bind (CAS _ _ _).
      iInv "Hinv" as "(:inv_inner)".
      wp_cas as _ | <-%lst_to_val_inj'.

      + iSplitR "HΦ". { iFrameSteps. }
        iSteps.

      + iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
        iMod (model_update (v :: vs) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        rewrite bool_decide_eq_true_2 //.
        iMod ("HΦ" with "[Hmodel₁] [//]") as "HΦ"; first iSteps.
        rewrite Z.add_1_r -Nat2Z.inj_succ.
        iSplitR "HΦ".
        { iFrameSteps. rewrite Nat.sub_0_r //. }
        iSteps.

    - iIntros "%Φ (:inv) HΦ".

      wp_rec. wp_pures.

      wp_bind (_.{front})%E.
      iInv "Hinv" as "(:inv_inner)".
      wp_load.
      destruct_decide (γ.(metadata_capacity) ≤ length vs) as Hlen.

      + iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
        rewrite bool_decide_eq_false_2; first lia.
        iMod ("HΦ" with "[Hmodel₁] [//]") as "HΦ"; first iSteps.
        iSplitR "HΦ". { iFrameSteps. }
        iModIntro. clear- Hcapacity Hlen.

        destruct vs as [| w vs]; first naive_solver lia.
        wp_load. wp_pures.
        rewrite bool_decide_eq_true_2; first naive_solver lia.
        iSteps.

      + iSplitR "HΦ". { iFrameSteps. }
        iModIntro. clear- Hlen.

        destruct vs as [| w vs]; wp_pures.

        * wp_apply ("IHpush_aux" $! _ _ [] with "[] HΦ"); first iSteps.

        * simpl in Hlen.
          wp_load. wp_pures.
          rewrite bool_decide_eq_false_2; first lia.
          wp_smart_apply ("IHpush_aux" $! _ _ (w :: vs) with "[] HΦ"); first iSteps.
  Qed.
  Lemma mpmc_bstack_push_spec t ι cap v :
    <<<
      mpmc_bstack_inv t ι cap
    | ∀∀ vs,
      mpmc_bstack_model t vs
    >>>
      mpmc_bstack_push t v @ ↑ι
    <<<
      ∃∃ b,
      ⌜b = bool_decide (length vs < cap)⌝ ∗
      mpmc_bstack_model t (if b then v :: vs else vs)
    | RET #b;
      True
    >>>.
  Proof.
    iPoseProof mpmc_bstack_push_aux_push_spec as "(_ & H)".
    iApply "H".
  Qed.

  Lemma mpmc_bstack_pop_spec t ι cap :
    <<<
      mpmc_bstack_inv t ι cap
    | ∀∀ vs,
      mpmc_bstack_model t vs
    >>>
      mpmc_bstack_pop t @ ↑ι
    <<<
      mpmc_bstack_model t (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    iLöb as "HLöb".

    wp_rec.

    wp_bind (_.{front})%E.
    iInv "Hinv" as "(:inv_inner =1)".
    wp_load.
    destruct vs1 as [| v vs1].

    - iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
      iSplitR "HΦ". { iFrameSteps. }
      iSteps.

    - iSplitR "HΦ". { iFrameSteps. }
      iIntros "{%} !>".

      wp_pures.

      wp_bind (CAS _ _ _).
      iInv "Hinv" as "(:inv_inner =2)".
      wp_cas as _ | Hcas; first iSteps.
      destruct vs2; first done.
      destruct Hcas as (_ & _ & [= ->%(inj _) -> ->%(inj _)]).
      iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod (model_update vs1 with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[$Hmodel₁]") as "HΦ".
      { simpl in Hvs. iSteps. }
      iSplitR "HΦ". { iFrameSteps. }
      iSteps.
  Qed.
End mpmc_bstack_G.

From zoo_saturn Require
  mpmc_bstack__opaque.

#[global] Opaque mpmc_bstack_inv.
#[global] Opaque mpmc_bstack_model.
