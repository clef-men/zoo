From zoo Require Import
  prelude.
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

  Record mpmc_bstack_meta := {
    mpmc_bstack_meta_capacity : nat ;
    mpmc_bstack_meta_model : gname ;
  }.
  Implicit Types γ : mpmc_bstack_meta.

  #[local] Instance mpmc_bstack_meta_eq_dec : EqDecision mpmc_bstack_meta :=
    ltac:(solve_decision).
  #[local] Instance mpmc_bstack_meta_countable :
    Countable mpmc_bstack_meta.
  Proof.
    pose encode γ := (
      γ.(mpmc_bstack_meta_capacity),
      γ.(mpmc_bstack_meta_model)
    ).
    pose decode := λ '(capacity, γ_model), {|
      mpmc_bstack_meta_capacity := capacity ;
      mpmc_bstack_meta_model := γ_model ;
    |}.
    refine (inj_countable' encode decode _). intros []. done.
  Qed.

  #[local] Fixpoint mpmc_bstack_lst sz vs :=
    match vs with
    | [] =>
        §Nil%V
    | v :: vs =>
        ‘Cons( #sz, v, mpmc_bstack_lst (sz - 1) vs )%V
    end.

  #[local] Instance mpmc_bstack_lst_physical sz vs :
    ValPhysical (mpmc_bstack_lst sz vs).
  Proof.
    induction vs; done.
  Qed.
  #[local] Instance mpmc_bstack_lst_inj sz :
    Inj (=) (=) (mpmc_bstack_lst sz).
  Proof.
    intros vs1. move: sz. induction vs1 => sz vs2; destruct vs2; naive_solver.
  Qed.

  Lemma mpmc_bstack_lst_inj' vs1 vs2 :
    val_eq (mpmc_bstack_lst (length vs1) vs1) (mpmc_bstack_lst (length vs2) vs2) →
    vs1 = vs2.
  Proof.
    destruct vs1, vs2; try naive_solver.
    intros (_ & _ & [= ->%(inj _) -> ?%(inj _)]). naive_solver.
  Qed.

  #[local] Definition mpmc_bstack_model₁' γ_model vs :=
    twins_twin1 γ_model (DfracOwn 1) vs.
  #[local] Definition mpmc_bstack_model₁ γ vs :=
    mpmc_bstack_model₁' γ.(mpmc_bstack_meta_model) vs.
  #[local] Definition mpmc_bstack_model₂' γ_model vs :=
    twins_twin2 γ_model vs.
  #[local] Definition mpmc_bstack_model₂ γ vs :=
    mpmc_bstack_model₂' γ.(mpmc_bstack_meta_model) vs.

  #[local] Definition mpmc_bstack_inv_inner l γ : iProp Σ :=
    ∃ vs,
    l.[front] ↦ mpmc_bstack_lst (length vs) vs ∗
    mpmc_bstack_model₂ γ vs.
  Definition mpmc_bstack_inv t ι cap : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    ⌜cap = γ.(mpmc_bstack_meta_capacity)⌝ ∗
    ⌜0 < cap⌝ ∗
    l.[capacity] ↦□ #cap ∗
    inv ι (mpmc_bstack_inv_inner l γ).

  Definition mpmc_bstack_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    ⌜length vs ≤ γ.(mpmc_bstack_meta_capacity)⌝ ∗
    mpmc_bstack_model₁ γ vs.

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

  #[local] Lemma mpmc_bstack_model_alloc :
    ⊢ |==>
      ∃ γ_model,
      mpmc_bstack_model₁' γ_model [] ∗
      mpmc_bstack_model₂' γ_model [].
  Proof.
    apply twins_alloc'.
  Qed.
  #[local] Lemma mpmc_bstack_model_agree γ vs1 vs2 :
    mpmc_bstack_model₁ γ vs1 -∗
    mpmc_bstack_model₂ γ vs2 -∗
    ⌜vs1 = vs2⌝.
  Proof.
    apply: twins_agree_L.
  Qed.
  #[local] Lemma mpmc_bstack_model_update {γ vs1 vs2} vs :
    mpmc_bstack_model₁ γ vs1 -∗
    mpmc_bstack_model₂ γ vs2 ==∗
      mpmc_bstack_model₁ γ vs ∗
      mpmc_bstack_model₂ γ vs.
  Proof.
    apply twins_update'.
  Qed.

  Lemma mpmc_bstack_model_valid t ι cap vs :
    mpmc_bstack_inv t ι cap -∗
    mpmc_bstack_model t vs -∗
    ⌜length vs ≤ cap⌝.
  Proof.
    iIntros "(%l & %γ & -> & #Hmeta & -> & %Hcap & #Hl_capacity & #Hinv) (%_l & %_γ & %Heq & _Hmeta & %Hvs & Hmodel₁)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iSteps.
  Qed.

  Lemma mpmc_bstack_create_spec ι (cap : Z) :
    (0 < cap)%Z →
    {{{
      True
    }}}
      mpmc_bstack_create #cap
    {{{ t,
      RET t;
      mpmc_bstack_inv t ι (Z.to_nat cap) ∗
      mpmc_bstack_model t []
    }}}.
  Proof.
    iIntros "%Hcap %Φ _ HΦ".

    wp_rec.
    wp_block l as "Hmeta" "(Hl_capacity & Hl_front & _)".
    iMod (pointsto_persist with "Hl_capacity") as "#Hl_capacity".
    rewrite -{1}(Z2Nat.id cap); first lia.

    iMod mpmc_bstack_model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".

    pose γ := {|
      mpmc_bstack_meta_capacity := Z.to_nat cap ;
      mpmc_bstack_meta_model := γ_model ;
    |}.
    iMod (meta_set _ _ γ with "Hmeta") as "#Hmeta"; first done.

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
    iIntros "!> %Φ #(%l & %γ & -> & #Hmeta & -> & %Hcap & #Hl_capacity & #Hinv) HΦ".

    wp_rec.

    wp_bind (_.{front})%E.
    iInv "Hinv" as "(%vs & Hl_front & Hmodel₂)".
    wp_load.
    iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & _Hmeta & %Hvs & Hmodel₁) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (mpmc_bstack_model_agree with "Hmodel₁ Hmodel₂") as %->.
    iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
    iSplitR "HΦ"; first iSteps.
    iModIntro. clear.

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
    iIntros "!> %Φ #(%l & %γ & -> & #Hmeta & -> & %Hcap & #Hl_capacity & #Hinv) HΦ".

    wp_rec.

    wp_bind (_.{front})%E.
    iInv "Hinv" as "(%vs & Hl_front & Hmodel₂)".
    wp_load.
    iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & _Hmeta & %Hvs & Hmodel₁) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (mpmc_bstack_model_agree with "Hmodel₁ Hmodel₂") as %->.
    iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
    iSplitR "HΦ"; first iSteps.
    iModIntro. clear.

    destruct vs as [| v vs]; iSteps.
  Qed.

  #[local] Lemma mpmc_bstack_push_aux_push_spec t ι cap v :
    ⊢ (
      ∀ (sz : Z) front ws,
      <<<
        ⌜sz = length ws⌝ ∗
        ⌜front = mpmc_bstack_lst (length ws) ws⌝ ∗
        ⌜length ws < cap⌝ ∗
        mpmc_bstack_inv t ι cap
      | ∀∀ vs,
        mpmc_bstack_model t vs
      >>>
        mpmc_bstack_push_aux t #sz v front @ ↑ι
      <<<
        mpmc_bstack_model t (if decide (length vs < cap) then v :: vs else vs)
      | RET #(bool_decide (length vs < cap));
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
        mpmc_bstack_model t (if decide (length vs < cap) then v :: vs else vs)
      | RET #(bool_decide (length vs < cap));
        True
      >>>
    ).
  Proof.
    iLöb as "HLöb".
    iDestruct "HLöb" as "(Hpush_aux & Hpush)".
    iSplit.

    - iIntros "%sz %front %ws !> %Φ (-> & -> & %Hws & #(%l & %γ & -> & #Hmeta & -> & %Hcap & #Hl_capacity & #Hinv)) HΦ".

      wp_recs. wp_pures.

      wp_bind (CAS _ _ _).
      iInv "Hinv" as "(%vs & Hl_front & Hmodel₂)".
      wp_cas as _ | <-%mpmc_bstack_lst_inj'.

      + iSplitR "HΦ"; first iSteps.
        iModIntro.

        wp_smart_apply ("Hpush" with "[] HΦ"); first iSteps.

      + iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & _Hmeta & %Hvs & Hmodel₁) & _ & HΦ)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
        iDestruct (mpmc_bstack_model_agree with "Hmodel₁ Hmodel₂") as %->.
        iMod (mpmc_bstack_model_update (v :: vs) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        rewrite decide_True; first lia. rewrite bool_decide_eq_true_2; first lia.
        iMod ("HΦ" with "[Hmodel₁] [//]") as "HΦ"; first iSteps.
        rewrite Z.add_1_r -Nat2Z.inj_succ.
        iSplitR "HΦ". { iExists (v :: vs). iSteps. rewrite Nat.sub_0_r //. }
        iSteps.

    - iIntros "!> %Φ #(%l & %γ & -> & #Hmeta & -> & %Hcap & #Hl_capacity & #Hinv) HΦ".

      wp_recs. wp_pures.

      wp_bind (_.{front})%E.
      iInv "Hinv" as "(%vs & Hl_front & Hmodel₂)".
      wp_load.
      destruct (decide (γ.(mpmc_bstack_meta_capacity) ≤ length vs)) as [Hlen | Hlen].

      + iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & _Hmeta & %Hvs & Hmodel₁) & _ & HΦ)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
        iDestruct (mpmc_bstack_model_agree with "Hmodel₁ Hmodel₂") as %->.
        rewrite decide_False; first lia. rewrite bool_decide_eq_false_2; first lia.
        iMod ("HΦ" with "[Hmodel₁] [//]") as "HΦ"; first iSteps.
        iSplitR "HΦ"; first iSteps.
        iModIntro.

        destruct vs as [| w vs]; first naive_solver lia.
        wp_load. wp_pures.
        rewrite bool_decide_eq_true_2; first naive_solver lia.
        iSteps.

      + iSplitR "HΦ"; first iSteps.
        iModIntro.

        destruct vs as [| w vs]; wp_pures.

        * wp_apply ("Hpush_aux" $! _ _ [] with "[] HΦ"); first iSteps.

        * simpl in Hlen.
          wp_load. wp_pures.
          rewrite bool_decide_eq_false_2; first lia.
          wp_smart_apply ("Hpush_aux" $! _ _ (w :: vs) with "[] HΦ"); first iSteps.
  Qed.
  Lemma mpmc_bstack_push_spec t ι cap v :
    <<<
      mpmc_bstack_inv t ι cap
    | ∀∀ vs,
      mpmc_bstack_model t vs
    >>>
      mpmc_bstack_push t v @ ↑ι
    <<<
        mpmc_bstack_model t (if decide (length vs < cap) then v :: vs else vs)
      | RET #(bool_decide (length vs < cap));
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
    iIntros "!> %Φ #(%l & %γ & -> & #Hmeta & -> & %Hcap & #Hl_capacity & #Hinv) HΦ".

    iLöb as "HLöb".

    wp_rec.

    wp_bind (_.{front})%E.
    iInv "Hinv" as "(%vs & Hl_front & Hmodel₂)".
    wp_load.
    destruct vs as [| v vs].

    - iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & _Hmeta & %Hvs & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (mpmc_bstack_model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
      iSplitR "HΦ". { iExists []. iSteps. }
      iSteps.

    - iSplitR "HΦ". { iExists (v :: vs). iSteps. }
      iModIntro.

      wp_pures.

      wp_bind (CAS _ _ _).
      iInv "Hinv" as "(%vs' & Hl_front & Hmodel₂)".
      wp_cas as _ | Hcas; first iSteps.
      destruct vs'; first naive_solver.
      destruct Hcas as (_ & _ & [= ->%(inj _) -> ->%(inj _)]).
      iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & _Hmeta & %Hvs & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (mpmc_bstack_model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod (mpmc_bstack_model_update vs with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      simpl in Hvs.
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
      iSplitR "HΦ"; first iSteps.
      iSteps.
  Qed.
End mpmc_bstack_G.

#[global] Opaque mpmc_bstack_create.
#[global] Opaque mpmc_bstack_size.
#[global] Opaque mpmc_bstack_is_empty.
#[global] Opaque mpmc_bstack_push.
#[global] Opaque mpmc_bstack_pop.

#[global] Opaque mpmc_bstack_inv.
#[global] Opaque mpmc_bstack_model.
