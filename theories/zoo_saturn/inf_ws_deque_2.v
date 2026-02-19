From zoo Require Import
  prelude.
From zoo.common Require Import
  countable
  relations.
From zoo.iris.base_logic Require Import
  lib.auth_twins.
From zoo.language Require Import
  notations.
From zoo.iris.bi Require Import
  big_op.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  option.
From zoo_saturn Require Export
  base
  inf_ws_deque_2__code.
From zoo_saturn Require Import
  inf_ws_deque_1.
From zoo Require Import
  options.

Import inf_ws_deque_1.base.

Implicit Types slot : location.
Implicit Types slots : list location.
Implicit Types v : val.
Implicit Types vs ws : list val.

Class InfWsDeque2G Σ `{zoo_G : !ZooG Σ} := {
  #[local] inf_ws_deque_2_G_base_G :: InfWsDeque1G Σ ;
  #[local] inf_ws_deque_2_G_model_G :: AuthTwinsG Σ (leibnizO (list val)) suffix ;
}.

Definition inf_ws_deque_2_Σ := #[
  inf_ws_deque_1_Σ ;
  auth_twins_Σ (leibnizO (list val)) suffix
].
#[global] Instance subG_inf_ws_deque_2_Σ Σ `{zoo_G : !ZooG Σ} :
  subG inf_ws_deque_2_Σ Σ →
  InfWsDeque2G Σ .
Proof.
  solve_inG.
Qed.

Module base.
  Section inf_ws_deque_2_G.
    Context `{inf_ws_deque_2_G : InfWsDeque2G Σ}.

    Implicit Types t : location.

    Record inf_ws_deque_2_name := {
      inf_ws_deque_2_name_base : inf_ws_deque_1_name ;
      inf_ws_deque_2_name_model : auth_twins_name ;
    }.
    Implicit Type γ : inf_ws_deque_2_name.

    #[global] Instance inf_ws_deque_2_name_eq_dec : EqDecision inf_ws_deque_2_name :=
      ltac:(solve_decision).
    #[global] Instance inf_ws_deque_2_name_countable :
      Countable inf_ws_deque_2_name.
    Proof.
      solve_countable.
    Qed.

    #[local] Definition model₁' γ_model vs :=
      auth_twins_twin1 _ γ_model vs.
    #[local] Definition model₁ γ :=
      model₁' γ.(inf_ws_deque_2_name_model).
    #[local] Definition model₂' γ_model vs :=
      auth_twins_twin2 _ γ_model vs.
    #[local] Definition model₂ γ :=
      model₂' γ.(inf_ws_deque_2_name_model).

    #[local] Definition owner' γ_owner ws :=
      auth_twins_auth _ γ_owner ws.
    #[local] Definition owner γ :=
      owner' γ.(inf_ws_deque_2_name_model).

    #[local] Definition inv_inner γ : iProp Σ :=
      ∃ vs slots,
      inf_ws_deque_1_model γ.(inf_ws_deque_2_name_base) (#@{location} <$> slots) ∗
      model₂ γ vs ∗
      [∗ list] slot; v ∈ slots; vs, slot ↦ᵣ v.
    #[local] Instance : CustomIpat "inv_inner" :=
      " ( %vs{} &
          %slots{} &
          >Hbase_model &
          >Hmodel₂ &
          >Hslots
        )
      ".
    Definition inf_ws_deque_2_inv t γ ι : iProp Σ :=
      inf_ws_deque_1_inv t γ.(inf_ws_deque_2_name_base) (ι.@"base") ∗
      inv (ι.@"inv") (inv_inner γ).
    #[local] Instance : CustomIpat "inv" :=
      " ( #Hbase_inv &
          #Hinv
        )
      ".

    Definition inf_ws_deque_2_model :=
      model₁.
    #[local] Instance : CustomIpat "model" :=
      " Hmodel₁{_{}}
      ".

    Definition inf_ws_deque_2_owner γ ws : iProp Σ :=
      ∃ slots_owner,
      inf_ws_deque_1_owner γ.(inf_ws_deque_2_name_base) (#@{location} <$> slots_owner) ∗
      owner γ ws.
    #[local] Instance : CustomIpat "owner" :=
      " ( %slots_owner{_{}} &
          Hbase_owner{_{}} &
          Howner{_{}}
        )
      ".

    #[global] Instance inf_ws_deque_2_model_timeless γ vs :
      Timeless (inf_ws_deque_2_model γ vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance inf_ws_deque_2_owner_timeless γ ws :
      Timeless (inf_ws_deque_2_owner γ ws).
    Proof.
      apply _.
    Qed.

    #[global] Instance inf_ws_deque_2_inv_persistent t γ ι :
      Persistent (inf_ws_deque_2_inv t γ ι).
    Proof.
      apply _.
    Qed.

    #[local] Lemma model_owner_alloc :
      ⊢ |==>
        ∃ γ_model,
        model₁' γ_model [] ∗
        model₂' γ_model [] ∗
        owner' γ_model [].
    Proof.
      iMod (auth_twins_alloc (auth_twins_G := inf_ws_deque_2_G_model_G) _ []) as "(%γ_model & $ & $ & $)".
      iSteps.
    Qed.
    #[local] Lemma model₁_valid γ ws vs :
      owner γ ws -∗
      model₁ γ vs -∗
      ⌜vs `suffix_of` ws⌝.
    Proof.
      rewrite -preorder_rtc.
      apply: auth_twins_valid_1.
    Qed.
    #[local] Lemma model₁_exclusive γ vs1 vs2 :
      model₁ γ vs1 -∗
      model₁ γ vs2 -∗
      False.
    Proof.
      apply auth_twins_twin1_exclusive.
    Qed.
    #[local] Lemma model₂_valid γ ws vs :
      owner γ ws -∗
      model₂ γ vs -∗
      ⌜vs `suffix_of` ws⌝.
    Proof.
      rewrite -preorder_rtc.
      apply: auth_twins_valid_2.
    Qed.
    #[local] Lemma model_agree γ vs1 vs2 :
      model₁ γ vs1 -∗
      model₂ γ vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      apply: auth_twins_agree_L.
    Qed.
    #[local] Lemma model_owner_agree γ ws vs1 vs2 :
      owner γ ws -∗
      model₁ γ vs1 -∗
      model₂ γ vs2 -∗
        ⌜vs1 `suffix_of` ws⌝ ∗
        ⌜vs1 = vs2⌝.
    Proof.
      iIntros "Howner₁ Hmodel₁ Hmodel₂".
      iDestruct (model₁_valid with "Howner₁ Hmodel₁") as %Hsuffix.
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      iSteps.
    Qed.
    #[local] Lemma model_empty {γ ws vs1 vs2} :
      owner γ ws -∗
      model₁ γ vs1 -∗
      model₂ γ vs2 ==∗
        owner γ [] ∗
        model₁ γ [] ∗
        model₂ γ [].
    Proof.
      apply auth_twins_update_auth.
    Qed.
    #[local] Lemma model_push {γ ws vs1 vs2} v :
      owner γ ws -∗
      model₁ γ vs1 -∗
      model₂ γ vs2 ==∗
        owner γ (vs1 ++ [v]) ∗
        model₁ γ (vs1 ++ [v]) ∗
        model₂ γ (vs1 ++ [v]).
    Proof.
      apply auth_twins_update_auth.
    Qed.
    #[local] Lemma model_steal γ vs1 vs2 :
      model₁ γ vs1 -∗
      model₂ γ vs2 ==∗
        model₁ γ (tail vs1) ∗
        model₂ γ (tail vs1).
    Proof.
      apply: auth_twins_update_twins_L.
      rewrite preorder_rtc. apply suffix_tail. done.
    Qed.
    #[local] Lemma model_pop γ ws vs1 vs2 :
      owner γ ws -∗
      model₁ γ vs1 -∗
      model₂ γ vs2 ==∗
        owner γ (removelast vs1) ∗
        model₁ γ (removelast vs1) ∗
        model₂ γ (removelast vs1).
    Proof.
      apply auth_twins_update_auth.
    Qed.

    #[local] Lemma owner_update γ ws vs :
      owner γ ws -∗
      model₁ γ vs -∗
      model₂ γ vs ==∗
        owner γ vs ∗
        model₁ γ vs ∗
        model₂ γ vs.
    Proof.
      apply auth_twins_update_auth.
    Qed.
    #[local] Lemma owner_exclusive γ ws1 ws2 :
      owner γ ws1 -∗
      owner γ ws2 -∗
      False.
    Proof.
      apply: auth_twins_auth_exclusive.
    Qed.

    Lemma inf_ws_deque_2_model_exclusive γ vs1 vs2 :
      inf_ws_deque_2_model γ vs1 -∗
      inf_ws_deque_2_model γ vs2 -∗
      False.
    Proof.
      iIntros "(:model =1) (:model =2)".
      iApply (model₁_exclusive with "Hmodel₁_1 Hmodel₁_2").
    Qed.

    Lemma inf_ws_deque_2_owner_exclusive γ ws1 ws2 :
      inf_ws_deque_2_owner γ ws1 -∗
      inf_ws_deque_2_owner γ ws2 -∗
      False.
    Proof.
      iIntros "(:owner =1) (:owner =2)".
      iApply (owner_exclusive with "Howner_1 Howner_2").
    Qed.
    Lemma inf_ws_deque_2_owner_model γ ws vs :
      inf_ws_deque_2_owner γ ws -∗
      inf_ws_deque_2_model γ vs -∗
      ⌜vs `suffix_of` ws⌝.
    Proof.
      iIntros "(:owner =1) (:model =2)".
      iApply (model₁_valid with "Howner_1 Hmodel₁_2").
    Qed.

    Lemma inf_ws_deque_2_create_spec ι :
      {{{
        True
      }}}
        inf_ws_deque_2_create ()
      {{{ t γ,
        RET #t;
        meta_token t ⊤ ∗
        inf_ws_deque_2_inv t γ ι ∗
        inf_ws_deque_2_model γ [] ∗
        inf_ws_deque_2_owner γ []
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      iApply wp_fupd.
      wp_apply (inf_ws_deque_1_create_spec with "[//]") as (t γ_base) "(Hmeta & #Hbase_inv & Hbase_model & Hbase_owner)".

      iMod model_owner_alloc as "(%γ_model & Hmodel₁ & Hmodel₂ & Howner)".

      pose γ := {|
        inf_ws_deque_2_name_base := γ_base ;
        inf_ws_deque_2_name_model := γ_model ;
      |}.

      iApply ("HΦ" $! t γ).
      iFrame "#∗". iSplitR "Hbase_owner".
      - iApply inv_alloc.
        iExists [], []. iFrameSteps.
      - iExists []. iFrameSteps.
    Qed.

    Lemma inf_ws_deque_2_size_spec t γ ι ws :
      <<<
        inf_ws_deque_2_inv t γ ι ∗
        inf_ws_deque_2_owner γ ws
      | ∀∀ vs,
        inf_ws_deque_2_model γ vs
      >>>
        inf_ws_deque_2_size #t @ ↑ι
      <<<
        ⌜vs `suffix_of` ws⌝ ∗
        inf_ws_deque_2_model γ vs
      | RET #(length vs);
        inf_ws_deque_2_owner γ vs
      >>>.
    Proof.
      iIntros "%Φ ((:inv) & (:owner)) HΦ".

      awp_apply (inf_ws_deque_1_size_spec with "[$]").
      iInv "Hinv" as "(:inv_inner)".
      iApply (aacc_aupd_commit with "HΦ"). 1: solve_ndisj. iIntros "%vs_ (:model)".
      iAaccIntro with "Hbase_model". 1: iSteps.
      iDestruct (model_owner_agree with "Howner Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
      iMod (owner_update with "Howner Hmodel₁ Hmodel₂") as "(Howner & $ & Hmodel₂)".
      rewrite length_fmap.
      iDestruct (big_sepL2_length with "Hslots") as %->.
      iSteps.
    Qed.

    Lemma inf_ws_deque_2_is_empty_spec t γ ι ws :
      <<<
        inf_ws_deque_2_inv t γ ι ∗
        inf_ws_deque_2_owner γ ws
      | ∀∀ vs,
        inf_ws_deque_2_model γ vs
      >>>
        inf_ws_deque_2_is_empty #t @ ↑ι
      <<<
        ⌜vs `suffix_of` ws⌝ ∗
        inf_ws_deque_2_model γ vs
      | RET #(bool_decide (vs = []%list));
        inf_ws_deque_2_owner γ vs
      >>>.
    Proof.
      iIntros "%Φ ((:inv) & (:owner)) HΦ".

      awp_apply (inf_ws_deque_1_is_empty_spec with "[$]").
      iInv "Hinv" as "(:inv_inner)".
      iApply (aacc_aupd_commit with "HΦ"). 1: solve_ndisj. iIntros "%vs_ (:model)".
      iAaccIntro with "Hbase_model". 1: iSteps.
      iDestruct (model_owner_agree with "Howner Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
      iMod (owner_update with "Howner Hmodel₁ Hmodel₂") as "(Howner & $ & Hmodel₂)".
      erewrite (bool_decide_ext (_ <$> _ = []) (length _ = 0)). 2: rewrite length_zero_iff_nil //.
      rewrite length_fmap.
      iDestruct (big_sepL2_length with "Hslots") as %->.
      erewrite (bool_decide_ext (length _ = 0)). 2: apply length_zero_iff_nil.
      iSteps.
    Qed.

    Lemma inf_ws_deque_2_push_spec t γ ι ws v :
      <<<
        inf_ws_deque_2_inv t γ ι ∗
        inf_ws_deque_2_owner γ ws
      | ∀∀ vs,
        inf_ws_deque_2_model γ vs
      >>>
        inf_ws_deque_2_push #t v @ ↑ι
      <<<
        ⌜vs `suffix_of` ws⌝ ∗
        inf_ws_deque_2_model γ (vs ++ [v])
      | RET ();
        inf_ws_deque_2_owner γ (vs ++ [v])
      >>>.
    Proof.
      iIntros "%Φ ((:inv) & (:owner)) HΦ".

      wp_rec.
      wp_ref slot as "Hslot".

      awp_apply (inf_ws_deque_1_push_spec with "[$]").
      iInv "Hinv" as "(:inv_inner)".
      iApply (aacc_aupd_commit with "HΦ"). 1: solve_ndisj. iIntros "%vs_ (:model)".
      iAaccIntro with "Hbase_model". 1: iSteps.
      iDestruct (model_owner_agree with "Howner Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
      iMod (model_push with "Howner Hmodel₁ Hmodel₂") as "(Howner & $ & Hmodel₂)".
      iDestruct (big_sepL2_snoc_2 with "Hslots Hslot") as "Hslots".
      rewrite -fmap_snoc. iSteps.
    Qed.

    Lemma inf_ws_deque_2_steal_spec t γ ι :
      <<<
        inf_ws_deque_2_inv t γ ι
      | ∀∀ vs,
        inf_ws_deque_2_model γ vs
      >>>
        inf_ws_deque_2_steal #t @ ↑ι
      <<<
        inf_ws_deque_2_model γ (tail vs)
      | RET head vs;
        True
      >>>.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      wp_rec.

      awp_apply (inf_ws_deque_1_steal_spec with "[$]").
      iInv "Hinv" as "(:inv_inner)".
      iApply (aacc_aupd_commit with "HΦ"). 1: solve_ndisj. iIntros "%vs_ (:model)".
      iAaccIntro with "Hbase_model". 1: iSteps. iIntros "Hbase_model".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod (model_steal with "Hmodel₁ Hmodel₂") as "($ & Hmodel₂)".
      iIntros "!> HΦ !>".
      destruct slots as [| slot slots], vs as [| v vs] => //.
      all: iFrameSteps.
    Qed.

    Lemma inf_ws_deque_2_pop_spec t γ ι ws :
      <<<
        inf_ws_deque_2_inv t γ ι ∗
        inf_ws_deque_2_owner γ ws
      | ∀∀ vs,
        inf_ws_deque_2_model γ vs
      >>>
        inf_ws_deque_2_pop #t @ ↑ι
      <<<
        ∃∃ o ws',
        ⌜vs `suffix_of` ws⌝ ∗
        match o with
        | None =>
            ⌜vs = []⌝ ∗
            ⌜ws' = []⌝ ∗
            inf_ws_deque_2_model γ []
        | Some v =>
            ∃ vs',
            ⌜vs = vs' ++ [v]⌝ ∗
            ⌜ws' = vs'⌝ ∗
            inf_ws_deque_2_model γ vs'
        end
      | RET o;
        inf_ws_deque_2_owner γ ws'
      >>>.
    Proof.
      iIntros "%Φ ((:inv) & (:owner)) HΦ".

      wp_rec.

      awp_smart_apply (inf_ws_deque_1_pop_spec with "[$]").
      iInv "Hinv" as "(:inv_inner)".
      iApply (aacc_aupd_commit with "HΦ"). 1: solve_ndisj. iIntros "%vs_ (:model)".
      iAaccIntro with "Hbase_model". 1: iSteps. iIntros "%o %𝑠𝑙𝑜𝑡s_owner (_ & Ho)".
      iDestruct (model_owner_agree with "Howner Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
      iMod (model_pop with "Howner Hmodel₁ Hmodel₂") as "(Howner & Hmodel₁ & Hmodel₂)".
      destruct o as [𝑠𝑙𝑜𝑡 |].

      - iDestruct "Ho" as "(%𝑠𝑙𝑜𝑡s' & %Hslots & -> & Hbase_model)".
        apply fmap_snoc_inv in Hslots as (slots' & slot & -> & -> & ->).
        iDestruct (big_sepL2_snoc_inv_l with "Hslots") as "(%vs' & %v & -> & Hslots & Hslot)".
        rewrite removelast_last.
        iExists (Some v), vs'. iFrameSteps.

      - iDestruct "Ho" as "(%Hslots & -> & Hbase_model)".
        apply fmap_nil_inv in Hslots as ->.
        iDestruct (big_sepL2_nil_inv_l with "Hslots") as %->.
        iExists None. iFrameSteps. do 2 (iExists []; iSteps).
    Qed.
  End inf_ws_deque_2_G.

  #[global] Opaque inf_ws_deque_2_inv.
  #[global] Opaque inf_ws_deque_2_model.
  #[global] Opaque inf_ws_deque_2_owner.
End base.

From zoo_saturn Require
  inf_ws_deque_2__opaque.

Section inf_ws_deque_2_G.
  Context `{inf_ws_deque_2_G : InfWsDeque2G Σ}.

  Implicit Types 𝑡 : location.
  Implicit Types t : val.

  Definition inf_ws_deque_2_inv t ι : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.inf_ws_deque_2_inv 𝑡 γ ι.
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡{} &
        %γ{} &
        {%Heq{};->} &
        #Hmeta{_{}} &
        Hinv{_{}}
      )
    ".

  Definition inf_ws_deque_2_model t vs : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.inf_ws_deque_2_model γ vs.
  #[local] Instance : CustomIpat "model" :=
    " ( %𝑡{} &
        %γ{} &
        {%Heq{};->} &
        #Hmeta{_{}} &
        Hmodel{_{}}
      )
    ".

  Definition inf_ws_deque_2_owner t ws : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.inf_ws_deque_2_owner γ ws.
  #[local] Instance : CustomIpat "owner" :=
    " ( %𝑡{} &
        %γ{} &
        {%Heq{};->} &
        #Hmeta{_{}} &
        Howner{_{}}
      )
    ".

  #[global] Instance inf_ws_deque_2_model_timeless γ vs :
    Timeless (inf_ws_deque_2_model γ vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance inf_ws_deque_2_owner_timeless γ ws :
    Timeless (inf_ws_deque_2_owner γ ws).
  Proof.
    apply _.
  Qed.

  #[global] Instance inf_ws_deque_2_inv_persistent t ι :
    Persistent (inf_ws_deque_2_inv t ι).
  Proof.
    apply _.
  Qed.

  Lemma inf_ws_deque_2_model_exclusive t vs1 vs2 :
    inf_ws_deque_2_model t vs1 -∗
    inf_ws_deque_2_model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.inf_ws_deque_2_model_exclusive with "Hmodel_1 Hmodel_2").
  Qed.

  Lemma inf_ws_deque_2_owner_exclusive t ws1 ws2 :
    inf_ws_deque_2_owner t ws1 -∗
    inf_ws_deque_2_owner t ws2 -∗
    False.
  Proof.
    iIntros "(:owner =1) (:owner =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.inf_ws_deque_2_owner_exclusive with "Howner_1 Howner_2").
  Qed.
  Lemma inf_ws_deque_2_owner_model γ ws vs :
    inf_ws_deque_2_owner γ ws -∗
    inf_ws_deque_2_model γ vs -∗
    ⌜vs `suffix_of` ws⌝.
  Proof.
    iIntros "(:owner =1) (:model =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.inf_ws_deque_2_owner_model with "Howner_1 Hmodel_2").
  Qed.

  Lemma inf_ws_deque_2_create_spec ι :
    {{{
      True
    }}}
      inf_ws_deque_2_create ()
    {{{ t,
      RET t;
      inf_ws_deque_2_inv t ι ∗
      inf_ws_deque_2_model t [] ∗
      inf_ws_deque_2_owner t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    iApply wp_fupd.
    wp_apply (base.inf_ws_deque_2_create_spec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hmodel)".
    iMod (meta_set γ with "Hmeta"); first done.
    iSteps.
  Qed.

  Lemma inf_ws_deque_2_size_spec t ι ws :
    <<<
      inf_ws_deque_2_inv t ι ∗
      inf_ws_deque_2_owner t ws
    | ∀∀ vs,
      inf_ws_deque_2_model t vs
    >>>
      inf_ws_deque_2_size t @ ↑ι
    <<<
      ⌜vs `suffix_of` ws⌝ ∗
      inf_ws_deque_2_model t vs
    | RET #(length vs);
      inf_ws_deque_2_owner t vs
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:owner =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp_apply (base.inf_ws_deque_2_size_spec with "[$]").
    { iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma inf_ws_deque_2_is_empty_spec t ι ws :
    <<<
      inf_ws_deque_2_inv t ι ∗
      inf_ws_deque_2_owner t ws
    | ∀∀ vs,
      inf_ws_deque_2_model t vs
    >>>
      inf_ws_deque_2_is_empty t @ ↑ι
    <<<
      ⌜vs `suffix_of` ws⌝ ∗
      inf_ws_deque_2_model t vs
    | RET #(bool_decide (vs = []%list));
      inf_ws_deque_2_owner t vs
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:owner =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp_apply (base.inf_ws_deque_2_is_empty_spec with "[$]").
    { iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma inf_ws_deque_2_push_spec t ι ws v :
    <<<
      inf_ws_deque_2_inv t ι ∗
      inf_ws_deque_2_owner t ws
    | ∀∀ vs,
      inf_ws_deque_2_model t vs
    >>>
      inf_ws_deque_2_push t v @ ↑ι
    <<<
      ⌜vs `suffix_of` ws⌝ ∗
      inf_ws_deque_2_model t (vs ++ [v])
    | RET ();
      inf_ws_deque_2_owner t (vs ++ [v])
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:owner =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp_apply (base.inf_ws_deque_2_push_spec with "[$]").
    { iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma inf_ws_deque_2_steal_spec t ι :
    <<<
      inf_ws_deque_2_inv t ι
    | ∀∀ vs,
      inf_ws_deque_2_model t vs
    >>>
      inf_ws_deque_2_steal t @ ↑ι
    <<<
      inf_ws_deque_2_model t (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp_apply (base.inf_ws_deque_2_steal_spec with "[$]").
    { iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta_agree with "Hmeta Hmeta_1") as %->. iClear "Hmeta".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma inf_ws_deque_2_pop_spec t ι ws :
    <<<
      inf_ws_deque_2_inv t ι ∗
      inf_ws_deque_2_owner t ws
    | ∀∀ vs,
      inf_ws_deque_2_model t vs
    >>>
      inf_ws_deque_2_pop t @ ↑ι
    <<<
      ∃∃ o ws',
      ⌜vs `suffix_of` ws⌝ ∗
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          ⌜ws' = []⌝ ∗
          inf_ws_deque_2_model t []
      | Some v =>
          ∃ vs',
          ⌜vs = vs' ++ [v]⌝ ∗
          ⌜ws' = vs'⌝ ∗
          inf_ws_deque_2_model t vs'
      end
    | RET o;
      inf_ws_deque_2_owner t ws'
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:owner =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp_apply (base.inf_ws_deque_2_pop_spec with "[$]").
    { iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
      iAaccIntro with "Hmodel_1". 1: iSteps. iIntros "%o %ws' ($ & Ho)".
      iExists o, ws'. destruct o.
      all: iDecompose "Ho".
      all: iFrameSteps.
    }
  Qed.
End inf_ws_deque_2_G.

#[global] Opaque inf_ws_deque_2_inv.
#[global] Opaque inf_ws_deque_2_model.
#[global] Opaque inf_ws_deque_2_owner.
