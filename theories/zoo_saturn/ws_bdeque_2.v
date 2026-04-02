From zoo Require Import
  prelude.
From zoo.common Require Import
  countable
  relations.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Import
  lib.auth_twins.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  option.
From zoo_saturn Require Export
  base
  ws_bdeque_2__code.
From zoo_saturn Require Import
  ws_bdeque_1.
From zoo Require Import
  options.

Import ws_bdeque_1.base.

Implicit Types b : bool.
Implicit Types slot : location.
Implicit Types slots : list location.
Implicit Types v : val.
Implicit Types vs ws : list val.

Class WsBdeque2G Σ `{zoo_G : !ZooG Σ} :=
  { #[local] ws_bdeque_2_G_base_G :: WsBdeque1G Σ
  ; #[local] ws_bdeque_2_G_model_G :: AuthTwinsG Σ (leibnizO (list val)) suffix
  }.

Definition ws_bdeque_2_Σ := #[
  ws_bdeque_1_Σ ;
  auth_twins_Σ (leibnizO (list val)) suffix
].
#[global] Instance subG_ws_bdeque_2_Σ Σ `{zoo_G : !ZooG Σ} :
  subG ws_bdeque_2_Σ Σ →
  WsBdeque2G Σ .
Proof.
  solve_inG.
Qed.

Module base.
  Section ws_bdeque_2_G.
    Context `{ws_bdeque_2_G : WsBdeque2G Σ}.

    Implicit Types t : location.

    Record ws_bdeque_2_name :=
      { ws_bdeque_2_name_capacity : nat
      ; ws_bdeque_2_name_base : ws_bdeque_1_name
      ; ws_bdeque_2_name_model : auth_twins_name
      }.
    Implicit Type γ : ws_bdeque_2_name.

    #[global] Instance ws_bdeque_2_name_eq_dec : EqDecision ws_bdeque_2_name :=
      ltac:(solve_decision).
    #[global] Instance ws_bdeque_2_name_countable :
      Countable ws_bdeque_2_name.
    Proof.
      solve_countable.
    Qed.

    #[local] Definition model₁' γ_model vs :=
      auth_twins_twin1 _ γ_model vs.
    #[local] Definition model₁ γ :=
      model₁' γ.(ws_bdeque_2_name_model).
    #[local] Definition model₂' γ_model vs :=
      auth_twins_twin2 _ γ_model vs.
    #[local] Definition model₂ γ :=
      model₂' γ.(ws_bdeque_2_name_model).

    #[local] Definition owner' γ_owner ws :=
      auth_twins_auth _ γ_owner ws.
    #[local] Definition owner γ :=
      owner' γ.(ws_bdeque_2_name_model).

    #[local] Definition inv_inner γ : iProp Σ :=
      ∃ vs slots,
      ws_bdeque_1_model γ.(ws_bdeque_2_name_base) (#*@{location} slots) ∗
      model₂ γ vs ∗
      [∗ list] slot; v ∈ slots; vs, slot ↦ᵣ v.
    #[local] Instance : CustomIpat "inv_inner" :=
      " ( %vs{}
        & %slots{}
        & >Hbase_model
        & >Hmodel₂
        & >Hslots
        )
      ".
    Definition ws_bdeque_2_inv t γ ι cap : iProp Σ :=
      ⌜cap = γ.(ws_bdeque_2_name_capacity)⌝ ∗
      ws_bdeque_1_inv t γ.(ws_bdeque_2_name_base) (ι.@"base") cap ∗
      inv (ι.@"inv") (inv_inner γ).
    #[local] Instance : CustomIpat "inv" :=
      " ( ->
        & #Hbase_inv
        & #Hinv
        )
      ".

    Definition ws_bdeque_2_model γ vs : iProp Σ :=
      model₁ γ vs ∗
      ⌜length vs ≤ γ.(ws_bdeque_2_name_capacity)⌝.
    #[local] Instance : CustomIpat "model" :=
      " ( Hmodel₁{_{}}
        & %Hvs{}
        )
      ".

    Definition ws_bdeque_2_owner t γ ws : iProp Σ :=
      ∃ slots_owner,
      ws_bdeque_1_owner t γ.(ws_bdeque_2_name_base) (#*@{location} slots_owner) ∗
      owner γ ws.
    #[local] Instance : CustomIpat "owner" :=
      " ( %slots_owner{_{}}
        & Hbase_owner{_{}}
        & Howner{_{}}
        )
      ".

    #[global] Instance ws_bdeque_2_model_timeless γ vs :
      Timeless (ws_bdeque_2_model γ vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance ws_bdeque_2_owner_timeless t γ ws :
      Timeless (ws_bdeque_2_owner t γ ws).
    Proof.
      apply _.
    Qed.

    #[global] Instance ws_bdeque_2_inv_persistent t γ ι cap :
      Persistent (ws_bdeque_2_inv t γ ι cap).
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
      iMod (auth_twins_alloc (auth_twins_G := ws_bdeque_2_G_model_G) _ []) as "(%γ_model & $ & $ & $)".
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

    Lemma ws_bdeque_2_model_valid t γ ι cap vs :
      ws_bdeque_2_inv t γ ι cap -∗
      ws_bdeque_2_model γ vs -∗
      ⌜length vs ≤ cap⌝.
    Proof.
      iSteps.
    Qed.
    Lemma ws_bdeque_2_model_exclusive γ vs1 vs2 :
      ws_bdeque_2_model γ vs1 -∗
      ws_bdeque_2_model γ vs2 -∗
      False.
    Proof.
      iIntros "(:model =1) (:model =2)".
      iApply (model₁_exclusive with "Hmodel₁_1 Hmodel₁_2").
    Qed.

    Lemma ws_bdeque_2_owner_exclusive t γ ws1 ws2 :
      ws_bdeque_2_owner t γ ws1 -∗
      ws_bdeque_2_owner t γ ws2 -∗
      False.
    Proof.
      iIntros "(:owner =1) (:owner =2)".
      iApply (owner_exclusive with "Howner_1 Howner_2").
    Qed.
    Lemma ws_bdeque_2_owner_model t γ ws vs :
      ws_bdeque_2_owner t γ ws -∗
      ws_bdeque_2_model γ vs -∗
      ⌜vs `suffix_of` ws⌝.
    Proof.
      iIntros "(:owner =1) (:model =2)".
      iApply (model₁_valid with "Howner_1 Hmodel₁_2").
    Qed.

    Lemma ws_bdeque_2_create_spec ι (cap : Z) :
      (0 < cap)%Z →
      {{{
        True
      }}}
        ws_bdeque_2_create #cap
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        ws_bdeque_2_inv t γ ι ₊cap ∗
        ws_bdeque_2_model γ [] ∗
        ws_bdeque_2_owner t γ []
      }}}.
    Proof.
      iIntros "%Hcap %Φ _ HΦ".

      iApply wp_fupd.
      wp_apply (ws_bdeque_1_create_spec with "[//]") as (t γ_base) "(Hmeta & #Hbase_inv & Hbase_model & Hbase_owner)". 1: done.

      iMod model_owner_alloc as "(%γ_model & Hmodel₁ & Hmodel₂ & Howner)".

      pose γ := {|
        ws_bdeque_2_name_capacity := ₊cap ;
        ws_bdeque_2_name_base := γ_base ;
        ws_bdeque_2_name_model := γ_model ;
      |}.

      iApply ("HΦ" $! t γ).
      iFrame "#∗". iSplitR "Hbase_owner"; iStep.
      - iApply inv_alloc.
        iExists [], []. iFrameSteps.
      - iExists []. iFrameSteps.
    Qed.

    Lemma ws_bdeque_2_size_spec t γ ι cap ws :
      <<<
        ws_bdeque_2_inv t γ ι cap ∗
        ws_bdeque_2_owner t γ ws
      | ∀∀ vs,
        ws_bdeque_2_model γ vs
      >>>
        ws_bdeque_2_size #t @ ↑ι
      <<<
        ⌜vs `suffix_of` ws⌝ ∗
        ws_bdeque_2_model γ vs
      | RET #(length vs);
        ws_bdeque_2_owner t γ vs
      >>>.
    Proof.
      iIntros "%Φ ((:inv) & (:owner)) HΦ".

      awp_apply (ws_bdeque_1_size_spec with "[$]").
      iInv "Hinv" as "(:inv_inner)".
      iApply (aacc_aupd_commit with "HΦ"). 1: solve_ndisj. iIntros "%vs_ (:model)".
      iAaccIntro with "Hbase_model". 1: iSteps.
      iDestruct (model_owner_agree with "Howner Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
      iMod (owner_update with "Howner Hmodel₁ Hmodel₂") as "(Howner & $ & Hmodel₂)".
      rewrite length_fmap.
      iDestruct (big_sepL2_length with "Hslots") as %->.
      iSteps.
    Qed.

    Lemma ws_bdeque_2_is_empty_spec t γ ι cap ws :
      <<<
        ws_bdeque_2_inv t γ ι cap ∗
        ws_bdeque_2_owner t γ ws
      | ∀∀ vs,
        ws_bdeque_2_model γ vs
      >>>
        ws_bdeque_2_is_empty #t @ ↑ι
      <<<
        ⌜vs `suffix_of` ws⌝ ∗
        ws_bdeque_2_model γ vs
      | RET #(bool_decide (vs = []%list));
        ws_bdeque_2_owner t γ vs
      >>>.
    Proof.
      iIntros "%Φ ((:inv) & (:owner)) HΦ".

      awp_apply (ws_bdeque_1_is_empty_spec with "[$]").
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

    Lemma ws_bdeque_2_push_spec t γ ι cap ws v :
      <<<
        ws_bdeque_2_inv t γ ι cap ∗
        ws_bdeque_2_owner t γ ws
      | ∀∀ vs,
        ws_bdeque_2_model γ vs
      >>>
        ws_bdeque_2_push #t v @ ↑ι
      <<<
        ∃∃ b,
        ⌜b = bool_decide (length vs < cap)⌝ ∗
        ⌜vs `suffix_of` ws⌝ ∗
        ws_bdeque_2_model γ (if b then vs ++ [v] else vs)
      | RET #b;
        ws_bdeque_2_owner t γ (if b then vs ++ [v] else ws)
      >>>.
    Proof.
      iIntros "%Φ ((:inv) & (:owner)) HΦ".

      wp_rec.
      wp_ref slot as "Hslot".

      awp_apply (ws_bdeque_1_push_spec with "[$]").
      iInv "Hinv" as "(:inv_inner)".
      iDestruct (big_sepL2_length with "Hslots") as %Hlength.
      iApply (aacc_aupd_commit with "HΦ"). 1: solve_ndisj. iIntros "%vs_ (:model)".
      iAaccIntro with "Hbase_model". 1: iSteps. iIntros "%b (-> & _ & Hbase_model)".
      iDestruct (model_owner_agree with "Howner Hmodel₁ Hmodel₂") as %(Hsuffix & ->).
      iEval (simpl_length) in "Hbase_model" |- *.
      case_bool_decide.

      - iExists true.
        iMod (model_push with "Howner Hmodel₁ Hmodel₂") as "(Howner & $ & Hmodel₂)".
        iDestruct (big_sepL2_snoc_2 with "Hslots Hslot") as "Hslots".
        rewrite -fmap_snoc. iSteps; iPureIntro.
        { rewrite bool_decide_eq_true_2 //. 1: lia. }
        { simpl_length/=. lia. }

      - iExists false. iFrameSteps. iPureIntro.
        rewrite bool_decide_eq_false_2 //. 1: lia.
    Qed.

    Lemma ws_bdeque_2_steal_spec t γ ι cap :
      <<<
        ws_bdeque_2_inv t γ ι cap
      | ∀∀ vs,
        ws_bdeque_2_model γ vs
      >>>
        ws_bdeque_2_steal #t @ ↑ι
      <<<
        ws_bdeque_2_model γ (tail vs)
      | RET head vs;
        True
      >>>.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      wp_rec.

      awp_apply (ws_bdeque_1_steal_spec with "[$]").
      iInv "Hinv" as "(:inv_inner)".
      iApply (aacc_aupd_commit with "HΦ"). 1: solve_ndisj. iIntros "%vs_ (:model)".
      iAaccIntro with "Hbase_model". 1: iSteps. iIntros "Hbase_model".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod (model_steal with "Hmodel₁ Hmodel₂") as "($ & Hmodel₂)".
      iSplitR.
      { iPureIntro. etrans. 2: done. apply length_tail. }
      iIntros "!> HΦ !>".
      destruct slots as [| slot slots], vs as [| v vs] => //.
      all: iFrameSteps.
    Qed.

    Lemma ws_bdeque_2_pop_spec t γ ι cap ws :
      <<<
        ws_bdeque_2_inv t γ ι cap ∗
        ws_bdeque_2_owner t γ ws
      | ∀∀ vs,
        ws_bdeque_2_model γ vs
      >>>
        ws_bdeque_2_pop #t @ ↑ι
      <<<
        ∃∃ o ws',
        ⌜vs `suffix_of` ws⌝ ∗
        match o with
        | None =>
            ⌜vs = []⌝ ∗
            ⌜ws' = []⌝ ∗
            ws_bdeque_2_model γ []
        | Some v =>
            ∃ vs',
            ⌜vs = vs' ++ [v]⌝ ∗
            ⌜ws' = vs'⌝ ∗
            ws_bdeque_2_model γ vs'
        end
      | RET o;
        ws_bdeque_2_owner t γ ws'
      >>>.
    Proof.
      iIntros "%Φ ((:inv) & (:owner)) HΦ".

      wp_rec.

      awp_apply+ (ws_bdeque_1_pop_spec with "[$]").
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
        iExists (Some v), vs'. iFrameSteps. iPureIntro.
        etrans. 2: done. simpl_length. lia.

      - iDestruct "Ho" as "(%Hslots & -> & Hbase_model)".
        apply fmap_nil_inv in Hslots as ->.
        iDestruct (big_sepL2_nil_inv_l with "Hslots") as %->.
        iExists None. iFrameSteps. do 2 (iExists []; iSteps).
    Qed.
  End ws_bdeque_2_G.

  #[global] Opaque ws_bdeque_2_inv.
  #[global] Opaque ws_bdeque_2_model.
  #[global] Opaque ws_bdeque_2_owner.
End base.

From zoo_saturn Require
  ws_bdeque_2__opaque.

Section ws_bdeque_2_G.
  Context `{ws_bdeque_2_G : WsBdeque2G Σ}.

  Implicit Types 𝑡 : location.
  Implicit Types t : val.

  Definition ws_bdeque_2_inv t ι cap : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.ws_bdeque_2_inv 𝑡 γ ι cap.
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hinv{_{}}
      )
    ".

  Definition ws_bdeque_2_model t vs : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.ws_bdeque_2_model γ vs.
  #[local] Instance : CustomIpat "model" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hmodel{_{}}
      )
    ".

  Definition ws_bdeque_2_owner t ws : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.ws_bdeque_2_owner 𝑡 γ ws.
  #[local] Instance : CustomIpat "owner" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Howner{_{}}
      )
    ".

  #[global] Instance ws_bdeque_2_model_timeless γ vs :
    Timeless (ws_bdeque_2_model γ vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance ws_bdeque_2_owner_timeless γ ws :
    Timeless (ws_bdeque_2_owner γ ws).
  Proof.
    apply _.
  Qed.

  #[global] Instance ws_bdeque_2_inv_persistent t ι cap :
    Persistent (ws_bdeque_2_inv t ι cap).
  Proof.
    apply _.
  Qed.

  Lemma ws_bdeque_2_model_valid t ι cap vs :
    ws_bdeque_2_inv t ι cap -∗
    ws_bdeque_2_model t vs -∗
    ⌜length vs ≤ cap⌝.
  Proof.
    iIntros "(:inv =1) (:model =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ws_bdeque_2_model_valid with "Hinv_1 Hmodel_2").
  Qed.
  Lemma ws_bdeque_2_model_exclusive t vs1 vs2 :
    ws_bdeque_2_model t vs1 -∗
    ws_bdeque_2_model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ws_bdeque_2_model_exclusive with "Hmodel_1 Hmodel_2").
  Qed.

  Lemma ws_bdeque_2_owner_exclusive t ws1 ws2 :
    ws_bdeque_2_owner t ws1 -∗
    ws_bdeque_2_owner t ws2 -∗
    False.
  Proof.
    iIntros "(:owner =1) (:owner =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ws_bdeque_2_owner_exclusive with "Howner_1 Howner_2").
  Qed.
  Lemma ws_bdeque_2_owner_model γ ws vs :
    ws_bdeque_2_owner γ ws -∗
    ws_bdeque_2_model γ vs -∗
    ⌜vs `suffix_of` ws⌝.
  Proof.
    iIntros "(:owner =1) (:model =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ws_bdeque_2_owner_model with "Howner_1 Hmodel_2").
  Qed.

  Lemma ws_bdeque_2_create_spec ι (cap : Z) :
    (0 < cap)%Z →
    {{{
      True
    }}}
      ws_bdeque_2_create #cap
    {{{
      t
    , RET t;
      ws_bdeque_2_inv t ι ₊cap ∗
      ws_bdeque_2_model t [] ∗
      ws_bdeque_2_owner t []
    }}}.
  Proof.
    iIntros "%Hcap %Φ _ HΦ".

    iApply wp_fupd.
    wp_apply (base.ws_bdeque_2_create_spec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hmodel)". 1: done.
    iMod (meta_set γ with "Hmeta"); first done.
    iSteps.
  Qed.

  Lemma ws_bdeque_2_size_spec t ι cap ws :
    <<<
      ws_bdeque_2_inv t ι cap ∗
      ws_bdeque_2_owner t ws
    | ∀∀ vs,
      ws_bdeque_2_model t vs
    >>>
      ws_bdeque_2_size t @ ↑ι
    <<<
      ⌜vs `suffix_of` ws⌝ ∗
      ws_bdeque_2_model t vs
    | RET #(length vs);
      ws_bdeque_2_owner t vs
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:owner =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp_apply (base.ws_bdeque_2_size_spec with "[$]").
    { iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma ws_bdeque_2_is_empty_spec t ι cap ws :
    <<<
      ws_bdeque_2_inv t ι cap ∗
      ws_bdeque_2_owner t ws
    | ∀∀ vs,
      ws_bdeque_2_model t vs
    >>>
      ws_bdeque_2_is_empty t @ ↑ι
    <<<
      ⌜vs `suffix_of` ws⌝ ∗
      ws_bdeque_2_model t vs
    | RET #(bool_decide (vs = []%list));
      ws_bdeque_2_owner t vs
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:owner =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp_apply (base.ws_bdeque_2_is_empty_spec with "[$]").
    { iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma ws_bdeque_2_push_spec t ι cap ws v :
    <<<
      ws_bdeque_2_inv t ι cap ∗
      ws_bdeque_2_owner t ws
    | ∀∀ vs,
      ws_bdeque_2_model t vs
    >>>
      ws_bdeque_2_push t v @ ↑ι
    <<<
      ∃∃ b,
      ⌜b = bool_decide (length vs < cap)⌝ ∗
      ⌜vs `suffix_of` ws⌝ ∗
      ws_bdeque_2_model t (if b then vs ++ [v] else vs)
    | RET #b;
      ws_bdeque_2_owner t (if b then vs ++ [v] else ws)
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:owner =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp_apply (base.ws_bdeque_2_push_spec with "[$]").
    { iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma ws_bdeque_2_steal_spec t ι cap :
    <<<
      ws_bdeque_2_inv t ι cap
    | ∀∀ vs,
      ws_bdeque_2_model t vs
    >>>
      ws_bdeque_2_steal t @ ↑ι
    <<<
      ws_bdeque_2_model t (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp_apply (base.ws_bdeque_2_steal_spec with "[$]").
    { iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta_agree with "Hmeta Hmeta_1") as %->. iClear "Hmeta".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma ws_bdeque_2_pop_spec t ι cap ws :
    <<<
      ws_bdeque_2_inv t ι cap ∗
      ws_bdeque_2_owner t ws
    | ∀∀ vs,
      ws_bdeque_2_model t vs
    >>>
      ws_bdeque_2_pop t @ ↑ι
    <<<
      ∃∃ o ws',
      ⌜vs `suffix_of` ws⌝ ∗
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          ⌜ws' = []⌝ ∗
          ws_bdeque_2_model t []
      | Some v =>
          ∃ vs',
          ⌜vs = vs' ++ [v]⌝ ∗
          ⌜ws' = vs'⌝ ∗
          ws_bdeque_2_model t vs'
      end
    | RET o;
      ws_bdeque_2_owner t ws'
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:owner =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp_apply (base.ws_bdeque_2_pop_spec with "[$]").
    { iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
      iAaccIntro with "Hmodel_1". 1: iSteps. iIntros "%o %ws' ($ & Ho)".
      iExists o, ws'. destruct o.
      all: iDecompose "Ho".
      all: iFrameSteps.
    }
  Qed.
End ws_bdeque_2_G.

#[global] Opaque ws_bdeque_2_inv.
#[global] Opaque ws_bdeque_2_model.
#[global] Opaque ws_bdeque_2_owner.
