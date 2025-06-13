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
  goption
  array.
From zoo_saturn Require Export
  base
  bag_1__code.
From zoo_saturn Require Import
  bag_1__types.
From zoo Require Import
  options.

Implicit Types front back : nat.
Implicit Types l slot : location.
Implicit Types slots : list location.
Implicit Types v t : val.
Implicit Types vs : gmultiset val.
Implicit Types o : option val.
Implicit Types os : list (option val).

Class Bag1G Σ `{zoo_G : !ZooG Σ} := {
  #[local] bag_1_G_model_G :: TwinsG Σ (leibnizO (gmultiset val)) ;
}.

Definition bag_1_Σ := #[
  twins_Σ (leibnizO (gmultiset val))
].
#[global] Instance subG_bag_1_Σ Σ `{zoo_G : !ZooG Σ} :
  subG bag_1_Σ Σ →
  Bag1G Σ.
Proof.
  solve_inG.
Qed.

Section bag_1_G.
  Context `{bag_1_G : Bag1G Σ}.

  Record metadata := {
    metadata_data : val ;
    metadata_slots : list location ;
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

  #[local] Definition model₁' γ_model vs :=
    twins_twin1 γ_model (DfracOwn 1) vs.
  #[local] Definition model₁ γ vs :=
    model₁' γ.(metadata_model) vs.
  #[local] Definition model₂' γ_model vs :=
    twins_twin2 γ_model vs.
  #[local] Definition model₂ γ vs :=
    model₂' γ.(metadata_model) vs.

  #[local] Definition inv_inner l γ : iProp Σ :=
    ∃ front back os vs,
    ⌜vs = foldr (λ o vs, from_option (λ v, {[+v+]} ⊎ vs) vs o) ∅ os⌝ ∗
    l.[front] ↦ #front ∗
    l.[back] ↦ #back ∗
    model₂ γ vs ∗
    [∗ list] slot; o ∈ γ.(metadata_slots); os,
      slot ↦ᵣ (o : val).
  Definition bag_1_inv t ι : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    ⌜0 < length γ.(metadata_slots)⌝ ∗
    meta l nroot γ ∗
    l.[data] ↦□ γ.(metadata_data) ∗
    array_model γ.(metadata_data) DfracDiscarded (#@{location} <$> γ.(metadata_slots)) ∗
    inv ι (inv_inner l γ).

  Definition bag_1_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    model₁ γ vs.

  Instance bag_1_inv_timeless t vs :
    Timeless (bag_1_model t vs).
  Proof.
    apply _.
  Qed.
  Instance bag_1_inv_persistent t ι :
    Persistent (bag_1_inv t ι).
  Proof.
    apply _.
  Qed.

  #[local] Lemma model_alloc :
    ⊢ |==>
      ∃ γ_model,
      model₁' γ_model ∅ ∗
      model₂' γ_model ∅.
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

  Lemma bag_1_create_spec ι (sz : Z) :
    (0 < sz)%Z →
    {{{
      True
    }}}
      bag_1_create #sz
    {{{ t,
      RET t;
      bag_1_inv t ι ∗
      bag_1_model t ∅
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".

    wp_rec.

    pose (Ψ := λ (_ : nat) (vs : list val), (
      ∃ slots,
      ⌜vs = #@{location} <$> slots⌝ ∗
      [∗ list] slot ∈ slots,
        slot ↦ᵣ None
    )%I).
    wp_smart_apply (array_unsafe_init_spec Ψ) as "%data % (%Hslots & Hdata_model & (%slots & -> & Hslots))"; first lia.
    { iSplitL.
      - iExists []. iSteps.
      - iIntros "!> %i %vs % % (%slots & %Hslots & Hslots)".
        wp_ref slot as "Hslot".
        iExists (slots ++ [slot]). iSteps.
        + list_simplifier. done.
        + iApply big_sepL_snoc.
          iSteps.
    }
    wp_block l as "Hmeta" "(Hdata & Hfront & Hback & _)".
    iMod (array_model_persist with "Hdata_model") as "#Hdata_model".

    iMod model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".

    pose γ := {|
      metadata_data := data ;
      metadata_slots := slots ;
      metadata_model := γ_model ;
    |}.
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁"; last iSteps.
    iExists l, γ. simpl_length in Hslots. iStep 5. iApply inv_alloc.
    iExists 0, 0, (replicate ₊sz None), ∅. iSteps.
    - iPureIntro. Z_to_nat sz. clear. rewrite Nat2Z.id.
      induction sz; first done. rewrite replicate_S //.
    - iApply big_sepL2_replicate_r; first done.
      iSteps.
  Qed.

  #[local] Lemma bag_1_push_0_spec slot v ι l γ :
    slot ∈ γ.(metadata_slots) →
    <<<
      meta l nroot γ ∗
      inv ι (inv_inner l γ)
    | ∀∀ vs,
      bag_1_model #l vs
    >>>
      bag_1_push_0 #slot ’Some[ v ] @ ↑ι
    <<<
      bag_1_model #l ({[+v+]} ⊎ vs)
    | RET ();
      True
    >>>.
  Proof.
    iIntros ((i & Hslots_lookup)%elem_of_list_lookup) "%Φ (#Hmeta & #Hinv) HΦ".
    pose proof Hslots_lookup as Hi%lookup_lt_Some.

    iLöb as "HLöb".

    wp_rec. wp_pures.

    wp_bind (CAS _ _ _).
    iInv "Hinv" as "(%front & %back & %os & %vs & >%Hvs & Hfront & Hback & Hmodel₂ & Hslots)".
    iDestruct (big_sepL2_length with "Hslots") as "#>%Hlen".
    destruct (lookup_lt_is_Some_2 os i) as (o & Hos_lookup); first congruence.
    iDestruct (big_sepL2_insert_acc with "Hslots") as "(Hslot & Hslots)"; [done.. |].
    wp_cas as _ | ->%(inj goption_to_val _ None).

    - iDestruct ("Hslots" with "Hslot") as "Hslots".
      rewrite !list_insert_id //.
      iSplitR "HΦ". { iExists front, back, os, vs. iSteps. }
      iSteps.

    - iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      set vs' := {[+v+]} ⊎ vs.
      set os' := <[i := Some v]> os.
      iMod (model_update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ". { repeat iExists _. iSteps. }
      iDestruct ("Hslots" $! _ (Some v) with "Hslot") as "Hslots".
      rewrite list_insert_id //.
      iSplitR "HΦ".
      { iExists front, back, os', vs'. iSteps. iPureIntro.
        rewrite (foldr_insert_strong _ option_union _ _ None (Some v)) //.
        { intros [w |] acc; last done. set_solver by lia. }
        set_solver.
      }
      iSteps.
  Qed.
  Lemma bag_1_push_spec t ι v :
    <<<
      bag_1_inv t ι
    | ∀∀ vs,
      bag_1_model t vs
    >>>
      bag_1_push t v @ ↑ι
    <<<
      bag_1_model t ({[+v+]} ⊎ vs)
    | RET ();
      True
    >>>.
  Proof.
    iIntros "%Φ (%l & %γ & -> & %Hsz & #Hmeta & #Hdata & #Hdata_model & #Hinv) HΦ".

    wp_rec. wp_load.
    wp_smart_apply (array_size_spec with "Hdata_model") as "_".
    wp_pures.

    wp_bind (FAA _ _).
    iInv "Hinv" as "(%front & %back & %os & %vs & >%Hvs & Hfront & Hback & Hmodel₂ & Hslots)".
    wp_faa.
    iSplitR "HΦ". { iExists front, (S back), os, vs. iSteps. }
    iModIntro. clear- Hsz.

    simpl_length.
    wp_smart_apply (array_unsafe_get_spec with "Hdata_model") as "_"; [lia | | done |].
    { rewrite list_lookup_fmap list_lookup_lookup_total_lt //. lia. }
    wp_apply (bag_1_push_0_spec with "[$Hmeta $Hinv] HΦ").
    apply elem_of_list_lookup_total_2. lia.
  Qed.

  #[local] Lemma bag_1_pop_0_spec slot ι l γ :
    slot ∈ γ.(metadata_slots) →
    <<<
      meta l nroot γ ∗
      inv ι (inv_inner l γ)
    | ∀∀ vs,
      bag_1_model #l vs
    >>>
      bag_1_pop_0 #slot @ ↑ι
    <<<
      ∃∃ v vs',
      ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
      bag_1_model #l vs'
    | RET v;
      True
    >>>.
  Proof.
    iIntros ((i & Hslots_lookup)%elem_of_list_lookup) "%Φ (#Hmeta & #Hinv) HΦ".
    pose proof Hslots_lookup as Hi%lookup_lt_Some.

    iLöb as "HLöb".

    wp_rec. wp_pures.

    wp_bind (!_)%E.
    iInv "Hinv" as "(%front & %back & %os & %vs & >%Hvs & Hfront & Hback & Hmodel₂ & Hslots)".
    iDestruct (big_sepL2_length with "Hslots") as "#>%Hlen".
    destruct (lookup_lt_is_Some_2 os i) as (o & Hos_lookup); first congruence.
    iDestruct (big_sepL2_lookup_acc with "Hslots") as "(Hslot & Hslots)"; [done.. |].
    wp_load.
    iSplitR "HΦ". { iExists front, back, os, vs. iSteps. }
    iModIntro. clear- Hslots_lookup Hi.

    destruct o as [v |]; last iSteps.
    wp_pures.

    wp_bind (CAS _ _ _).
    iInv "Hinv" as "(%front & %back & %os & %vs & >%Hvs & Hfront & Hback & Hmodel₂ & Hslots)".
    iDestruct (big_sepL2_length with "Hslots") as "#>%Hlen".
    destruct (lookup_lt_is_Some_2 os i) as (o & Hos_lookup); first congruence.
    iDestruct (big_sepL2_insert_acc with "Hslots") as "(Hslot & Hslots)"; [done.. |].
    wp_cas as _ | ->%(inj goption_to_val _ (Some v)).

    - iDestruct ("Hslots" with "Hslot") as "Hslots".
      rewrite !list_insert_id //.
      iSplitR "HΦ". { iExists front, back, os, vs. iSteps. }
      iSteps.

    - iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      set vs' := vs ∖ {[+v+]}.
      set os' := <[i := None]> os.
      iMod (model_update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ".
      { iSplit; last iSteps. iPureIntro.
        apply gmultiset_disj_union_difference'.
        rewrite Hvs -(take_drop_middle os i (Some v)) // foldr_app /=.
        rewrite foldr_comm_acc_strong. { intros []; set_solver by lia. }
        set_solver.
      }
      iDestruct ("Hslots" $! _ None with "Hslot") as "Hslots".
      rewrite list_insert_id //.
      iSplitR "HΦ".
      { iExists front, back, os', vs'. iSteps. iPureIntro.
        rewrite /vs' /os' insert_take_drop; first congruence.
        rewrite Hvs -{1}(take_drop_middle os i (Some v)) // !foldr_app /=.
        rewrite foldr_comm_acc_strong. { intros []; set_solver by lia. }
        multiset_solver.
      }
      iSteps.
  Qed.
  Lemma bag_1_pop_spec t ι :
    <<<
      bag_1_inv t ι
    | ∀∀ vs,
      bag_1_model t vs
    >>>
      bag_1_pop t @ ↑ι
    <<<
      ∃∃ v vs',
      ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
      bag_1_model t vs'
    | RET v;
      True
    >>>.
  Proof.
    iIntros "%Φ (%l & %γ & -> & %Hsz & #Hmeta & #Hdata & #Hdata_model & #Hinv) HΦ".

    wp_rec. wp_load.
    wp_smart_apply (array_size_spec with "Hdata_model") as "_".
    wp_pures.

    wp_bind (FAA _ _).
    iInv "Hinv" as "(%front & %back & %os & %vs & >%Hvs & Hfront & Hback & Hmodel₂ & Hslots)".
    wp_faa.
    iSplitR "HΦ". { iExists (S front), back, os, vs. iSteps. }
    iModIntro. clear- Hsz.

    simpl_length.
    wp_smart_apply (array_unsafe_get_spec with "Hdata_model") as "_"; [lia | | done |].
    { rewrite list_lookup_fmap list_lookup_lookup_total_lt //. lia. }
    wp_apply (bag_1_pop_0_spec with "[$Hmeta $Hinv] HΦ").
    apply elem_of_list_lookup_total_2. lia.
  Qed.
End bag_1_G.

From zoo_saturn Require
  bag_1__opaque.

#[global] Opaque bag_1_inv.
#[global] Opaque bag_1_model.
