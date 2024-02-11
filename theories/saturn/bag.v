(* Based on:
   https://github.com/ocaml-multicore/saturn/blob/65211c5176b632bd9ed268c0c608ac483f88a992/src_lockfree/mpmc_relaxed_queue.ml
*)

From iris.algebra Require Import
  gmultiset.

From zebre Require Import
  prelude.
From zebre.iris.base_logic Require Import
  lib.auth_excl.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Import
  opt
  array.
From zebre.saturn Require Export
  base.
From zebre Require Import
  options.

Implicit Types front back : nat.
Implicit Types l slot : loc.
Implicit Types slots : list loc.
Implicit Types v t data : val.
Implicit Types vs : gmultiset val.
Implicit Types o : option val.
Implicit Types os : list (option val).

Notation "'data'" :=
  0
( in custom zebre_field
).
Notation "'front'" :=
1
( in custom zebre_field
).
Notation "'back'" :=
  2
( in custom zebre_field
).

Definition bag_create : val :=
  λ: "sz",
    { array_init "sz" (λ: <>, ref §None); #0; #0 }.

#[local] Definition bag_push_aux : val :=
  rec: "bag_push_aux" "slot" "o" :=
    ifnot: Cas "slot" §None "o" then (
      "bag_push_aux" "slot" "o"
    ).
Definition bag_push : val :=
  λ: "t" "v",
    let: "data" := "t".{data} in
    let: "i" := Faa "t".[back] #1 `rem` array_size "data" in
    bag_push_aux (array_unsafe_get "data" "i") ‘Some{ "v" }.

#[local] Definition bag_pop_aux : val :=
  rec: "bag_pop_aux" "slot" :=
    match: !"slot" with
    | None =>
        "bag_pop_aux" "slot"
    | Some "v" as "o" =>
        if: Cas "slot" "o" §None then (
          "v"
        ) else (
          "bag_pop_aux" "slot"
        )
    end.
Definition bag_pop : val :=
  λ: "t",
    let: "data" := "t".{data} in
    let: "i" := Faa "t".[front] #1 `rem` array_size "data" in
    bag_pop_aux (array_unsafe_get "data" "i").

Class BagG Σ `{zebre_G : !ZebreG Σ} := {
  #[local] bag_G_model_G :: AuthExclG Σ (gmultisetO val) ;
}.

Definition bag_Σ := #[
  auth_excl_Σ (gmultisetO val)
].
#[global] Instance subG_bag_Σ Σ `{zebre_G : !ZebreG Σ} :
  subG bag_Σ Σ →
  BagG Σ.
Proof.
  solve_inG.
Qed.

Section bag_G.
  Context `{bag_G : BagG Σ}.

  Record bag_meta := {
    bag_meta_model : gname ;
    bag_meta_slots : list loc ;
  }.
  Implicit Types γ : bag_meta.

  #[local] Instance bag_meta_eq_dec : EqDecision bag_meta :=
    ltac:(solve_decision).
  #[local] Instance bag_meta_countable :
    Countable bag_meta.
  Proof.
    pose encode γ := (
      γ.(bag_meta_model),
      γ.(bag_meta_slots)
    ).
    pose decode := λ '(γ_model, γ_slots), {|
      bag_meta_model := γ_model ;
      bag_meta_slots := γ_slots ;
    |}.
    refine (inj_countable' encode decode _). intros []. done.
  Qed.

  #[local] Definition bag_model₁' γ_model vs :=
    auth_excl_auth γ_model (DfracOwn 1) vs.
  #[local] Definition bag_model₁ γ vs :=
    bag_model₁' γ.(bag_meta_model) vs.
  #[local] Definition bag_model₂' γ_model vs :=
    auth_excl_frag γ_model vs.
  #[local] Definition bag_model₂ γ vs :=
    bag_model₂' γ.(bag_meta_model) vs.

  #[local] Definition bag_inv_inner l γ : iProp Σ :=
    ∃ front back os vs,
    ⌜vs = foldr (λ o vs, from_option (λ v, {[+v+]} ⊎ vs) vs o) ∅ os⌝ ∗
    l.[front] ↦ #front ∗
    l.[back] ↦ #back ∗
    bag_model₂ γ vs ∗
    [∗ list] slot; o ∈ γ.(bag_meta_slots); os,
      slot ↦ (o : val).
  Definition bag_inv t ι : iProp Σ :=
    ∃ l γ data,
    ⌜t = #l⌝ ∗
    ⌜0 < length γ.(bag_meta_slots)⌝ ∗
    meta l nroot γ ∗
    l.[data] ↦□ data ∗
    array_model data DfracDiscarded ((λ slot, #slot) <$> γ.(bag_meta_slots)) ∗
    inv ι (bag_inv_inner l γ).

  Definition bag_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    bag_model₁ γ vs.

  Instance bag_inv_timeless t vs :
    Timeless (bag_model t vs).
  Proof.
    apply _.
  Qed.
  Instance bag_inv_persistent t ι :
    Persistent (bag_inv t ι).
  Proof.
    apply _.
  Qed.

  #[local] Lemma bag_model_alloc :
    ⊢ |==>
      ∃ γ_model,
      bag_model₁' γ_model ∅ ∗
      bag_model₂' γ_model ∅.
  Proof.
    apply auth_excl_alloc'.
  Qed.
  #[local] Lemma bag_model_agree γ vs1 vs2 :
    bag_model₁ γ vs1 -∗
    bag_model₂ γ vs2 -∗
    ⌜vs1 = vs2⌝.
  Proof.
    apply: auth_excl_agree_L.
  Qed.
  #[local] Lemma bag_model_update {γ vs1 vs2} vs :
    bag_model₁ γ vs1 -∗
    bag_model₂ γ vs2 ==∗
      bag_model₁ γ vs ∗
      bag_model₂ γ vs.
  Proof.
    apply auth_excl_update'.
  Qed.

  Lemma bag_create_spec ι (sz : Z) :
    (0 < sz)%Z →
    {{{ True }}}
      bag_create #sz
    {{{ t,
      RET t;
      bag_inv t ι ∗
      bag_model t ∅
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".

    wp_rec.

    pose (Ψ := λ (_ : nat) (vs : list val), (
      ∃ slots,
      ⌜vs = (λ slot, #slot) <$> slots⌝ ∗
      [∗ list] slot ∈ slots,
        slot ↦ §None
    )%I).
    wp_smart_apply (array_init_spec Ψ) as "%data % (%Hslots & Hdata_model & (%slots & -> & Hslots))"; first lia.
    { iSplitL.
      - iExists []. iSteps.
      - iIntros "!> %i %vs %Hi (%slots & %Hslots & Hslots)".
        wp_alloc slot as "Hslot".
        iExists (slots ++ [slot]). iSteps.
        + list_simplifier. done.
        + iApply big_sepL_snoc.
          iSteps.
    }
    wp_record l as "Hmeta" "(Hdata & Hfront & Hback & _)".
    iMod (array_model_persist with "Hdata_model") as "#Hdata_model".

    iMod bag_model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".

    pose γ := {|
      bag_meta_model := γ_model ;
      bag_meta_slots := slots ;
    |}.
    iMod (meta_set _ _ γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁"; last iSteps.
    iExists l, γ. rewrite fmap_length in Hslots. iStep 5. iApply inv_alloc.
    iExists 0, 0, (replicate (Z.to_nat sz) None), ∅. iSteps.
    - iPureIntro. Z_to_nat sz. clear. rewrite Nat2Z.id.
      induction sz; first done. rewrite replicate_S //.
    - iApply big_sepL2_replicate_r; first done.
      iSteps.
  Qed.

  #[local] Lemma bag_push_aux_spec slot v ι l γ :
    slot ∈ γ.(bag_meta_slots) →
    <<<
      meta l nroot γ ∗
      inv ι (bag_inv_inner l γ)
    | ∀∀ vs,
      bag_model #l vs
    >>>
      bag_push_aux #slot ’Some{ v } @ ↑ι
    <<<
      bag_model #l ({[+v+]} ⊎ vs)
    | RET (); True
    >>>.
  Proof.
    iIntros ((i & Hslots_lookup)%elem_of_list_lookup) "!> %Φ (#Hmeta & #Hinv) HΦ".
    pose proof Hslots_lookup as Hi%lookup_lt_Some.

    iLöb as "HLöb".

    wp_rec. wp_pures.

    wp_bind (Cas _ _ _).
    iInv "Hinv" as "(%front & %back & %os & %vs & >%Hvs & Hfront & Hback & Hmodel₂ & Hslots)".
    iDestruct (big_sepL2_length with "Hslots") as "#>%Hlen".
    destruct (lookup_lt_is_Some_2 os i) as (o & Hos_lookup); first congruence.
    iDestruct (big_sepL2_insert_acc with "Hslots") as "(Hslot & Hslots)"; [done.. |].
    wp_cas as _ | ->%(inj opt_to_val _ None).

    - iDestruct ("Hslots" with "Hslot") as "Hslots".
      rewrite !list_insert_id //.
      iSplitR "HΦ". { iExists front, back, os, vs. iSteps. }
      iSteps.

    - iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (bag_model_agree with "Hmodel₁ Hmodel₂") as %->.
      set vs' := {[+v+]} ⊎ vs.
      set os' := <[i := Some v]> os.
      iMod (bag_model_update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ". { repeat iExists _. iSteps. }
      iDestruct ("Hslots" $! _ (Some v) with "Hslot") as "Hslots".
      rewrite list_insert_id //.
      iSplitR "HΦ".
      { iExists front, back, os', vs'. iSteps. iPureIntro.
        rewrite /vs' /os' insert_take_drop; first congruence.
        rewrite Hvs -{1}(take_drop_middle os i None) // !foldr_app /=.
        rewrite -foldr_comm_acc_strong //. { intros []; set_solver by lia. }
      }
      iSteps.
  Qed.
  Lemma bag_push_spec t ι v :
    <<<
      bag_inv t ι
    | ∀∀ vs,
      bag_model t vs
    >>>
      bag_push t v @ ↑ι
    <<<
      bag_model t ({[+v+]} ⊎ vs)
    | RET (); True
    >>>.
  Proof.
    iIntros "!> %Φ (%l & %γ & %data & -> & %Hsz & #Hmeta & #Hdata & #Hdata_model & #Hinv) HΦ".

    wp_rec. wp_load.
    wp_smart_apply (array_size_spec with "Hdata_model") as "_".
    wp_pures.

    wp_bind (Faa _ _).
    iInv "Hinv" as "(%front & %back & %os & %vs & >%Hvs & Hfront & Hback & Hmodel₂ & Hslots)".
    wp_faa.
    iSplitR "HΦ". { iExists front, (S back), os, vs. iSteps. }
    iModIntro. clear- Hsz.

    rewrite fmap_length.
    wp_smart_apply (array_unsafe_get_spec with "Hdata_model") as "_"; [lia | | done |].
    { rewrite list_lookup_fmap list_lookup_lookup_total_lt //. lia. }
    wp_apply (bag_push_aux_spec with "[$Hmeta $Hinv] HΦ").
    apply elem_of_list_lookup_total_2. lia.
  Qed.

  #[local] Lemma bag_pop_aux_spec slot ι l γ :
    slot ∈ γ.(bag_meta_slots) →
    <<<
      meta l nroot γ ∗
      inv ι (bag_inv_inner l γ)
    | ∀∀ vs,
      bag_model #l vs
    >>>
      bag_pop_aux #slot @ ↑ι
    <<<
      ∃∃ v vs',
      ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
      bag_model #l vs'
    | RET v; True
    >>>.
  Proof.
    iIntros ((i & Hslots_lookup)%elem_of_list_lookup) "!> %Φ (#Hmeta & #Hinv) HΦ".
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

    wp_bind (Cas _ _ _).
    iInv "Hinv" as "(%front & %back & %os & %vs & >%Hvs & Hfront & Hback & Hmodel₂ & Hslots)".
    iDestruct (big_sepL2_length with "Hslots") as "#>%Hlen".
    destruct (lookup_lt_is_Some_2 os i) as (o & Hos_lookup); first congruence.
    iDestruct (big_sepL2_insert_acc with "Hslots") as "(Hslot & Hslots)"; [done.. |].
    wp_cas as _ | ->%(inj opt_to_val _ (Some v)).

    - iDestruct ("Hslots" with "Hslot") as "Hslots".
      rewrite !list_insert_id //.
      iSplitR "HΦ". { iExists front, back, os, vs. iSteps. }
      iSteps.

    - iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (bag_model_agree with "Hmodel₁ Hmodel₂") as %->.
      set vs' := vs ∖ {[+v+]}.
      set os' := <[i := None]> os.
      iMod (bag_model_update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ".
      { iSplit; last iSteps. iPureIntro.
        apply gmultiset_disj_union_difference'.
        rewrite Hvs -(take_drop_middle os i (Some v)) // foldr_app /=.
        rewrite foldr_comm_acc_strong. { intros []; set_solver by lia. }
        multiset_solver.
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
  Lemma bag_pop_spec t ι :
    <<<
      bag_inv t ι
    | ∀∀ vs,
      bag_model t vs
    >>>
      bag_pop t @ ↑ι
    <<<
      ∃∃ v vs',
      ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
      bag_model t vs'
    | RET v; True
    >>>.
  Proof.
    iIntros "!> %Φ (%l & %γ & %data & -> & %Hsz & #Hmeta & #Hdata & #Hdata_model & #Hinv) HΦ".

    wp_rec. wp_load.
    wp_smart_apply (array_size_spec with "Hdata_model") as "_".
    wp_pures.

    wp_bind (Faa _ _).
    iInv "Hinv" as "(%front & %back & %os & %vs & >%Hvs & Hfront & Hback & Hmodel₂ & Hslots)".
    wp_faa.
    iSplitR "HΦ". { iExists (S front), back, os, vs. iSteps. }
    iModIntro. clear- Hsz.

    rewrite fmap_length.
    wp_smart_apply (array_unsafe_get_spec with "Hdata_model") as "_"; [lia | | done |].
    { rewrite list_lookup_fmap list_lookup_lookup_total_lt //. lia. }
    wp_apply (bag_pop_aux_spec with "[$Hmeta $Hinv] HΦ").
    apply elem_of_list_lookup_total_2. lia.
  Qed.
End bag_G.

#[global] Opaque bag_create.
#[global] Opaque bag_push.
#[global] Opaque bag_pop.

#[global] Opaque bag_inv.
#[global] Opaque bag_model.
