Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.common.gmultiset.
Require Import zoo.common.list.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Export zoo_saturn.bag_1__code.
Require Import zoo_saturn.bag_1__types.
Require Import zoo.options.

Implicit Type front back : nat.
Implicit Type l slot : location.
Implicit Type slots : list location.
Implicit Type v t data : val.
Implicit Type vs : gmultiset val.
Implicit Type o : option val.
Implicit Type os : list (option val).

Class Bag1G Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] bag_1۰G۰model۰G :: TwinsG Σ (leibnizO (gmultiset val))
  }.

Definition bag_1۰Σ :=
  #[twins۰Σ (leibnizO (gmultiset val))
  ].
#[global] Instance subGｰbag_1۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG bag_1۰Σ Σ →
  Bag1G Σ.
Proof.
  solve_inG.
Qed.

Section consistent.
  #[local] Definition consistent vs os :=
    vs = ⋃+ (singletonMS <$> oflatten os).

  #[local] Lemma consistentｰlookup vs os i v :
    os !! i = Some $ Some v →
    consistent vs os →
    v ∈ vs.
  Proof.
    intros Hlookup%list_elem_of_lookup_2 ->.
    setoid_rewrite elem_of_gmultiset_disj_union_list.
    setoid_rewrite list_elem_of_fmap.
    setoid_rewrite elem_ofｰoflatten.
    eexists. split; naive_solver set_solver.
  Qed.
  #[local] Lemma consistentｰinsert {vs os i} v :
    os !! i = Some None →
    consistent vs os →
    consistent ({[+v+]} ⊎ vs) (<[i := Some v]> os).
  Proof.
    intros Hlookup ->.
    rewrite /consistent oflattenｰinsertｰNoneｰSome //.
  Qed.
  #[local] Lemma consistentｰremove vs os i v :
    os !! i = Some $ Some v →
    consistent vs os →
    consistent (vs ∖ {[+v+]}) (<[i := None]> os).
  Proof.
    intros Hlookup ->.
    rewrite /consistent.
    erewrite oflattenｰinsertｰSomeｰNone; last done.
    rewrite list_fmap_delete.
    erewrite gmultisetｰdisj_union_listｰdelete; first done.
    rewrite list_lookup_fmap_Some.
    erewrite oflattenｰlookupｰSome; last done.
    eauto.
  Qed.
End consistent.

Opaque consistent.

Section bag_1۰G.
  Context `{bag_1۰G : Bag1G Σ}.

  Record metadata :=
    { metadata۰data : val
    ; metadata۰slots : list location
    ; metadata۰inv : namespace
    ; metadata۰model : gname
    }.
  Implicit Type γ : metadata.

  #[local] Instance metadataｰeq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[local] Instance metadataｰcountable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition model₁' γ_model vs :=
    twins۰twin₁ γ_model (DfracOwn 1) vs.
  #[local] Definition model₁ γ vs :=
    model₁' γ.(metadata۰model) vs.
  #[local] Definition model₂' γ_model vs :=
    twins۰twin₂ γ_model vs.
  #[local] Definition model₂ γ vs :=
    model₂' γ.(metadata۰model) vs.

  #[local] Definition inv۰inner l γ : iProp Σ :=
    ∃ front back vs os,
    l.[front] ↦ #front ∗
    l.[back] ↦ #back ∗
    model₂ γ vs ∗
    ⌜consistent vs os⌝ ∗
    [∗ list] slot; o ∈ γ.(metadata۰slots); os,
      slot ↦ᵣ (o : val).
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %front
      & %back
      & %vs
      & %os
      & Hfront
      & Hback
      & Hmodel₂
      & >%Hconsistent
      & Hslots
      )
    ".
  #[local] Definition inv' l γ :=
    inv γ.(metadata۰inv) (inv۰inner l γ).
  Definition bag_1۰inv t ι : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    ⌜ι = γ.(metadata۰inv)⌝ ∗
    ⌜0 < length γ.(metadata۰slots)⌝ ∗
    l ↪ γ ∗
    l.[data] ↦□ γ.(metadata۰data) ∗
    array۰model γ.(metadata۰data) DfracDiscarded (#*@{location} γ.(metadata۰slots)) ∗
    inv' l γ.
  #[local] Instance : CustomIpat "inv" :=
    " ( %l
      & %γ
      & ->
      & ->
      & %Hsz
      & #Hmeta
      & #Hdata
      & #Hdata_model
      & #Hinv
      )
    ".

  Definition bag_1۰model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    l ↪ γ ∗
    model₁ γ vs.
  #[local] Instance : CustomIpat "model" :=
    " ( %l{;_}
      & %γ{;_}
      & %Heq{}
      & #Hmeta_{}
      & Hmodel₁{_{}}
      )
    ".

  #[global] Instance bag_1۰modelｰtimeless t vs :
    Timeless (bag_1۰model t vs).
  Proof.
    apply _.
  Qed.

  #[global] Instance bag_1۰invｰpersistent t ι :
    Persistent (bag_1۰inv t ι).
  Proof.
    apply _.
  Qed.

  #[local] Lemma modelｰalloc :
    ⊢ |==>
      ∃ γ_model,
      model₁' γ_model ∅ ∗
      model₂' γ_model ∅.
  Proof.
    apply twinsｰalloc'.
  Qed.
  #[local] Lemma model₁ｰexclusive γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₁ γ vs2 -∗
    False.
  Proof.
    apply twins۰twin₁ｰexclusive.
  Qed.
  #[local] Lemma modelｰagree γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₂ γ vs2 -∗
    ⌜vs1 = vs2⌝.
  Proof.
    apply: twinsｰagreeｰL.
  Qed.
  #[local] Lemma modelｰupdate {γ vs1 vs2} vs :
    model₁ γ vs1 -∗
    model₂ γ vs2 ==∗
      model₁ γ vs ∗
      model₂ γ vs.
  Proof.
    apply twinsｰupdate.
  Qed.

  Lemma bag_1۰modelｰexclusive t vs1 vs2 :
    bag_1۰model t vs1 -∗
    bag_1۰model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iApply (model₁ｰexclusive with "Hmodel₁_1 Hmodel₁_2").
  Qed.

  Lemma bag_1٠createｰspec ι (sz : Z) :
    (0 < sz)%Z →
    {{{
      True
    }}}
      bag_1٠create #sz
    {{{
      t
    , RET t;
      bag_1۰inv t ι ∗
      bag_1۰model t ∅
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".

    wp۰rec.

    pose (Ψ := λ data (_ : nat) (vs : list val), (
      ∃ slots,
      ⌜vs = #*@{location} slots⌝ ∗
      [∗ list] slot ∈ slots,
        slot ↦ᵣ None
    )%I).
    wp۰apply+ (array٠unsafe_initｰspec Ψ) as "%data % (%Hslots & Hdata_model & (%slots & -> & Hslots))"; first lia.
    { iSplitL.
      - iSteps. iExists []. iSteps.
      - iIntros "!> %data %i %vs % % (%slots & %Hslots & Hslots)".
        wp۰ref slot as "Hslot".
        iExists (slots ++ [slot]). iSteps.
        + list_simplifier. done.
        + iApply big_sepL_snoc.
          iSteps.
    }
    wp۰block l as "Hmeta" "(Hdata & Hfront & Hback & _)".
    iMod (array۰modelｰpersist with "Hdata_model") as "#Hdata_model".

    iMod modelｰalloc as "(%γ_model & Hmodel₁ & Hmodel₂)".

    pose γ :=
      {|metadata۰data := data
      ; metadata۰slots := slots
      ; metadata۰inv := ι
      ; metadata۰model := γ_model
      |}.
    iMod (metaｰset γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁"; last iSteps.
    iExists l, γ. simp_length in Hslots. iStep 6.
    iApply inv_alloc.
    iExists 0, 0, ∅, (replicate ₊sz None). iSteps.
    - iPureIntro. Z_to_nat sz. clear. rewrite Nat2Z.id.
      induction sz; first done. rewrite replicate_S //.
    - iApply big_sepL2_replicate_r; first done.
      iSteps.
  Qed.

  #[local] Lemma bag_1٠push₁ｰspec slot v l γ :
    slot ∈ γ.(metadata۰slots) →
    <<<
      l ↪ γ ∗
      inv' l γ
    | ∀∀ vs,
      bag_1۰model #l vs
    >>>
      bag_1٠push₁ #slot ’Some[ v ] @ ↑γ.(metadata۰inv)
    <<<
      bag_1۰model #l ({[+v+]} ⊎ vs)
    | RET ();
      True
    >>>.
  Proof.
    iIntros ((i & Hslots_lookup)%list_elem_of_lookup) "%Φ (#Hmeta & #Hinv) HΦ".
    pose proof Hslots_lookup as Hi%lookup_lt_Some.

    iLöb as "HLöb".

    wp۰rec. wp۰pures.

    wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
    iInv "Hinv" as "(:inv۰inner)".
    iDestruct (big_sepL2_length with "Hslots") as "#>%Hlen".
    destruct (lookup_lt_is_Some_2 os i) as (o & Hos_lookup); first congruence.
    iDestruct (big_sepL2_insert_acc with "Hslots") as "(Hslot & Hslots)"; [done.. |].
    wp۰cas as _ | ->%(inj goption۰to_val _ None).

    - iDestruct ("Hslots" with "Hslot") as "Hslots".
      rewrite !list_insert_id //.
      iSplitR "HΦ". { iFrameSteps. }
      iSteps.

    - iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod (modelｰupdate with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
      iDestruct ("Hslots" $! _ (Some v) with "Hslot") as "Hslots".
      rewrite list_insert_id //.
      iSplitR "HΦ".
      { iFrameSteps. iPureIntro.
        apply consistentｰinsert; done.
      }
      iSteps.
  Qed.
  Lemma bag_1٠pushｰspec t ι v :
    <<<
      bag_1۰inv t ι
    | ∀∀ vs,
      bag_1۰model t vs
    >>>
      bag_1٠push t v @ ↑ι
    <<<
      bag_1۰model t ({[+v+]} ⊎ vs)
    | RET ();
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec. wp۰load.
    wp۰apply+ (array٠sizeｰspec with "Hdata_model") as "_".
    wp۰pures.

    wp۰bind (𝗳𝗮𝗮 _ _)%E.
    iInv "Hinv" as "(:inv۰inner)".
    wp۰faa.
    iSplitR "HΦ". { iFrameSteps. }
    iIntros "!> {%- Hsz}".

    simp_length.
    wp۰apply+ (array٠unsafe_getｰspec with "Hdata_model") as "_"; [lia | | done |].
    { rewrite list_lookup_fmap list_lookup_lookup_total_lt //. lia. }
    wp۰apply (bag_1٠push₁ｰspec with "[$Hmeta $Hinv] HΦ").
    apply list_elem_of_lookup_total_2. lia.
  Qed.

  #[local] Lemma bag_1٠pop₁ｰspec slot l γ :
    slot ∈ γ.(metadata۰slots) →
    <<<
      l ↪ γ ∗
      inv' l γ
    | ∀∀ vs,
      bag_1۰model #l vs
    >>>
      bag_1٠pop₁ #slot @ ↑γ.(metadata۰inv)
    <<<
      ∃∃ v vs',
      ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
      bag_1۰model #l vs'
    | RET v;
      True
    >>>.
  Proof.
    iIntros ((i & Hslots_lookup)%list_elem_of_lookup) "%Φ (#Hmeta & #Hinv) HΦ".
    pose proof Hslots_lookup as Hi%lookup_lt_Some.

    iLöb as "HLöb".

    wp۰rec. wp۰pures.

    wp۰bind (!_)%E.
    iInv "Hinv" as "(:inv۰inner)".
    iDestruct (big_sepL2_length with "Hslots") as "#>%Hlen".
    destruct (lookup_lt_is_Some_2 os i) as (o & Hos_lookup); first congruence.
    iDestruct (big_sepL2_lookup_acc with "Hslots") as "(Hslot & Hslots)"; [done.. |].
    wp۰load.
    iSplitR "HΦ". { iFrameSteps. }
    iIntros "!> {%- Hslots_lookup Hi}".

    destruct o as [v |]; last iSteps.
    wp۰pures.

    wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
    iInv "Hinv" as "(:inv۰inner)".
    iDestruct (big_sepL2_length with "Hslots") as "#>%Hlen".
    destruct (lookup_lt_is_Some_2 os i) as (o & Hos_lookup); first congruence.
    iDestruct (big_sepL2_insert_acc with "Hslots") as "(Hslot & Hslots)"; [done.. |].
    wp۰cas as _ | ->%(inj goption۰to_val _ (Some v)).

    - iDestruct ("Hslots" with "Hslot") as "Hslots".
      rewrite !list_insert_id //.
      iSplitR "HΦ". { iFrameSteps. }
      iSteps.

    - iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod (modelｰupdate with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[$Hmodel₁]") as "HΦ".
      { iSplit; last iSteps. iPureIntro.
        eapply gmultiset_disj_union_difference', consistentｰlookup; done.
      }
      iDestruct ("Hslots" $! _ None with "Hslot") as "Hslots".
      rewrite list_insert_id //.
      iSplitR "HΦ".
      { iFrameSteps. iPureIntro.
        apply consistentｰremove; done.
      }
      iSteps.
  Qed.
  Lemma bag_1٠popｰspec t ι :
    <<<
      bag_1۰inv t ι
    | ∀∀ vs,
      bag_1۰model t vs
    >>>
      bag_1٠pop t @ ↑ι
    <<<
      ∃∃ v vs',
      ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
      bag_1۰model t vs'
    | RET v;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec. wp۰load.
    wp۰apply+ (array٠sizeｰspec with "Hdata_model") as "_".
    wp۰pures.

    wp۰bind (𝗳𝗮𝗮 _ _)%E.
    iInv "Hinv" as "(:inv۰inner)".
    wp۰faa.
    iSplitR "HΦ". { iFrameSteps. }
    iIntros "!> {%- Hsz}".

    simp_length.
    wp۰apply+ (array٠unsafe_getｰspec with "Hdata_model") as "_"; [lia | | done |].
    { rewrite list_lookup_fmap list_lookup_lookup_total_lt //. lia. }
    wp۰apply (bag_1٠pop₁ｰspec with "[$Hmeta $Hinv] HΦ").
    apply list_elem_of_lookup_total_2. lia.
  Qed.
End bag_1۰G.

Require zoo_saturn.bag_1__opaque.

#[global] Opaque bag_1۰inv.
#[global] Opaque bag_1۰model.
