From zoo Require Import
  prelude.
From zoo.common Require Import
  gset.
From zoo.iris.algebra Require Import
  big_op.
From zoo.iris.base_logic Require Import
  mono_set.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  lst
  xdlchain.
From zoo_partition Require Import
  partition__types.
From zoo_partition Require Export
  partition__code.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types sz : nat.
Implicit Types elt first last split class : location.
Implicit Types v v_elts : val.
Implicit Types cl : gset location.
Implicit Types part : gset (gset location).
Implicit Types γ : gname.

Record partition_descr := {
  partition_descr_class : location ;
  partition_descr_elts : list location ;
}.

#[local] Instance partition_descr_inhabited : Inhabited partition_descr :=
  populate {|
    partition_descr_class := inhabitant ;
    partition_descr_elts := inhabitant ;
  |}.
#[local] Instance partition_descr_eq_dec : EqDecision partition_descr :=
  ltac:(solve_decision).
#[local] Instance partition_descr_countable :
  Countable partition_descr.
Proof.
  pose encode descr := (
    descr.(partition_descr_class),
    descr.(partition_descr_elts)
  ).
  pose decode := λ '(class, elts), {|
    partition_descr_class := class ;
    partition_descr_elts := elts ;
  |}.
  refine (inj_countable' encode decode _). intros []. done.
Qed.

Implicit Types descr : partition_descr.
Implicit Types descrs : gset partition_descr.

Class PartitionG Σ `{zoo_G : !ZooG Σ} := {
  #[local] partition_G_elts_G :: MonoSetG Σ location ;
}.

Definition partition_Σ := #[
  mono_set_Σ location
].
#[global] Instance subG_partition_Σ Σ `{zoo_G : !ZooG Σ} :
  subG partition_Σ Σ →
  PartitionG Σ.
Proof.
  solve_inG.
Qed.

Section partition_G.
  Context `{partition_G : PartitionG Σ}.

  #[local] Definition partition_elts_auth γ elts :=
    mono_set_auth γ (DfracOwn 1) elts.
  #[local] Definition partition_elts_elem γ elt :=
    mono_set_elem γ elt.

  #[local] Definition partition_model_elt descr elt : iProp Σ :=
    elt.[class_] ↦ #descr.(partition_descr_class) ∗
    elt.[seen] ↦ #false.
  #[local] Instance : CustomIpatFormat "partition_model_elt" :=
    "(
      Helt{}_class{_{suff}} &
      Helt{}_seen{_{suff}}
    )".
  #[local] Definition partition_model_descr descrs descr : iProp Σ :=
    ∃ first last prev_descr prev next_descr next,
    ⌜head descr.(partition_descr_elts) = Some first⌝ ∗
    ⌜list.last descr.(partition_descr_elts) = Some last⌝ ∗
    ⌜prev_descr ∈ descrs⌝ ∗
    ⌜list.last prev_descr.(partition_descr_elts) = Some prev⌝ ∗
    ⌜next_descr ∈ descrs⌝ ∗
    ⌜head next_descr.(partition_descr_elts) = Some next⌝ ∗
    descr.(partition_descr_class).[first] ↦ #first ∗
    descr.(partition_descr_class).[last] ↦ #last ∗
    descr.(partition_descr_class).[len] ↦ #(length descr.(partition_descr_elts)) ∗
    descr.(partition_descr_class).[split] ↦ #first ∗
    descr.(partition_descr_class).[split_len] ↦ #0 ∗
    xdlchain_model #prev descr.(partition_descr_elts) #next ∗
    [∗ list] elt ∈ descr.(partition_descr_elts),
      partition_model_elt descr elt.
  #[local] Instance : CustomIpatFormat "partition_model_descr" :=
    "(
      %first{} &
      %last{} &
      %prev{}_descr &
      %prev{} &
      %next{}_descr &
      %next{} &
      %Hfirst{} &
      %Hlast{} &
      %Hdescrs{}_elem_prev &
      %Hprev{} &
      %Hdescrs{}_elem_next &
      %Hnext{} &
      Hclass{}_first &
      Hclass{}_last &
      Hclass{}_len &
      Hclass{}_split &
      Hclass{}_split_len &
      Hchain{} &
      Helts{}
    )".
  #[local] Definition partition_model' γ descrs : iProp Σ :=
    partition_elts_auth γ ([∪ set] descr ∈ descrs, list_to_set descr.(partition_descr_elts)) ∗
    [∗ set] descr ∈ descrs,
      partition_model_descr descrs descr.
  #[local] Instance : CustomIpat0 "partition_model'" :=
    "(
      Helts_auth &
      Hdescrs
    )".
  Definition partition_model γ part : iProp Σ :=
    ∃ descrs,
    ⌜part = set_map (list_to_set ∘ partition_descr_elts) descrs⌝ ∗
    partition_model' γ descrs.
  #[local] Instance : CustomIpat0 "partition_model" :=
    "(
      %descrs &
      -> &
      Hmodel
    )".

  Definition partition_elt γ elt v : iProp Σ :=
    partition_elts_elem γ elt ∗
    elt.[data] ↦□ v.
  #[local] Instance : CustomIpatFormat "partition_elt" :=
    "(
      Helts_elem{}{_{suff}} &
      Helt{}_data{_{suff}}
    )".

  #[global] Instance partition_model_timeless γ part :
    Timeless (partition_model γ part).
  Proof.
    apply _.
  Qed.
  #[global] Instance partition_elt_timeless γ elt v :
    Timeless (partition_elt γ elt v).
  Proof.
    apply _.
  Qed.
  #[global] Instance partition_elt_persistent γ elt v :
    Persistent (partition_elt γ elt v).
  Proof.
    apply _.
  Qed.

  #[local] Lemma partition_elts_alloc :
    ⊢ |==>
      ∃ γ,
      partition_elts_auth γ ∅.
  Proof.
    apply mono_set_alloc.
  Qed.
  #[local] Lemma partition_elts_elem_valid γ elts elt :
    partition_elts_auth γ elts -∗
    partition_elts_elem γ elt -∗
    ⌜elt ∈ elts⌝.
  Proof.
    apply mono_set_elem_valid.
  Qed.
  #[local] Lemma partition_elts_insert {γ elts} elt :
    partition_elts_auth γ elts ⊢ |==>
      partition_elts_auth γ ({[elt]} ∪ elts) ∗
      partition_elts_elem γ elt.
  Proof.
    apply mono_set_insert'.
  Qed.

  #[local] Lemma partition_model_disjoint_strong {γ descrs} descr1 descr2 :
    descr1 ∈ descrs →
    descr2 ∈ descrs →
    partition_model' γ descrs ⊢
      ⌜ descr1 ≠ descr2 →
        descr1.(partition_descr_class) ≠ descr2.(partition_descr_class)
      ⌝ ∗
      ⌜ ∀ elt,
        elt ∈ descr1.(partition_descr_elts) →
        elt ∈ descr2.(partition_descr_elts) →
        descr1 = descr2
      ⌝.
  Proof.
    iIntros "%Hdescrs_elem_1 %Hdescrs_elem_2 (:partition_model')".
    destruct (decide (descr1 = descr2)) as [<- | Hneq]; first done.
    iDestruct (big_sepS_delete _ _ descr1 with "Hdescrs") as "((:partition_model_descr =1) & Hdescrs)"; first done.
    iDestruct (big_sepS_elem_of _ _ descr2 with "Hdescrs") as "(:partition_model_descr =2)"; first set_solver.
    iSplit.
    - iIntros "_ <-".
      iApply (pointsto_exclusive with "Hclass1_first Hclass2_first").
    - iIntros (elt (i1 & Hlookup_1)%elem_of_list_lookup (i2 & Hlookup_2)%elem_of_list_lookup).
      iDestruct (big_sepL_lookup with "Helts1") as "(:partition_model_elt suff=1)"; first done.
      iDestruct (big_sepL_lookup with "Helts2") as "(:partition_model_elt suff=2)"; first done.
      iDestruct (pointsto_exclusive with "Helt_class_1 Helt_class_2") as %[].
  Qed.
  #[local] Lemma partition_model_class_unique {γ descrs} descr1 descr2 :
    descr1 ∈ descrs →
    descr2 ∈ descrs →
    descr1 ≠ descr2 →
    partition_model' γ descrs ⊢
    ⌜descr1.(partition_descr_class) ≠ descr2.(partition_descr_class)⌝.
  Proof.
    iIntros "%Hdescrs_elem_1 %Hdescrs_elem_2 %Hneq Hmodel".
    iDestruct (partition_model_disjoint_strong descr1 descr2 with "Hmodel") as "(% & _)"; [done.. |].
    iSteps.
  Qed.
  #[local] Lemma partition_model_disjoint' {γ descrs} elt descr1 descr2 :
    descr1 ∈ descrs →
    elt ∈ descr1.(partition_descr_elts) →
    descr2 ∈ descrs →
    elt ∈ descr2.(partition_descr_elts) →
    partition_model' γ descrs ⊢
    ⌜descr1 = descr2⌝.
  Proof.
    iIntros "%Hdescrs_elem_1 %Hdescr1_elem %Hdescrs_elem_2 %Hdescr2_elem Hmodel".
    iDestruct (partition_model_disjoint_strong descr1 descr2 with "Hmodel") as "(_ & %)"; [done.. |].
    iSteps.
  Qed.
  #[local] Lemma partition_model_disjoint'' {γ descrs} elt descr :
    descr ∈ descrs →
    elt ∈ descr.(partition_descr_elts) →
    partition_model' γ descrs ⊢
    ⌜ ∀ descr',
      descr' ∈ descrs →
      elt ∈ descr'.(partition_descr_elts) →
      descr' = descr
    ⌝.
  Proof.
    iIntros "%Hdescrs_elem %Helt_elem Hmodel %descr' %Hdescr_elem' %Helts_elem'".
    iApply (partition_model_disjoint' with "Hmodel"); done.
  Qed.
  #[local] Lemma partition_elt_valid' γ descrs elt v :
    partition_model' γ descrs -∗
    partition_elt γ elt v -∗
      ∃ descr,
      ⌜descr ∈ descrs⌝ ∗
      ⌜elt ∈ descr.(partition_descr_elts)⌝ ∧
      ⌜ ∀ descr',
        descr' ∈ descrs →
        elt ∈ descr'.(partition_descr_elts) →
        descr' = descr
      ⌝.
  Proof.
    iIntros "(:partition_model') (:partition_elt)".
    iDestruct (partition_elts_elem_valid with "Helts_auth Helts_elem") as %(descr & Hdescr & Helts_elem%elem_of_list_to_set)%big_unionS_elem_of.
    iExists descr. iStep 5 as (descr' Hdescr' Helts_elem').
    iApply partition_model_disjoint'; [done.. |].
    iSteps.
  Qed.
  #[local] Lemma partition_model_descr_elts_NoDup {γ descrs} descr :
    descr ∈ descrs →
    partition_model' γ descrs ⊢
    ⌜NoDup descr.(partition_descr_elts)⌝.
  Proof.
    iIntros "%Hdescrs_lookup (:partition_model')".
    iDestruct (big_sepS_elem_of with "Hdescrs") as "(:partition_model_descr)"; first done.
    iApply (xdlchain_model_NoDup with "Hchain").
  Qed.

  #[local] Lemma partition_model_empty :
    ⊢ |==>
      ∃ γ,
      partition_model γ ∅.
  Proof.
    iMod partition_elts_alloc as "(%γ & Helts_auth)".
    iExists γ, ∅.
    rewrite set_map_empty /partition_model' !big_opS_empty.
    iSteps.
  Qed.
  Lemma partition_model_non_empty {γ part} cl :
    cl ∈ part →
    partition_model γ part ⊢
    ⌜cl ≠ ∅⌝.
  Proof.
    iIntros "%Hcl (:partition_model)".
    iDestruct "Hmodel" as "(:partition_model')".
    apply elem_of_map in Hcl as (descr & -> & Hdescr).
    iDestruct (big_sepS_elem_of with "Hdescrs") as "(:partition_model_descr)"; first done.
    iPureIntro. eapply list_to_set_not_empty, hd_error_some_nil. done.
  Qed.
  Lemma partition_model_disjoint {γ part} elt cl1 cl2 :
    cl1 ∈ part →
    elt ∈ cl1 →
    cl2 ∈ part →
    elt ∈ cl2 →
    partition_model γ part ⊢
    ⌜cl1 = cl2⌝.
  Proof.
    iIntros "%Hpart_elem_1 %Hcl1_elem %Hpart_elem_2 %Hcl2_elem (:partition_model)".
    apply elem_of_map in Hpart_elem_1 as (descr1 & -> & Hdescrs_elem_1).
    apply elem_of_map in Hpart_elem_2 as (descr2 & -> & Hdescrs_elem_2).
    iDestruct (partition_model_disjoint' elt descr1 descr2 with "Hmodel") as %<-; last iSteps.
    { done. }
    { apply elem_of_list_to_set in Hcl1_elem. done. }
    { done. }
    { apply elem_of_list_to_set in Hcl2_elem. done. }
  Qed.

  Lemma partition_elt_valid γ part elt v :
    partition_model γ part -∗
    partition_elt γ elt v -∗
      ∃ cl,
      ⌜cl ∈ part⌝ ∗
      ⌜elt ∈ cl⌝.
  Proof.
    iIntros "(:partition_model) Helt".
    iDestruct (partition_elt_valid' with "Hmodel Helt") as "(%descr & %descrs_elem & %Helts_elem & _)".
    iExists (list_to_set descr.(partition_descr_elts)). iSplit; iPureIntro.
    - apply elem_of_map. naive_solver.
    - rewrite elem_of_list_to_set //.
  Qed.
  Lemma partition_elt_agree γ elt v1 v2 :
    partition_elt γ elt v1 -∗
    partition_elt γ elt v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    iIntros "(:partition_elt suff=1) (:partition_elt suff=2)".
    iApply (pointsto_agree with "Helt_data_1 Helt_data_2").
  Qed.

  Lemma partition_elt_equal_spec γ elt1 v1 elt2 v2 :
    {{{
      True
    }}}
      partition_elt_equal #elt1 #elt2
    {{{
      RET #(bool_decide (elt1 = elt2));
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma partition_get_class_spec γ descrs elt v :
    {{{
      partition_model' γ descrs ∗
      partition_elt γ elt v
    }}}
      (#elt).{class_}
    {{{ descr,
      RET #descr.(partition_descr_class);
      partition_model' γ descrs ∗
      partition_elt γ elt v ∗
      ⌜descr ∈ descrs⌝ ∗
      ⌜elt ∈ descr.(partition_descr_elts)⌝ ∗
      ⌜ ∀ descr',
        descr' ∈ descrs →
        elt ∈ descr'.(partition_descr_elts) →
        descr' = descr
      ⌝
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Helt) HΦ".
    iDestruct (partition_elt_valid' with "Hmodel Helt") as "(%descr & %Hdescrs_elem & %Helts_elem & %Hdescr)".
    iDestruct "Hmodel" as "(:partition_model')".
    iDestruct (big_sepS_elem_of_acc with "Hdescrs") as "((:partition_model_descr) & Hdescrs)"; first done.
    odestruct elem_of_list_lookup_1 as (i & Helts_lookup); first done.
    iDestruct (big_sepL_lookup_acc with "Helts") as "((:partition_model_elt) & Helts)"; first done.
    wp_load.
    iDestruct ("Helts" with "[$]") as "Helts".
    iDestruct ("Hdescrs" with "[- Helts_auth Helt HΦ]") as "Hdescrs".
    { iExists first, last, prev_descr, prev, next_descr, next. iSteps. }
    iSteps.
  Qed.

  Lemma partition_elt_equiv_spec γ part elt1 v1 elt2 v2 :
    {{{
      partition_model γ part ∗
      partition_elt γ elt1 v1 ∗
      partition_elt γ elt2 v2
    }}}
      partition_elt_equiv #elt1 #elt2
    {{{ b,
      RET #b;
      partition_model γ part ∗
      partition_elt γ elt1 v1 ∗
      partition_elt γ elt2 v2 ∗
      ⌜ ∀ cl1 cl2,
        cl1 ∈ part →
        elt1 ∈ cl1 →
        cl2 ∈ part →
        elt2 ∈ cl2 →
        if b then cl1 = cl2 else cl1 ≠ cl2
      ⌝
    }}}.
  Proof.
    iIntros "%Φ ((:partition_model) & Helt1 & Helt2) HΦ".
    wp_rec.
    wp_smart_apply (partition_get_class_spec with "[$Hmodel $Helt2]") as (descr2) "(Hmodel & Helt2 & %Hdescrs_elem_2 & %Helts_elem_2 & %Hdescr2)".
    wp_apply (partition_get_class_spec with "[$Hmodel $Helt1]") as (descr1) "(Hmodel & Helt1 & %Hdescrs_elem_1 & %Helts_elem_1 & %Hdescr1)".
    wp_pures.
    destruct (decide (descr1 = descr2)) as [<- | Hneq].
    - rewrite bool_decide_eq_true_2 //.
      iSteps as (cl1 cl2 (descr1' & -> & Hdescrs_elem_1')%elem_of_map Hcl1_elem (descr2' & -> & Hdescrs_elem_2')%elem_of_map Hcl2_elem) / --silent. iPureIntro.
      rewrite !elem_of_list_to_set in Hcl1_elem Hcl2_elem.
      opose proof* Hdescr1 as ->; [done.. |].
      opose proof* Hdescr2 as <-; [done.. |].
      done.
    - iDestruct (partition_model_class_unique descr1 descr2 with "Hmodel") as %?; [done.. |].
      rewrite bool_decide_eq_false_2 //.
      iSteps as (cl Hcl_elem_1 (descr & -> & Hdescrs_elem)%elem_of_map _ Hcl_elem_2) / --silent. iPureIntro.
      rewrite !elem_of_list_to_set in Hcl_elem_1 Hcl_elem_2.
      opose proof* Hdescr1 as Heq1; [done.. |].
      opose proof* Hdescr2 as Heq2; [done.. |].
      congruence.
  Qed.

  Lemma partition_elt_repr_spec γ part elt v :
    {{{
      partition_model γ part ∗
      partition_elt γ elt v
    }}}
      partition_elt_repr #elt
    {{{ elt',
      RET #elt';
      partition_model γ part ∗
      partition_elt γ elt v ∗
      ⌜ ∀ cl,
        cl ∈ part →
        elt ∈ cl ↔ elt' ∈ cl
      ⌝
    }}}.
  Proof.
    iIntros "%Φ ((:partition_model) & Helt) HΦ".
    wp_rec.
    wp_apply (partition_get_class_spec with "[$Hmodel $Helt]") as (descr) "(Hmodel & Helt & %Hdescrs_elem & %Helts_elem & %Helt_descr)".
    iDestruct "Hmodel" as "(:partition_model')".
    iDestruct (big_sepS_elem_of_acc with "Hdescrs") as "((:partition_model_descr) & Hdescrs)"; first done.
    wp_load.
    iDestruct ("Hdescrs" with "[- Helts_auth Helt HΦ]") as "Hdescrs".
    { iExists first, last, prev_descr, prev, next_descr, next. iSteps. }
    apply head_Some_elem_of in Hfirst.
    iDestruct (partition_model_disjoint'' first descr with "[$]") as %Hfirst_descr; [done.. |].
    iSteps as (cl (descr' & -> & Hdescr_elem')%elem_of_map) / --silent. iPureIntro.
    rewrite !elem_of_list_to_set. naive_solver.
  Qed.

  Lemma partition_elt_get_spec γ elt v :
    {{{
      partition_elt γ elt v
    }}}
      partition_elt_get #elt
    {{{
      RET v;
      partition_elt γ elt v
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma partition_elt_cardinal_spec γ part elt v :
    {{{
      partition_model γ part ∗
      partition_elt γ elt v
    }}}
      partition_elt_cardinal #elt
    {{{ sz,
      RET #sz;
      partition_model γ part ∗
      partition_elt γ elt v ∗
      ⌜ ∀ cl,
        cl ∈ part →
        elt ∈ cl →
        size cl = sz
      ⌝
    }}}.
  Proof.
    iIntros "%Φ ((:partition_model) & Helt) HΦ".
    wp_rec.
    wp_apply (partition_get_class_spec with "[$Hmodel $Helt]") as (descr) "(Hmodel & Helt & %Hdescrs_elem & %Helts_elem & %Helt_descr)".
    iDestruct (partition_model_descr_elts_NoDup with "Hmodel") as %?; first done.
    iDestruct "Hmodel" as "(:partition_model')".
    iDestruct (big_sepS_elem_of_acc with "Hdescrs") as "((:partition_model_descr) & Hdescrs)"; first done.
    wp_load.
    iDestruct ("Hdescrs" with "[- Helts_auth Helt HΦ]") as "Hdescrs".
    { iExists first, last, prev_descr, prev, next_descr, next. iSteps. }
    iSteps as (cl (descr' & -> & Hdescr_elem')%elem_of_map ->%elem_of_list_to_set%Helt_descr) / --silent; last done. iPureIntro.
    rewrite size_list_to_set //.
  Qed.

  Lemma partition_add_new_class_spec γ part v :
    {{{
      partition_model γ part
    }}}
      partition_add_new_class v
    {{{ elt,
      RET #elt;
      partition_model γ (part ∪ {[{[elt]}]}) ∗
      partition_elt γ elt v
    }}}.
  Proof.
    iIntros "%Φ (:partition_model) HΦ".
    iDestruct "Hmodel" as "(:partition_model')".

    wp_rec.
    wp_block elt as "(Helt_prev & Helt_next & Helt_data & Helt_class & Helt_seen & _)".
    iMod (pointsto_persist with "Helt_data") as "#Helt_data".
    wp_block class as "(Hclass_first & Hclass_last & Hclass_len & Hclass_split & Hclass_split_len & _)".
    do 3 wp_store. wp_pures.

    pose descr := {|
      partition_descr_class := class ;
      partition_descr_elts := [elt] ;
    |}.
    iMod (partition_elts_insert elt with "Helts_auth") as "(Helts_auth & #Helts_elem)".

    iAssert ⌜descr ∉ descrs⌝%I as %Hdescr.
    { iIntros "%Hdescrs_elem".
      iDestruct (big_sepS_elem_of with "Hdescrs") as "(:partition_model_descr =')"; first done.
      iApply (pointsto_exclusive with "Hclass_first Hclass'_first").
    }

    iApply "HΦ". iModIntro.
    iSplitL; last iSteps.
    iExists ({[descr]} ∪ descrs).
    iSplit.
    { iPureIntro. rewrite set_map_union_L set_map_singleton_L /= right_id_L (comm_L (∪)) //. }
    iSplitL "Helts_auth".
    { iApply (mono_set_auth_proper with "Helts_auth").
      rewrite big_opS_insert //. set_solver.
    }
    iApply (big_sepS_insert_2 with "[- Hdescrs] [Hdescrs]").
    - iExists elt, elt, descr, elt, descr, elt.
      rewrite xdlchain_model_singleton.
      iSteps; iPureIntro; set_solver.
    - iApply (big_sepS_impl with "Hdescrs"). iIntros "!> %descr' %Hdescrs_elem (:partition_model_descr)".
      iExists first, last, prev_descr, prev, next_descr, next.
      iSteps; iPureIntro; set_solver.
  Qed.

  Lemma partition_create_spec v :
    {{{
      True
    }}}
      partition_create v
    {{{ γ elt,
      RET #elt;
      partition_model γ {[{[elt]}]} ∗
      partition_elt γ elt v
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    iMod partition_model_empty as "(%γ & Hmodel)".
    wp_apply (partition_add_new_class_spec with "Hmodel") as (elt) "Hmodel".
    rewrite left_id_L.
    iApply ("HΦ" with "Hmodel").
  Qed.

  Lemma partition_add_same_class_spec γ part elt v v' :
    {{{
      partition_model γ part ∗
      partition_elt γ elt v
    }}}
      partition_add_same_class #elt v'
    {{{ elt' part',
      RET #elt';
      partition_model γ part' ∗
      partition_elt γ elt v ∗
      partition_elt γ elt' v' ∗
      ⌜ ∃ part'' cl,
        elt ∈ cl ∧
        part = part'' ∪ {[cl]} ∧
        part' = part'' ∪ {[cl ∪ {[elt']}]}
      ⌝
    }}}.
  Proof.
  Admitted.

  Lemma partition_refine_spec {γ part v_elts} elts :
    lst_model' v_elts (#@{location} <$> elts) →
    {{{
      partition_model γ part
    }}}
      partition_refine v_elts
    {{{ part',
      RET ();
      partition_model γ part' ∗
      ⌜ ∀ cl',
        cl' ∈ part' ↔
          cl' ≠ ∅ ∧
            ∃ cl,
            cl ∈ part ∧
            ( cl' = cl ∩ list_to_set elts
            ∨ cl' = cl ∖ list_to_set elts
            )
      ⌝
    }}}.
  Proof.
  Admitted.
End partition_G.

#[global] Opaque partition_elt_equal.
#[global] Opaque partition_elt_equiv.
#[global] Opaque partition_elt_repr.
#[global] Opaque partition_elt_get.
#[global] Opaque partition_elt_cardinal.
#[global] Opaque partition_add_new_class.
#[global] Opaque partition_create.
#[global] Opaque partition_add_same_class.
#[global] Opaque partition_refine.

#[global] Opaque partition_model.
#[global] Opaque partition_elt.
