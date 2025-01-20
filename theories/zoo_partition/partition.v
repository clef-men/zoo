From zoo Require Import
  prelude.
From zoo.common Require Import
  countable
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

Record descriptor := {
  descriptor_elts : list location ;
  descriptor_prev : location ;
  descriptor_next : location ;
}.

#[local] Instance descriptor_inhabited : Inhabited descriptor :=
  populate {|
    descriptor_elts := inhabitant ;
    descriptor_prev := inhabitant ;
    descriptor_next := inhabitant ;
  |}.
#[local] Instance descriptor_eq_dec : EqDecision descriptor :=
  ltac:(solve_decision).
#[local] Instance descriptor_countable :
  Countable descriptor.
Proof.
  solve_countable.
Qed.

Implicit Types descr : descriptor.
Implicit Types descrs : gmap location descriptor.

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

  #[local] Definition metadata :=
    gname.
  Implicit Types γ : metadata.

  #[local] Definition elements_auth γ elts :=
    mono_set_auth γ (DfracOwn 1) elts.
  #[local] Definition elements_elem γ elt :=
    mono_set_elem γ elt.

  #[local] Definition element_model class descr elt : iProp Σ :=
    elt.[class_] ↦ #class ∗
    elt.[seen] ↦ #false.
  #[local] Instance : CustomIpatFormat "element_model" :=
    "(
      Helt{}_class{_{suff}} &
      Helt{}_seen{_{suff}}
    )".
  #[local] Definition descriptor_model class descrs descr : iProp Σ :=
    ∃ first last prev_descr prev next_descr next,
    ⌜head descr.(descriptor_elts) = Some first⌝ ∗
    ⌜list.last descr.(descriptor_elts) = Some last⌝ ∗
    ⌜descrs !! descr.(descriptor_prev) = Some prev_descr⌝ ∗
    ⌜list.last prev_descr.(descriptor_elts) = Some prev⌝ ∗
    ⌜descrs !! descr.(descriptor_next) = Some next_descr⌝ ∗
    ⌜head next_descr.(descriptor_elts) = Some next⌝ ∗
    class.[first] ↦ #first ∗
    class.[last] ↦ #last ∗
    class.[len] ↦ #(length descr.(descriptor_elts)) ∗
    class.[split] ↦ #first ∗
    class.[split_len] ↦ #0 ∗
    xdlchain #prev descr.(descriptor_elts) #next ∗
    [∗ list] elt ∈ descr.(descriptor_elts),
      element_model class descr elt.
  #[local] Instance : CustomIpatFormat "descriptor_model" :=
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
  #[local] Definition model' γ descrs : iProp Σ :=
    elements_auth γ ([∪ map] descr ∈ descrs, list_to_set descr.(descriptor_elts)) ∗
    [∗ map] class ↦ descr ∈ descrs,
      descriptor_model class descrs descr.
  #[local] Instance : CustomIpatFormat "model'" :=
    "(
      Helts_auth &
      Hdescrs
    )".
  Definition partition_model γ part : iProp Σ :=
    ∃ descrs,
    ⌜part = map_to_set (λ _, list_to_set ∘ descriptor_elts) descrs⌝ ∗
    model' γ descrs.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %descrs &
      -> &
      Hmodel
    )".

  Definition partition_element γ elt v : iProp Σ :=
    elements_elem γ elt ∗
    elt.[data] ↦□ v.
  #[local] Instance : CustomIpatFormat "element" :=
    "(
      Helts_elem{}{_{suff}} &
      Helt{}_data{_{suff}}
    )".

  #[global] Instance partition_model_timeless γ part :
    Timeless (partition_model γ part).
  Proof.
    apply _.
  Qed.
  #[global] Instance partition_element_timeless γ elt v :
    Timeless (partition_element γ elt v).
  Proof.
    apply _.
  Qed.
  #[global] Instance partition_element_persistent γ elt v :
    Persistent (partition_element γ elt v).
  Proof.
    apply _.
  Qed.

  #[local] Lemma elements_alloc :
    ⊢ |==>
      ∃ γ,
      elements_auth γ ∅.
  Proof.
    apply mono_set_alloc.
  Qed.
  #[local] Lemma elements_elem_valid γ elts elt :
    elements_auth γ elts -∗
    elements_elem γ elt -∗
    ⌜elt ∈ elts⌝.
  Proof.
    apply mono_set_elem_valid.
  Qed.
  #[local] Lemma elements_insert {γ elts} elt :
    elements_auth γ elts ⊢ |==>
      elements_auth γ ({[elt]} ∪ elts) ∗
      elements_elem γ elt.
  Proof.
    apply mono_set_insert'.
  Qed.

  #[local] Lemma model_disjoint' {γ descrs} class1 descr1 class2 descr2 elt :
    descrs !! class1 = Some descr1 →
    elt ∈ descr1.(descriptor_elts) →
    descrs !! class2 = Some descr2 →
    elt ∈ descr2.(descriptor_elts) →
    model' γ descrs ⊢
      ⌜class1 = class2⌝ ∗
      ⌜descr1 = descr2⌝.
  Proof.
    iIntros (Hdescrs_lookup_1 (i1 & Helts1_lookup)%elem_of_list_lookup Hdescrs_lookup_2 (i2 & Helts2_lookup)%elem_of_list_lookup) "(:model')".
    destruct (decide (class1 = class2)) as [<- | Hneq]; first naive_solver.
    iDestruct (big_sepM_delete _ _ class1 with "Hdescrs") as "((:descriptor_model =1) & Hdescrs)"; first done.
    iDestruct (big_sepM_lookup _ _ class2 with "Hdescrs") as "(:descriptor_model =2)".
    { rewrite lookup_delete_ne //. }
    iDestruct (big_sepL_lookup with "Helts1") as "(:element_model suff=1)"; first done.
    iDestruct (big_sepL_lookup with "Helts2") as "(:element_model suff=2)"; first done.
    iDestruct (pointsto_exclusive with "Helt_class_1 Helt_class_2") as %[].
  Qed.
  #[local] Lemma model_disjoint'' {γ descrs} class descr elt :
    descrs !! class = Some descr →
    elt ∈ descr.(descriptor_elts) →
    model' γ descrs ⊢
    ⌜ ∀ class' descr',
      descrs !! class' = Some descr' →
      elt ∈ descr'.(descriptor_elts) →
        class' = class ∧
        descr' = descr
    ⌝.
  Proof.
    iIntros "%Hdescrs_lookup %Helts_elem Hmodel %class' %descr' %Hdescrs_lookup' %Helts_elem'".
    iDestruct (model_disjoint' class _ class' with "Hmodel") as %(<- & <-); done.
  Qed.
  #[local] Lemma partition_element_valid' γ descrs elt v :
    model' γ descrs -∗
    partition_element γ elt v -∗
      ∃ class descr,
      ⌜descrs !! class = Some descr⌝ ∗
      ⌜elt ∈ descr.(descriptor_elts)⌝ ∗
      ⌜ ∀ class' descr',
        descrs !! class' = Some descr' →
        elt ∈ descr'.(descriptor_elts) →
          class' = class ∧
          descr' = descr
      ⌝.
  Proof.
    iIntros "(:model') (:element)".
    iDestruct (elements_elem_valid with "Helts_auth Helts_elem") as %(class & descr & Hdescrs_lookup & Helts_elem%elem_of_list_to_set)%big_unionM_elem_of.
    iStep 2.
    iApply (model_disjoint'' with "[$]"); done.
  Qed.
  #[local] Lemma model_NoDup {γ descrs} class descr :
    descrs !! class = Some descr →
    model' γ descrs ⊢
    ⌜NoDup descr.(descriptor_elts)⌝.
  Proof.
    iIntros "%Hdescrs_lookup (:model')".
    iDestruct (big_sepM_lookup with "Hdescrs") as "(:descriptor_model)"; first done.
    iApply (xdlchain_NoDup with "Hchain").
  Qed.

  Lemma partition_model_empty :
    ⊢ |==>
      ∃ γ,
      partition_model γ ∅.
  Proof.
    iMod elements_alloc as "(%γ & Helts_auth)".
    iExists γ, ∅. rewrite /model' !big_opM_empty. iSteps.
  Qed.
  Lemma partition_model_non_empty {γ part} cl :
    cl ∈ part →
    partition_model γ part ⊢
    ⌜cl ≠ ∅⌝.
  Proof.
    iIntros "%Hcl (:model)".
    iDestruct "Hmodel" as "(:model')".
    apply elem_of_map_to_set in Hcl as (class & descr & Hdescrs_lookup & <-).
    iDestruct (big_sepM_lookup with "Hdescrs") as "(:descriptor_model)"; first done.
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
    iIntros (Hpart_elem_1 Hcl1_elem Hpart_elem_2 Hcl2_elem) "(:model)".
    apply elem_of_map_to_set in Hpart_elem_1 as (class1 & descr1 & Hdescrs_lookup_1 & <-).
    apply elem_of_list_to_set in Hcl1_elem.
    apply elem_of_map_to_set in Hpart_elem_2 as (class2 & descr2 & Hdescrs_lookup_2 & <-).
    apply elem_of_list_to_set in Hcl2_elem.
    iDestruct (model_disjoint' class1 descr1 class2 descr2 with "Hmodel") as %(<- & <-); done.
  Qed.

  Lemma partition_element_valid γ part elt v :
    partition_model γ part -∗
    partition_element γ elt v -∗
      ∃ cl,
      ⌜cl ∈ part⌝ ∗
      ⌜elt ∈ cl⌝.
  Proof.
    iIntros "(:model) Helt".
    iDestruct (partition_element_valid' with "Hmodel Helt") as "(%class & %descr & %Hdescrs_lookup & %Helts_elem & _)".
    iExists (list_to_set descr.(descriptor_elts)). iSplit; iPureIntro.
    - apply elem_of_map_to_set. naive_solver.
    - rewrite elem_of_list_to_set //.
  Qed.
  Lemma partition_element_agree γ elt v1 v2 :
    partition_element γ elt v1 -∗
    partition_element γ elt v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    iIntros "(:element suff=1) (:element suff=2)".
    iApply (pointsto_agree with "Helt_data_1 Helt_data_2").
  Qed.

  #[local] Lemma partition_dllist_create_spec v v_class :
    {{{
      True
    }}}
      partition_dllist_create v v_class
    {{{ elt,
      RET #elt;
      elt.[prev] ↦ #elt ∗
      elt.[next] ↦ #elt ∗
      elt.[data] ↦□ v ∗
      elt.[class_] ↦ v_class ∗
      elt.[seen] ↦ #false
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma partition_get_class_spec γ descrs elt v :
    {{{
      model' γ descrs ∗
      partition_element γ elt v
    }}}
      (#elt).{class_}
    {{{ class descr,
      RET #class;
      model' γ descrs ∗
      ⌜descrs !! class = Some descr⌝ ∗
      ⌜elt ∈ descr.(descriptor_elts)⌝ ∗
      ⌜ ∀ class' descr',
        descrs !! class' = Some descr' →
        elt ∈ descr'.(descriptor_elts) →
          class' = class ∧
          descr' = descr
      ⌝
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Helt) HΦ".
    iDestruct (partition_element_valid' with "Hmodel Helt") as "(%class & %descr & %Hdescrs_lookup & %Helts_elem & %Helt)".
    iDestruct "Hmodel" as "(:model')".
    iDestruct (big_sepM_lookup_acc with "Hdescrs") as "((:descriptor_model) & Hdescrs)"; first done.
    odestruct elem_of_list_lookup_1 as (i & Helts_lookup); first done.
    iDestruct (big_sepL_lookup_acc with "Helts") as "((:element_model) & Helts)"; first done.
    wp_load.
    iDestruct ("Helts" with "[$]") as "Helts".
    iDestruct ("Hdescrs" with "[- Helts_auth Helt HΦ]") as "Hdescrs"; first iSteps.
    iSteps; naive_solver.
  Qed.

  Lemma partition_make_spec γ part v :
    {{{
      partition_model γ part
    }}}
      partition_make v
    {{{ elt,
      RET #elt;
      partition_model γ (part ∪ {[{[elt]}]}) ∗
      partition_element γ elt v
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    iDestruct "Hmodel" as "(:model')".

    wp_rec.
    wp_apply (partition_dllist_create_spec with "[//]") as (elt) "(Helt_prev & Helt_next & #Helt_data & Helt_class & Helt_seen)".
    wp_block class as "(Hclass_first & Hclass_last & Hclass_len & Hclass_split & Hclass_split_len & _)".
    wp_store. wp_pures.

    iAssert ⌜descrs !! class = None⌝%I as %Hclass.
    { rewrite -eq_None_ne_Some. iIntros "%descr %Hdescrs_lookup".
      iDestruct (big_sepM_lookup with "Hdescrs") as "(:descriptor_model =')"; first done.
      iApply (pointsto_exclusive with "Hclass_first Hclass'_first").
    }

    pose descr := {|
      descriptor_elts := [elt] ;
      descriptor_prev := class ;
      descriptor_next := class ;
    |}.
    iMod (elements_insert elt with "Helts_auth") as "(Helts_auth & #Helts_elem)".

    iApply "HΦ".
    iModIntro. iSplitL; last iSteps.
    iExists (<[class := descr]> descrs). iSplit.
    { iPureIntro.
      rewrite map_to_set_insert_L //= right_id_L. set_solver.
    }
    iSplitL "Helts_auth".
    { iApply (mono_set_auth_proper with "Helts_auth").
      rewrite big_opM_insert //. set_solver.
    }
    iApply (big_sepM_insert_2 with "[- Hdescrs] [Hdescrs]").
    - iExists elt, elt, descr, elt, descr, elt.
      rewrite xdlchain_singleton lookup_insert //. iSteps.
    - iApply (big_sepM_impl with "Hdescrs"). iIntros "!> %class' %descr' %Hdescrs_lookup' (:descriptor_model)".
      iExists first, last, prev_descr, prev, next_descr, next.
      rewrite !lookup_insert_ne //; [naive_solver.. |]. iSteps.
  Qed.

  Lemma partition_make_same_class_spec γ part elt v v' :
    {{{
      partition_model γ part ∗
      partition_element γ elt v
    }}}
      partition_make_same_class #elt v'
    {{{ elt' part',
      RET #elt';
      partition_model γ part' ∗
      partition_element γ elt' v' ∗
      ⌜ ∃ part'' cl,
        elt ∈ cl ∧
        part = part'' ∪ {[cl]} ∧
        part' = part'' ∪ {[cl ∪ {[elt']}]}
      ⌝
    }}}.
  Proof.
    iIntros "%Φ ((:model) & #Helt) HΦ".

    wp_rec.
    wp_smart_apply (partition_get_class_spec with "[$Hmodel $Helt]") as (class descr) "(Hmodel & %Hdescrs_lookup & %Helts_elem & %Helt)".
    wp_smart_apply (partition_dllist_create_spec with "[//]") as (elt') "(Helt'_prev & Helt'_next & #Helt'_data & Helt'_class & Helt'_seen)".
  Admitted.

  Lemma partition_get_spec γ elt v :
    {{{
      partition_element γ elt v
    }}}
      partition_get #elt
    {{{
      RET v;
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma partition_equal_spec γ elt1 v1 elt2 v2 :
    {{{
      True
    }}}
      partition_equal #elt1 #elt2
    {{{
      RET #(bool_decide (elt1 = elt2));
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma partition_equiv_spec γ part elt1 v1 elt2 v2 :
    {{{
      partition_model γ part ∗
      partition_element γ elt1 v1 ∗
      partition_element γ elt2 v2
    }}}
      partition_equiv #elt1 #elt2
    {{{ b,
      RET #b;
      partition_model γ part ∗
      ⌜ ∀ cl1 cl2,
        cl1 ∈ part →
        elt1 ∈ cl1 →
        cl2 ∈ part →
        elt2 ∈ cl2 →
        if b then cl1 = cl2 else cl1 ≠ cl2
      ⌝
    }}}.
  Proof.
    iIntros "%Φ ((:model) & #Helt1 & #Helt2) HΦ".
    wp_rec.
    wp_smart_apply (partition_get_class_spec with "[$Hmodel $Helt2]") as (class2 descr2) "(Hmodel & %Hdescrs_lookup_2 & %Helts2_elem & %Helt2)".
    wp_apply (partition_get_class_spec with "[$Hmodel $Helt1]") as (class1 descr1) "(Hmodel & %Hdescrs_lookup_1 & %Helts1_elem & %Helt1)".
    wp_pures. case_bool_decide as Hcase.
    - subst class2.
      iSteps as (cl1 cl2 (class1' & descr1' & Hdescrs_lookup_1' & <-)%elem_of_map_to_set Helts1'_elem (class2' & descr2' & Hdescrs_lookup_2' & <-)%elem_of_map_to_set Helts2'_elem) / --silent. iPureIntro.
      rewrite !elem_of_list_to_set in Helts1'_elem Helts2'_elem.
      edestruct (Helt1 class1' descr1') as (-> & ->); [done.. |].
      edestruct (Helt2 class2' descr2') as (-> & ->); [done.. |].
      congruence.
    - iSteps as (cl Helts_elem_1 (class & descr & Hdescrs_lookup & <-)%elem_of_map_to_set _ Helts_elem_2) / --silent. iPureIntro.
      rewrite !elem_of_list_to_set in Helts_elem_1 Helts_elem_2.
      edestruct (Helt1 class descr) as (<- & <-); [done.. |].
      edestruct (Helt2 class descr) as (<- & <-); [done.. |].
      congruence.
  Qed.

  Lemma partition_repr_spec γ part elt v :
    {{{
      partition_model γ part ∗
      partition_element γ elt v
    }}}
      partition_repr #elt
    {{{ elt',
      RET #elt';
      partition_model γ part ∗
      ⌜ ∀ cl,
        cl ∈ part →
        elt ∈ cl ↔ elt' ∈ cl
      ⌝
    }}}.
  Proof.
    iIntros "%Φ ((:model) & #Helt) HΦ".
    wp_rec.
    wp_apply (partition_get_class_spec with "[$Hmodel $Helt]") as (class descr) "(Hmodel & %Hdescrs_lookup & %Helts_elem & %Helt)".
    iDestruct "Hmodel" as "(:model')".
    iDestruct (big_sepM_lookup_acc with "Hdescrs") as "((:descriptor_model) & Hdescrs)"; first done.
    wp_load.
    iDestruct ("Hdescrs" with "[- Helts_auth Helt HΦ]") as "Hdescrs"; first iSteps.
    apply head_Some_elem_of in Hfirst.
    iDestruct (model_disjoint'' class descr first with "[$]") as %?; [done.. |].
    iSteps as (cl (class' & descr' & Hdescrs_lookup' & <-)%elem_of_map_to_set) / --silent. iPureIntro.
    rewrite !elem_of_list_to_set. naive_solver.
  Qed.

  Lemma partition_cardinal_spec γ part elt v :
    {{{
      partition_model γ part ∗
      partition_element γ elt v
    }}}
      partition_cardinal #elt
    {{{ sz,
      RET #sz;
      partition_model γ part ∗
      ⌜ ∀ cl,
        cl ∈ part →
        elt ∈ cl →
        size cl = sz
      ⌝
    }}}.
  Proof.
    iIntros "%Φ ((:model) & #Helt) HΦ".
    wp_rec.
    wp_apply (partition_get_class_spec with "[$Hmodel $Helt]") as (class descr) "(Hmodel & %Hdescrs_lookup & %Helts_elem & %Helt)".
    iDestruct (model_NoDup with "Hmodel") as %?; first done.
    iDestruct "Hmodel" as "(:model')".
    iDestruct (big_sepM_lookup_acc with "Hdescrs") as "((:descriptor_model) & Hdescrs)"; first done.
    wp_load.
    iDestruct ("Hdescrs" with "[- Helts_auth Helt HΦ]") as "Hdescrs"; first iSteps.
    iSteps as (cl (class' & descr' & Hdescrs_lookup' & <-)%elem_of_map_to_set Helts'_elem%elem_of_list_to_set) / --silent. iPureIntro.
    edestruct (Helt class' descr') as (-> & ->); [done.. |].
    rewrite size_list_to_set //.
  Qed.

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

#[global] Opaque partition_make.
#[global] Opaque partition_make_same_class.
#[global] Opaque partition_get.
#[global] Opaque partition_equal.
#[global] Opaque partition_equiv.
#[global] Opaque partition_repr.
#[global] Opaque partition_cardinal.
#[global] Opaque partition_refine.

#[global] Opaque partition_model.
#[global] Opaque partition_element.
