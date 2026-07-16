Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.common.gset.
Require Import zoo.iris.algebra.big_op.
Require Import zoo.iris.base_logic.lib.mono_gset.
Require Import zoo.base.
Require Import zoo_std.list.
Require Import zoo_std.xdlchain.
Require Import zoo_partition.partition__types.
Require Export zoo_partition.partition__code.
Require Import zoo.options.

Implicit Types b : bool.
Implicit Types sz : nat.
Implicit Types elt first last split class : location.
Implicit Types v v_elts : val.
Implicit Types cl : gset location.
Implicit Types part : gset (gset location).

Record descriptor :=
  { descriptor۰elts : list location
  ; descriptor۰prev : location
  ; descriptor۰next : location
  }.

#[local] Instance descriptor𑁒inhabited : Inhabited descriptor :=
  populate
    {|descriptor۰elts := inhabitant
    ; descriptor۰prev := inhabitant
    ; descriptor۰next := inhabitant
    |}.
#[local] Instance descriptor𑁒eq_dec : EqDecision descriptor :=
  ltac:(solve_decision).
#[local] Instance descriptor𑁒countable :
  Countable descriptor.
Proof.
  solve_countable.
Qed.

Implicit Types descr : descriptor.
Implicit Types descrs : gmap location descriptor.

Class PartitionG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] partition۰G۰elts۰G :: MonoGsetG Σ location
  }.

Definition partition۰Σ :=
  #[mono_gset۰Σ location
  ].
#[global] Instance subG𑁒partition۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG partition۰Σ Σ →
  PartitionG Σ.
Proof.
  solve_inG.
Qed.

Section partition۰G.
  Context `{partition۰G : PartitionG Σ}.

  #[local] Definition metadata :=
    gname.
  Implicit Types γ : metadata.

  #[local] Definition elements۰auth γ elts :=
    mono_gset۰auth γ (DfracOwn 1) elts.
  #[local] Definition elements۰elem γ elt :=
    mono_gset۰elem γ elt.

  #[local] Definition element۰model class descr elt : iProp Σ :=
    elt.[class_] ↦ #class ∗
    elt.[seen] ↦ false.
  #[local] Instance : CustomIpat "element۰model" :=
    " ( Helt{}_class{_{suff}}
      & Helt{}_seen{_{suff}}
      )
    ".
  #[local] Definition descriptor۰model class descrs descr : iProp Σ :=
    ∃ first last prev_descr prev next_descr next,
    ⌜head descr.(descriptor۰elts) = Some first⌝ ∗
    ⌜list.last descr.(descriptor۰elts) = Some last⌝ ∗
    ⌜descrs !! descr.(descriptor۰prev) = Some prev_descr⌝ ∗
    ⌜list.last prev_descr.(descriptor۰elts) = Some prev⌝ ∗
    ⌜descrs !! descr.(descriptor۰next) = Some next_descr⌝ ∗
    ⌜head next_descr.(descriptor۰elts) = Some next⌝ ∗
    class.[first] ↦ #first ∗
    class.[last] ↦ #last ∗
    class.[len] ↦ #(length descr.(descriptor۰elts)) ∗
    class.[split] ↦ #first ∗
    class.[split_len] ↦ 0 ∗
    xdlchain #prev descr.(descriptor۰elts) #next ∗
    [∗ list] elt ∈ descr.(descriptor۰elts),
      element۰model class descr elt.
  #[local] Instance : CustomIpat "descriptor۰model" :=
    " ( %first{}
      & %last{}
      & %prev{}_descr
      & %prev{}
      & %next{}_descr
      & %next{}
      & %Hfirst{}
      & %Hlast{}
      & %Hdescrs{}_elem_prev
      & %Hprev{}
      & %Hdescrs{}_elem_next
      & %Hnext{}
      & Hclass{}_first
      & Hclass{}_last
      & Hclass{}_len
      & Hclass{}_split
      & Hclass{}_split_len
      & Hchain{}
      & Helts{}
      )
    ".
  #[local] Definition model' γ descrs : iProp Σ :=
    elements۰auth γ ([∪ map] descr ∈ descrs, list_to_set descr.(descriptor۰elts)) ∗
    [∗ map] class ↦ descr ∈ descrs,
      descriptor۰model class descrs descr.
  #[local] Instance : CustomIpat "model'" :=
    " ( Helts_auth
      & Hdescrs
      )
    ".
  Definition partition۰model γ part : iProp Σ :=
    ∃ descrs,
    ⌜part = map_to_set (λ _, list_to_set ∘ descriptor۰elts) descrs⌝ ∗
    model' γ descrs.
  #[local] Instance : CustomIpat "model" :=
    " ( %descrs
      & ->
      & Hmodel
      )
    ".

  Definition partition۰element γ elt v : iProp Σ :=
    elements۰elem γ elt ∗
    elt.[data] ↦□ v.
  #[local] Instance : CustomIpat "element" :=
    " ( Helts_elem{}{_{suff}}
      & Helt{}_data{_{suff}}
      )
    ".

  #[global] Instance partition۰model𑁒timeless γ part :
    Timeless (partition۰model γ part).
  Proof.
    apply _.
  Qed.
  #[global] Instance partition۰element𑁒timeless γ elt v :
    Timeless (partition۰element γ elt v).
  Proof.
    apply _.
  Qed.

  #[global] Instance partition۰element𑁒persistent γ elt v :
    Persistent (partition۰element γ elt v).
  Proof.
    apply _.
  Qed.

  #[local] Lemma elements𑁒alloc :
    ⊢ |==>
      ∃ γ,
      elements۰auth γ ∅.
  Proof.
    apply mono_gset𑁒alloc.
  Qed.
  #[local] Lemma elements۰elem𑁒valid γ elts elt :
    elements۰auth γ elts -∗
    elements۰elem γ elt -∗
    ⌜elt ∈ elts⌝.
  Proof.
    apply mono_gset۰elem𑁒valid.
  Qed.
  #[local] Lemma elements𑁒insert {γ elts} elt :
    elements۰auth γ elts ⊢ |==>
      elements۰auth γ ({[elt]} ∪ elts) ∗
      elements۰elem γ elt.
  Proof.
    apply mono_gset𑁒insert'.
  Qed.

  #[local] Lemma model𑁒disjoint' {γ descrs} class1 descr1 class2 descr2 elt :
    descrs !! class1 = Some descr1 →
    elt ∈ descr1.(descriptor۰elts) →
    descrs !! class2 = Some descr2 →
    elt ∈ descr2.(descriptor۰elts) →
    model' γ descrs ⊢
      ⌜class1 = class2⌝ ∗
      ⌜descr1 = descr2⌝.
  Proof.
    iIntros (Hdescrs_lookup_1 (i1 & Helts1_lookup)%list_elem_of_lookup Hdescrs_lookup_2 (i2 & Helts2_lookup)%list_elem_of_lookup) "(:model')".
    destruct_decide (class1 = class2) as <- | Hneq; first naive_solver.
    iDestruct (big_sepM_delete _ _ class1 with "Hdescrs") as "((:descriptor۰model =1) & Hdescrs)"; first done.
    iDestruct (big_sepM_lookup _ _ class2 with "Hdescrs") as "(:descriptor۰model =2)".
    { rewrite lookup_delete_ne //. }
    iDestruct (big_sepL_lookup with "Helts1") as "(:element۰model suff=1)"; first done.
    iDestruct (big_sepL_lookup with "Helts2") as "(:element۰model suff=2)"; first done.
    iDestruct (pointsto𑁒exclusive with "Helt_class_1 Helt_class_2") as %[].
  Qed.
  #[local] Lemma model𑁒disjoint'' {γ descrs} class descr elt :
    descrs !! class = Some descr →
    elt ∈ descr.(descriptor۰elts) →
    model' γ descrs ⊢
    ⌜ ∀ class' descr',
      descrs !! class' = Some descr' →
      elt ∈ descr'.(descriptor۰elts) →
        class' = class ∧
        descr' = descr
    ⌝.
  Proof.
    iIntros "%Hdescrs_lookup %Helts_elem Hmodel %class' %descr' %Hdescrs_lookup' %Helts_elem'".
    iDestruct (model𑁒disjoint' class _ class' with "Hmodel") as %(<- & <-); done.
  Qed.
  #[local] Lemma partition۰element𑁒valid' γ descrs elt v :
    model' γ descrs -∗
    partition۰element γ elt v -∗
      ∃ class descr,
      ⌜descrs !! class = Some descr⌝ ∗
      ⌜elt ∈ descr.(descriptor۰elts)⌝ ∗
      ⌜ ∀ class' descr',
        descrs !! class' = Some descr' →
        elt ∈ descr'.(descriptor۰elts) →
          class' = class ∧
          descr' = descr
      ⌝.
  Proof.
    iIntros "(:model') (:element)".
    iDestruct (elements۰elem𑁒valid with "Helts_auth Helts_elem") as %(class & descr & Hdescrs_lookup & Helts_elem%elem_of_list_to_set)%big_unionM𑁒elem_of.
    iStep 2.
    iApply (model𑁒disjoint'' with "[$]"); done.
  Qed.
  #[local] Lemma model𑁒NoDup {γ descrs} class descr :
    descrs !! class = Some descr →
    model' γ descrs ⊢
    ⌜NoDup descr.(descriptor۰elts)⌝.
  Proof.
    iIntros "%Hdescrs_lookup (:model')".
    iDestruct (big_sepM_lookup with "Hdescrs") as "(:descriptor۰model)"; first done.
    iApply (xdlchain𑁒NoDup with "Hchain").
  Qed.

  Lemma partition۰model𑁒empty :
    ⊢ |==>
      ∃ γ,
      partition۰model γ ∅.
  Proof.
    iMod elements𑁒alloc as "(%γ & Helts_auth)".
    iExists γ, ∅. rewrite /model' !big_opM_empty. iSteps.
  Qed.
  Lemma partition۰model𑁒non_empty {γ part} cl :
    cl ∈ part →
    partition۰model γ part ⊢
    ⌜cl ≠ ∅⌝.
  Proof.
    iIntros "%Hcl (:model)".
    iDestruct "Hmodel" as "(:model')".
    apply elem_of_map_to_set in Hcl as (class & descr & Hdescrs_lookup & <-).
    iDestruct (big_sepM_lookup with "Hdescrs") as "(:descriptor۰model)"; first done.
    iPureIntro. eapply list_to_set𑁒not_empty, hd_error_some_nil. done.
  Qed.
  Lemma partition۰model𑁒disjoint {γ part} elt cl1 cl2 :
    cl1 ∈ part →
    elt ∈ cl1 →
    cl2 ∈ part →
    elt ∈ cl2 →
    partition۰model γ part ⊢
    ⌜cl1 = cl2⌝.
  Proof.
    iIntros (Hpart_elem_1 Hcl1_elem Hpart_elem_2 Hcl2_elem) "(:model)".
    apply elem_of_map_to_set in Hpart_elem_1 as (class1 & descr1 & Hdescrs_lookup_1 & <-).
    apply elem_of_list_to_set in Hcl1_elem.
    apply elem_of_map_to_set in Hpart_elem_2 as (class2 & descr2 & Hdescrs_lookup_2 & <-).
    apply elem_of_list_to_set in Hcl2_elem.
    iDestruct (model𑁒disjoint' class1 descr1 class2 descr2 with "Hmodel") as %(<- & <-); done.
  Qed.

  Lemma partition۰element𑁒valid γ part elt v :
    partition۰model γ part -∗
    partition۰element γ elt v -∗
      ∃ cl,
      ⌜cl ∈ part⌝ ∗
      ⌜elt ∈ cl⌝.
  Proof.
    iIntros "(:model) Helt".
    iDestruct (partition۰element𑁒valid' with "Hmodel Helt") as "(%class & %descr & %Hdescrs_lookup & %Helts_elem & _)".
    iExists (list_to_set descr.(descriptor۰elts)). iSplit; iPureIntro.
    - apply elem_of_map_to_set. naive_solver.
    - rewrite elem_of_list_to_set //.
  Qed.
  Lemma partition۰element𑁒agree γ elt v1 v2 :
    partition۰element γ elt v1 -∗
    partition۰element γ elt v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    iIntros "(:element suff=1) (:element suff=2)".
    iApply (pointsto𑁒agree with "Helt_data_1 Helt_data_2").
  Qed.

  #[local] Lemma partition٠dllist_create𑁒spec v v_class :
    {{{
      True
    }}}
      partition٠dllist_create v v_class
    {{{
      elt
    , RET #elt;
      elt.[prev] ↦ #elt ∗
      elt.[next] ↦ #elt ∗
      elt.[data] ↦□ v ∗
      elt.[class_] ↦ v_class ∗
      elt.[seen] ↦ false
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma partition٠get_class𑁒spec γ descrs elt v :
    {{{
      model' γ descrs ∗
      partition۰element γ elt v
    }}}
      (#elt).{class_}
    {{{
      class descr
    , RET #class;
      model' γ descrs ∗
      ⌜descrs !! class = Some descr⌝ ∗
      ⌜elt ∈ descr.(descriptor۰elts)⌝ ∗
      ⌜ ∀ class' descr',
        descrs !! class' = Some descr' →
        elt ∈ descr'.(descriptor۰elts) →
          class' = class ∧
          descr' = descr
      ⌝
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Helt) HΦ".
    iDestruct (partition۰element𑁒valid' with "Hmodel Helt") as "(%class & %descr & %Hdescrs_lookup & %Helts_elem & %Helt)".
    iDestruct "Hmodel" as "(:model')".
    iDestruct (big_sepM_lookup_acc with "Hdescrs") as "((:descriptor۰model) & Hdescrs)"; first done.
    odestruct list_elem_of_lookup_1 as (i & Helts_lookup); first done.
    iDestruct (big_sepL_lookup_acc with "Helts") as "((:element۰model) & Helts)"; first done.
    wp۰load.
    iDestruct ("Helts" with "[$]") as "Helts".
    iDestruct ("Hdescrs" with "[- Helts_auth Helt HΦ]") as "Hdescrs"; first iSteps.
    iSteps; naive_solver.
  Qed.

  Lemma partition٠make𑁒spec γ part v :
    {{{
      partition۰model γ part
    }}}
      partition٠make v
    {{{
      elt
    , RET #elt;
      partition۰model γ (part ∪ {[{[elt]}]}) ∗
      partition۰element γ elt v
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    iDestruct "Hmodel" as "(:model')".

    wp۰rec.
    wp۰apply (partition٠dllist_create𑁒spec with "[//]") as (elt) "(Helt_prev & Helt_next & #Helt_data & Helt_class & Helt_seen)".
    wp۰block class as "(Hclass_first & Hclass_last & Hclass_len & Hclass_split & Hclass_split_len & _)".
    wp۰store. wp۰pures.

    iAssert ⌜descrs !! class = None⌝%I as %Hclass.
    { rewrite -eq_None_ne_Some. iIntros "%descr %Hdescrs_lookup".
      iDestruct (big_sepM_lookup with "Hdescrs") as "(:descriptor۰model =')"; first done.
      iApply (pointsto𑁒exclusive with "Hclass_first Hclass'_first").
    }

    pose descr :=
      {|descriptor۰elts := [elt]
      ; descriptor۰prev := class
      ; descriptor۰next := class
      |}.
    iMod (elements𑁒insert elt with "Helts_auth") as "(Helts_auth & #Helts_elem)".

    iApply "HΦ".
    iModIntro. iSplitL; last iSteps.
    iExists (<[class := descr]> descrs). iSplit.
    { iPureIntro.
      rewrite map_to_set_insert_L //= right_id_L. set_solver.
    }
    iSplitL "Helts_auth".
    { iApply (mono_gset۰auth𑁒proper with "Helts_auth").
      rewrite big_opM_insert //. set_solver.
    }
    iApply (big_sepM_insert_2 with "[- Hdescrs] [Hdescrs]").
    - iExists elt, elt, descr, elt, descr, elt.
      rewrite xdlchain𑁒singleton lookup_insert_eq //. iSteps.
    - iApply (big_sepM_impl with "Hdescrs"). iIntros "!> %class' %descr' %Hdescrs_lookup' (:descriptor۰model)".
      iExists first, last, prev_descr, prev, next_descr, next.
      rewrite !lookup_insert_ne //; [naive_solver.. |]. iSteps.
  Qed.

  Lemma partition٠make_same_class𑁒spec γ part elt v v' :
    {{{
      partition۰model γ part ∗
      partition۰element γ elt v
    }}}
      partition٠make_same_class #elt v'
    {{{
      elt' part'
    , RET #elt';
      partition۰model γ part' ∗
      partition۰element γ elt' v' ∗
      ⌜ ∃ part'' cl,
        elt ∈ cl ∧
        part = part'' ∪ {[cl]} ∧
        part' = part'' ∪ {[cl ∪ {[elt']}]}
      ⌝
    }}}.
  Proof.
    iIntros "%Φ ((:model) & #Helt) HΦ".

    wp۰rec.
    wp۰apply+ (partition٠get_class𑁒spec with "[$Hmodel $Helt]") as (class descr) "(Hmodel & %Hdescrs_lookup & %Helts_elem & %Helt)".
    wp۰apply+ (partition٠dllist_create𑁒spec with "[//]") as (elt') "(Helt'_prev & Helt'_next & #Helt'_data & Helt'_class & Helt'_seen)".
  Admitted.

  Lemma partition٠get𑁒spec γ elt v :
    {{{
      partition۰element γ elt v
    }}}
      partition٠get #elt
    {{{
      RET v;
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma partition٠equal𑁒spec γ elt1 v1 elt2 v2 :
    {{{
      True
    }}}
      partition٠equal #elt1 #elt2
    {{{
      RET #(bool_decide (elt1 = elt2));
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma partition٠equiv𑁒spec γ part elt1 v1 elt2 v2 :
    {{{
      partition۰model γ part ∗
      partition۰element γ elt1 v1 ∗
      partition۰element γ elt2 v2
    }}}
      partition٠equiv #elt1 #elt2
    {{{
      b
    , RET #b;
      partition۰model γ part ∗
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
    wp۰rec.
    wp۰apply+ (partition٠get_class𑁒spec with "[$Hmodel $Helt2]") as (class2 descr2) "(Hmodel & %Hdescrs_lookup_2 & %Helts2_elem & %Helt2)".
    wp۰apply (partition٠get_class𑁒spec with "[$Hmodel $Helt1]") as (class1 descr1) "(Hmodel & %Hdescrs_lookup_1 & %Helts1_elem & %Helt1)".
    wp۰pures. case_bool_decide as Hcase.
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

  Lemma partition٠repr𑁒spec γ part elt v :
    {{{
      partition۰model γ part ∗
      partition۰element γ elt v
    }}}
      partition٠repr #elt
    {{{
      elt'
    , RET #elt';
      partition۰model γ part ∗
      ⌜ ∀ cl,
        cl ∈ part →
        elt ∈ cl ↔ elt' ∈ cl
      ⌝
    }}}.
  Proof.
    iIntros "%Φ ((:model) & #Helt) HΦ".
    wp۰rec.
    wp۰apply (partition٠get_class𑁒spec with "[$Hmodel $Helt]") as (class descr) "(Hmodel & %Hdescrs_lookup & %Helts_elem & %Helt)".
    iDestruct "Hmodel" as "(:model')".
    iDestruct (big_sepM_lookup_acc with "Hdescrs") as "((:descriptor۰model) & Hdescrs)"; first done.
    wp۰load.
    iDestruct ("Hdescrs" with "[- Helts_auth Helt HΦ]") as "Hdescrs"; first iSteps.
    apply head_Some_elem_of in Hfirst.
    iDestruct (model𑁒disjoint'' class descr first with "[$]") as %?; [done.. |].
    iSteps as (cl (class' & descr' & Hdescrs_lookup' & <-)%elem_of_map_to_set) / --silent. iPureIntro.
    rewrite !elem_of_list_to_set. naive_solver.
  Qed.

  Lemma partition٠cardinal𑁒spec γ part elt v :
    {{{
      partition۰model γ part ∗
      partition۰element γ elt v
    }}}
      partition٠cardinal #elt
    {{{
      sz
    , RET #sz;
      partition۰model γ part ∗
      ⌜ ∀ cl,
        cl ∈ part →
        elt ∈ cl →
        size cl = sz
      ⌝
    }}}.
  Proof.
    iIntros "%Φ ((:model) & #Helt) HΦ".
    wp۰rec.
    wp۰apply (partition٠get_class𑁒spec with "[$Hmodel $Helt]") as (class descr) "(Hmodel & %Hdescrs_lookup & %Helts_elem & %Helt)".
    iDestruct (model𑁒NoDup with "Hmodel") as %?; first done.
    iDestruct "Hmodel" as "(:model')".
    iDestruct (big_sepM_lookup_acc with "Hdescrs") as "((:descriptor۰model) & Hdescrs)"; first done.
    wp۰load.
    iDestruct ("Hdescrs" with "[- Helts_auth Helt HΦ]") as "Hdescrs"; first iSteps.
    iSteps as (cl (class' & descr' & Hdescrs_lookup' & <-)%elem_of_map_to_set Helts'_elem%elem_of_list_to_set) / --silent. iPureIntro.
    edestruct (Helt class' descr') as (-> & ->); [done.. |].
    rewrite size_list_to_set //.
  Qed.

  Lemma partition٠refine𑁒spec {γ part v_elts} elts :
    list۰model' v_elts (#*@{location} elts) →
    {{{
      partition۰model γ part
    }}}
      partition٠refine v_elts
    {{{
      part'
    , RET ();
      partition۰model γ part' ∗
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
End partition۰G.

Require zoo_partition.partition__opaque.

#[global] Opaque partition۰model.
#[global] Opaque partition۰element.
