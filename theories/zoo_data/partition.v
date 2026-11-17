Require Import zoo.prelude.
Require Import zoo.iris.base_logic.lib.mono_gset.
Require Import zoo.base.
Require Export zoo_data.partition__code.
Require Import zoo_data.partition__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type sz : nat.
Implicit Type elt repr class first last : location.
Implicit Type elts split_list : list location.
Implicit Type elements X cl : gset location.
Implicit Type prevs nexts classes : location → location.
Implicit Type seens : location → bool.
Implicit Type part : gmap location (gset location).
Implicit Type v 𝑒𝑙𝑡𝑠 : val.

Record partition۰name :=
  { partition۰name۰elements : gname
  }.
Implicit Type γ : partition۰name.

Please derive Inhabited for partition۰name.
Please derive EqDecision for partition۰name.
Please derive Countable for partition۰name.

Zoo global :=
  { elements : mono_gset location
  }.

Section swap.
  Context {A : Type} `{!EqDecision A}.

  Implicit Types x : A.
  Implicit Types xs : list A.

  #[local] Definition swap x1 x2 x :=
    if decide (x = x1) then
      x2
    else if decide (x = x2) then
      x1
    else
      x.

  #[local] Lemma swapｰl x1 x2 :
    swap x1 x2 x1 = x2.
  Proof.
    rewrite /swap decide_True //.
  Qed.
  #[local] Lemma swapｰr x1 x2 :
    swap x1 x2 x2 = x1.
  Proof.
    rewrite /swap. repeat case_decide; naive.
  Qed.
  #[local] Lemma swapｰne {x1 x2} x :
    x ≠ x1 →
    x ≠ x2 →
    swap x1 x2 x = x.
  Proof.
    rewrite /swap. repeat case_decide; naive.
  Qed.
  #[local] Lemma swapｰdiag x1 x :
    swap x1 x1 x = x.
  Proof.
    rewrite /swap. repeat case_decide; naive.
  Qed.
  #[local] Lemma swapｰinvolutive x1 x2 x :
    swap x1 x2 (swap x1 x2 x) = x.
  Proof.
    rewrite /swap. repeat case_decide; naive.
  Qed.
  #[local] Lemma swapｰinj x1 x2 x x' :
    swap x1 x2 x = swap x1 x2 x' →
    x = x'.
  Proof.
    intros Heq.
    rewrite -(swapｰinvolutive x1 x2 x) -(swapｰinvolutive x1 x2 x') Heq //.
  Qed.

  #[local] Lemma swapｰelem_of {x1 x2} xs x :
    x1 ∈ xs →
    x2 ∈ xs →
      swap x1 x2 x ∈ xs ↔
      x ∈ xs.
  Proof.
    rewrite /swap. repeat case_decide; naive.
  Qed.
  #[local] Lemma swapｰfmapｰelem_of {x1 x2} xs x :
    x1 ∈ xs →
    x2 ∈ xs →
      x ∈ swap x1 x2 <$> xs ↔
      x ∈ xs.
  Proof.
    intros Hx1 Hx2.
    rewrite list_elem_of_fmap. split.
    - intros (x' & -> & Hx'). apply swapｰelem_of; done.
    - intros Hx. exists (swap x1 x2 x).
      rewrite swapｰinvolutive swapｰelem_of //.
  Qed.
  #[local] Lemma swapｰfmapｰid {x1 x2} xs :
    x1 ∉ xs →
    x2 ∉ xs →
    swap x1 x2 <$> xs = xs.
  Proof.
    induction xs as [| x xs IH]; first done.
    intros Hx1 Hx2.
    rewrite fmap_cons IH; [set_solver.. |].
    rewrite swapｰne //; set_solver.
  Qed.
End swap.

Record descriptor := Descriptor
  { descriptor۰class : location
  ; descriptor۰elts : list location
  ; descriptor۰seen : nat
  }.
Implicit Type descr : descriptor.
Implicit Type descrs : gmap location descriptor.

#[local] Definition links۰valid elements prevs nexts :=
  ∀ elt,
  elt ∈ elements →
    nexts elt ∈ elements ∧
    prevs elt ∈ elements ∧
    prevs (nexts elt) = elt ∧
    nexts (prevs elt) = elt.

#[local] Ltac solve۰swap elt elt1 elt2 :=
  simpl;
  destruct (decide (elt = elt1)) as [-> | ?];
  [| destruct (decide (elt = elt2)) as [-> | ?];
     [| rewrite (swapｰne elt) //]
  ];
  rewrite /swap /insert /fn_insert /=;
  repeat case_decide; congruence.

Record model۰valid elements prevs nexts classes seens descrs : Prop :=
  { model۰validｰnext elt :
      elt ∈ elements →
      nexts elt ∈ elements
  ; model۰validｰprev elt :
      elt ∈ elements →
      prevs elt ∈ elements
  ; model۰validｰprevｰnext elt :
      elt ∈ elements →
      prevs (nexts elt) = elt
  ; model۰validｰnextｰprev elt :
      elt ∈ elements →
      nexts (prevs elt) = elt
  ; model۰validｰelements elt :
      elt ∈ elements ↔
        ∃ repr descr,
        descrs !! repr = Some descr ∧
        elt ∈ descr.(descriptor۰elts)
  ; model۰validｰhead repr descr :
      descrs !! repr = Some descr →
      head descr.(descriptor۰elts) = Some repr
  ; model۰validｰNoDup repr descr :
      descrs !! repr = Some descr →
      NoDup descr.(descriptor۰elts)
  ; model۰validｰseen repr descr :
      descrs !! repr = Some descr →
      descr.(descriptor۰seen) ≤ length descr.(descriptor۰elts)
  ; model۰validｰclass repr1 descr1 repr2 descr2 :
      descrs !! repr1 = Some descr1 →
      descrs !! repr2 = Some descr2 →
      descr1.(descriptor۰class) = descr2.(descriptor۰class) →
      repr1 = repr2
  ; model۰validｰclasses repr descr elt :
      descrs !! repr = Some descr →
      elt ∈ descr.(descriptor۰elts) →
      classes elt = descr.(descriptor۰class)
  ; model۰validｰseens repr descr elt :
      descrs !! repr = Some descr →
      elt ∈ descr.(descriptor۰elts) →
      seens elt = bool_decide (elt ∈ take descr.(descriptor۰seen) descr.(descriptor۰elts))
  ; model۰validｰchain repr descr i elt1 elt2 :
      descrs !! repr = Some descr →
      descr.(descriptor۰elts) !! i = Some elt1 →
      descr.(descriptor۰elts) !! ˖i = Some elt2 →
      nexts elt1 = elt2
  }.
#[local] Arguments model۰validｰnext {_ _ _ _ _ _} _ {_}.
#[local] Arguments model۰validｰprev {_ _ _ _ _ _} _ {_}.
#[local] Arguments model۰validｰprevｰnext {_ _ _ _ _ _} _ {_}.
#[local] Arguments model۰validｰnextｰprev {_ _ _ _ _ _} _ {_}.
#[local] Arguments model۰validｰelements {_ _ _ _ _ _} _ _.
#[local] Arguments model۰validｰhead {_ _ _ _ _ _} _ {_ _}.
#[local] Arguments model۰validｰNoDup {_ _ _ _ _ _} _ {_ _}.
#[local] Arguments model۰validｰseen {_ _ _ _ _ _} _ {_ _}.
#[local] Arguments model۰validｰclass {_ _ _ _ _ _} _ {_ _ _ _}.
#[local] Arguments model۰validｰclasses {_ _ _ _ _ _} _ {_ _ _}.
#[local] Arguments model۰validｰseens {_ _ _ _ _ _} _ {_ _ _}.
#[local] Arguments model۰validｰchain {_ _ _ _ _ _} _ {_ _ _ _ _}.

Section model۰valid.
  Context {elements prevs nexts classes seens descrs}.
  Context (Hvalid : model۰valid elements prevs nexts classes seens descrs).

  #[local] Lemma model۰validｰelement {repr descr elt} :
    descrs !! repr = Some descr →
    elt ∈ descr.(descriptor۰elts) →
    elt ∈ elements.
  Proof.
    intros. apply (model۰validｰelements Hvalid). naive.
  Qed.
  #[local] Lemma model۰validｰrepr {repr descr} :
    descrs !! repr = Some descr →
    repr ∈ descr.(descriptor۰elts).
  Proof.
    intros Hlookup.
    apply head_Some_elem_of, (model۰validｰhead Hvalid Hlookup).
  Qed.
  #[local] Lemma model۰validｰdisjoint {repr1 descr1 repr2 descr2} elt :
    descrs !! repr1 = Some descr1 →
    descrs !! repr2 = Some descr2 →
    elt ∈ descr1.(descriptor۰elts) →
    elt ∈ descr2.(descriptor۰elts) →
      repr1 = repr2 ∧
      descr1 = descr2.
  Proof.
    intros Hlookup1 Hlookup2 Helt1 Helt2.
    assert (repr1 = repr2) as <-.
    { apply (model۰validｰclass Hvalid Hlookup1 Hlookup2).
      rewrite -(model۰validｰclasses Hvalid Hlookup1 Helt1) -(model۰validｰclasses Hvalid Hlookup2 Helt2) //.
    }
    naive.
  Qed.
  #[local] Lemma model۰validｰlength {repr descr} :
    descrs !! repr = Some descr →
    0 < length descr.(descriptor۰elts).
  Proof.
    intros Hlookup.
    pose proof (model۰validｰhead Hvalid Hlookup) as Hhead.
    destruct (descr.(descriptor۰elts)); [done | simpl; lia].
  Qed.
  #[local] Lemma model۰validｰnextｰinj elt1 elt2 :
    elt1 ∈ elements →
    elt2 ∈ elements →
    nexts elt1 = nexts elt2 →
    elt1 = elt2.
  Proof.
    intros Helt1 Helt2 Heq.
    rewrite -(model۰validｰprevｰnext Hvalid Helt1) -(model۰validｰprevｰnext Hvalid Helt2) Heq //.
  Qed.
  #[local] Lemma model۰validｰnextｰne {repr descr} elt :
    descrs !! repr = Some descr →
    2 ≤ length descr.(descriptor۰elts) →
    elt ∈ descr.(descriptor۰elts) →
    nexts elt ≠ elt.
  Proof.
    intros Hlookup Hlength (i & Hlookup_elt)%list_elem_of_lookup Hnext.
    pose proof (model۰validｰNoDup Hvalid Hlookup) as Hnodup.
    pose proof Hlookup_elt as Hi%lookup_lt_Some.
    destruct (decide (˖i < length descr.(descriptor۰elts))) as [Hi' | Hi'].
    - destruct (lookup_lt_is_Some_2 descr.(descriptor۰elts) ˖i) as (elt' & Hlookup_elt'); first done.
      rewrite (model۰validｰchain Hvalid Hlookup Hlookup_elt Hlookup_elt') in Hnext. subst elt'.
      opose proof* (NoDup_lookup _ i ˖i); [done.. | lia].
    - destruct i as [| i]; first lia.
      destruct (lookup_lt_is_Some_2 descr.(descriptor۰elts) i) as (elt' & Hlookup_elt'); first lia.
      pose proof (model۰validｰchain Hvalid Hlookup Hlookup_elt' Hlookup_elt) as Hnext'.
      assert (elt' = elt) as ->.
      { apply (model۰validｰnextｰinj elt' elt); last congruence.
        - eapply model۰validｰelement; first done.
          eapply list_elem_of_lookup_2; done.
        - eapply model۰validｰelement; first done.
          eapply list_elem_of_lookup_2; done.
      }
      opose proof* (NoDup_lookup _ i ˖i); [done.. | lia].
  Qed.
  #[local] Lemma model۰validｰlinks :
    links۰valid elements prevs nexts.
  Proof.
    intros elt Helt. split_and!.
    - apply (model۰validｰnext Hvalid Helt).
    - apply (model۰validｰprev Hvalid Helt).
    - apply (model۰validｰprevｰnext Hvalid Helt).
    - apply (model۰validｰnextｰprev Hvalid Helt).
  Qed.

  #[local] Lemma model۰validｰlookupｰNone repr :
    repr ∉ elements →
    descrs !! repr = None.
  Proof.
    intros Hrepr.
    destruct (descrs !! repr) as [descr |] eqn:Hlookup; last done.
    exfalso. apply Hrepr.
    eapply model۰validｰelement; first done.
    apply (model۰validｰrepr Hlookup).
  Qed.

  #[local] Lemma model۰validｰmake elt class :
    elt ∉ elements →
    ( ∀ repr descr,
      descrs !! repr = Some descr →
      descr.(descriptor۰class) ≠ class
    ) →
    model۰valid
      ({[elt]} ∪ elements)
      (<[elt := elt]> prevs)
      (<[elt := elt]> nexts)
      (<[elt := class]> classes)
      (<[elt := false]> seens)
      (<[elt := Descriptor class [elt] 0]> descrs).
  Proof.
    intros Helt Hclass.
    pose proof (model۰validｰlookupｰNone elt Helt) as Hlookup_elt.
    constructor.
    - intros elt' [->%elem_of_singleton | Helt']%elem_of_union.
      + rewrite fn_lookup_insert. set_solver.
      + assert (elt ≠ elt') by set_solver.
        rewrite fn_lookup_insert_ne //.
        apply elem_of_union_r, (model۰validｰnext Hvalid Helt').
    - intros elt' [->%elem_of_singleton | Helt']%elem_of_union.
      + rewrite fn_lookup_insert. set_solver.
      + assert (elt ≠ elt') by set_solver.
        rewrite fn_lookup_insert_ne //.
        apply elem_of_union_r, (model۰validｰprev Hvalid Helt').
    - intros elt' [->%elem_of_singleton | Helt']%elem_of_union.
      + rewrite !fn_lookup_insert //.
      + assert (elt ≠ elt') by set_solver.
        assert (elt ≠ nexts elt').
        { intros ->. apply Helt, (model۰validｰnext Hvalid Helt'). }
        rewrite !fn_lookup_insert_ne //.
        apply (model۰validｰprevｰnext Hvalid Helt').
    - intros elt' [->%elem_of_singleton | Helt']%elem_of_union.
      + rewrite !fn_lookup_insert //.
      + assert (elt ≠ elt') by set_solver.
        assert (elt ≠ prevs elt').
        { intros ->. apply Helt, (model۰validｰprev Hvalid Helt'). }
        rewrite !fn_lookup_insert_ne //.
        apply (model۰validｰnextｰprev Hvalid Helt').
    - intros elt'.
      rewrite elem_of_union elem_of_singleton (model۰validｰelements Hvalid).
      setoid_rewrite lookup_insert_Some. split.
      + intros [-> | (repr & descr & Hlookup & Helt')].
        * exists elt, (Descriptor class [elt] 0). simpl. set_solver.
        * exists repr, descr. split; last done.
          right. split; last done.
          intros ->. congruence.
      + intros (repr & descr & [(<- & <-) | (Hne & Hlookup)] & Helt').
        * left. set_solver.
        * right. naive.
    - intros repr descr [(<- & <-) | (Hne & Hlookup)]%lookup_insert_Some; first done.
      apply (model۰validｰhead Hvalid Hlookup).
    - intros repr descr [(<- & <-) | (Hne & Hlookup)]%lookup_insert_Some.
      + apply NoDup_singleton.
      + apply (model۰validｰNoDup Hvalid Hlookup).
    - intros repr descr [(<- & <-) | (Hne & Hlookup)]%lookup_insert_Some.
      + simpl. lia.
      + apply (model۰validｰseen Hvalid Hlookup).
    - intros repr1 descr1 repr2 descr2 [(<- & <-) | (Hne1 & Hlookup1)]%lookup_insert_Some [(<- & <-) | (Hne2 & Hlookup2)]%lookup_insert_Some Heq.
      + done.
      + exfalso. apply (Hclass _ _ Hlookup2). done.
      + exfalso. apply (Hclass _ _ Hlookup1). done.
      + apply (model۰validｰclass Hvalid Hlookup1 Hlookup2 Heq).
    - intros repr descr elt' [(<- & <-) | (Hne & Hlookup)]%lookup_insert_Some Helt'.
      + apply list_elem_of_singleton in Helt' as ->.
        rewrite fn_lookup_insert //.
      + assert (elt ≠ elt').
        { intros ->. apply Helt. eapply model۰validｰelement; done. }
        rewrite fn_lookup_insert_ne //.
        apply (model۰validｰclasses Hvalid Hlookup Helt').
    - intros repr descr elt' [(<- & <-) | (Hne & Hlookup)]%lookup_insert_Some Helt'.
      + apply list_elem_of_singleton in Helt' as ->.
        rewrite fn_lookup_insert. symmetry.
        apply bool_decide_eq_false_2, not_elem_of_nil.
      + assert (elt ≠ elt').
        { intros ->. apply Helt. eapply model۰validｰelement; done. }
        rewrite fn_lookup_insert_ne //.
        apply (model۰validｰseens Hvalid Hlookup Helt').
    - intros repr descr i elt1 elt2 [(<- & <-) | (Hne & Hlookup)]%lookup_insert_Some Hlookup1 Hlookup2.
      + apply lookup_lt_Some in Hlookup2. simpl in Hlookup2. lia.
      + assert (elt ≠ elt1).
        { intros ->. apply Helt. eapply model۰validｰelement; first done.
          eapply list_elem_of_lookup_2; done.
        }
        rewrite fn_lookup_insert_ne //.
        apply (model۰validｰchain Hvalid Hlookup Hlookup1 Hlookup2).
  Qed.

  #[local] Lemma model۰validｰadd {repr descr} elt last :
    descrs !! repr = Some descr →
    descr.(descriptor۰seen) = 0 →
    list.last descr.(descriptor۰elts) = Some last →
    elt ∉ elements →
    model۰valid
      ({[elt]} ∪ elements)
      (<[elt := last]> (<[nexts last := elt]> prevs))
      (<[last := elt]> (<[elt := nexts last]> nexts))
      (<[elt := descr.(descriptor۰class)]> classes)
      (<[elt := false]> seens)
      (<[repr := Descriptor descr.(descriptor۰class) (descr.(descriptor۰elts) ++ [elt]) 0]> descrs).
  Proof.
    intros Hlookup Hseen Hlast Helt.
    pose proof (model۰validｰNoDup Hvalid Hlookup) as Hnodup.
    assert (last ∈ descr.(descriptor۰elts)) as Hlast_elts.
    { apply last_Some_elem_of. done. }
    assert (last ∈ elements) as Hlast_elements.
    { eapply model۰validｰelement; done. }
    assert (nexts last ∈ elements) as Hnext_elements.
    { apply (model۰validｰnext Hvalid Hlast_elements). }
    assert (elt ≠ last) as Hne_last by set_solver.
    assert (elt ≠ nexts last) as Hne_next by set_solver.
    assert (
      ∀ elt',
      elt' ∈ descr.(descriptor۰elts) →
      elt ≠ elt'
    ) as Hne_elts.
    { intros elt' Helt' ->. apply Helt. eapply model۰validｰelement; done. }
    constructor.
    - intros elt' [->%elem_of_singleton | Helt']%elem_of_union.
      + rewrite fn_lookup_insert_ne // fn_lookup_insert. set_solver.
      + destruct (decide (elt' = last)) as [-> | Hne].
        * rewrite fn_lookup_insert. set_solver.
        * assert (elt ≠ elt') by set_solver.
          rewrite !fn_lookup_insert_ne //.
          apply elem_of_union_r, (model۰validｰnext Hvalid Helt').
    - intros elt' [->%elem_of_singleton | Helt']%elem_of_union.
      + rewrite fn_lookup_insert. set_solver.
      + assert (elt ≠ elt') by set_solver.
        rewrite fn_lookup_insert_ne //.
        destruct (decide (elt' = nexts last)) as [-> | Hne].
        * rewrite fn_lookup_insert. set_solver.
        * rewrite fn_lookup_insert_ne //.
          apply elem_of_union_r, (model۰validｰprev Hvalid Helt').
    - intros elt' [->%elem_of_singleton | Helt']%elem_of_union.
      + rewrite (fn_lookup_insert_ne _ last) // fn_lookup_insert.
        rewrite fn_lookup_insert_ne // fn_lookup_insert //.
      + destruct (decide (elt' = last)) as [-> | Hne].
        * rewrite !fn_lookup_insert //.
        * assert (elt ≠ elt') by set_solver.
          assert (<[last := elt]> (<[elt := nexts last]> nexts) elt' = nexts elt') as ->.
          { rewrite !fn_lookup_insert_ne //. }
          assert (elt ≠ nexts elt').
          { intros Heq. apply Helt. rewrite Heq. apply (model۰validｰnext Hvalid Helt'). }
          assert (nexts last ≠ nexts elt').
          { intros Heq. apply Hne. symmetry. apply model۰validｰnextｰinj; done. }
          rewrite !fn_lookup_insert_ne //.
          apply (model۰validｰprevｰnext Hvalid Helt').
    - intros elt' [->%elem_of_singleton | Helt']%elem_of_union.
      + rewrite !fn_lookup_insert //.
      + assert (elt ≠ elt') by set_solver.
        destruct (decide (elt' = nexts last)) as [-> | Hne].
        * assert (<[elt := last]> (<[nexts last := elt]> prevs) (nexts last) = elt) as ->.
          { rewrite fn_lookup_insert_ne // fn_lookup_insert //. }
          rewrite fn_lookup_insert_ne // fn_lookup_insert //.
        * assert (<[elt := last]> (<[nexts last := elt]> prevs) elt' = prevs elt') as ->.
          { rewrite !fn_lookup_insert_ne //. }
          assert (prevs elt' ≠ last).
          { intros Heq. apply Hne. rewrite -Heq (model۰validｰnextｰprev Hvalid Helt') //. }
          assert (elt ≠ prevs elt').
          { intros Heq. apply Helt. rewrite Heq. apply (model۰validｰprev Hvalid Helt'). }
          rewrite !fn_lookup_insert_ne //.
          apply (model۰validｰnextｰprev Hvalid Helt').
    - intros elt'.
      rewrite elem_of_union elem_of_singleton (model۰validｰelements Hvalid).
      setoid_rewrite lookup_insert_Some. split.
      + intros [-> | (repr' & descr' & Hlookup' & Helt')].
        * exists repr, (Descriptor descr.(descriptor۰class) (descr.(descriptor۰elts) ++ [elt]) 0).
          simpl. set_solver.
        * destruct (decide (repr = repr')) as [<- | Hne].
          -- simplify_eq.
             exists repr, (Descriptor descr.(descriptor۰class) (descr.(descriptor۰elts) ++ [elt]) 0).
             simpl. set_solver.
          -- exists repr', descr'. naive.
      + intros (repr' & descr' & [(<- & <-) | (Hne & Hlookup')] & Helt').
        * simpl in Helt'. apply elem_of_app in Helt' as [Helt' | ->%list_elem_of_singleton].
          -- right. naive.
          -- left. done.
        * right. naive.
    - intros repr' descr' [(<- & <-) | (Hne & Hlookup')]%lookup_insert_Some.
      + pose proof (model۰validｰhead Hvalid Hlookup) as Hhead.
        rewrite /= head_app Hhead //.
      + apply (model۰validｰhead Hvalid Hlookup').
    - intros repr' descr' [(<- & <-) | (Hne & Hlookup')]%lookup_insert_Some.
      + apply NoDup_app. split_and!; [done | | apply NoDup_singleton].
        intros elt' Helt' ->%list_elem_of_singleton. naive.
      + apply (model۰validｰNoDup Hvalid Hlookup').
    - intros repr' descr' [(<- & <-) | (Hne & Hlookup')]%lookup_insert_Some.
      + simpl. lia.
      + apply (model۰validｰseen Hvalid Hlookup').
    - assert (
        ∀ repr' descr',
        <[repr := Descriptor descr.(descriptor۰class) (descr.(descriptor۰elts) ++ [elt]) 0]> descrs !! repr' = Some descr' →
          ∃ descr'',
          descrs !! repr' = Some descr'' ∧
          descr''.(descriptor۰class) = descr'.(descriptor۰class)
      ) as Hclasses.
      { intros repr' descr' [(<- & <-) | (Hne & Hlookup')]%lookup_insert_Some; naive. }
      intros repr1 descr1 repr2 descr2 (descr1' & Hlookup1 & <-)%Hclasses (descr2' & Hlookup2 & <-)%Hclasses Heq.
      apply (model۰validｰclass Hvalid Hlookup1 Hlookup2 Heq).
    - intros repr' descr' elt' [(<- & <-) | (Hne & Hlookup')]%lookup_insert_Some Helt'.
      + simpl in Helt'. apply elem_of_app in Helt' as [Helt' | ->%list_elem_of_singleton].
        * rewrite fn_lookup_insert_ne; first naive.
          apply (model۰validｰclasses Hvalid Hlookup Helt').
        * rewrite fn_lookup_insert //.
      + assert (elt ≠ elt').
        { intros ->. apply Helt. eapply model۰validｰelement; done. }
        rewrite fn_lookup_insert_ne //.
        apply (model۰validｰclasses Hvalid Hlookup' Helt').
    - intros repr' descr' elt' [(<- & <-) | (Hne & Hlookup')]%lookup_insert_Some Helt'.
      + transitivity false; last first.
        { symmetry. apply bool_decide_eq_false_2. simpl. rewrite ?take_0. apply not_elem_of_nil. }
        simpl in Helt'. apply elem_of_app in Helt' as [Helt' | ->%list_elem_of_singleton].
        * rewrite fn_lookup_insert_ne; first naive.
          rewrite (model۰validｰseens Hvalid Hlookup Helt') Hseen.
          apply bool_decide_eq_false_2. rewrite ?take_0. apply not_elem_of_nil.
        * rewrite fn_lookup_insert //.
      + assert (elt ≠ elt').
        { intros ->. apply Helt. eapply model۰validｰelement; done. }
        rewrite fn_lookup_insert_ne //.
        apply (model۰validｰseens Hvalid Hlookup' Helt').
    - intros repr' descr' i elt1 elt2 [(<- & <-) | (Hne & Hlookup')]%lookup_insert_Some Hlookup1 Hlookup2.
      + simpl in *.
        apply lookup_app_Some in Hlookup1 as [Hlookup1 | (Hi & Hlookup1)]; last first.
        { apply lookup_app_Some in Hlookup2 as [Hlookup2%lookup_lt_Some | (_ & Hlookup2%lookup_lt_Some)]; simpl in *; lia. }
        apply lookup_app_Some in Hlookup2 as [Hlookup2 | (Hi & Hlookup2)].
        * assert (elt1 ≠ last).
          { intros ->.
            rewrite last_lookup in Hlast.
            pose proof Hlookup2 as ?%lookup_lt_Some.
            opose proof* (NoDup_lookup _ i (pred (length descr.(descriptor۰elts)))); [done.. | lia].
          }
          rewrite fn_lookup_insert_ne; first naive.
          rewrite fn_lookup_insert_ne; first (apply Hne_elts; eapply list_elem_of_lookup_2; done).
          apply (model۰validｰchain Hvalid Hlookup Hlookup1 Hlookup2).
        * apply list_lookup_singleton_Some in Hlookup2 as (Hi' & <-).
          assert (elt1 = last) as ->.
          { rewrite last_lookup in Hlast. pose proof Hlookup1 as ?%lookup_lt_Some.
            rewrite (_ : pred (length descr.(descriptor۰elts)) = i) in Hlast; first lia.
            congruence.
          }
          rewrite fn_lookup_insert //.
      + assert (elt1 ∈ descr'.(descriptor۰elts)) as Helt1.
        { eapply list_elem_of_lookup_2; done. }
        assert (elt1 ≠ last).
        { intros ->. apply Hne. eapply (model۰validｰdisjoint last Hlookup Hlookup'); done. }
        assert (elt ≠ elt1).
        { intros ->. apply Helt. eapply model۰validｰelement; done. }
        rewrite !fn_lookup_insert_ne //.
        apply (model۰validｰchain Hvalid Hlookup' Hlookup1 Hlookup2).
  Qed.
  #[local] Lemma model۰validｰother {repr descr repr' descr'} elt :
    descrs !! repr = Some descr →
    descrs !! repr' = Some descr' →
    repr' ≠ repr →
    elt ∈ descr'.(descriptor۰elts) →
    elt ∉ descr.(descriptor۰elts).
  Proof.
    intros Hlookup Hlookup' Hne Helt' Helt.
    apply Hne. symmetry.
    apply (model۰validｰdisjoint elt Hlookup Hlookup'); done.
  Qed.

  #[local] Lemma model۰validｰswap {repr descr} elt1 elt2 :
    descrs !! repr = Some descr →
    elt1 ∈ descr.(descriptor۰elts) →
    elt2 ∈ descr.(descriptor۰elts) →
    elt1 ∉ take descr.(descriptor۰seen) descr.(descriptor۰elts) →
    elt2 ∉ take descr.(descriptor۰seen) descr.(descriptor۰elts) →
    model۰valid
      elements
      (swap elt1 elt2 ∘ prevs ∘ swap elt1 elt2)
      (swap elt1 elt2 ∘ nexts ∘ swap elt1 elt2)
      classes
      seens
      (<[swap elt1 elt2 repr := Descriptor descr.(descriptor۰class) (swap elt1 elt2 <$> descr.(descriptor۰elts)) descr.(descriptor۰seen)]> (delete repr descrs)).
  Proof.
    intros Hlookup Helt1 Helt2 Helt1_seen Helt2_seen.
    pose proof (model۰validｰNoDup Hvalid Hlookup) as Hnodup.
    pose proof (model۰validｰrepr Hlookup) as Hrepr.
    assert (elt1 ∈ elements) as Helt1_elements.
    { eapply model۰validｰelement; done. }
    assert (elt2 ∈ elements) as Helt2_elements.
    { eapply model۰validｰelement; done. }
    assert (
      ∀ elt,
      swap elt1 elt2 elt ∈ elements ↔
      elt ∈ elements
    ) as Hswap_elements.
    { intros elt. rewrite /swap. repeat case_decide; naive. }
    assert (
      ∀ elt,
      elt ∉ descr.(descriptor۰elts) →
      swap elt1 elt2 elt = elt
    ) as Hswap_other.
    { intros elt Helt. apply swapｰne; set_solver. }
    set descr' := Descriptor descr.(descriptor۰class) (swap elt1 elt2 <$> descr.(descriptor۰elts)) descr.(descriptor۰seen).
    assert (
      ∀ repr' descr'',
      <[swap elt1 elt2 repr := descr']> (delete repr descrs) !! repr' = Some descr'' ↔
          repr' = swap elt1 elt2 repr ∧
          descr'' = descr'
        ∨ repr' ≠ repr ∧
          descrs !! repr' = Some descr''
    ) as Hlookup'.
    { intros repr' descr''.
      rewrite lookup_insert_Some lookup_delete_Some. split.
      - intros [(<- & <-) | (_ & Hne & Hlookup')]; naive.
      - intros [(-> & ->) | (Hne & Hlookup')]; first naive.
        right. split_and!; try done.
        intros Heq.
        apply (model۰validｰother repr' Hlookup Hlookup'); first done.
        + apply (model۰validｰrepr Hlookup').
        + rewrite -Heq swapｰelem_of //.
    }
    constructor.
    - intros elt Helt. simpl.
      apply Hswap_elements, (model۰validｰnext Hvalid), Hswap_elements. done.
    - intros elt Helt. simpl.
      apply Hswap_elements, (model۰validｰprev Hvalid), Hswap_elements. done.
    - intros elt Helt. simpl.
      assert (swap elt1 elt2 elt ∈ elements) by (apply Hswap_elements; done).
      rewrite swapｰinvolutive (model۰validｰprevｰnext Hvalid) // swapｰinvolutive //.
    - intros elt Helt. simpl.
      assert (swap elt1 elt2 elt ∈ elements) by (apply Hswap_elements; done).
      rewrite swapｰinvolutive (model۰validｰnextｰprev Hvalid) // swapｰinvolutive //.
    - intros elt. rewrite (model۰validｰelements Hvalid).
      setoid_rewrite Hlookup'. split.
      + intros (repr' & descr'' & Hlookup'' & Helt).
        destruct (decide (repr' = repr)) as [-> | Hne].
        * simplify_eq. exists (swap elt1 elt2 repr), descr'. split; first naive.
          rewrite swapｰfmapｰelem_of //.
        * exists repr', descr''. naive.
      + intros (repr' & descr'' & [(-> & ->) | (Hne & Hlookup'')] & Helt).
        * exists repr, descr. split; first done.
          rewrite swapｰfmapｰelem_of // in Helt.
        * exists repr', descr''. done.
    - intros repr' descr'' [(-> & ->) | (Hne & Hlookup'')]%Hlookup'.
      + rewrite /= head_lookup list_lookup_fmap -head_lookup (model۰validｰhead Hvalid Hlookup) //.
      + apply (model۰validｰhead Hvalid Hlookup'').
    - intros repr' descr'' [(-> & ->) | (Hne & Hlookup'')]%Hlookup'.
      + apply NoDup_fmap_2_strong; last done.
        intros ? ? _ _. apply swapｰinj.
      + apply (model۰validｰNoDup Hvalid Hlookup'').
    - intros repr' descr'' [(-> & ->) | (Hne & Hlookup'')]%Hlookup'.
      + rewrite /= length_fmap. apply (model۰validｰseen Hvalid Hlookup).
      + apply (model۰validｰseen Hvalid Hlookup'').
    - intros repr1 descr1 repr2 descr2 [(-> & ->) | (Hne1 & Hlookup1)]%Hlookup' [(-> & ->) | (Hne2 & Hlookup2)]%Hlookup' Heq.
      + done.
      + exfalso. apply Hne2. symmetry. apply (model۰validｰclass Hvalid Hlookup Hlookup2 Heq).
      + exfalso. apply Hne1. apply (model۰validｰclass Hvalid Hlookup1 Hlookup Heq).
      + apply (model۰validｰclass Hvalid Hlookup1 Hlookup2 Heq).
    - intros repr' descr'' elt [(-> & ->) | (Hne & Hlookup'')]%Hlookup' Helt.
      + rewrite /= swapｰfmapｰelem_of // in Helt.
        apply (model۰validｰclasses Hvalid Hlookup Helt).
      + apply (model۰validｰclasses Hvalid Hlookup'' Helt).
    - intros repr' descr'' elt [(-> & ->) | (Hne & Hlookup'')]%Hlookup' Helt.
      + rewrite /= swapｰfmapｰelem_of // in Helt.
        rewrite /= -fmap_take swapｰfmapｰid //.
        apply (model۰validｰseens Hvalid Hlookup Helt).
      + apply (model۰validｰseens Hvalid Hlookup'' Helt).
    - intros repr' descr'' i elt elt' [(-> & ->) | (Hne & Hlookup'')]%Hlookup' Hlookup1 Hlookup2.
      + simpl in *.
        apply list_lookup_fmap_Some in Hlookup1 as (elt_ & -> & Hlookup1).
        apply list_lookup_fmap_Some in Hlookup2 as (elt_' & -> & Hlookup2).
        rewrite /= swapｰinvolutive (model۰validｰchain Hvalid Hlookup Hlookup1 Hlookup2) //.
      + assert (elt ∉ descr.(descriptor۰elts)).
        { eapply (model۰validｰother elt Hlookup Hlookup''); first done.
          eapply list_elem_of_lookup_2. done.
        }
        assert (elt' ∉ descr.(descriptor۰elts)).
        { eapply (model۰validｰother elt' Hlookup Hlookup''); first done.
          eapply list_elem_of_lookup_2. done.
        }
        rewrite /= (Hswap_other elt) // (model۰validｰchain Hvalid Hlookup'' Hlookup1 Hlookup2) (Hswap_other elt') //.
  Qed.

  #[local] Lemma model۰validｰupdate {repr descr} descr' seens' :
    descrs !! repr = Some descr →
    descr'.(descriptor۰class) = descr.(descriptor۰class) →
    descr'.(descriptor۰elts) = descr.(descriptor۰elts) →
    descr'.(descriptor۰seen) ≤ length descr.(descriptor۰elts) →
    ( ∀ elt,
      elt ∈ descr.(descriptor۰elts) →
      seens' elt = bool_decide (elt ∈ take descr'.(descriptor۰seen) descr.(descriptor۰elts))
    ) →
    ( ∀ elt,
      elt ∉ descr.(descriptor۰elts) →
      seens' elt = seens elt
    ) →
    model۰valid elements prevs nexts classes seens' (<[repr := descr']> descrs).
  Proof.
    intros Hlookup Hclass Helts Hseen Hseens_in Hseens_out.
    assert (
      ∀ repr' descr'',
      <[repr := descr']> descrs !! repr' = Some descr'' →
        ∃ descr''',
        descrs !! repr' = Some descr''' ∧
        descr''.(descriptor۰class) = descr'''.(descriptor۰class) ∧
        descr''.(descriptor۰elts) = descr'''.(descriptor۰elts)
    ) as Hlookup'.
    { intros repr' descr'' [(<- & <-) | (Hne & Hlookup'')]%lookup_insert_Some; naive. }
    constructor.
    - intros elt. apply (model۰validｰnext Hvalid).
    - intros elt. apply (model۰validｰprev Hvalid).
    - intros elt. apply (model۰validｰprevｰnext Hvalid).
    - intros elt. apply (model۰validｰnextｰprev Hvalid).
    - intros elt. rewrite (model۰validｰelements Hvalid).
      setoid_rewrite lookup_insert_Some. split.
      + intros (repr' & descr'' & Hlookup'' & Helt).
        destruct (decide (repr = repr')) as [<- | Hne].
        * simplify_eq. exists repr, descr'. rewrite Helts. naive.
        * exists repr', descr''. naive.
      + intros (repr' & descr'' & [(<- & <-) | (Hne & Hlookup'')] & Helt).
        * exists repr, descr. rewrite -Helts //.
        * exists repr', descr''. done.
    - intros repr' descr'' (descr''' & Hlookup'' & _ & ->)%Hlookup'.
      apply (model۰validｰhead Hvalid Hlookup'').
    - intros repr' descr'' (descr''' & Hlookup'' & _ & ->)%Hlookup'.
      apply (model۰validｰNoDup Hvalid Hlookup'').
    - intros repr' descr'' [(<- & <-) | (Hne & Hlookup'')]%lookup_insert_Some.
      + rewrite Helts //.
      + apply (model۰validｰseen Hvalid Hlookup'').
    - intros repr1 descr1 repr2 descr2 (descr1' & Hlookup1 & -> & _)%Hlookup' (descr2' & Hlookup2 & -> & _)%Hlookup'.
      apply (model۰validｰclass Hvalid Hlookup1 Hlookup2).
    - intros repr' descr'' elt (descr''' & Hlookup'' & -> & ->)%Hlookup'.
      apply (model۰validｰclasses Hvalid Hlookup'').
    - intros repr' descr'' elt [(<- & <-) | (Hne & Hlookup'')]%lookup_insert_Some Helt.
      + rewrite Helts in Helt |- *. auto.
      + assert (elt ∉ descr.(descriptor۰elts)).
        { apply (model۰validｰother elt Hlookup Hlookup''); done. }
        rewrite Hseens_out //.
        apply (model۰validｰseens Hvalid Hlookup'' Helt).
    - intros repr' descr'' i elt1 elt2 (descr''' & Hlookup'' & _ & ->)%Hlookup'.
      apply (model۰validｰchain Hvalid Hlookup'').
  Qed.

  #[local] Lemma model۰validｰmark {repr descr} elt :
    descrs !! repr = Some descr →
    descr.(descriptor۰elts) !! descr.(descriptor۰seen) = Some elt →
    model۰valid elements prevs nexts classes
      (<[elt := true]> seens)
      (<[repr := Descriptor descr.(descriptor۰class) descr.(descriptor۰elts) ˖descr.(descriptor۰seen)]> descrs).
  Proof.
    intros Hlookup Hlookup_elt.
    pose proof (model۰validｰNoDup Hvalid Hlookup) as Hnodup.
    apply (model۰validｰupdate _ _ Hlookup); try done.
    - simpl. apply lookup_lt_Some in Hlookup_elt. lia.
    - intros elt' Helt'. simpl.
      rewrite (take_S_r _ _ elt) //.
      destruct (decide (elt' = elt)) as [-> | Hne].
      + rewrite fn_lookup_insert bool_decide_eq_true_2 //. set_solver.
      + rewrite fn_lookup_insert_ne // (model۰validｰseens Hvalid Hlookup Helt').
        apply bool_decide_ext. set_solver.
    - intros elt' Helt'.
      rewrite fn_lookup_insert_ne //.
      intros ->. apply Helt'. eapply list_elem_of_lookup_2. done.
  Qed.

  #[local] Lemma model۰validｰreset {repr descr} :
    descrs !! repr = Some descr →
    model۰valid elements prevs nexts classes
      (λ elt, if decide (elt ∈ descr.(descriptor۰elts)) then false else seens elt)
      (<[repr := Descriptor descr.(descriptor۰class) descr.(descriptor۰elts) 0]> descrs).
  Proof.
    intros Hlookup.
    apply (model۰validｰupdate _ _ Hlookup); [done | done | simpl; lia | |].
    - intros elt Helt. simpl.
      rewrite decide_True // take_0 bool_decide_eq_false_2 //.
    - intros elt Helt. simpl.
      rewrite decide_False //.
  Qed.

  #[local] Lemma model۰validｰsplit {repr descr} class split :
    descrs !! repr = Some descr →
    0 < descr.(descriptor۰seen) →
    descr.(descriptor۰elts) !! descr.(descriptor۰seen) = Some split →
    ( ∀ repr' descr',
      descrs !! repr' = Some descr' →
      descr'.(descriptor۰class) ≠ class
    ) →
    model۰valid elements prevs nexts
      (λ elt, if decide (elt ∈ take descr.(descriptor۰seen) descr.(descriptor۰elts)) then class else classes elt)
      (λ elt, if decide (elt ∈ take descr.(descriptor۰seen) descr.(descriptor۰elts)) then false else seens elt)
      ( <[repr := Descriptor class (take descr.(descriptor۰seen) descr.(descriptor۰elts)) 0]> $
        <[split := Descriptor descr.(descriptor۰class) (drop descr.(descriptor۰seen) descr.(descriptor۰elts)) 0]> descrs
      ).
  Proof.
    intros Hlookup Hn Hlookup_split Hclass.
    destruct descr as [descr_class elts n]. simpl in *.
    pose proof (model۰validｰNoDup Hvalid Hlookup) as Hnodup.
    pose proof Hnodup as Hnodup'.
    rewrite -(take_drop n elts) in Hnodup'.
    apply NoDup_app in Hnodup' as (Hnodup1 & Hdisjoint & Hnodup2).
    pose proof (model۰validｰhead Hvalid Hlookup) as Hhead.
    assert (head (take n elts) = Some repr) as Hhead1.
    { rewrite head_lookup lookup_take_Some -head_lookup //. }
    assert (head (drop n elts) = Some split) as Hhead2.
    { rewrite head_lookup lookup_drop Nat.add_0_r //. }
    assert (repr ∈ take n elts) as Hrepr.
    { apply head_Some_elem_of. done. }
    assert (split ∈ drop n elts) as Hsplit.
    { apply head_Some_elem_of. done. }
    assert (repr ≠ split) as Hne_split.
    { intros ->. apply (Hdisjoint split); done. }
    assert (descrs !! split = None) as Hlookup_split'.
    { destruct (descrs !! split) as [descr' |] eqn:Hlookup'; last done.
      exfalso. apply Hne_split.
      apply (model۰validｰdisjoint split Hlookup Hlookup').
      - rewrite -(take_drop n elts). set_solver.
      - apply (model۰validｰrepr Hlookup').
    }
    assert (
      ∀ elt,
      elt ∈ elts ↔
          elt ∈ take n elts
        ∨ elt ∈ drop n elts
    ) as Helts.
    { intros elt. rewrite -elem_of_app take_drop //. }
    set descr1 := Descriptor class (take n elts) 0.
    set descr2 := Descriptor descr_class (drop n elts) 0.
    assert (
      ∀ repr' descr',
      <[repr := descr1]> (<[split := descr2]> descrs) !! repr' = Some descr' ↔
          repr' = repr ∧
          descr' = descr1
        ∨ repr' = split ∧
          descr' = descr2
        ∨ repr' ≠ repr ∧
          repr' ≠ split ∧
          descrs !! repr' = Some descr'
    ) as Hlookup'.
    { intros repr' descr'.
      rewrite !lookup_insert_Some. naive.
    }
    constructor.
    - intros elt. apply (model۰validｰnext Hvalid).
    - intros elt. apply (model۰validｰprev Hvalid).
    - intros elt. apply (model۰validｰprevｰnext Hvalid).
    - intros elt. apply (model۰validｰnextｰprev Hvalid).
    - intros elt. rewrite (model۰validｰelements Hvalid).
      setoid_rewrite Hlookup'. split.
      + intros (repr' & descr' & Hlookup'' & Helt).
        destruct (decide (repr' = repr)) as [-> | Hne].
        * simplify_eq.
          apply Helts in Helt as [Helt | Helt].
          -- exists repr, descr1. naive.
          -- exists split, descr2. naive.
        * exists repr', descr'. split; last done.
          right. right. split_and!; try done.
          intros ->. rewrite Hlookup_split' // in Hlookup''.
      + intros (repr' & descr' & [(-> & ->) | [(-> & ->) | (Hne1 & Hne2 & Hlookup'')]] & Helt).
        * eexists repr, _. split; first done. naive.
        * eexists repr, _. split; first done. naive.
        * exists repr', descr'. done.
    - intros repr' descr' [(-> & ->) | [(-> & ->) | (Hne1 & Hne2 & Hlookup'')]]%Hlookup'.
      + done.
      + done.
      + apply (model۰validｰhead Hvalid Hlookup'').
    - intros repr' descr' [(-> & ->) | [(-> & ->) | (Hne1 & Hne2 & Hlookup'')]]%Hlookup'.
      + done.
      + done.
      + apply (model۰validｰNoDup Hvalid Hlookup'').
    - intros repr' descr' [(-> & ->) | [(-> & ->) | (Hne1 & Hne2 & Hlookup'')]]%Hlookup'.
      + simpl. lia.
      + simpl. lia.
      + apply (model۰validｰseen Hvalid Hlookup'').
    - intros repr1 descr1' repr2 descr2' [(-> & ->) | [(-> & ->) | (Hne11 & Hne12 & Hlookup1)]]%Hlookup' [(-> & ->) | [(-> & ->) | (Hne21 & Hne22 & Hlookup2)]]%Hlookup' Heq; simpl in Heq.
      + done.
      + exfalso. apply (Hclass _ _ Hlookup). done.
      + exfalso. apply (Hclass _ _ Hlookup2). done.
      + exfalso. apply (Hclass _ _ Hlookup). done.
      + done.
      + exfalso. apply Hne21. symmetry. apply (model۰validｰclass Hvalid Hlookup Hlookup2 Heq).
      + exfalso. apply (Hclass _ _ Hlookup1). done.
      + exfalso. apply Hne11. apply (model۰validｰclass Hvalid Hlookup1 Hlookup Heq).
      + apply (model۰validｰclass Hvalid Hlookup1 Hlookup2 Heq).
    - intros repr' descr' elt [(-> & ->) | [(-> & ->) | (Hne1 & Hne2 & Hlookup'')]]%Hlookup' Helt; simpl in *.
      + rewrite decide_True //.
      + rewrite decide_False.
        { intros Helt'. apply (Hdisjoint elt); done. }
        apply (model۰validｰclasses Hvalid Hlookup). naive.
      + assert (elt ∉ elts).
        { apply (model۰validｰother elt Hlookup Hlookup''); done. }
        rewrite decide_False; first set_solver.
        apply (model۰validｰclasses Hvalid Hlookup'' Helt).
    - intros repr' descr' elt [(-> & ->) | [(-> & ->) | (Hne1 & Hne2 & Hlookup'')]]%Hlookup' Helt; simpl in *.
      + rewrite decide_True // take_0 bool_decide_eq_false_2 //.
      + rewrite decide_False.
        { intros Helt'. apply (Hdisjoint elt); done. }
        rewrite ?take_0 (model۰validｰseens Hvalid Hlookup); first naive.
        rewrite !bool_decide_eq_false_2 //.
        intros Helt'. apply (Hdisjoint elt); done.
      + assert (elt ∉ elts).
        { apply (model۰validｰother elt Hlookup Hlookup''); done. }
        rewrite decide_False; first set_solver.
        apply (model۰validｰseens Hvalid Hlookup'' Helt).
    - intros repr' descr' i elt1 elt2 [(-> & ->) | [(-> & ->) | (Hne1 & Hne2 & Hlookup'')]]%Hlookup' Hlookup1 Hlookup2; simpl in *.
      + apply lookup_take_Some in Hlookup1 as (Hlookup1 & _).
        apply lookup_take_Some in Hlookup2 as (Hlookup2 & _).
        apply (model۰validｰchain Hvalid Hlookup Hlookup1 Hlookup2).
      + rewrite lookup_drop in Hlookup1.
        rewrite lookup_drop Nat.add_succ_r in Hlookup2.
        apply (model۰validｰchain Hvalid Hlookup Hlookup1 Hlookup2).
      + apply (model۰validｰchain Hvalid Hlookup'' Hlookup1 Hlookup2).
  Qed.
End model۰valid.

Record record۰inv part X descrs split_list : Prop :=
  { record۰invｰclass repr descr :
      descrs !! repr = Some descr →
        ∃ repr0,
        part !! repr0 = Some (list_to_set descr.(descriptor۰elts))
  ; record۰invｰclass' repr0 cl0 :
      part !! repr0 = Some cl0 →
        ∃ repr descr,
        descrs !! repr = Some descr ∧
        list_to_set descr.(descriptor۰elts) = cl0
  ; record۰invｰseen repr descr elt :
      descrs !! repr = Some descr →
        elt ∈ take descr.(descriptor۰seen) descr.(descriptor۰elts) ↔
          elt ∈ descr.(descriptor۰elts) ∧
          elt ∈ X ∧
          length descr.(descriptor۰elts) ≠ 1
  ; record۰invｰunseen repr descr :
      descrs !! repr = Some descr →
      descr.(descriptor۰seen) = 0 →
      part !! repr = Some (list_to_set descr.(descriptor۰elts))
  ; record۰invｰNoDup :
      NoDup split_list
  ; record۰invｰsplit_list class :
      class ∈ split_list ↔
        ∃ repr descr,
        descrs !! repr = Some descr ∧
        descr.(descriptor۰class) = class ∧
        descr.(descriptor۰seen) ≠ 0
  }.
#[local] Arguments record۰invｰclass {_ _ _ _} _ {_ _}.
#[local] Arguments record۰invｰclass' {_ _ _ _} _ {_ _}.
#[local] Arguments record۰invｰseen {_ _ _ _} _ {_ _} _ _.
#[local] Arguments record۰invｰunseen {_ _ _ _} _ {_ _}.
#[local] Arguments record۰invｰNoDup {_ _ _ _} _.
#[local] Arguments record۰invｰsplit_list {_ _ _ _} _ _.

Section record۰inv.
  Context {elements prevs nexts classes seens descrs}.
  Context (Hvalid : model۰valid elements prevs nexts classes seens descrs).
  Context {part X split_list}.
  Context (Hinv : record۰inv part X descrs split_list).

  #[local] Lemma record۰invｰsingleton {repr descr} elt :
    descrs !! repr = Some descr →
    length descr.(descriptor۰elts) = 1 →
    elt ∈ descr.(descriptor۰elts) →
    record۰inv part ({[elt]} ∪ X) descrs split_list.
  Proof.
    intros Hlookup Hlength Helt.
    constructor.
    - intros repr' descr'. apply (record۰invｰclass Hinv).
    - intros repr0 cl0. apply (record۰invｰclass' Hinv).
    - intros repr' descr' elt' Hlookup'.
      rewrite (record۰invｰseen Hinv elt' Hlookup').
      destruct (decide (repr' = repr)) as [-> | Hne].
      + simplify_eq. rewrite Hlength. naive.
      + assert (elt' ∈ descr'.(descriptor۰elts) → elt' ≠ elt).
        { intros Helt' ->. apply (model۰validｰother Hvalid elt Hlookup Hlookup'); done. }
        set_solver.
    - intros repr' descr'. apply (record۰invｰunseen Hinv).
    - apply (record۰invｰNoDup Hinv).
    - apply (record۰invｰsplit_list Hinv).
  Qed.

  #[local] Lemma record۰invｰreset {repr descr} elt :
    descrs !! repr = Some descr →
    descr.(descriptor۰elts) !! descr.(descriptor۰seen) = Some elt →
    ˖descr.(descriptor۰seen) = length descr.(descriptor۰elts) →
    length descr.(descriptor۰elts) ≠ 1 →
    record۰inv part ({[elt]} ∪ X)
      (<[repr := Descriptor descr.(descriptor۰class) descr.(descriptor۰elts) ˖descr.(descriptor۰seen)]> descrs)
      split_list.
  Proof.
    intros Hlookup Hlookup_elt Hseen Hlength.
    assert (descr.(descriptor۰seen) ≠ 0) as Hseen' by lia.
    constructor.
    - intros repr' descr' [(<- & <-) | (Hne & Hlookup')]%lookup_insert_Some.
      + apply (record۰invｰclass Hinv Hlookup).
      + apply (record۰invｰclass Hinv Hlookup').
    - intros repr0 cl0 (repr' & descr' & Hlookup' & <-)%(record۰invｰclass' Hinv).
      destruct (decide (repr' = repr)) as [-> | Hne].
      + simplify_eq. eexists repr, _. rewrite lookup_insert_eq //.
      + exists repr', descr'. rewrite lookup_insert_ne //.
    - intros repr' descr' elt' [(<- & <-) | (Hne & Hlookup')]%lookup_insert_Some.
      + simpl. rewrite take_ge; first lia.
        split; last naive.
        intros Helt'. split_and!; try done.
        apply list_elem_of_lookup in Helt' as (i & Hlookup_i).
        pose proof Hlookup_i as Hi%lookup_lt_Some.
        destruct (decide (i = descr.(descriptor۰seen))) as [-> | Hi'].
        * simplify_eq. set_solver.
        * apply elem_of_union_r.
          eapply (record۰invｰseen Hinv elt' Hlookup).
          apply elem_of_take. exists i. split; [done | lia].
      + rewrite (record۰invｰseen Hinv elt' Hlookup').
        assert (elt' ∈ descr'.(descriptor۰elts) → elt' ≠ elt).
        { intros Helt' ->. apply (model۰validｰother Hvalid elt Hlookup Hlookup'); first done.
          - done.
          - eapply list_elem_of_lookup_2. done.
        }
        set_solver.
    - intros repr' descr' [(<- & <-) | (Hne & Hlookup')]%lookup_insert_Some.
      + simpl. lia.
      + apply (record۰invｰunseen Hinv Hlookup').
    - apply (record۰invｰNoDup Hinv).
    - intros class. rewrite (record۰invｰsplit_list Hinv). split.
      + intros (repr' & descr' & Hlookup' & <- & Hseen'').
        destruct (decide (repr' = repr)) as [-> | Hne].
        * simplify_eq. eexists repr, _. rewrite lookup_insert_eq //.
        * exists repr', descr'. rewrite lookup_insert_ne //.
      + intros (repr' & descr' & [(<- & <-) | (Hne & Hlookup')]%lookup_insert_Some & <- & Hseen'').
        * exists repr, descr. done.
        * exists repr', descr'. done.
  Qed.

  #[local] Lemma record۰invｰstep {repr descr} split elt :
    descrs !! repr = Some descr →
    descr.(descriptor۰elts) !! descr.(descriptor۰seen) = Some split →
    elt ∈ descr.(descriptor۰elts) →
    elt ∉ take descr.(descriptor۰seen) descr.(descriptor۰elts) →
    length descr.(descriptor۰elts) ≠ 1 →
    record۰inv part ({[elt]} ∪ X)
      (<[swap split elt repr := Descriptor descr.(descriptor۰class) (swap split elt <$> descr.(descriptor۰elts)) ˖descr.(descriptor۰seen)]> (delete repr descrs))
      (if decide (descr.(descriptor۰seen) = 0) then descr.(descriptor۰class) :: split_list else split_list).
  Proof.
    intros Hlookup Hlookup_split Helt Helt_seen Hlength.
    pose proof (model۰validｰNoDup Hvalid Hlookup) as Hnodup.
    pose proof (model۰validｰrepr Hvalid Hlookup) as Hrepr.
    assert (split ∈ descr.(descriptor۰elts)) as Hsplit.
    { eapply list_elem_of_lookup_2. done. }
    assert (split ∉ take descr.(descriptor۰seen) descr.(descriptor۰elts)) as Hsplit_seen.
    { rewrite elem_of_take. intros (i & Hlookup_i & Hi).
      opose proof* (NoDup_lookup _ i descr.(descriptor۰seen)); [done.. | lia].
    }
    assert (elt ∉ X) as Helt_X.
    { intros HX. apply Helt_seen. apply (record۰invｰseen Hinv elt Hlookup). done. }
    set descr' := Descriptor descr.(descriptor۰class) (swap split elt <$> descr.(descriptor۰elts)) ˖descr.(descriptor۰seen).
    assert (
      ∀ repr' descr'',
      <[swap split elt repr := descr']> (delete repr descrs) !! repr' = Some descr'' ↔
          repr' = swap split elt repr ∧
          descr'' = descr'
        ∨ repr' ≠ repr ∧
          descrs !! repr' = Some descr''
    ) as Hlookup'.
    { intros repr' descr''.
      rewrite lookup_insert_Some lookup_delete_Some. split.
      - intros [(<- & <-) | (_ & Hne & Hlookup')]; naive.
      - intros [(-> & ->) | (Hne & Hlookup')]; first naive.
        right. split_and!; try done.
        intros Heq.
        apply (model۰validｰother Hvalid repr' Hlookup Hlookup'); first done.
        + apply (model۰validｰrepr Hvalid Hlookup').
        + rewrite -Heq swapｰelem_of //.
    }
    assert (list_to_set descr'.(descriptor۰elts) = list_to_set (C := gset location) descr.(descriptor۰elts)) as Hdescr'_elts.
    { apply set_eq. intros elt'.
      rewrite /= !elem_of_list_to_set swapｰfmapｰelem_of //.
    }
    assert (take ˖descr.(descriptor۰seen) descr'.(descriptor۰elts) = take descr.(descriptor۰seen) descr.(descriptor۰elts) ++ [elt]) as Htake.
    { rewrite /= -fmap_take (take_S_r _ _ split) // fmap_app swapｰfmapｰid // /= swapｰl //. }
    constructor.
    - intros repr' descr'' [(-> & ->) | (Hne & Hlookup'')]%Hlookup'.
      + rewrite Hdescr'_elts. apply (record۰invｰclass Hinv Hlookup).
      + apply (record۰invｰclass Hinv Hlookup'').
    - intros repr0 cl0 (repr' & descr'' & Hlookup'' & <-)%(record۰invｰclass' Hinv).
      destruct (decide (repr' = repr)) as [-> | Hne].
      + simplify_eq. exists (swap split elt repr), descr'. rewrite Hlookup'. naive.
      + exists repr', descr''. rewrite Hlookup'. naive.
    - intros repr' descr'' elt' [(-> & ->) | (Hne & Hlookup'')]%Hlookup'.
      + rewrite Htake elem_of_app list_elem_of_singleton (record۰invｰseen Hinv _ Hlookup).
        rewrite /= swapｰfmapｰelem_of // length_fmap.
        set_solver.
      + rewrite (record۰invｰseen Hinv elt' Hlookup'').
        assert (elt' ∈ descr''.(descriptor۰elts) → elt' ≠ elt).
        { intros Helt' ->. apply (model۰validｰother Hvalid elt Hlookup Hlookup''); done. }
        set_solver.
    - intros repr' descr'' [(-> & ->) | (Hne & Hlookup'')]%Hlookup'.
      + simpl. lia.
      + apply (record۰invｰunseen Hinv Hlookup'').
    - destruct (decide (descr.(descriptor۰seen) = 0)) as [Hseen | Hseen].
      + apply NoDup_cons. split; last apply (record۰invｰNoDup Hinv).
        rewrite (record۰invｰsplit_list Hinv).
        intros (repr' & descr'' & Hlookup'' & Hclass & Hseen'').
        opose proof* (model۰validｰclass Hvalid Hlookup Hlookup''); first done.
        simplify_eq.
      + apply (record۰invｰNoDup Hinv).
    - intros class. setoid_rewrite Hlookup'.
      destruct (decide (descr.(descriptor۰seen) = 0)) as [Hseen | Hseen].
      + rewrite elem_of_cons (record۰invｰsplit_list Hinv). split.
        * intros [-> | (repr' & descr'' & Hlookup'' & <- & Hseen'')].
          -- exists (swap split elt repr), descr'. split_and!; [left; done | done | simpl; lia].
          -- exists repr', descr''. split_and!; try done.
             right. split; last done.
             intros ->. simplify_eq.
        * intros (repr' & descr'' & [(-> & ->) | (Hne & Hlookup'')] & <- & Hseen'').
          -- left. done.
          -- right. exists repr', descr''. done.
      + rewrite (record۰invｰsplit_list Hinv). split.
        * intros (repr' & descr'' & Hlookup'' & <- & Hseen'').
          destruct (decide (repr' = repr)) as [-> | Hne].
          -- simplify_eq. exists (swap split elt repr), descr'. split_and!; [left; done | done | simpl; lia].
          -- exists repr', descr''. split_and!; try done. right. done.
        * intros (repr' & descr'' & [(-> & ->) | (Hne & Hlookup'')] & <- & Hseen'').
          -- exists repr, descr. done.
          -- exists repr', descr''. done.
  Qed.
End record۰inv.

#[local] Lemma record۰invｰinit descrs :
  map_Forall (λ _ descr, descr.(descriptor۰seen) = 0) descrs →
  record۰inv ((λ descr, list_to_set descr.(descriptor۰elts)) <$> descrs) ∅ descrs [].
Proof.
  intros Hunseen.
  constructor.
  - intros repr descr Hlookup.
    exists repr. rewrite lookup_fmap Hlookup //.
  - intros repr0 cl0 (descr & Hcl0 & Hlookup)%lookup_fmap_Some.
    exists repr0, descr. done.
  - intros repr descr elt Hlookup.
    rewrite (Hunseen _ _ Hlookup) take_0. set_solver.
  - intros repr descr Hlookup _.
    rewrite lookup_fmap Hlookup //.
  - apply NoDup_nil_2.
  - intros class. split; first set_solver.
    intros (repr & descr & Hlookup & _ & Hseen).
    exfalso. apply Hseen, (Hunseen _ _ Hlookup).
Qed.

Record split۰inv part X descrs split_list : Prop :=
  { split۰invｰpending repr descr :
      descrs !! repr = Some descr →
      descr.(descriptor۰class) ∈ split_list →
        descr.(descriptor۰seen) ≠ 0 ∧
        ( ∃ repr0,
          part !! repr0 = Some (list_to_set descr.(descriptor۰elts))
        ) ∧
        ( ∀ elt,
          elt ∈ take descr.(descriptor۰seen) descr.(descriptor۰elts) ↔
            elt ∈ descr.(descriptor۰elts) ∧
            elt ∈ X
        )
  ; split۰invｰdone repr descr :
      descrs !! repr = Some descr →
      descr.(descriptor۰class) ∉ split_list →
        descr.(descriptor۰seen) = 0 ∧
        ∃ repr0 cl0,
        part !! repr0 = Some cl0 ∧
        ( list_to_set descr.(descriptor۰elts) = cl0 ∩ X
        ∨ list_to_set descr.(descriptor۰elts) = cl0 ∖ X
        )
  ; split۰invｰcomplete repr0 cl0 :
      part !! repr0 = Some cl0 →
        ( ∃ repr descr,
          descrs !! repr = Some descr ∧
          descr.(descriptor۰class) ∈ split_list ∧
          list_to_set descr.(descriptor۰elts) = cl0
        ) ∨ (
          ∀ cl,
          (cl = cl0 ∩ X ∨ cl = cl0 ∖ X) →
          cl ≠ ∅ →
            ∃ repr descr,
            descrs !! repr = Some descr ∧
            descr.(descriptor۰class) ∉ split_list ∧
            list_to_set descr.(descriptor۰elts) = cl
        )
  ; split۰invｰuntouched repr0 cl0 :
      part !! repr0 = Some cl0 →
      cl0 ## X →
        ∃ descr,
        descrs !! repr0 = Some descr ∧
        list_to_set descr.(descriptor۰elts) = cl0
  ; split۰invｰNoDup :
      NoDup split_list
  ; split۰invｰsplit_list class :
      class ∈ split_list →
        ∃ repr descr,
        descrs !! repr = Some descr ∧
        descr.(descriptor۰class) = class
  }.
#[local] Arguments split۰invｰpending {_ _ _ _} _ {_ _}.
#[local] Arguments split۰invｰdone {_ _ _ _} _ {_ _}.
#[local] Arguments split۰invｰcomplete {_ _ _ _} _ {_ _}.
#[local] Arguments split۰invｰuntouched {_ _ _ _} _ {_ _}.
#[local] Arguments split۰invｰNoDup {_ _ _ _} _.
#[local] Arguments split۰invｰsplit_list {_ _ _ _} _ {_}.

Section split۰inv.
  Context {elements prevs nexts classes seens descrs}.
  Context (Hvalid : model۰valid elements prevs nexts classes seens descrs).

  #[local] Lemma split۰invｰinit {part X split_list} :
    ( ∀ repr1 repr2 cl,
      part !! repr1 = Some cl →
      part !! repr2 = Some cl →
      repr1 = repr2
    ) →
    record۰inv part X descrs split_list →
    split۰inv part X descrs split_list.
  Proof.
    intros Hpart Hinv.
    assert (
      ∀ repr descr,
      descrs !! repr = Some descr →
      descr.(descriptor۰seen) = 0 →
        list_to_set (C := gset location) descr.(descriptor۰elts) ∩ X = ∅ ∨
        list_to_set (C := gset location) descr.(descriptor۰elts) ⊆ X
    ) as Hunseen.
    { intros repr descr Hlookup Hseen.
      destruct (decide (length descr.(descriptor۰elts) = 1)) as [Hlength | Hlength].
      - destruct descr.(descriptor۰elts) as [| elt [|]] eqn:Helts; try done.
        destruct (decide (elt ∈ X)); [right | left]; set_solver.
      - left. apply set_eq. intros elt.
        rewrite elem_of_intersection elem_of_list_to_set.
        split; last set_solver.
        intros (Helt & HX).
        opose proof* (proj2 (record۰invｰseen Hinv elt Hlookup)) as Helt'; first done.
        rewrite Hseen take_0 in Helt'. set_solver.
    }
    assert (
      ∀ class,
      class ∉ split_list →
      ∀ repr descr,
      descrs !! repr = Some descr →
      descr.(descriptor۰class) = class →
      descr.(descriptor۰seen) = 0
    ) as Hsplit_list.
    { intros class Hclass repr descr Hlookup <-.
      destruct (decide (descr.(descriptor۰seen) = 0)) as [? | Hseen]; first done.
      exfalso. apply Hclass, (record۰invｰsplit_list Hinv). naive.
    }
    constructor.
    - intros repr descr Hlookup Hclass.
      apply (record۰invｰsplit_list Hinv) in Hclass as (repr' & descr' & Hlookup' & Hclass & Hseen).
      opose proof* (model۰validｰclass Hvalid Hlookup' Hlookup); first done.
      simplify_eq.
      split_and!; first done.
      + apply (record۰invｰclass Hinv Hlookup).
      + intros elt. rewrite (record۰invｰseen Hinv elt Hlookup).
        split; first naive.
        intros (Helt & HX). split_and!; try done.
        intros Hlength.
        pose proof (model۰validｰseen Hvalid Hlookup) as Hseen_le.
        opose proof* (proj1 (record۰invｰseen Hinv elt Hlookup)) as (_ & _ & Hlength').
        { rewrite take_ge //. lia. }
        done.
    - intros repr descr Hlookup Hclass.
      pose proof (Hsplit_list _ Hclass _ _ Hlookup eq_refl) as Hseen.
      split; first done.
      exists repr, (list_to_set descr.(descriptor۰elts)).
      split; first apply (record۰invｰunseen Hinv Hlookup Hseen).
      destruct (Hunseen _ _ Hlookup Hseen); [right | left]; set_solver.
    - intros repr0 cl0 Hlookup0.
      pose proof Hlookup0 as (repr & descr & Hlookup & Hcl0)%(record۰invｰclass' Hinv).
      destruct (decide (descr.(descriptor۰class) ∈ split_list)) as [Hclass | Hclass].
      + left. naive.
      + right. intros cl Hcl Hcl_ne.
        pose proof (Hsplit_list _ Hclass _ _ Hlookup eq_refl) as Hseen.
        exists repr, descr. split_and!; try done.
        destruct (Hunseen _ _ Hlookup Hseen); set_solver.
    - intros repr0 cl0 Hlookup0 Hdisjoint.
      pose proof Hlookup0 as (repr & descr & Hlookup & Hcl0)%(record۰invｰclass' Hinv).
      exists descr. split; last done.
      assert (descr.(descriptor۰seen) = 0) as Hseen.
      { destruct (decide (descr.(descriptor۰seen) = 0)) as [? | Hseen]; first done.
        exfalso.
        pose proof (model۰validｰseen Hvalid Hlookup) as Hseen_le.
        destruct (lookup_lt_is_Some_2 descr.(descriptor۰elts) 0) as (elt & Hlookup_elt); first lia.
        opose proof* (proj1 (record۰invｰseen Hinv elt Hlookup)) as (Helt & HX & _).
        { apply elem_of_take. exists 0. split; [done | lia]. }
        set_solver.
      }
      pose proof (record۰invｰunseen Hinv Hlookup Hseen) as Hlookup0'.
      assert (repr0 = repr) as ->.
      { apply (Hpart repr0 repr cl0); first done. rewrite -Hcl0 //. }
      done.
    - apply (record۰invｰNoDup Hinv).
    - intros class (repr & descr & Hlookup & Hclass & _)%(record۰invｰsplit_list Hinv).
      naive.
  Qed.

  #[local] Lemma split۰invｰreset {part X class split_list repr descr} :
    split۰inv part X descrs (class :: split_list) →
    descrs !! repr = Some descr →
    descr.(descriptor۰class) = class →
    descr.(descriptor۰seen) = length descr.(descriptor۰elts) →
    split۰inv part X (<[repr := Descriptor class descr.(descriptor۰elts) 0]> descrs) split_list.
  Proof.
    intros Hinv Hlookup Hclass Hseen.
    pose proof (split۰invｰNoDup Hinv) as (Hclass_split_list & Hnodup)%NoDup_cons.
    opose proof* (split۰invｰpending Hinv Hlookup) as (Hseen' & (repr0 & Hlookup0) & Htake).
    { rewrite Hclass. set_solver. }
    rewrite take_ge in Htake; first lia.
    assert (
      ∀ repr' descr',
      descrs !! repr' = Some descr' →
      descr'.(descriptor۰class) = class →
      repr' = repr
    ) as Hclass_unique.
    { intros repr' descr' Hlookup' Hclass'.
      apply (model۰validｰclass Hvalid Hlookup' Hlookup). congruence.
    }
    pose proof (model۰validｰrepr Hvalid Hlookup) as Hrepr.
    constructor.
    - intros repr' descr' [(<- & <-) | (Hne & Hlookup')]%lookup_insert_Some Hclass'.
      + done.
      + apply (split۰invｰpending Hinv Hlookup'). set_solver.
    - intros repr' descr' [(<- & <-) | (Hne & Hlookup')]%lookup_insert_Some Hclass'.
      + split; first done.
        exists repr0, (list_to_set descr.(descriptor۰elts)). split; first done.
        left. set_solver.
      + apply (split۰invｰdone Hinv Hlookup').
        intros [Hclass'' | Hclass'']%elem_of_cons; last done.
        apply Hne. symmetry. apply (Hclass_unique _ _ Hlookup' Hclass'').
    - intros repr0' cl0 Hlookup0'.
      destruct (split۰invｰcomplete Hinv Hlookup0') as [(repr' & descr' & Hlookup' & Hclass' & Hcl0) | Hcomplete].
      + destruct (decide (descr'.(descriptor۰class) = class)) as [Hclass'' | Hclass''].
        * pose proof (Hclass_unique _ _ Hlookup' Hclass'') as ->. simplify_eq.
          right. intros cl [-> | ->] Hcl.
          -- exists repr, (Descriptor descr.(descriptor۰class) descr.(descriptor۰elts) 0).
             rewrite lookup_insert_eq. split_and!; try done.
             set_solver.
          -- exfalso. apply Hcl. set_solver.
        * left. exists repr', descr'.
          rewrite lookup_insert_ne; first (intros ->; simplify_eq).
          set_solver.
      + right. intros cl Hcl Hcl_ne.
        destruct (Hcomplete cl Hcl Hcl_ne) as (repr' & descr' & Hlookup' & Hclass' & Hcl').
        exists repr', descr'.
        rewrite lookup_insert_ne; first (intros ->; simplify_eq; set_solver).
        set_solver.
    - intros repr0' cl0 Hlookup0' Hdisjoint.
      destruct (split۰invｰuntouched Hinv Hlookup0' Hdisjoint) as (descr' & Hlookup' & Hcl0).
      exists descr'.
      rewrite lookup_insert_ne; last done.
      intros ->. simplify_eq.
      set_solver.
    - done.
    - intros class' Hclass'.
      destruct (split۰invｰsplit_list Hinv (class := class')) as (repr' & descr' & Hlookup' & <-); first set_solver.
      exists repr', descr'.
      rewrite lookup_insert_ne; first (intros ->; simplify_eq).
      done.
  Qed.

  #[local] Lemma split۰invｰsplit {part X class split_list repr descr} class' split :
    split۰inv part X descrs (class :: split_list) →
    descrs !! repr = Some descr →
    descr.(descriptor۰class) = class →
    descr.(descriptor۰seen) < length descr.(descriptor۰elts) →
    descr.(descriptor۰elts) !! descr.(descriptor۰seen) = Some split →
    ( ∀ repr' descr',
      descrs !! repr' = Some descr' →
      descr'.(descriptor۰class) ≠ class'
    ) →
    split۰inv part X
      ( <[repr := Descriptor class' (take descr.(descriptor۰seen) descr.(descriptor۰elts)) 0]> $
        <[split := Descriptor class (drop descr.(descriptor۰seen) descr.(descriptor۰elts)) 0]> descrs
      )
      split_list.
  Proof.
    intros Hinv Hlookup Hclass Hseen_lt Hlookup_split Hclass'.
    pose proof (split۰invｰNoDup Hinv) as (Hclass_split_list & Hnodup)%NoDup_cons.
    opose proof* (split۰invｰpending Hinv Hlookup) as (Hseen & (repr0 & Hlookup0) & Htake).
    { rewrite Hclass. set_solver. }
    destruct descr as [descr_class elts n]. simpl in *. subst descr_class.
    pose proof (model۰validｰNoDup Hvalid Hlookup) as Hnodup_elts.
    pose proof Hnodup_elts as Hnodup_elts'.
    rewrite -(take_drop n elts) in Hnodup_elts'.
    apply NoDup_app in Hnodup_elts' as (_ & Hdisjoint & _).
    assert (
      ∀ elt,
      elt ∈ elts ↔
          elt ∈ take n elts
        ∨ elt ∈ drop n elts
    ) as Helts.
    { intros elt. rewrite -elem_of_app take_drop //. }
    assert (split ∈ drop n elts) as Hsplit.
    { apply head_Some_elem_of. rewrite head_lookup lookup_drop Nat.add_0_r //. }
    pose proof (model۰validｰrepr Hvalid Hlookup) as Hrepr.
    assert (repr ∈ take n elts) as Hrepr_take.
    { apply head_Some_elem_of. rewrite head_lookup lookup_take_Some -head_lookup (model۰validｰhead Hvalid Hlookup). split; [done | lia]. }
    assert (repr ≠ split) as Hne_split.
    { intros ->. apply (Hdisjoint split); done. }
    assert (descrs !! split = None) as Hlookup_split'.
    { destruct (descrs !! split) as [descr' |] eqn:Hlookup'; last done.
      exfalso. apply Hne_split.
      apply (model۰validｰdisjoint Hvalid split Hlookup Hlookup').
      - simpl. rewrite Helts. naive.
      - apply (model۰validｰrepr Hvalid Hlookup').
    }
    assert (
      ∀ repr' descr',
      descrs !! repr' = Some descr' →
      descr'.(descriptor۰class) = class →
      repr' = repr
    ) as Hclass_unique.
    { intros repr' descr' Hlookup' Hclass''.
      apply (model۰validｰclass Hvalid Hlookup' Hlookup). done.
    }
    assert (class' ∉ split_list) as Hclass'_split_list.
    { intros Hclass''.
      destruct (split۰invｰsplit_list Hinv (class := class')) as (repr' & descr' & Hlookup' & Hclass'''); first set_solver.
      apply (Hclass' _ _ Hlookup' Hclass''').
    }
    assert (list_to_set (C := gset location) (take n elts) = list_to_set elts ∩ X) as Htake'.
    { apply set_eq. intros elt. rewrite elem_of_intersection !elem_of_list_to_set Htake //. }
    assert (list_to_set (C := gset location) (drop n elts) = list_to_set elts ∖ X) as Hdrop'.
    { apply set_eq. intros elt.
      rewrite elem_of_difference !elem_of_list_to_set.
      split.
      - intros Helt. split; first (apply Helts; naive).
        intros HX. apply (Hdisjoint elt); last done.
        apply Htake. split; last done. apply Helts. naive.
      - intros (Helt & HX). apply Helts in Helt as [Helt | Helt]; last done.
        exfalso. apply HX. apply Htake. done.
    }
    set descr1 := Descriptor class' (take n elts) 0.
    set descr2 := Descriptor class (drop n elts) 0.
    assert (
      ∀ repr' descr',
      <[repr := descr1]> (<[split := descr2]> descrs) !! repr' = Some descr' ↔
          repr' = repr ∧
          descr' = descr1
        ∨ repr' = split ∧
          descr' = descr2
        ∨ repr' ≠ repr ∧
          repr' ≠ split ∧
          descrs !! repr' = Some descr'
    ) as Hlookup'.
    { intros repr' descr'.
      rewrite !lookup_insert_Some. naive.
    }
    constructor.
    - intros repr' descr' [(-> & ->) | [(-> & ->) | (Hne1 & Hne2 & Hlookup'')]]%Hlookup' Hclass''.
      + done.
      + done.
      + apply (split۰invｰpending Hinv Hlookup''). set_solver.
    - intros repr' descr' [(-> & ->) | [(-> & ->) | (Hne1 & Hne2 & Hlookup'')]]%Hlookup' Hclass''.
      + split; first done.
        exists repr0, (list_to_set elts). naive.
      + split; first done.
        exists repr0, (list_to_set elts). naive.
      + apply (split۰invｰdone Hinv Hlookup'').
        intros [Hclass''' | Hclass''']%elem_of_cons; last done.
        apply Hne1. apply (Hclass_unique _ _ Hlookup'' Hclass''').
    - intros repr0' cl0 Hlookup0'.
      destruct (split۰invｰcomplete Hinv Hlookup0') as [(repr' & descr' & Hlookup'' & Hclass'' & Hcl0) | Hcomplete].
      + destruct (decide (descr'.(descriptor۰class) = class)) as [Hclass''' | Hclass'''].
        * pose proof (Hclass_unique _ _ Hlookup'' Hclass''') as ->.
          rewrite Hlookup in Hlookup''. injection Hlookup'' as <-.
          simpl in Hcl0. subst cl0.
          right. intros cl [-> | ->] Hcl.
          -- exists repr, descr1. rewrite Hlookup'.
             split_and!; [left; done | done | done].
          -- exists split, descr2. rewrite Hlookup'.
             split_and!; [right; left; done | done | done].
        * left. exists repr', descr'.
          rewrite Hlookup'. split_and!.
          -- right. right. split_and!; try done.
             ++ intros ->. apply Hclass'''.
                rewrite Hlookup in Hlookup''. injection Hlookup'' as <-. done.
             ++ intros ->. congruence.
          -- apply elem_of_cons in Hclass'' as [? | ?]; done.
          -- done.
      + right. intros cl Hcl Hcl_ne.
        destruct (Hcomplete cl Hcl Hcl_ne) as (repr' & descr' & Hlookup'' & Hclass'' & Hcl').
        exists repr', descr'.
        rewrite Hlookup'. split_and!.
        * right. right. split_and!; try done.
          -- intros ->. apply Hclass''.
             rewrite Hlookup in Hlookup''. injection Hlookup'' as <-.
             apply elem_of_cons. left. done.
          -- intros ->. congruence.
        * intros ?. apply Hclass''. apply elem_of_cons. right. done.
        * done.
    - intros repr0' cl0 Hlookup0' Hdisjoint'.
      destruct (split۰invｰuntouched Hinv Hlookup0' Hdisjoint') as (descr' & Hlookup'' & Hcl0).
      exists descr'. rewrite Hlookup'. split; last done.
      right. right. split_and!; try done.
      + intros ->. simplify_eq.
        apply (Hdisjoint' repr); last first.
        * apply Htake. done.
        * apply elem_of_list_to_set. done.
      + intros ->. congruence.
    - done.
    - intros class'' Hclass''.
      destruct (split۰invｰsplit_list Hinv (class := class'')) as (repr' & descr' & Hlookup'' & <-); first set_solver.
      exists repr', descr'. rewrite Hlookup'. split; last done.
      right. right. split_and!; try done.
      + intros ->. simplify_eq.
      + intros ->. congruence.
    Qed.

  #[local] Lemma split۰invｰfinal {part X} :
    split۰inv part X descrs [] →
      map_Forall (λ _ descr, descr.(descriptor۰seen) = 0) descrs ∧
      ( ∀ cl',
        cl' ∈ map_img (SA := gset (gset location)) ((λ descr, list_to_set descr.(descriptor۰elts)) <$> descrs) ↔
          cl' ≠ ∅ ∧
            ∃ repr cl,
            part !! repr = Some cl ∧
            ( cl' = cl ∩ X
            ∨ cl' = cl ∖ X
            )
      ) ∧
      ( ∀ repr cl,
        part !! repr = Some cl →
        cl ## X →
        ((λ descr, list_to_set descr.(descriptor۰elts)) <$> descrs) !! repr = Some cl
      ).
  Proof.
    intros Hinv. split_and!.
    - intros repr descr Hlookup.
      apply (split۰invｰdone Hinv Hlookup). apply not_elem_of_nil.
    - intros cl'. rewrite elem_of_map_img. split.
      + intros (repr & (descr & Hcl' & Hlookup)%lookup_fmap_Some). subst cl'.
        destruct (split۰invｰdone Hinv Hlookup) as (_ & repr0 & cl0 & Hlookup0 & Hcl); first apply not_elem_of_nil.
        split; last naive.
        pose proof (model۰validｰrepr Hvalid Hlookup). set_solver.
      + intros (Hcl'_ne & repr0 & cl0 & Hlookup0 & Hcl').
        destruct (split۰invｰcomplete Hinv Hlookup0) as [(repr & descr & Hlookup & Hclass & _) | Hcomplete].
        * set_solver.
        * destruct (Hcomplete cl' Hcl' Hcl'_ne) as (repr & descr & Hlookup & _ & <-).
          exists repr. rewrite lookup_fmap Hlookup //.
    - intros repr cl Hlookup Hdisjoint.
      destruct (split۰invｰuntouched Hinv Hlookup Hdisjoint) as (descr & Hlookup' & <-).
      rewrite lookup_fmap Hlookup' //.
  Qed.
End split۰inv.

Section partition۰G.
  Context `{partition۰G : PartitionG Σ}.

  #[local] Definition elements۰auth γ elements :=
    mono_gset۰auth γ.(partition۰name۰elements) (DfracOwn 1) elements.
  #[local] Definition elements۰elem γ elt :=
    mono_gset۰elem γ.(partition۰name۰elements) elt.

  #[local] Definition nodes elements prevs nexts classes seens : iProp Σ :=
    [∗ set] elt ∈ elements,
      elt.[prev] ↦ #(prevs elt) ∗
      elt.[next] ↦ #(nexts elt) ∗
      elt.[class_] ↦ #(classes elt) ∗
      elt.[seen] ↦ #(seens elt).

  #[local] Definition descriptor۰model repr descr : iProp Σ :=
    ∃ last,
    ⌜list.last descr.(descriptor۰elts) = Some last⌝ ∗
    descr.(descriptor۰class).[first] ↦ #repr ∗
    descr.(descriptor۰class).[last] ↦ #last ∗
    descr.(descriptor۰class).[len] ↦ #(length descr.(descriptor۰elts)) ∗
    descr.(descriptor۰class).[split] ↦ #(default repr (descr.(descriptor۰elts) !! descr.(descriptor۰seen))) ∗
    descr.(descriptor۰class).[split_len] ↦ #(if decide (descr.(descriptor۰seen) = length descr.(descriptor۰elts)) then 0 else descr.(descriptor۰seen)).
  #[local] Instance : CustomIpat "descriptor۰model" :=
    " ( %last{}
      & %Hlast{}
      & Hclass{}_first
      & Hclass{}_last
      & Hclass{}_len
      & Hclass{}_split
      & Hclass{}_split_len
      )
    ".

  #[local] Definition model' γ elements prevs nexts classes seens descrs : iProp Σ :=
    ⌜model۰valid elements prevs nexts classes seens descrs⌝ ∗
    elements۰auth γ elements ∗
    nodes elements prevs nexts classes seens ∗
    [∗ map] repr ↦ descr ∈ descrs,
      descriptor۰model repr descr.
  #[local] Instance : CustomIpat "model'" :=
    " ( %Hvalid{}
      & Helements_auth{}
      & Hnodes{}
      & Hdescrs{}
      )
    ".

  Please Definition partition۰model γ part : iProp Σ :=
    ∃ elements prevs nexts classes seens descrs,
    ⌜part = (λ descr, list_to_set descr.(descriptor۰elts)) <$> descrs⌝ ∗
    ⌜map_Forall (λ _ descr, descr.(descriptor۰seen) = 0) descrs⌝ ∗
    model' γ elements prevs nexts classes seens descrs.
  #[local] Instance : CustomIpat "model" :=
    " ( %elements{}
      & %prevs{}
      & %nexts{}
      & %classes{}
      & %seens{}
      & %descrs{}
      & ->
      & %Hunseen{}
      & (:model' /={})
      )
    ".

  Please Definition partition۰element γ elt v : iProp Σ :=
    elements۰elem γ elt ∗
    elt.[data] ↦□ v.
  #[local] Instance : CustomIpat "element" :=
    " ( #Helements_elem{}
      & #Helt{}_data
      )
    ".

  Zoo derive Timeless for partition۰model.
  Zoo derive Timeless for partition۰element.

  Zoo derive Persistent for partition۰element.

  Record partition۰valid part :=
    { partition۰validｰrepr repr cl :
        part !! repr = Some cl →
        repr ∈ cl
    ; partition۰validｰdisjoint repr1 cl1 repr2 cl2 :
        part !! repr1 = Some cl1 →
        part !! repr2 = Some cl2 →
        repr1 ≠ repr2 →
        cl1 ## cl2
    }.

  #[local] Lemma elementsｰalloc :
    ⊢ |==>
      ∃ γ_elements,
      mono_gset۰auth γ_elements (DfracOwn 1) (∅ : gset location).
  Proof.
    apply mono_gsetｰalloc.
  Qed.
  #[local] Lemma elements۰elemｰvalid γ elements elt :
    elements۰auth γ elements -∗
    elements۰elem γ elt -∗
    ⌜elt ∈ elements⌝.
  Proof.
    apply mono_gset۰elemｰvalid.
  Qed.
  #[local] Lemma elementsｰinsert {γ elements} elt :
    elements۰auth γ elements ⊢ |==>
      elements۰auth γ ({[elt]} ∪ elements) ∗
      elements۰elem γ elt.
  Proof.
    apply mono_gsetｰinsert'.
  Qed.

  #[local] Lemma nodesｰproper elements prevs1 nexts1 classes1 seens1 prevs2 nexts2 classes2 seens2 :
    ( ∀ elt,
      elt ∈ elements →
        prevs1 elt = prevs2 elt ∧
        nexts1 elt = nexts2 elt ∧
        classes1 elt = classes2 elt ∧
        seens1 elt = seens2 elt
    ) →
    nodes elements prevs1 nexts1 classes1 seens1 ⊢
    nodes elements prevs2 nexts2 classes2 seens2.
  Proof.
    iIntros "%Heq Hnodes".
    iApply (big_sepS_impl with "Hnodes"). iIntros "!> %elt %Helt".
    destruct (Heq elt Helt) as (Hprev & Hnext & Hclass & Hseen).
    rewrite Hprev Hnext Hclass Hseen. iIntros "$".
  Qed.
  #[local] Lemma nodesｰacc {elements prevs nexts classes seens} elt :
    elt ∈ elements →
    nodes elements prevs nexts classes seens ⊢
      elt.[prev] ↦ #(prevs elt) ∗
      elt.[next] ↦ #(nexts elt) ∗
      elt.[class_] ↦ #(classes elt) ∗
      elt.[seen] ↦ #(seens elt) ∗
      ( ∀ (elt_prev elt_next elt_class : location) (elt_seen : bool),
        elt.[prev] ↦ #elt_prev -∗
        elt.[next] ↦ #elt_next -∗
        elt.[class_] ↦ #elt_class -∗
        elt.[seen] ↦ #elt_seen -∗
        nodes elements
          (<[elt := elt_prev]> prevs)
          (<[elt := elt_next]> nexts)
          (<[elt := elt_class]> classes)
          (<[elt := elt_seen]> seens)
      ).
  Proof.
    iIntros "%Helt Hnodes".
    iDestruct (big_sepS_delete with "Hnodes") as "((Helt_prev & Helt_next & Helt_class & Helt_seen) & Hnodes)"; first done.
    iFrame. iIntros "%elt_prev %elt_next %elt_class %elt_seen Helt_prev Helt_next Helt_class Helt_seen".
    iApply (big_sepS_delete _ _ elt); first done.
    rewrite !fn_lookup_insert. iFrame.
    iApply (big_sepS_impl with "Hnodes"). iIntros "!> %elt' %Helt'".
    assert (elt ≠ elt') by set_solver.
    rewrite !fn_lookup_insert_ne //. iIntros "$".
  Qed.
  #[local] Lemma nodesｰlookupｰacc {elements prevs nexts classes seens} elt :
    elt ∈ elements →
    nodes elements prevs nexts classes seens ⊢
      elt.[prev] ↦ #(prevs elt) ∗
      elt.[next] ↦ #(nexts elt) ∗
      elt.[class_] ↦ #(classes elt) ∗
      elt.[seen] ↦ #(seens elt) ∗
      ( elt.[prev] ↦ #(prevs elt) -∗
        elt.[next] ↦ #(nexts elt) -∗
        elt.[class_] ↦ #(classes elt) -∗
        elt.[seen] ↦ #(seens elt) -∗
        nodes elements prevs nexts classes seens
      ).
  Proof.
    iIntros "%Helt Hnodes".
    iDestruct (big_sepS_delete with "Hnodes") as "((Helt_prev & Helt_next & Helt_class & Helt_seen) & Hnodes)"; first done.
    iFrame. iIntros "Helt_prev Helt_next Helt_class Helt_seen".
    iApply (big_sepS_delete _ _ elt); first done.
    iFrame.
  Qed.
  #[local] Lemma nodesｰprevｰacc {elements prevs nexts classes seens} elt :
    elt ∈ elements →
    nodes elements prevs nexts classes seens ⊢
      elt.[prev] ↦ #(prevs elt) ∗
      ( ∀ (elt_prev : location),
        elt.[prev] ↦ #elt_prev -∗
        nodes elements (<[elt := elt_prev]> prevs) nexts classes seens
      ).
  Proof.
    iIntros "%Helt Hnodes".
    iDestruct (nodesｰacc with "Hnodes") as "($ & Helt_next & Helt_class & Helt_seen & Hnodes)"; first done.
    iIntros "%elt_prev Helt_prev".
    iDestruct ("Hnodes" with "Helt_prev Helt_next Helt_class Helt_seen") as "Hnodes".
    iApply (nodesｰproper with "Hnodes"). intros elt' _.
    rewrite /insert /fn_insert. repeat case_decide; naive.
  Qed.
  #[local] Lemma nodesｰnextｰacc {elements prevs nexts classes seens} elt :
    elt ∈ elements →
    nodes elements prevs nexts classes seens ⊢
      elt.[next] ↦ #(nexts elt) ∗
      ( ∀ (elt_next : location),
        elt.[next] ↦ #elt_next -∗
        nodes elements prevs (<[elt := elt_next]> nexts) classes seens
      ).
  Proof.
    iIntros "%Helt Hnodes".
    iDestruct (nodesｰacc with "Hnodes") as "(Helt_prev & $ & Helt_class & Helt_seen & Hnodes)"; first done.
    iIntros "%elt_next Helt_next".
    iDestruct ("Hnodes" with "Helt_prev Helt_next Helt_class Helt_seen") as "Hnodes".
    iApply (nodesｰproper with "Hnodes"). intros elt' _.
    rewrite /insert /fn_insert. repeat case_decide; naive.
  Qed.
  #[local] Lemma nodesｰclassｰacc {elements prevs nexts classes seens} elt :
    elt ∈ elements →
    nodes elements prevs nexts classes seens ⊢
      elt.[class_] ↦ #(classes elt) ∗
      ( ∀ (elt_class : location),
        elt.[class_] ↦ #elt_class -∗
        nodes elements prevs nexts (<[elt := elt_class]> classes) seens
      ).
  Proof.
    iIntros "%Helt Hnodes".
    iDestruct (nodesｰacc with "Hnodes") as "(Helt_prev & Helt_next & $ & Helt_seen & Hnodes)"; first done.
    iIntros "%elt_class Helt_class".
    iDestruct ("Hnodes" with "Helt_prev Helt_next Helt_class Helt_seen") as "Hnodes".
    iApply (nodesｰproper with "Hnodes"). intros elt' _.
    rewrite /insert /fn_insert. repeat case_decide; naive.
  Qed.
  #[local] Lemma nodesｰseenｰacc {elements prevs nexts classes seens} elt :
    elt ∈ elements →
    nodes elements prevs nexts classes seens ⊢
      elt.[seen] ↦ #(seens elt) ∗
      ( ∀ (elt_seen : bool),
        elt.[seen] ↦ #elt_seen -∗
        nodes elements prevs nexts classes (<[elt := elt_seen]> seens)
      ).
  Proof.
    iIntros "%Helt Hnodes".
    iDestruct (nodesｰacc with "Hnodes") as "(Helt_prev & Helt_next & Helt_class & $ & Hnodes)"; first done.
    iIntros "%elt_seen Helt_seen".
    iDestruct ("Hnodes" with "Helt_prev Helt_next Helt_class Helt_seen") as "Hnodes".
    iApply (nodesｰproper with "Hnodes"). intros elt' _.
    rewrite /insert /fn_insert. repeat case_decide; naive.
  Qed.
  #[local] Lemma nodesｰinsert {elements prevs nexts classes seens} elt (elt_prev elt_next elt_class : location) (elt_seen : bool) :
    elt ∉ elements →
    nodes elements prevs nexts classes seens -∗
    elt.[prev] ↦ #elt_prev -∗
    elt.[next] ↦ #elt_next -∗
    elt.[class_] ↦ #elt_class -∗
    elt.[seen] ↦ #elt_seen -∗
    nodes ({[elt]} ∪ elements)
      (<[elt := elt_prev]> prevs)
      (<[elt := elt_next]> nexts)
      (<[elt := elt_class]> classes)
      (<[elt := elt_seen]> seens).
  Proof.
    iIntros "%Helt Hnodes Helt_prev Helt_next Helt_class Helt_seen".
    iApply big_sepS_insert; first done.
    rewrite !fn_lookup_insert. iFrame.
    iApply (big_sepS_impl with "Hnodes"). iIntros "!> %elt' %Helt'".
    assert (elt ≠ elt') by set_solver.
    rewrite !fn_lookup_insert_ne //. iIntros "$".
  Qed.
  #[local] Lemma nodesｰfresh elements prevs nexts classes seens elt v :
    nodes elements prevs nexts classes seens -∗
    elt.[prev] ↦ v -∗
    ⌜elt ∉ elements⌝.
  Proof.
    iIntros "Hnodes Helt_prev %Helt".
    iDestruct (nodesｰlookupｰacc with "Hnodes") as "(Helt_prev' & _)"; first done.
    iApply (pointstoｰexclusive with "Helt_prev Helt_prev'").
  Qed.

  #[local] Lemma nodes٠classｰspec {elements prevs nexts classes seens descrs repr descr} elt :
    model۰valid elements prevs nexts classes seens descrs →
    descrs !! repr = Some descr →
    elt ∈ descr.(descriptor۰elts) →
    {{{
      nodes elements prevs nexts classes seens
    }}}
      (#elt).{partition٠class_}
    {{{
      RET #descr.(descriptor۰class);
      nodes elements prevs nexts classes seens
    }}}.
  Proof.
    iIntros "%Hvalid %Hlookup %Helt %Φ Hnodes HΦ".

    iDestruct (nodesｰlookupｰacc with "Hnodes") as "(Helt_prev & Helt_next & Helt_class & Helt_seen & Hnodes)".
    { apply (model۰validｰelement Hvalid Hlookup Helt). }
    rewrite (model۰validｰclasses Hvalid Hlookup Helt).
    wp۰load.
    iApply "HΦ".
    iApply ("Hnodes" with "Helt_prev Helt_next Helt_class Helt_seen").
  Qed.
  #[local] Lemma nodes٠nextｰspec {elements prevs nexts classes seens} elt :
    elt ∈ elements →
    {{{
      nodes elements prevs nexts classes seens
    }}}
      (#elt).{partition٠next}
    {{{
      RET #(nexts elt);
      nodes elements prevs nexts classes seens
    }}}.
  Proof.
    iIntros "%Helt %Φ Hnodes HΦ".

    iDestruct (nodesｰlookupｰacc with "Hnodes") as "(Helt_prev & Helt_next & Helt_class & Helt_seen & Hnodes)"; first done.
    wp۰load.
    iApply "HΦ".
    iApply ("Hnodes" with "Helt_prev Helt_next Helt_class Helt_seen").
  Qed.
  #[local] Lemma nodes٠prevｰspec {elements prevs nexts classes seens} elt :
    elt ∈ elements →
    {{{
      nodes elements prevs nexts classes seens
    }}}
      (#elt).{partition٠prev}
    {{{
      RET #(prevs elt);
      nodes elements prevs nexts classes seens
    }}}.
  Proof.
    iIntros "%Helt %Φ Hnodes HΦ".

    iDestruct (nodesｰlookupｰacc with "Hnodes") as "(Helt_prev & Helt_next & Helt_class & Helt_seen & Hnodes)"; first done.
    wp۰load.
    iApply "HΦ".
    iApply ("Hnodes" with "Helt_prev Helt_next Helt_class Helt_seen").
  Qed.
  #[local] Lemma nodes٠seenｰspec {elements prevs nexts classes seens} elt :
    elt ∈ elements →
    {{{
      nodes elements prevs nexts classes seens
    }}}
      (#elt).{partition٠seen}
    {{{
      RET #(seens elt);
      nodes elements prevs nexts classes seens
    }}}.
  Proof.
    iIntros "%Helt %Φ Hnodes HΦ".

    iDestruct (nodesｰlookupｰacc with "Hnodes") as "(Helt_prev & Helt_next & Helt_class & Helt_seen & Hnodes)"; first done.
    wp۰load.
    iApply "HΦ".
    iApply ("Hnodes" with "Helt_prev Helt_next Helt_class Helt_seen").
  Qed.

  #[local] Lemma descriptor۰modelｰunseen repr descr :
    descr.(descriptor۰seen) = 0 →
    head descr.(descriptor۰elts) = Some repr →
    descriptor۰model repr descr ⊣⊢
      ∃ last,
      ⌜list.last descr.(descriptor۰elts) = Some last⌝ ∗
      descr.(descriptor۰class).[first] ↦ #repr ∗
      descr.(descriptor۰class).[last] ↦ #last ∗
      descr.(descriptor۰class).[len] ↦ #(length descr.(descriptor۰elts)) ∗
      descr.(descriptor۰class).[split] ↦ #repr ∗
      descr.(descriptor۰class).[split_len] ↦ #0.
  Proof.
    intros Hseen Hhead.
    rewrite /descriptor۰model Hseen -head_lookup Hhead /=.
    destruct (decide _); done.
  Qed.

  #[local] Lemma descriptorsｰfresh descrs class v :
    ([∗ map] repr ↦ descr ∈ descrs, descriptor۰model repr descr) -∗
    class.[first] ↦ v -∗
    ⌜ ∀ repr descr,
      descrs !! repr = Some descr →
      descr.(descriptor۰class) ≠ class
    ⌝.
  Proof.
    iIntros "Hdescrs Hclass_first %repr %descr %Hlookup %Hclass".
    iDestruct (big_sepM_lookup with "Hdescrs") as "(:descriptor۰model =')"; first done.
    rewrite Hclass.
    iApply (pointstoｰexclusive with "Hclass_first Hclass'_first").
  Qed.

  Lemma partition۰modelｰempty :
    ⊢ |==>
      ∃ γ,
      partition۰model γ ∅.
  Proof.
    iMod elementsｰalloc as "(%γ_elements & Helements_auth)".
    pose γ :=
      {|partition۰name۰elements := γ_elements
      |}.
    iExists γ, ∅, id, id, id, (λ _, false), ∅.
    rewrite /model' /nodes !big_opS_empty !big_opM_empty fmap_empty.
    iFrame. iPureIntro. split_and!; [done | apply map_Forall_empty | | done..].
    constructor; try set_solver; try (intros *; rewrite lookup_empty; done).
  Qed.
  Lemma partition۰modelｰvalid γ part :
    partition۰model γ part ⊢
    ⌜partition۰valid part⌝.
  Proof.
    iIntros "(:model)". iPureIntro. split.
    - intros repr cl (descr & Hcl & Hlookup)%lookup_fmap_Some. subst cl.
      rewrite elem_of_list_to_set. apply (model۰validｰrepr Hvalid Hlookup).
    - intros repr1 cl1 repr2 cl2 (descr1 & Hcl1 & Hlookup1)%lookup_fmap_Some (descr2 & Hcl2 & Hlookup2)%lookup_fmap_Some Hne. subst cl1 cl2.
      apply elem_of_disjoint. simpl. intros elt Helt1%elem_of_list_to_set Helt2%elem_of_list_to_set.
      apply Hne, (model۰validｰdisjoint Hvalid elt Hlookup1 Hlookup2); done.
  Qed.
  Lemma partition۰modelｰexclusive γ part1 part2 :
    partition۰model γ part1 -∗
    partition۰model γ part2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)".
    iApply (mono_gset۰authｰexclusive with "Helements_auth1 Helements_auth2").
  Qed.

  Lemma partition۰elementｰlookup γ part elt v :
    partition۰model γ part -∗
    partition۰element γ elt v -∗
      ∃ repr cl,
      ⌜part !! repr = Some cl⌝ ∗
      ⌜elt ∈ cl⌝.
  Proof.
    iIntros "(:model) (:element)".
    iDestruct (elements۰elemｰvalid with "Helements_auth Helements_elem") as %(repr & descr & Hlookup & Helt)%(model۰validｰelements Hvalid).
    iExists repr, (list_to_set descr.(descriptor۰elts)). iPureIntro. split.
    - rewrite lookup_fmap Hlookup //.
    - rewrite elem_of_list_to_set //.
  Qed.
  Lemma partition۰elementｰagree γ elt v1 v2 :
    partition۰element γ elt v1 -∗
    partition۰element γ elt v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    iIntros "(:element =1) (:element =2)".
    iApply (pointstoｰagree with "Helt1_data Helt2_data").
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [Dllist.create]. *)

  #[local] Lemma partition٠dllist٠createｰspec v v_class :
    {{{
      True
    }}}
      partition٠dllist٠create v v_class
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

  (* ------------------------------------------------------------------------ *)
  (* [Dllist.link]. *)

  #[local] Lemma partition٠dllist٠linkｰspec elements prevs nexts classes seens elt1 elt2 :
    elt1 ∈ elements →
    elt2 ∈ elements →
    {{{
      nodes elements prevs nexts classes seens
    }}}
      partition٠dllist٠link #elt1 #elt2
    {{{
      RET ();
      nodes elements (<[elt2 := elt1]> prevs) (<[elt1 := elt2]> nexts) classes seens
    }}}.
  Proof.
    iIntros "%Helt1 %Helt2 %Φ Hnodes HΦ".

    wp۰rec.
    iDestruct (nodesｰnextｰacc elt1 with "Hnodes") as "(Helt1_next & Hnodes)"; first done.
    wp۰store.
    iDestruct ("Hnodes" with "Helt1_next") as "Hnodes".
    iDestruct (nodesｰprevｰacc elt2 with "Hnodes") as "(Helt2_prev & Hnodes)"; first done.
    wp۰store.
    iDestruct ("Hnodes" with "Helt2_prev") as "Hnodes".
    iApply ("HΦ" with "Hnodes").
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [Dllist.insert_right]. *)

  #[local] Lemma partition٠dllist٠insert_rightｰspec elements prevs nexts classes seens dst elt :
    dst ∈ elements →
    elt ∈ elements →
    nexts dst ∈ elements →
    {{{
      nodes elements prevs nexts classes seens
    }}}
      partition٠dllist٠insert_right #dst #elt
    {{{
      RET ();
      nodes elements
        (<[elt := dst]> (<[nexts dst := elt]> prevs))
        (<[dst := elt]> (<[elt := nexts dst]> nexts))
        classes
        seens
    }}}.
  Proof.
    iIntros "%Hdst %Helt %Hnext %Φ Hnodes HΦ".

    wp۰rec.
    wp۰apply+ (nodes٠nextｰspec with "Hnodes") as "Hnodes"; first done.
    wp۰apply (partition٠dllist٠linkｰspec with "Hnodes") as "Hnodes"; [done.. |].
    wp۰apply+ (partition٠dllist٠linkｰspec with "Hnodes HΦ"); done.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [Dllist.swap]. *)

  #[local] Lemma partition٠dllist٠swapｰspec elements prevs nexts classes seens elt1 elt2 :
    links۰valid elements prevs nexts →
    elt1 ∈ elements →
    elt2 ∈ elements →
    elt1 ≠ elt2 →
    nexts elt1 ≠ elt1 →
    nexts elt2 ≠ elt2 →
    {{{
      nodes elements prevs nexts classes seens
    }}}
      partition٠dllist٠swap #elt1 #elt2
    {{{
      RET ();
      nodes elements
        (swap elt1 elt2 ∘ prevs ∘ swap elt1 elt2)
        (swap elt1 elt2 ∘ nexts ∘ swap elt1 elt2)
        classes
        seens
    }}}.
  Proof.
    iIntros "%Hlinks %Helt1 %Helt2 %Hne %Hnext1 %Hnext2 %Φ Hnodes HΦ".

    pose proof (Hlinks elt1 Helt1) as (Hnext1_elem & Hprev1_elem & Hprev_next1 & Hnext_prev1).
    pose proof (Hlinks elt2 Helt2) as (Hnext2_elem & Hprev2_elem & Hprev_next2 & Hnext_prev2).
    pose proof (Hlinks _ Hnext1_elem) as (_ & _ & ? & ?).
    pose proof (Hlinks _ Hprev1_elem) as (_ & _ & ? & ?).
    pose proof (Hlinks _ Hnext2_elem) as (_ & _ & ? & ?).
    pose proof (Hlinks _ Hprev2_elem) as (_ & _ & ? & ?).
    assert (prevs elt1 ≠ elt1) by congruence.
    assert (prevs elt2 ≠ elt2) by congruence.

    wp۰rec. wp۰pures.
    rewrite bool_decide_eq_false_2 //.
    wp۰apply+ (nodes٠prevｰspec elt1 with "Hnodes") as "Hnodes"; first done.
    wp۰apply+ (nodes٠nextｰspec elt1 with "Hnodes") as "Hnodes"; first done.
    wp۰apply+ (nodes٠prevｰspec elt2 with "Hnodes") as "Hnodes"; first done.
    wp۰apply+ (nodes٠nextｰspec elt2 with "Hnodes") as "Hnodes"; first done.
    wp۰pures.
    case_bool_decide as Hcase1; wp۰pures.

    - case_bool_decide as Hcase2; wp۰pures.

      + iApply "HΦ".
        iApply (nodesｰproper with "Hnodes"). intros elt Helt.
        pose proof (Hlinks elt Helt) as (_ & _ & ? & ?).
        split_and!; [solve۰swap elt elt1 elt2.. | done | done].

      + wp۰apply+ (partition٠dllist٠linkｰspec with "Hnodes") as "Hnodes"; [done.. |].
        wp۰apply+ (partition٠dllist٠linkｰspec with "Hnodes") as "Hnodes"; [done.. |].
        wp۰apply+ (partition٠dllist٠linkｰspec with "Hnodes") as "Hnodes"; [done.. |].
        iApply "HΦ".
        iApply (nodesｰproper with "Hnodes"). intros elt Helt.
        pose proof (Hlinks elt Helt) as (_ & _ & ? & ?).
        split_and!; [solve۰swap elt elt1 elt2.. | done | done].

    - case_bool_decide as Hcase2; wp۰pures.

      + wp۰apply+ (partition٠dllist٠linkｰspec with "Hnodes") as "Hnodes"; [done.. |].
        wp۰apply+ (partition٠dllist٠linkｰspec with "Hnodes") as "Hnodes"; [done.. |].
        wp۰apply+ (partition٠dllist٠linkｰspec with "Hnodes") as "Hnodes"; [done.. |].
        iApply "HΦ".
        iApply (nodesｰproper with "Hnodes"). intros elt Helt.
        pose proof (Hlinks elt Helt) as (_ & _ & ? & ?).
        split_and!; [solve۰swap elt elt1 elt2.. | done | done].

      + wp۰apply+ (partition٠dllist٠linkｰspec with "Hnodes") as "Hnodes"; [done.. |].
        wp۰apply+ (partition٠dllist٠linkｰspec with "Hnodes") as "Hnodes"; [done.. |].
        wp۰apply+ (partition٠dllist٠linkｰspec with "Hnodes") as "Hnodes"; [done.. |].
        wp۰apply+ (partition٠dllist٠linkｰspec with "Hnodes") as "Hnodes"; [done.. |].
        iApply "HΦ".
        iApply (nodesｰproper with "Hnodes"). intros elt Helt.
        pose proof (Hlinks elt Helt) as (_ & _ & ? & ?).
        split_and!; [solve۰swap elt elt1 elt2.. | done | done].
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [Dllist.iter]. *)

  #[local] Lemma partition٠dllist٠iterｰspecｰaux Ψ (fn : val) elements prevs nexts elts elts2 elts1 elt1 elt2 classes seens :
    elts = elts1 ++ elts2 →
    NoDup elts →
    head elts2 = Some elt1 →
    list.last elts = Some elt2 →
    ( ∀ i elt elt',
      elts !! i = Some elt →
      elts !! ˖i = Some elt' →
      nexts elt = elt'
    ) →
    ( ∀ elt,
      elt ∈ elts →
      elt ∈ elements
    ) →
    {{{
      nodes elements prevs nexts classes seens ∗
      Ψ elts1 classes seens ∗
      □ (
        ∀ elts1 elt elts2 classes seens,
        ⌜elts = elts1 ++ elt :: elts2⌝ -∗
        nodes elements prevs nexts classes seens -∗
        Ψ elts1 classes seens -∗
        WP fn #elt {{ _,
          ∃ classes seens,
          nodes elements prevs nexts classes seens ∗
          Ψ (elts1 ++ [elt]) classes seens
        }}
      )
    }}}
      partition٠dllist٠iter fn #elt1 #elt2
    {{{
      classes seens
    , RET ();
      nodes elements prevs nexts classes seens ∗
      Ψ elts classes seens
    }}}.
  Proof.
    induction elts2 as [| elt elts2 IH] in elts1, elt1, classes, seens |- *; first done.
    iIntros "%Helts %Hnodup %Hhead %Hlast %Hchain %Hsubset %Φ (Hnodes & HΨ & #Hfn) HΦ".

    injection Hhead as <-.

    wp۰rec. wp۰pures.
    wp۰bind (fn _)%E.
    iApply (wpｰwand with "(Hfn [//] Hnodes HΨ)"). iIntros "%res (%classes' & %seens' & Hnodes & HΨ)".
    wp۰pures.
    destruct elts2 as [| elt' elts2].

    - rewrite Helts last_snoc in Hlast. injection Hlast as <-.
      rewrite bool_decide_eq_true_2 //.
      wp۰pures.
      iApply "HΦ".
      rewrite Helts. iFrameSteps.

    - assert (elt ≠ elt2).
      { intros <-.
        rewrite Helts in Hnodup Hlast.
        apply NoDup_app in Hnodup as (_ & _ & Hnodup).
        apply NoDup_cons in Hnodup as (Helt & _).
        apply Helt.
        rewrite last_app /= in Hlast.
        destruct (list.last (elt' :: elts2)) as [elt'' |] eqn:Hlast'; last first.
        { apply last_None in Hlast'. done. }
        apply last_Some_elem_of. congruence.
      }
      rewrite bool_decide_eq_false_2 //.
      wp۰apply+ (nodes٠nextｰspec elt with "Hnodes") as "Hnodes".
      { apply Hsubset. rewrite Helts. set_solver. }
      rewrite (Hchain (length elts1) elt elt').
      { rewrite Helts lookup_app_r // Nat.sub_diag //. }
      { rewrite Helts lookup_app_r; first lia.
        rewrite (_ : ˖(length elts1) - length elts1 = 1); first lia. done.
      }
      wp۰apply (IH (elts1 ++ [elt]) with "[$Hnodes $HΨ $Hfn] HΦ").
      { rewrite -assoc //. }
      all: done.
  Qed.

  #[local] Lemma partition٠dllist٠iterｰspec Ψ (fn : val) elements prevs nexts classes seens elts elt1 elt2 :
    NoDup elts →
    head elts = Some elt1 →
    list.last elts = Some elt2 →
    ( ∀ i elt elt',
      elts !! i = Some elt →
      elts !! ˖i = Some elt' →
      nexts elt = elt'
    ) →
    ( ∀ elt,
      elt ∈ elts →
      elt ∈ elements
    ) →
    {{{
      nodes elements prevs nexts classes seens ∗
      Ψ [] classes seens ∗
      □ (
        ∀ elts1 elt elts2 classes seens,
        ⌜elts = elts1 ++ elt :: elts2⌝ -∗
        nodes elements prevs nexts classes seens -∗
        Ψ elts1 classes seens -∗
        WP fn #elt {{ _,
          ∃ classes seens,
          nodes elements prevs nexts classes seens ∗
          Ψ (elts1 ++ [elt]) classes seens
        }}
      )
    }}}
      partition٠dllist٠iter fn #elt1 #elt2
    {{{
      classes seens
    , RET ();
      nodes elements prevs nexts classes seens ∗
      Ψ elts classes seens
    }}}.
  Proof.
    intros.
    apply (partition٠dllist٠iterｰspecｰaux _ _ _ _ _ _ elts []); done.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [class_is_singleton]. *)

  #[local] Lemma partition٠class_is_singletonｰspec class (len : nat) :
    {{{
      class.[len] ↦ #len
    }}}
      partition٠class_is_singleton #class
    {{{
      RET #(bool_decide (len = 1)%nat);
      class.[len] ↦ #len
    }}}.
  Proof.
    iIntros "%Φ Hclass_len HΦ".

    wp۰rec. wp۰load. wp۰pures.
    destruct (decide (len = 1)) as [-> | Hlen].
    - rewrite !bool_decide_eq_true_2 //.
      iApply ("HΦ" with "Hclass_len").
    - rewrite !bool_decide_eq_false_2 //; first lia.
      iApply ("HΦ" with "Hclass_len").
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [class_add]. *)

  #[local] Lemma partition٠class_addｰspec elements prevs nexts classes seens class last (len : nat) elt :
    last ∈ elements →
    elt ∈ elements →
    nexts last ∈ elements →
    {{{
      nodes elements prevs nexts classes seens ∗
      class.[last] ↦ #last ∗
      class.[len] ↦ #len
    }}}
      partition٠class_add #class #elt
    {{{
      RET ();
      nodes elements
        (<[elt := last]> (<[nexts last := elt]> prevs))
        (<[last := elt]> (<[elt := nexts last]> nexts))
        classes
        seens ∗
      class.[last] ↦ #elt ∗
      class.[len] ↦ #(len + 1)
    }}}.
  Proof.
    iIntros "%Hlast %Helt %Hnext %Φ (Hnodes & Hclass_last & Hclass_len) HΦ".

    wp۰rec. wp۰load.
    wp۰apply (partition٠dllist٠insert_rightｰspec with "Hnodes") as "Hnodes"; [done.. |].
    wp۰store. wp۰load. wp۰store.
    iApply "HΦ".
    iFrameSteps.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [class_swap]. *)

  #[local] Lemma partition٠class_swapｰspec elements prevs nexts classes seens class first last elt1 elt2 :
    links۰valid elements prevs nexts →
    elt1 ∈ elements →
    elt2 ∈ elements →
    nexts elt1 ≠ elt1 →
    nexts elt2 ≠ elt2 →
    {{{
      nodes elements prevs nexts classes seens ∗
      class.[first] ↦ #first ∗
      class.[last] ↦ #last
    }}}
      partition٠class_swap #class #elt1 #elt2
    {{{
      RET ();
      nodes elements
        (swap elt1 elt2 ∘ prevs ∘ swap elt1 elt2)
        (swap elt1 elt2 ∘ nexts ∘ swap elt1 elt2)
        classes
        seens ∗
      class.[first] ↦ #(swap elt1 elt2 first) ∗
      class.[last] ↦ #(swap elt1 elt2 last)
    }}}.
  Proof.
    iIntros "%Hlinks %Helt1 %Helt2 %Hnext1 %Hnext2 %Φ (Hnodes & Hclass_first & Hclass_last) HΦ".

    wp۰rec. wp۰pures.
    destruct (decide (elt1 = elt2)) as [<- | Hne].

    - rewrite bool_decide_eq_true_2 //.
      wp۰pures.
      iApply "HΦ".
      rewrite !swapｰdiag. iFrame.
      iApply (nodesｰproper with "Hnodes"). intros elt _.
      rewrite /= !swapｰdiag //.

    - rewrite bool_decide_eq_false_2 //.
      wp۰load. wp۰load. wp۰pures.

      wp۰bind (𝗶𝗳 _ 𝘁𝗵𝗲𝗻 _ 𝗲𝗹𝘀𝗲 _)%E.
      wp۰apply (wpｰwand (λ _,
        class.[first] ↦ #(swap elt1 elt2 first)
      )%I with "[Hclass_first]") as "%v Hclass_first".
      { case_bool_decide as Hfirst1; wp۰pures.
        - wp۰store. subst first. rewrite swapｰl. iSteps.
        - case_bool_decide as Hfirst2; wp۰pures.
          + wp۰store. subst first. rewrite swapｰr. iSteps.
          + rewrite swapｰne //.
      }

      wp۰pures.

      wp۰bind (𝗶𝗳 _ 𝘁𝗵𝗲𝗻 _ 𝗲𝗹𝘀𝗲 _)%E.
      wp۰apply (wpｰwand (λ _,
        class.[last] ↦ #(swap elt1 elt2 last)
      )%I with "[Hclass_last]") as "%v' Hclass_last".
      { case_bool_decide as Hlast2; wp۰pures.
        - wp۰store. subst last. rewrite swapｰr. iSteps.
        - case_bool_decide as Hlast1; wp۰pures.
          + wp۰store. subst last. rewrite swapｰl. iSteps.
          + rewrite swapｰne //.
      }

      wp۰apply+ (partition٠dllist٠swapｰspec with "Hnodes") as "Hnodes"; [done.. |].
      iApply "HΦ".
      iFrame.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [class_iter]. *)

  #[local] Lemma partition٠class_iterｰspec Ψ (fn : val) elements prevs nexts classes seens class first last elts :
    NoDup elts →
    head elts = Some first →
    list.last elts = Some last →
    ( ∀ i elt elt',
      elts !! i = Some elt →
      elts !! ˖i = Some elt' →
      nexts elt = elt'
    ) →
    ( ∀ elt,
      elt ∈ elts →
      elt ∈ elements
    ) →
    {{{
      class.[first] ↦ #first ∗
      class.[last] ↦ #last ∗
      nodes elements prevs nexts classes seens ∗
      Ψ [] classes seens ∗
      □ (
        ∀ elts1 elt elts2 classes seens,
        ⌜elts = elts1 ++ elt :: elts2⌝ -∗
        nodes elements prevs nexts classes seens -∗
        Ψ elts1 classes seens -∗
        WP fn #elt {{ _,
          ∃ classes seens,
          nodes elements prevs nexts classes seens ∗
          Ψ (elts1 ++ [elt]) classes seens
        }}
      )
    }}}
      partition٠class_iter fn #class
    {{{
      classes seens
    , RET ();
      class.[first] ↦ #first ∗
      class.[last] ↦ #last ∗
      nodes elements prevs nexts classes seens ∗
      Ψ elts classes seens
    }}}.
  Proof.
    iIntros "%Hnodup %Hhead %Hlast %Hchain %Hsubset %Φ (Hclass_first & Hclass_last & Hnodes & HΨ & #Hfn) HΦ".

    wp۰rec. wp۰load. wp۰load.
    wp۰apply (partition٠dllist٠iterｰspec Ψ with "[$Hnodes $HΨ $Hfn]") as (classes' seens') "(Hnodes & HΨ)"; [done.. |].
    iApply "HΦ".
    iFrame.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [make]. *)

  Lemma partition٠makeｰspec γ part v :
    {{{
      partition۰model γ part
    }}}
      partition٠make v
    {{{
      elt
    , RET #elt;
      ⌜part !! elt = None⌝ ∗
      partition۰model γ (<[elt := {[elt]}]> part) ∗
      partition۰element γ elt v
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".

    wp۰rec.
    wp۰apply (partition٠dllist٠createｰspec with "[//]") as (elt) "(Helt_prev & Helt_next & #Helt_data & Helt_class & Helt_seen)".
    wp۰block class as "Hclass_first Hclass_last Hclass_len Hclass_split Hclass_split_len".
    wp۰store. wp۰pures.

    iDestruct (nodesｰfresh with "Hnodes Helt_prev") as %Helt.
    iDestruct (descriptorsｰfresh with "Hdescrs Hclass_first") as %Hclass.
    pose proof (model۰validｰlookupｰNone Hvalid elt Helt) as Hlookup.
    iMod (elementsｰinsert elt with "Helements_auth") as "(Helements_auth & #Helements_elem)".
    iDestruct (nodesｰinsert elt elt elt class false with "Hnodes Helt_prev Helt_next Helt_class Helt_seen") as "Hnodes"; first done.

    iApply "HΦ".
    iSplitR. { rewrite lookup_fmap Hlookup //. }
    iSplitL; last iSteps.
    iExists _, _, _, _, _, (<[elt := Descriptor class [elt] 0]> descrs). iFrame.
    iSplitR. { rewrite fmap_insert /= right_id_L //. }
    iSplitR. { iPureIntro. apply map_Forall_insert_2; done. }
    iSplitR. { iPureIntro. apply (model۰validｰmake Hvalid); done. }
    iApply (big_sepM_insert_2 with "[- Hdescrs] Hdescrs").
    iExists elt. iSteps.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [make_same_class]. *)

  Lemma partition٠make_same_classｰspec {γ part elt v v'} repr cl :
    part !! repr = Some cl →
    elt ∈ cl →
    {{{
      partition۰model γ part ∗
      partition۰element γ elt v
    }}}
      partition٠make_same_class #elt v'
    {{{
      elt'
    , RET #elt';
      partition۰model γ (<[repr := cl ∪ {[elt']}]> part) ∗
      partition۰element γ elt' v'
    }}}.
  Proof.
    iIntros "%Hpart_lookup %Helt %Φ ((:model) & (:element)) HΦ".

    apply lookup_fmap_Some in Hpart_lookup as (descr & Hcl & Hlookup). subst cl.
    rewrite elem_of_list_to_set in Helt.
    pose proof (Hunseen _ _ Hlookup) as Hseen. simpl in Hseen.
    assert (elt ∈ elements) as Helt_elements.
    { eapply (model۰validｰelement Hvalid); done. }

    wp۰rec.
    wp۰apply+ (nodes٠classｰspec elt Hvalid Hlookup Helt with "Hnodes") as "Hnodes".
    wp۰apply+ (partition٠dllist٠createｰspec with "[//]") as (elt') "(Helt'_prev & Helt'_next & #Helt'_data & Helt'_class & Helt'_seen)".
    iDestruct (nodesｰfresh with "Hnodes Helt'_prev") as %Helt'.
    iDestruct (nodesｰinsert elt' elt' elt' descr.(descriptor۰class) false with "Hnodes Helt'_prev Helt'_next Helt'_class Helt'_seen") as "Hnodes"; first done.
    iDestruct (big_sepM_insert_acc with "Hdescrs") as "(Hdescr & Hdescrs)"; first done.
    iEval (rewrite descriptor۰modelｰunseen //; first apply (model۰validｰhead Hvalid Hlookup)) in "Hdescr".
    iDestruct "Hdescr" as "(%last & %Hlast & Hclass_first & Hclass_last & Hclass_len & Hclass_split & Hclass_split_len)".
    assert (last ∈ elements) as Hlast_elements.
    { eapply (model۰validｰelement Hvalid); first done. apply last_Some_elem_of. done. }
    assert (elt' ≠ last) by set_solver.
    wp۰apply+ (partition٠class_addｰspec with "[$Hnodes $Hclass_last $Hclass_len]") as "(Hnodes & Hclass_last & Hclass_len)".
    { set_solver. }
    { set_solver. }
    { rewrite fn_lookup_insert_ne //. apply elem_of_union_r, (model۰validｰnext Hvalid Hlast_elements). }
    rewrite fn_lookup_insert_ne //.
    iMod (elementsｰinsert elt' with "Helements_auth") as "(Helements_auth & #Helements_elem')".

    wp۰pures.
    iApply "HΦ".
    iSplitL; last iSteps.
    iExists ({[elt']} ∪ elements),
      (<[elt' := last]> (<[nexts last := elt']> prevs)),
      (<[last := elt']> (<[elt' := nexts last]> nexts)),
      (<[elt' := descr.(descriptor۰class)]> classes),
      (<[elt' := false]> seens),
      (<[repr := Descriptor descr.(descriptor۰class) (descr.(descriptor۰elts) ++ [elt']) 0]> descrs).
    iFrame "Helements_auth". iSplitR.
    { rewrite fmap_insert /= list_to_set_app_L /= right_id_L //. }
    iSplitR. { iPureIntro. apply map_Forall_insert_2; done. }
    iSplitR. { iPureIntro. apply (model۰validｰadd Hvalid); done. }
    iSplitL "Hnodes".
    { iApply (nodesｰproper with "Hnodes"). intros x _.
      rewrite /insert /fn_insert. repeat case_decide; naive.
    }
    iApply "Hdescrs".
    rewrite descriptor۰modelｰunseen //=.
    { rewrite head_app (model۰validｰhead Hvalid Hlookup) //. }
    iExists elt'. rewrite last_snoc length_app /=. iSteps.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [get]. *)

  Lemma partition٠getｰspec γ elt v :
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

  (* ------------------------------------------------------------------------ *)
  (* [equal]. *)

  Lemma partition٠equalｰspec γ elt1 elt2 :
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

  (* ------------------------------------------------------------------------ *)
  (* [equiv]. *)

  Lemma partition٠equivｰspec {γ part elt1 v1 elt2 v2} repr1 cl1 repr2 cl2 :
    part !! repr1 = Some cl1 →
    elt1 ∈ cl1 →
    part !! repr2 = Some cl2 →
    elt2 ∈ cl2 →
    {{{
      partition۰model γ part ∗
      partition۰element γ elt1 v1 ∗
      partition۰element γ elt2 v2
    }}}
      partition٠equiv #elt1 #elt2
    {{{
      RET #(bool_decide (repr1 = repr2));
      partition۰model γ part
    }}}.
  Proof.
    iIntros "%Hpart_lookup_1 %Helt1 %Hpart_lookup_2 %Helt2 %Φ ((:model) & (:element =1) & (:element =2)) HΦ".

    apply lookup_fmap_Some in Hpart_lookup_1 as (descr1 & Hcl1 & Hlookup1). subst cl1.
    apply lookup_fmap_Some in Hpart_lookup_2 as (descr2 & Hcl2 & Hlookup2). subst cl2.
    rewrite elem_of_list_to_set in Helt1.
    rewrite elem_of_list_to_set in Helt2.

    wp۰rec.
    wp۰apply+ (nodes٠classｰspec elt2 Hvalid Hlookup2 Helt2 with "Hnodes") as "Hnodes".
    wp۰apply (nodes٠classｰspec elt1 Hvalid Hlookup1 Helt1 with "Hnodes") as "Hnodes".
    wp۰pures.
    rewrite (bool_decide_ext (descr1.(descriptor۰class) = descr2.(descriptor۰class)) (repr1 = repr2)).
    { split.
      - apply (model۰validｰclass Hvalid Hlookup1 Hlookup2).
      - intros <-. congruence.
    }
    iApply "HΦ".
    iFrameSteps.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [repr]. *)

  Lemma partition٠reprｰspec {γ part elt v} repr cl :
    part !! repr = Some cl →
    elt ∈ cl →
    {{{
      partition۰model γ part ∗
      partition۰element γ elt v
    }}}
      partition٠repr #elt
    {{{
      RET #repr;
      partition۰model γ part
    }}}.
  Proof.
    iIntros "%Hpart_lookup %Helt %Φ ((:model) & (:element)) HΦ".

    apply lookup_fmap_Some in Hpart_lookup as (descr & Hcl & Hlookup). subst cl.
    rewrite elem_of_list_to_set in Helt.

    wp۰rec.
    wp۰apply+ (nodes٠classｰspec elt Hvalid Hlookup Helt with "Hnodes") as "Hnodes".
    iDestruct (big_sepM_lookup_acc with "Hdescrs") as "((:descriptor۰model) & Hdescrs)"; first done.
    wp۰load.
    iDestruct ("Hdescrs" with "[Hclass_first Hclass_last Hclass_len Hclass_split Hclass_split_len]") as "Hdescrs"; first iSteps.
    iApply "HΦ".
    iFrameSteps.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [cardinal]. *)

  Lemma partition٠cardinalｰspec {γ part elt v} repr cl :
    part !! repr = Some cl →
    elt ∈ cl →
    {{{
      partition۰model γ part ∗
      partition۰element γ elt v
    }}}
      partition٠cardinal #elt
    {{{
      RET #(size cl);
      partition۰model γ part
    }}}.
  Proof.
    iIntros "%Hpart_lookup %Helt %Φ ((:model) & (:element)) HΦ".

    apply lookup_fmap_Some in Hpart_lookup as (descr & Hcl & Hlookup). subst cl.
    rewrite elem_of_list_to_set in Helt.

    wp۰rec.
    wp۰apply+ (nodes٠classｰspec elt Hvalid Hlookup Helt with "Hnodes") as "Hnodes".
    iDestruct (big_sepM_lookup_acc with "Hdescrs") as "((:descriptor۰model) & Hdescrs)"; first done.
    wp۰load.
    iDestruct ("Hdescrs" with "[Hclass_first Hclass_last Hclass_len Hclass_split Hclass_split_len]") as "Hdescrs"; first iSteps.
    rewrite size_list_to_set; first apply (model۰validｰNoDup Hvalid Hlookup).
    iApply "HΦ".
    iFrameSteps.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [record₁]. *)

  #[local] Lemma partition٠record₁ｰspec γ part X elements prevs nexts classes seens descrs split_list elt v :
    record۰inv part X descrs split_list →
    {{{
      model' γ elements prevs nexts classes seens descrs ∗
      partition۰element γ elt v
    }}}
      partition٠record₁ (list۰to_val (#*ˡ split_list)) #elt
    {{{
      prevs' nexts' seens' descrs' split_list'
    , RET list۰to_val (#*ˡ split_list');
      model' γ elements prevs' nexts' classes seens' descrs' ∗
      ⌜record۰inv part ({[elt]} ∪ X) descrs' split_list'⌝
    }}}.
  Proof.
    iIntros "%Hinv %Φ ((:model') & (:element)) HΦ".

    iDestruct (elements۰elemｰvalid with "Helements_auth Helements_elem") as %(repr & descr & Hlookup & Helt)%(model۰validｰelements Hvalid).
    pose proof (model۰validｰelement Hvalid Hlookup Helt) as Helt_elements.
    pose proof (model۰validｰNoDup Hvalid Hlookup) as Hnodup.
    pose proof (model۰validｰseen Hvalid Hlookup) as Hseen.
    pose proof (model۰validｰhead Hvalid Hlookup) as Hhead.
    pose proof (model۰validｰlength Hvalid Hlookup) as Hlength_pos.
    iDestruct (big_sepM_delete with "Hdescrs") as "((:descriptor۰model) & Hdescrs)"; first done.

    wp۰rec.
    wp۰apply+ (nodes٠classｰspec elt Hvalid Hlookup Helt with "Hnodes") as "Hnodes".
    wp۰apply+ (partition٠class_is_singletonｰspec with "Hclass_len") as "Hclass_len".
    destruct (decide (length descr.(descriptor۰elts) = 1)) as [Hlength | Hlength].

    - rewrite bool_decide_eq_true_2 //.
      wp۰pures.
      iApply ("HΦ" $! prevs nexts seens descrs split_list).
      iSplitL.
      { iFrame "%∗". iApply (big_sepM_delete _ _ repr); first done. iFrameSteps. }
      iPureIntro. apply (record۰invｰsingleton Hvalid Hinv elt Hlookup Hlength Helt).

    - rewrite bool_decide_eq_false_2 //.
      wp۰apply+ (nodes٠seenｰspec with "Hnodes") as "Hnodes"; first done.
      rewrite (model۰validｰseens Hvalid Hlookup Helt).
      destruct (decide (elt ∈ take descr.(descriptor۰seen) descr.(descriptor۰elts))) as [Helt_seen | Helt_seen].

      + rewrite bool_decide_eq_true_2 //.
        wp۰pures.
        assert ({[elt]} ∪ X = X) as ->.
        { apply (record۰invｰseen Hinv elt Hlookup) in Helt_seen. set_solver. }
        iApply ("HΦ" $! prevs nexts seens descrs split_list).
        iSplitL; last done.
        iFrame "%∗". iApply (big_sepM_delete _ _ repr); first done. iFrameSteps.

      + rewrite bool_decide_eq_false_2 //.
        wp۰pures.
        assert (descr.(descriptor۰seen) < length descr.(descriptor۰elts)) as Hseen_lt.
        { destruct (decide (descr.(descriptor۰seen) < length descr.(descriptor۰elts))) as [? | Hge]; first done.
          rewrite take_ge in Helt_seen; [lia | done].
        }
        destruct (lookup_lt_is_Some_2 descr.(descriptor۰elts) descr.(descriptor۰seen)) as (split & Hlookup_split); first done.
        assert (split ∈ descr.(descriptor۰elts)) as Hsplit.
        { eapply list_elem_of_lookup_2. done. }
        assert (split ∉ take descr.(descriptor۰seen) descr.(descriptor۰elts)) as Hsplit_seen.
        { rewrite elem_of_take. intros (i & Hlookup_i & Hi).
          opose proof* (NoDup_lookup _ i descr.(descriptor۰seen)); [done.. | lia].
        }
        apply list_elem_of_lookup in Helt as Helt'. destruct Helt' as (k & Hlookup_k).
        assert (descr.(descriptor۰seen) ≤ k) as Hk.
        { destruct (decide (descr.(descriptor۰seen) ≤ k)) as [? | Hk]; first done.
          exfalso. apply Helt_seen, elem_of_take. exists k. split; [done | lia].
        }
        iDestruct (nodesｰseenｰacc elt with "Hnodes") as "(Helt_seen & Hnodes)"; first done.
        wp۰store.
        iSpecialize ("Hnodes" with "Helt_seen").
        rewrite Hlookup_split /=.
        wp۰load. wp۰load. wp۰pures.
        pose proof Hlast as Hlast_lookup. rewrite last_lookup in Hlast_lookup.
        destruct (decide (split = last)) as [<- | Hsplit_last].

        * rewrite bool_decide_eq_true_2 //.
          assert (descr.(descriptor۰seen) = pred (length descr.(descriptor۰elts))) as Hseen_eq.
          { apply (NoDup_lookup descr.(descriptor۰elts) _ _ split); done. }
          assert (k = descr.(descriptor۰seen)) as ->.
          { apply lookup_lt_Some in Hlookup_k. lia. }
          simplify_eq.
          wp۰pures. wp۰load. wp۰store. wp۰store. wp۰pures.
          iApply ("HΦ" $! prevs nexts (<[split := true]> seens) (<[repr := Descriptor descr.(descriptor۰class) descr.(descriptor۰elts) ˖descr.(descriptor۰seen)]> descrs) split_list).
          iSplitL.
          { iFrame. iModIntro. iSplit.
            { iPureIntro. apply (model۰validｰmark Hvalid split Hlookup Hlookup_split). }
            iApply big_sepM_insert_delete. iFrame.
            rewrite /= lookup_ge_None_2; first lia.
            rewrite decide_True; first lia.
            iFrame. done.
          }
          iPureIntro. apply (record۰invｰreset Hvalid Hinv split Hlookup Hlookup_split); lia.

        * rewrite bool_decide_eq_false_2 //.
          assert (˖descr.(descriptor۰seen) < length descr.(descriptor۰elts)) as Hseen_lt'.
          { destruct (decide (˖descr.(descriptor۰seen) < length descr.(descriptor۰elts))) as [? | Hge]; first done.
            exfalso. apply Hsplit_last.
            rewrite (_ : pred (length descr.(descriptor۰elts)) = descr.(descriptor۰seen)) in Hlast_lookup; first lia.
            congruence.
          }
          destruct (lookup_lt_is_Some_2 descr.(descriptor۰elts) ˖descr.(descriptor۰seen)) as (split' & Hlookup_split'); first done.
          assert (2 ≤ length descr.(descriptor۰elts)) as Hlength2 by lia.
          wp۰pures. wp۰load. wp۰pures.
          wp۰apply+ (partition٠class_swapｰspec with "[$Hnodes $Hclass_first $Hclass_last]") as "(Hnodes & Hclass_first & Hclass_last)".
          { apply (model۰validｰlinks Hvalid). }
          { apply (model۰validｰelement Hvalid Hlookup Hsplit). }
          { done. }
          { apply (model۰validｰnextｰne Hvalid split Hlookup); done. }
          { apply (model۰validｰnextｰne Hvalid elt Hlookup); done. }
          wp۰apply+ (nodes٠nextｰspec elt with "Hnodes") as "Hnodes"; first done.
          rewrite /= swapｰr (model۰validｰchain Hvalid Hlookup Hlookup_split Hlookup_split').
          wp۰store. wp۰load.
          rewrite decide_False; first lia.
          wp۰store. wp۰pures.
          pose proof (model۰validｰswap Hvalid split elt Hlookup Hsplit Helt Hsplit_seen Helt_seen) as Hvalid'.
          opose proof* (model۰validｰmark Hvalid' elt) as Hvalid''.
          { apply lookup_insert_eq. }
          { rewrite /= list_lookup_fmap Hlookup_split /= swapｰl //. }
          rewrite insert_insert_eq in Hvalid''.
          assert (delete repr descrs !! swap split elt repr = None) as Hlookup_repr'.
          { rewrite lookup_delete_None.
            destruct (decide (repr = swap split elt repr)) as [? | Hne]; first naive.
            right.
            destruct (descrs !! swap split elt repr) as [descr' |] eqn:Hlookup'; last done.
            exfalso. apply Hne.
            apply (model۰validｰdisjoint Hvalid (swap split elt repr) Hlookup Hlookup').
            - rewrite swapｰelem_of //. apply (model۰validｰrepr Hvalid Hlookup).
            - apply (model۰validｰrepr Hvalid Hlookup').
          }
          set descrs' := <[swap split elt repr := Descriptor descr.(descriptor۰class) (swap split elt <$> descr.(descriptor۰elts)) ˖descr.(descriptor۰seen)]> (delete repr descrs).
          assert (split = repr ↔ descr.(descriptor۰seen) = 0) as Hrecord_class.
          { rewrite head_lookup in Hhead. split.
            - intros ->. apply (NoDup_lookup descr.(descriptor۰elts) _ _ repr); done.
            - intros Hzero. rewrite Hzero in Hlookup_split. congruence.
          }
          iAssert (
            model' γ elements
              (swap split elt ∘ prevs ∘ swap split elt)
              (swap split elt ∘ nexts ∘ swap split elt)
              classes
              (<[elt := true]> seens)
              descrs'
          )%I with "[- HΦ]" as "Hmodel".
          { rewrite /model'.
            iSplitR; first done.
            iFrame "Helements_auth Hnodes".
            iApply big_sepM_insert; first done.
            iFrame "Hdescrs".
            iExists (swap split elt last).
            rewrite /= fmap_last Hlast ?length_fmap list_lookup_fmap Hlookup_split' /=.
            rewrite decide_False; first (rewrite ?length_fmap; lia).
            rewrite Nat2Z.inj_succ -Z.add_1_r.
            iFrame. done.
          }
          destruct (decide (descr.(descriptor۰seen) = 0)) as [Hzero | Hzero].
          -- rewrite bool_decide_eq_true_2; first naive.
             wp۰pures.
             iApply ("HΦ" $! _ _ _ descrs' (descr.(descriptor۰class) :: split_list) with "[$Hmodel]").
             iPureIntro.
             pose proof (record۰invｰstep Hvalid Hinv split elt Hlookup Hlookup_split Helt Helt_seen Hlength) as Hinv'.
             rewrite decide_True // in Hinv'.
          -- rewrite bool_decide_eq_false_2; first naive.
             wp۰pures.
             iApply ("HΦ" $! _ _ _ descrs' split_list with "[$Hmodel]").
             iPureIntro.
             pose proof (record۰invｰstep Hvalid Hinv split elt Hlookup Hlookup_split Helt Helt_seen Hlength) as Hinv'.
             rewrite decide_False // in Hinv'.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [record]. *)

  #[local] Lemma partition٠recordｰspec γ part elements prevs nexts classes seens descrs 𝑒𝑙𝑡𝑠 elts :
    list۰model' 𝑒𝑙𝑡𝑠 (#*ˡ elts) →
    record۰inv part ∅ descrs [] →
    {{{
      model' γ elements prevs nexts classes seens descrs ∗
      [∗ list] elt ∈ elts,
        ∃ v,
        partition۰element γ elt v
    }}}
      partition٠record 𝑒𝑙𝑡𝑠
    {{{
      prevs' nexts' seens' descrs' split_list
    , RET list۰to_val (#*ˡ split_list);
      model' γ elements prevs' nexts' classes seens' descrs' ∗
      ⌜record۰inv part (list_to_set elts) descrs' split_list⌝
    }}}.
  Proof.
    iIntros "%H𝑒𝑙𝑡𝑠 %Hinv %Φ (Hmodel & #Helts) HΦ".

    wp۰rec.
    pose (Ψ := (λ i (_ : list val) acc,
      ∃ prevs nexts seens descrs split_list,
      ⌜acc = list۰to_val (#*ˡ split_list)⌝ ∗
      model' γ elements prevs nexts classes seens descrs ∗
      ⌜record۰inv part (list_to_set (take i elts)) descrs split_list⌝
    )%I).
    wp۰apply (list٠foldlｰspec Ψ with "[Hmodel]") as (acc) "(%prevs' & %nexts' & %seens' & %descrs' & %split_list & -> & Hmodel & %Hinv')"; first done.
    { iSplitL.
      - iExists prevs, nexts, seens, descrs, []. iFrame.
        rewrite take_0. iSteps.
      - iIntros "!> %i %v %acc %Hlookup (%prevs' & %nexts' & %seens' & %descrs' & %split_list & -> & Hmodel & %Hinv')".
        apply list_lookup_fmap_Some in Hlookup as (elt & -> & Hlookup).
        iDestruct (big_sepL_lookup with "Helts") as "(%v & Helt)"; first done.
        wp۰apply (partition٠record₁ｰspec with "[$Hmodel $Helt]") as (prevs'' nexts'' seens'' descrs'' split_list') "(Hmodel & %Hinv'')"; first done.
        iModIntro. iExists prevs'', nexts'', seens'', descrs'', split_list'. iFrame. iSplit; first done.
        iPureIntro.
        rewrite (take_S_r _ _ elt) // list_to_set_app_L.
        rewrite (_ : list_to_set (take i elts) ∪ list_to_set [elt] = {[elt]} ∪ list_to_set (take i elts)); first set_solver.
        done.
    }
    rewrite length_fmap take_ge // in Hinv'.
    iApply ("HΦ" with "[$Hmodel //]").
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [split₁]. *)

  #[local] Lemma partition٠split₁ｰspec γ part X elements prevs nexts classes seens descrs class split_list :
    split۰inv part X descrs (class :: split_list) →
    {{{
      model' γ elements prevs nexts classes seens descrs
    }}}
      partition٠split₁ #class
    {{{
      classes' seens' descrs'
    , RET ();
      model' γ elements prevs nexts classes' seens' descrs' ∗
      ⌜split۰inv part X descrs' split_list⌝
    }}}.
  Proof.
    iIntros "%Hinv %Φ (:model') HΦ".

    destruct (split۰invｰsplit_list Hinv (class := class)) as (repr & descr & Hlookup & Hclass); first set_solver.
    opose proof* (split۰invｰpending Hinv Hlookup) as (Hseen & _ & Htake).
    { rewrite Hclass. set_solver. }
    pose proof (model۰validｰNoDup Hvalid Hlookup) as Hnodup.
    pose proof (model۰validｰseen Hvalid Hlookup) as Hseen_le.
    pose proof (model۰validｰhead Hvalid Hlookup) as Hhead.
    pose proof (λ i elt elt', @model۰validｰchain _ _ _ _ _ _ Hvalid _ _ i elt elt' Hlookup) as Hchain.
    assert (
      ∀ elt,
      elt ∈ descr.(descriptor۰elts) →
      elt ∈ elements
    ) as Hsubset.
    { intros elt Helt. apply (model۰validｰelement Hvalid Hlookup Helt). }
    destruct descr as [descr_class elts n]. simpl in *. subst descr_class.
    iDestruct (big_sepM_delete with "Hdescrs") as "((:descriptor۰model) & Hdescrs)"; first done.
    cbn [descriptor۰class descriptor۰elts descriptor۰seen].

    wp۰rec. wp۰load. wp۰load. wp۰pures.
    destruct (decide (n = length elts)) as [-> | Hn].

    - rewrite lookup_ge_None_2 // bool_decide_eq_true_2 //.
      wp۰pures.
      wp۰apply (partition٠class_iterｰspec (λ elts1 classes' seens',
        ⌜ ∀ elt,
          elt ∈ elements →
            classes' elt = classes elt ∧
            seens' elt = if decide (elt ∈ elts1) then false else seens elt
        ⌝
      )%I with "[$Hclass_first $Hclass_last $Hnodes]") as (classes' seens') "(Hclass_first & Hclass_last & Hnodes & %HΨ)"; [done.. | |].
      { iSplit.
        - iPureIntro. intros elt _. split; first done.
          case_decide; [set_solver | done].
        - iIntros "!> %elts1 %elt %elts2 %classes1 %seens1 %Helts Hnodes %HΨ".
          assert (elt ∈ elements) as Helt.
          { apply Hsubset. rewrite Helts. set_solver. }
          wp۰rec.
          iDestruct (nodesｰseenｰacc elt with "Hnodes") as "(Helt_seen & Hnodes)"; first done.
          wp۰store.
          iSpecialize ("Hnodes" with "Helt_seen").
          iExists classes1, (<[elt := false]> seens1). iFrame.
          iPureIntro. intros elt' Helt'.
          destruct (HΨ elt' Helt') as (Hclasses & Hseens).
          split; first done.
          destruct (decide (elt' = elt)) as [-> | Hne].
          + rewrite fn_lookup_insert decide_True //. set_solver.
          + rewrite fn_lookup_insert_ne // Hseens.
            repeat case_decide; set_solver.
      }
      iApply ("HΦ" $! classes (λ elt, if decide (elt ∈ elts) then false else seens elt) (<[repr := Descriptor class elts 0]> descrs)).
      iSplitL.
      + iFrame. iSplitR.
        { iPureIntro. apply (model۰validｰreset Hvalid Hlookup). }
        iSplitL "Hnodes".
        { iApply (nodesｰproper with "Hnodes"). intros elt Helt.
          destruct (HΨ elt Helt) as (-> & ->). done.
        }
        iApply big_sepM_insert_delete. iFrame.
        rewrite /= -head_lookup Hhead /=.
        rewrite decide_False; first lia.
        iFrame. done.
      + iPureIntro. apply (split۰invｰreset Hvalid Hinv Hlookup); done.

    - assert (n < length elts) as Hn' by lia.
      destruct (lookup_lt_is_Some_2 elts n) as (split & Hlookup_split); first done.
      destruct (lookup_lt_is_Some_2 elts (pred n)) as (prev & Hlookup_prev); first lia.
      assert (repr ≠ split) as Hne_split.
      { intros ->. rewrite head_lookup in Hhead.
        opose proof* (NoDup_lookup elts 0 n); [done.. | lia].
      }
      rewrite Hlookup_split. cbn [default].
      rewrite bool_decide_eq_false_2 //.
      wp۰pures.
      wp۰store. wp۰store. wp۰load.
      wp۰store. wp۰load. wp۰store.
      assert (prevs split = prev) as Hprev.
      { assert (nexts prev = split) as <-.
        { apply (Hchain (pred n)); first done.
          rewrite (_ : ˖(pred n) = n) //. lia.
        }
        apply (model۰validｰprevｰnext Hvalid). apply Hsubset. eapply list_elem_of_lookup_2. done.
      }
      wp۰apply+ (nodes٠prevｰspec split with "Hnodes") as "Hnodes".
      { apply Hsubset. eapply list_elem_of_lookup_2. done. }
      rewrite Hprev.
      wp۰block class' as "Hclass'_first Hclass'_last Hclass'_len Hclass'_split Hclass'_split_len".
      iDestruct (descriptorsｰfresh with "Hdescrs Hclass'_first") as %Hfresh.
      iDestruct (pointstoｰne with "Hclass'_first Hclass_first") as %Hne_class.
      assert (
        ∀ repr' descr',
        descrs !! repr' = Some descr' →
        descr'.(descriptor۰class) ≠ class'
      ) as Hfresh'.
      { intros repr' descr' Hlookup'.
        destruct (decide (repr' = repr)) as [-> | Hne].
        - simplify_eq. simpl. intros <-. done.
        - apply (Hfresh repr'). rewrite lookup_delete_ne //.
      }
      wp۰apply+ (partition٠dllist٠iterｰspec (λ elts1 classes' seens',
        ⌜ ∀ elt,
          elt ∈ elements →
            classes' elt = (if decide (elt ∈ elts1) then class' else classes elt) ∧
            seens' elt = if decide (elt ∈ elts1) then false else seens elt
        ⌝
      )%I _ _ _ _ _ _ (take n elts) with "[$Hnodes]") as (classes' seens') "(Hnodes & %HΨ)".
      { pose proof Hnodup as Hnodup'.
        rewrite -(take_drop n elts) NoDup_app in Hnodup'. naive.
      }
      { rewrite head_lookup lookup_take_Some -head_lookup Hhead. split; [done | lia]. }
      { rewrite last_lookup length_take_le; first lia.
        rewrite lookup_take_Some. split; [done | lia].
      }
      { intros i elt elt' (Hlookup1 & _)%lookup_take_Some (Hlookup2 & _)%lookup_take_Some.
        apply (Hchain i); done.
      }
      { intros elt Helt. apply Hsubset, (subseteq_take n elts), Helt. }
      { iSplit.
        - iPureIntro. intros elt _.
          split; case_decide; [set_solver | done | set_solver | done].
        - iIntros "!> %elts1 %elt %elts2 %classes1 %seens1 %Helts Hnodes %HΨ".
          assert (elt ∈ elements) as Helt.
          { apply Hsubset, (subseteq_take n elts). rewrite Helts. set_solver. }
          wp۰rec.
          iDestruct (nodesｰclassｰacc elt with "Hnodes") as "(Helt_class & Hnodes)"; first done.
          wp۰store.
          iSpecialize ("Hnodes" with "Helt_class").
          iDestruct (nodesｰseenｰacc elt with "Hnodes") as "(Helt_seen & Hnodes)"; first done.
          wp۰store.
          iSpecialize ("Hnodes" with "Helt_seen").
          iExists (<[elt := class']> classes1), (<[elt := false]> seens1). iFrame.
          iPureIntro. intros elt' Helt'.
          destruct (HΨ elt' Helt') as (Hclasses & Hseens).
          destruct (decide (elt' = elt)) as [-> | Hne].
          + rewrite !fn_lookup_insert !decide_True //; set_solver.
          + rewrite !fn_lookup_insert_ne // Hclasses Hseens.
            split; repeat case_decide; set_solver.
      }
      iApply ("HΦ" $!
        (λ elt, if decide (elt ∈ take n elts) then class' else classes elt)
        (λ elt, if decide (elt ∈ take n elts) then false else seens elt)
        (<[repr := Descriptor class' (take n elts) 0]> (<[split := Descriptor class (drop n elts) 0]> descrs))
      ).
      iSplitL.
      + iFrame. iSplitR.
        { iPureIntro. apply (model۰validｰsplit Hvalid class' split Hlookup); simpl; [lia | done | done]. }
        iSplitL "Hnodes".
        { iApply (nodesｰproper with "Hnodes"). intros elt Helt.
          destruct (HΨ elt Helt) as (-> & ->). done.
        }
        iApply big_sepM_insert_delete.
        rewrite delete_insert_ne //.
        assert (list.last (take n elts) = Some prev) as Hlast_take.
        { rewrite last_lookup length_take_le; first lia.
          rewrite lookup_take_Some. split; [done | lia].
        }
        assert (take n elts !! 0 = Some repr) as Hhead_take.
        { rewrite lookup_take_Some -head_lookup Hhead. split; [done | lia]. }
        assert (list.last (drop n elts) = Some last) as Hlast_drop.
        { rewrite last_lookup length_drop lookup_drop.
          rewrite last_lookup in Hlast.
          rewrite (_ : n + pred (length elts - n) = pred (length elts)) //. lia.
        }
        iSplitL "Hclass'_first Hclass'_last Hclass'_len Hclass'_split Hclass'_split_len".
        * iExists prev.
          rewrite /= length_take_le; first lia.
          rewrite Hhead_take decide_False; first lia.
          iFrame. done.
        * iApply big_sepM_insert.
          { rewrite lookup_delete_ne //.
            destruct (descrs !! split) as [descr' |] eqn:Hlookup'; last done.
            exfalso. apply Hne_split.
            apply (model۰validｰdisjoint Hvalid split Hlookup Hlookup').
            - eapply list_elem_of_lookup_2. done.
            - apply (model۰validｰrepr Hvalid Hlookup').
          }
          iFrame "Hdescrs".
          iExists last.
          rewrite /= length_drop decide_False; first lia.
          rewrite lookup_drop Nat.add_0_r Hlookup_split /=.
          rewrite Nat2Z.inj_sub; first lia.
          iFrame. done.
      + iPureIntro. apply (split۰invｰsplit Hvalid class' split Hinv Hlookup); simpl; done.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [split]. *)

  #[local] Lemma partition٠splitｰspec γ part X elements prevs nexts classes seens descrs split_list :
    split۰inv part X descrs split_list →
    {{{
      model' γ elements prevs nexts classes seens descrs
    }}}
      partition٠split (list۰to_val (#*ˡ split_list))
    {{{
      classes' seens' descrs'
    , RET ();
      model' γ elements prevs nexts classes' seens' descrs' ∗
      ⌜split۰inv part X descrs' []⌝
    }}}.
  Proof.
    iIntros "%Hinv %Φ Hmodel HΦ".

    wp۰rec.
    wp۰apply (list٠iterｰspec (λ i _,
      ∃ classes seens descrs,
      model' γ elements prevs nexts classes seens descrs ∗
      ⌜split۰inv part X descrs (drop i split_list)⌝
    )%I with "[Hmodel]") as "(%classes' & %seens' & %descrs' & Hmodel & %Hinv')"; first done.
    { iSplitL.
      - iExists classes, seens, descrs. iFrame. rewrite drop_0 //.
      - iIntros "!> %i %v %Hlookup (%classes' & %seens' & %descrs' & Hmodel & %Hinv')".
        apply list_lookup_fmap_Some in Hlookup as (class & -> & Hlookup).
        rewrite (drop_S _ class) // in Hinv'.
        wp۰apply (partition٠split₁ｰspec with "Hmodel") as (classes'' seens'' descrs'') "(Hmodel & %Hinv'')"; first done.
        iSplitR; first done.
        iModIntro. iExists classes'', seens'', descrs''. iFrame. done.
    }
    rewrite length_fmap drop_ge // in Hinv'.
    iApply ("HΦ" with "[$Hmodel //]").
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [refine]. *)

  Lemma partition٠refineｰspec {γ part 𝑒𝑙𝑡𝑠} elts :
    list۰model' 𝑒𝑙𝑡𝑠 (#*ˡ elts) →
    {{{
      partition۰model γ part ∗
      [∗ list] elt ∈ elts,
        ∃ v,
        partition۰element γ elt v
    }}}
      partition٠refine 𝑒𝑙𝑡𝑠
    {{{
      part'
    , RET ();
      partition۰model γ part' ∗
      ⌜ ∀ cl',
        cl' ∈ map_img (SA := gset (gset location)) part' ↔
          cl' ≠ ∅ ∧
            ∃ repr cl,
            part !! repr = Some cl ∧
            ( cl' = cl ∩ list_to_set elts
            ∨ cl' = cl ∖ list_to_set elts
            )
      ⌝ ∗
      ⌜ ∀ repr cl,
        part !! repr = Some cl →
        cl ## list_to_set elts →
        part' !! repr = Some cl
      ⌝
    }}}.
  Proof.
    iIntros "%H𝑒𝑙𝑡𝑠 %Φ ((:model) & #Helts) HΦ".

    assert (
      ∀ repr1 repr2 cl,
      ((λ descr, list_to_set descr.(descriptor۰elts)) <$> descrs) !! repr1 = Some cl →
      ((λ descr, list_to_set descr.(descriptor۰elts)) <$> descrs) !! repr2 = Some cl →
      repr1 = repr2
    ) as Hpart.
    { intros repr1 repr2 cl (descr1 & Hcl1 & Hlookup1)%lookup_fmap_Some (descr2 & Hcl2 & Hlookup2)%lookup_fmap_Some.
      apply (model۰validｰdisjoint Hvalid repr1 Hlookup1 Hlookup2).
      - apply (model۰validｰrepr Hvalid Hlookup1).
      - rewrite -(elem_of_list_to_set (C := gset location)) Hcl2 -Hcl1 elem_of_list_to_set.
        apply (model۰validｰrepr Hvalid Hlookup1).
    }

    wp۰rec.
    wp۰apply+ (partition٠recordｰspec with "[Helements_auth Hnodes Hdescrs]") as (prevs' nexts' seens' descrs' split_list) "(Hmodel & %Hinv)".
    { done. }
    { apply record۰invｰinit. done. }
    { iFrame "∗ # %". }
    iDestruct "Hmodel" as "(:model' =')".
    wp۰apply (partition٠splitｰspec with "[Helements_auth' Hnodes' Hdescrs']") as (classes'' seens'' descrs'') "((:model' ='') & %Hinv')".
    { apply (split۰invｰinit Hvalid' Hpart Hinv). }
    { iFrame "∗ %". }
    destruct (split۰invｰfinal Hvalid'' Hinv') as (Hunseen'' & Hpart' & Huntouched).
    iApply ("HΦ" $! ((λ descr, list_to_set descr.(descriptor۰elts)) <$> descrs'')).
    iSplitL.
    - iExists _, _, _, _, _, descrs''. iFrame "∗ %". done.
    - iPureIntro. split; done.
  Qed.
End partition۰G.

Require zoo_data.partition__opaque.

Please opacify.
