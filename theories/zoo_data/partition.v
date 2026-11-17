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
  #[local] Lemma swapｰfmapｰdiag x xs :
    swap x x <$> xs = xs.
  Proof.
    induction xs as [| x' xs IH]; first done.
    rewrite fmap_cons IH swapｰdiag //.
  Qed.
End swap.

Record descriptor := Descriptor
  { descriptor۰elts : list location
  ; descriptor۰seen : nat
  }.
Implicit Type descr : descriptor.
Implicit Type descrs : gmap location descriptor.

#[local] Abbreviation descriptor۰set descr :=
  (list_to_set (C := gset location) descr.(descriptor۰elts)).

#[local] Definition links۰valid elements prevs nexts :=
  ∀ elt,
  elt ∈ elements →
    nexts elt ∈ elements ∧
    prevs elt ∈ elements ∧
    prevs (nexts elt) = elt ∧
    nexts (prevs elt) = elt.

#[local] Lemma links۰validｰswap {elements prevs nexts} elt1 elt2 :
  links۰valid elements prevs nexts →
  elt1 ∈ elements →
  elt2 ∈ elements →
  links۰valid elements
    (swap elt1 elt2 ∘ prevs ∘ swap elt1 elt2)
    (swap elt1 elt2 ∘ nexts ∘ swap elt1 elt2).
Proof.
  intros Hlinks Helt1 Helt2.
  assert (
    ∀ elt,
    swap elt1 elt2 elt ∈ elements ↔
    elt ∈ elements
  ) as Helements.
  { intros elt. rewrite /swap. repeat case_decide; naive. }
  intros elt Helt.
  apply Helements in Helt as (Hnext & Hprev & Hprev_next & Hnext_prev)%Hlinks.
  rewrite /= !swapｰinvolutive Hprev_next Hnext_prev swapｰinvolutive.
  rewrite !Helements //.
Qed.

#[local] Lemma links۰validｰmake {elements prevs nexts} elt :
  links۰valid elements prevs nexts →
  elt ∉ elements →
  links۰valid ({[elt]} ∪ elements)
    (<[elt := elt]> prevs)
    (<[elt := elt]> nexts).
Proof.
  intros Hlinks Helt elt' [->%elem_of_singleton | Helt']%elem_of_union.
  - rewrite !fn_lookup_insert. set_solver.
  - destruct (Hlinks elt' Helt') as (? & ? & ? & ?).
    assert (elt ≠ elt') by set_solver.
    assert (elt ≠ nexts elt') by set_solver.
    assert (elt ≠ prevs elt') by set_solver.
    rewrite /insert /fn_insert.
    split_and!; repeat case_decide; try congruence; set_solver.
Qed.
#[local] Lemma links۰validｰadd {elements prevs nexts} elt last :
  links۰valid elements prevs nexts →
  elt ∉ elements →
  last ∈ elements →
  links۰valid ({[elt]} ∪ elements)
    (<[elt := last]> (<[nexts last := elt]> prevs))
    (<[last := elt]> (<[elt := nexts last]> nexts)).
Proof.
  intros Hlinks Helt Hlast.
  destruct (Hlinks last Hlast) as (? & ? & ? & ?).
  assert (elt ≠ last) by set_solver.
  assert (elt ≠ nexts last) by set_solver.
  intros elt' [->%elem_of_singleton | Helt']%elem_of_union.
  - rewrite /insert /fn_insert.
    split_and!; repeat case_decide; try congruence; set_solver.
  - destruct (Hlinks elt' Helt') as (? & ? & ? & ?).
    assert (elt ≠ elt') by set_solver.
    assert (elt ≠ nexts elt') by set_solver.
    assert (elt ≠ prevs elt') by set_solver.
    rewrite /insert /fn_insert.
    split_and!; repeat case_decide; try congruence; set_solver.
Qed.

#[local] Ltac solve۰swap elt elt1 elt2 :=
  simpl;
  destruct (decide (elt = elt1)) as [-> | ?];
  [| destruct (decide (elt = elt2)) as [-> | ?];
     [| rewrite (swapｰne elt) //]
  ];
  rewrite /swap /insert /fn_insert /=;
  repeat case_decide; congruence.

Record model۰valid elements prevs nexts classes seens descrs : Prop :=
  { model۰validｰlinks :
      links۰valid elements prevs nexts
  ; model۰validｰelements elt :
      elt ∈ elements ↔
        ∃ class descr,
        descrs !! class = Some descr ∧
        elt ∈ descr.(descriptor۰elts)
  ; model۰validｰnonempty class descr :
      descrs !! class = Some descr →
      descr.(descriptor۰elts) ≠ []
  ; model۰validｰNoDup class descr :
      descrs !! class = Some descr →
      NoDup descr.(descriptor۰elts)
  ; model۰validｰseen class descr :
      descrs !! class = Some descr →
      descr.(descriptor۰seen) ≤ length descr.(descriptor۰elts)
  ; model۰validｰclasses class descr elt :
      descrs !! class = Some descr →
      elt ∈ descr.(descriptor۰elts) →
      classes elt = class
  ; model۰validｰseens class descr elt :
      descrs !! class = Some descr →
      elt ∈ descr.(descriptor۰elts) →
      seens elt = bool_decide (elt ∈ take descr.(descriptor۰seen) descr.(descriptor۰elts))
  ; model۰validｰchain class descr i elt1 elt2 :
      descrs !! class = Some descr →
      descr.(descriptor۰elts) !! i = Some elt1 →
      descr.(descriptor۰elts) !! ˖i = Some elt2 →
      nexts elt1 = elt2
  }.
#[local] Arguments model۰validｰlinks {_ _ _ _ _ _} _.
#[local] Arguments model۰validｰelements {_ _ _ _ _ _} _ _.
#[local] Arguments model۰validｰnonempty {_ _ _ _ _ _} _ {_ _}.
#[local] Arguments model۰validｰNoDup {_ _ _ _ _ _} _ {_ _}.
#[local] Arguments model۰validｰseen {_ _ _ _ _ _} _ {_ _}.
#[local] Arguments model۰validｰclasses {_ _ _ _ _ _} _ {_ _ _}.
#[local] Arguments model۰validｰseens {_ _ _ _ _ _} _ {_ _ _}.
#[local] Arguments model۰validｰchain {_ _ _ _ _ _} _ {_ _ _ _ _}.

Section model۰valid.
  Context {elements prevs nexts classes seens descrs}.
  Context (Hvalid : model۰valid elements prevs nexts classes seens descrs).

  #[local] Lemma model۰validｰnext elt :
    elt ∈ elements →
    nexts elt ∈ elements.
  Proof.
    intros Helt. apply (model۰validｰlinks Hvalid elt Helt).
  Qed.
  #[local] Lemma model۰validｰprevｰnext elt :
    elt ∈ elements →
    prevs (nexts elt) = elt.
  Proof.
    intros Helt. apply (model۰validｰlinks Hvalid elt Helt).
  Qed.
  #[local] Lemma model۰validｰelement {class descr elt} :
    descrs !! class = Some descr →
    elt ∈ descr.(descriptor۰elts) →
    elt ∈ elements.
  Proof.
    intros. apply (model۰validｰelements Hvalid). naive.
  Qed.
  #[local] Lemma model۰validｰdisjoint {class1 descr1 class2 descr2} elt :
    descrs !! class1 = Some descr1 →
    descrs !! class2 = Some descr2 →
    elt ∈ descr1.(descriptor۰elts) →
    elt ∈ descr2.(descriptor۰elts) →
    class1 = class2.
  Proof.
    intros Hlookup1 Hlookup2 Helt1 Helt2.
    rewrite -(model۰validｰclasses Hvalid Hlookup1 Helt1) -(model۰validｰclasses Hvalid Hlookup2 Helt2) //.
  Qed.
  #[local] Lemma model۰validｰother {class descr class' descr'} elt :
    descrs !! class = Some descr →
    descrs !! class' = Some descr' →
    class' ≠ class →
    elt ∈ descr'.(descriptor۰elts) →
    elt ∉ descr.(descriptor۰elts).
  Proof.
    intros Hlookup Hlookup' Hne Helt' Helt.
    apply Hne, (model۰validｰdisjoint elt Hlookup' Hlookup); done.
  Qed.
  #[local] Lemma model۰validｰhead {class descr} :
    descrs !! class = Some descr →
      ∃ first,
      head descr.(descriptor۰elts) = Some first.
  Proof.
    intros Hlookup.
    apply headｰis_Some, (model۰validｰnonempty Hvalid Hlookup).
  Qed.
  #[local] Lemma model۰validｰnextｰne {class descr} elt :
    descrs !! class = Some descr →
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
      assert (elt' ∈ elements) as Helt'.
      { eapply model۰validｰelement; first done. eapply list_elem_of_lookup_2. done. }
      assert (elt ∈ elements) as Helt.
      { eapply model۰validｰelement; first done. eapply list_elem_of_lookup_2. done. }
      assert (elt' = elt) as ->.
      { rewrite -(model۰validｰprevｰnext elt') // -(model۰validｰprevｰnext elt) //. congruence. }
      opose proof* (NoDup_lookup _ i ˖i); [done.. | lia].
  Qed.

  #[local] Lemma model۰validｰupdate {class descr} prevs' nexts' seens' descr' :
    descrs !! class = Some descr →
    links۰valid elements prevs' nexts' →
    ( ∀ elt1 elt2,
      elt1 ∉ descr.(descriptor۰elts) →
      elt2 ∉ descr.(descriptor۰elts) →
      nexts elt1 = elt2 →
      nexts' elt1 = elt2
    ) →
    ( ∀ elt,
      elt ∉ descr.(descriptor۰elts) →
      seens' elt = seens elt
    ) →
    ( ∀ elt,
      elt ∈ descr'.(descriptor۰elts) ↔
      elt ∈ descr.(descriptor۰elts)
    ) →
    NoDup descr'.(descriptor۰elts) →
    descr'.(descriptor۰seen) ≤ length descr'.(descriptor۰elts) →
    ( ∀ elt,
      elt ∈ descr'.(descriptor۰elts) →
      seens' elt = bool_decide (elt ∈ take descr'.(descriptor۰seen) descr'.(descriptor۰elts))
    ) →
    ( ∀ i elt1 elt2,
      descr'.(descriptor۰elts) !! i = Some elt1 →
      descr'.(descriptor۰elts) !! ˖i = Some elt2 →
      nexts' elt1 = elt2
    ) →
    model۰valid elements prevs' nexts' classes seens' (<[class := descr']> descrs).
  Proof.
    intros Hlookup Hlinks Hnexts Hseens Helts Hnodup Hseen Hseens' Hchain.
    assert (
      ∀ class' descr'',
      <[class := descr']> descrs !! class' = Some descr'' ↔
          class' = class ∧
          descr'' = descr'
        ∨ class' ≠ class ∧
          descrs !! class' = Some descr''
    ) as Hlookup'.
    { intros class' descr''. rewrite lookup_insert_Some. naive. }
    constructor.
    - done.
    - intros elt. rewrite (model۰validｰelements Hvalid).
      setoid_rewrite Hlookup'. split.
      + intros (class' & descr'' & Hlookup'' & Helt).
        destruct (decide (class' = class)) as [-> | Hne].
        * rewrite Hlookup in Hlookup''. injection Hlookup'' as <-.
          exists class, descr'. split; first (left; done).
          apply Helts. done.
        * exists class', descr''. split; first (right; done). done.
      + intros (class' & descr'' & [(-> & ->) | (Hne & Hlookup'')] & Helt).
        * exists class, descr. split; first done.
          apply Helts. done.
        * exists class', descr''. done.
    - intros class' descr'' [(-> & ->) | (Hne & Hlookup'')]%Hlookup'.
      + destruct (model۰validｰhead Hlookup) as (first & Hfirst%head_Some_elem_of).
        intros Hnil. apply (not_elem_of_nil first).
        rewrite -Hnil Helts //.
      + apply (model۰validｰnonempty Hvalid Hlookup'').
    - intros class' descr'' [(-> & ->) | (Hne & Hlookup'')]%Hlookup'; first done.
      apply (model۰validｰNoDup Hvalid Hlookup'').
    - intros class' descr'' [(-> & ->) | (Hne & Hlookup'')]%Hlookup'; first done.
      apply (model۰validｰseen Hvalid Hlookup'').
    - intros class' descr'' elt [(-> & ->) | (Hne & Hlookup'')]%Hlookup' Helt.
      + apply Helts in Helt. apply (model۰validｰclasses Hvalid Hlookup Helt).
      + apply (model۰validｰclasses Hvalid Hlookup'' Helt).
    - intros class' descr'' elt [(-> & ->) | (Hne & Hlookup'')]%Hlookup' Helt; first auto.
      assert (elt ∉ descr.(descriptor۰elts)).
      { apply (model۰validｰother elt Hlookup Hlookup''); done. }
      rewrite Hseens //.
      apply (model۰validｰseens Hvalid Hlookup'' Helt).
    - intros class' descr'' i elt1 elt2 [(-> & ->) | (Hne & Hlookup'')]%Hlookup' Hlookup1 Hlookup2; first eauto.
      apply Hnexts; last apply (model۰validｰchain Hvalid Hlookup'' Hlookup1 Hlookup2).
      + apply (model۰validｰother elt1 Hlookup Hlookup''); first done.
        eapply list_elem_of_lookup_2. done.
      + apply (model۰validｰother elt2 Hlookup Hlookup''); first done.
        eapply list_elem_of_lookup_2. done.
  Qed.

  #[local] Lemma model۰validｰmark {class descr} elt :
    descrs !! class = Some descr →
    descr.(descriptor۰elts) !! descr.(descriptor۰seen) = Some elt →
    model۰valid elements prevs nexts classes
      (<[elt := true]> seens)
      (<[class := Descriptor descr.(descriptor۰elts) ˖descr.(descriptor۰seen)]> descrs).
  Proof.
    intros Hlookup Hlookup_elt.
    refine (model۰validｰupdate prevs nexts (<[elt := true]> seens) (Descriptor descr.(descriptor۰elts) ˖descr.(descriptor۰seen)) Hlookup _ _ _ _ _ _ _ _).
    - apply (model۰validｰlinks Hvalid).
    - naive.
    - intros elt' Helt'. rewrite fn_lookup_insert_ne //.
      intros ->. apply Helt'. eapply list_elem_of_lookup_2. done.
    - naive.
    - apply (model۰validｰNoDup Hvalid Hlookup).
    - simpl. apply lookup_lt_Some in Hlookup_elt. lia.
    - intros elt' Helt'. simpl.
      rewrite (take_S_r _ _ elt) //.
      destruct (decide (elt' = elt)) as [-> | Hne].
      + rewrite fn_lookup_insert bool_decide_eq_true_2 //. set_solver.
      + rewrite fn_lookup_insert_ne // (model۰validｰseens Hvalid Hlookup Helt').
        apply bool_decide_ext. set_solver.
    - intros i elt1 elt2. apply (model۰validｰchain Hvalid Hlookup).
  Qed.

  #[local] Lemma model۰validｰswapｰmark {class descr} split elt :
    descrs !! class = Some descr →
    descr.(descriptor۰elts) !! descr.(descriptor۰seen) = Some split →
    elt ∈ descr.(descriptor۰elts) →
    elt ∉ take descr.(descriptor۰seen) descr.(descriptor۰elts) →
    model۰valid elements
      (swap split elt ∘ prevs ∘ swap split elt)
      (swap split elt ∘ nexts ∘ swap split elt)
      classes
      (<[elt := true]> seens)
      (<[class := Descriptor (swap split elt <$> descr.(descriptor۰elts)) ˖descr.(descriptor۰seen)]> descrs).
  Proof.
    intros Hlookup Hlookup_split Helt Helt_seen.
    pose proof (model۰validｰNoDup Hvalid Hlookup) as Hnodup.
    assert (split ∈ descr.(descriptor۰elts)) as Hsplit.
    { eapply list_elem_of_lookup_2. done. }
    assert (split ∉ take descr.(descriptor۰seen) descr.(descriptor۰elts)) as Hsplit_seen.
    { rewrite elem_of_take. intros (i & Hlookup_i & Hi).
      opose proof* (NoDup_lookup _ i descr.(descriptor۰seen)); [done.. | lia].
    }
    assert (
      ∀ elt',
      elt' ∉ descr.(descriptor۰elts) →
      swap split elt elt' = elt'
    ) as Hswap.
    { intros elt' Helt'. apply swapｰne; set_solver. }
    refine (model۰validｰupdate _ _ (<[elt := true]> seens) (Descriptor (swap split elt <$> descr.(descriptor۰elts)) ˖descr.(descriptor۰seen)) Hlookup _ _ _ _ _ _ _ _).
    - apply links۰validｰswap; first apply (model۰validｰlinks Hvalid).
      + eapply model۰validｰelement; done.
      + eapply model۰validｰelement; done.
    - intros elt1 elt2 Helt1 Helt2 <-.
      rewrite /= !Hswap //.
    - intros elt' Helt'. rewrite fn_lookup_insert_ne //. set_solver.
    - intros elt'. rewrite swapｰfmapｰelem_of //.
    - apply NoDup_fmap_2_strong; last done.
      intros ? ? _ _. apply swapｰinj.
    - rewrite /= length_fmap.
      pose proof (lookup_lt_Some _ _ _ Hlookup_split). lia.
    - intros elt' Helt'. simpl in Helt' |- *.
      rewrite -fmap_take (take_S_r _ _ split) // fmap_app swapｰfmapｰid // fmap_cons fmap_nil swapｰl.
      rewrite swapｰfmapｰelem_of // in Helt'.
      destruct (decide (elt' = elt)) as [-> | Hne].
      + rewrite fn_lookup_insert bool_decide_eq_true_2 //. set_solver.
      + rewrite fn_lookup_insert_ne // (model۰validｰseens Hvalid Hlookup Helt').
        apply bool_decide_ext. set_solver.
    - intros i elt1 elt2 (elt1_ & -> & Hlookup1)%list_lookup_fmap_Some (elt2_ & -> & Hlookup2)%list_lookup_fmap_Some.
      rewrite /= swapｰinvolutive (model۰validｰchain Hvalid Hlookup Hlookup1 Hlookup2) //.
  Qed.

  #[local] Lemma model۰validｰreset {class descr} :
    descrs !! class = Some descr →
    model۰valid elements prevs nexts classes
      (λ elt, if decide (elt ∈ descr.(descriptor۰elts)) then false else seens elt)
      (<[class := Descriptor descr.(descriptor۰elts) 0]> descrs).
  Proof.
    intros Hlookup.
    refine (model۰validｰupdate prevs nexts _ (Descriptor descr.(descriptor۰elts) 0) Hlookup _ _ _ _ _ _ _ _).
    - apply (model۰validｰlinks Hvalid).
    - naive.
    - intros elt Helt. rewrite decide_False //.
    - naive.
    - apply (model۰validｰNoDup Hvalid Hlookup).
    - simpl. lia.
    - intros elt Helt. simpl.
      rewrite decide_True // take_0 bool_decide_eq_false_2 //.
    - intros i elt1 elt2. apply (model۰validｰchain Hvalid Hlookup).
  Qed.

  #[local] Lemma model۰validｰsplit {class descr} class' :
    descrs !! class = Some descr →
    descrs !! class' = None →
    0 < descr.(descriptor۰seen) < length descr.(descriptor۰elts) →
    model۰valid elements prevs nexts
      (λ elt, if decide (elt ∈ take descr.(descriptor۰seen) descr.(descriptor۰elts)) then class' else classes elt)
      (λ elt, if decide (elt ∈ take descr.(descriptor۰seen) descr.(descriptor۰elts)) then false else seens elt)
      ( <[class := Descriptor (drop descr.(descriptor۰seen) descr.(descriptor۰elts)) 0]> $
        <[class' := Descriptor (take descr.(descriptor۰seen) descr.(descriptor۰elts)) 0]> descrs
      ).
  Proof.
    intros Hlookup Hlookup' Hn.
    pose proof (model۰validｰseen Hvalid Hlookup) as Hn'.
    pose proof (model۰validｰNoDup Hvalid Hlookup) as Hnodup.
    destruct descr as [elts n]. simpl in *.
    assert (class' ≠ class) as Hne by congruence.
    assert (
      ∀ class'' descr',
      <[class := Descriptor (drop n elts) 0]> (<[class' := Descriptor (take n elts) 0]> descrs) !! class'' = Some descr' ↔
          class'' = class ∧
          descr' = Descriptor (drop n elts) 0
        ∨ class'' = class' ∧
          descr' = Descriptor (take n elts) 0
        ∨ class'' ≠ class ∧
          class'' ≠ class' ∧
          descrs !! class'' = Some descr'
    ) as Hlookup''.
    { intros class'' descr'. rewrite !lookup_insert_Some. naive. }
    constructor.
    - apply (model۰validｰlinks Hvalid).
    - intros elt. rewrite (model۰validｰelements Hvalid).
      setoid_rewrite Hlookup''. split.
      + intros (class'' & descr' & Hlookup''' & Helt).
        destruct (decide (class'' = class)) as [-> | Hne'].
        * simplify_eq. apply (elem_ofｰtakeｰdrop _ n) in Helt as [Helt | Helt]; naive.
        * exists class'', descr'. split; last done.
          right. right. split_and!; try done. congruence.
      + intros (class'' & descr' & [(-> & ->) | [(-> & ->) | (Hne1 & Hne2 & Hlookup''')]] & Helt).
        * exists class, (Descriptor elts n). split; first done.
          apply (elem_ofｰtakeｰdrop elts n). naive.
        * exists class, (Descriptor elts n). split; first done.
          apply (elem_ofｰtakeｰdrop elts n). naive.
        * naive.
    - intros class'' descr' [(-> & ->) | [(-> & ->) | (Hne1 & Hne2 & Hlookup''')]]%Hlookup''.
      + simpl. rewrite -length_zero_iff_nil length_drop. lia.
      + simpl. rewrite -length_zero_iff_nil length_take. lia.
      + apply (model۰validｰnonempty Hvalid Hlookup''').
    - intros class'' descr' [(-> & ->) | [(-> & ->) | (Hne1 & Hne2 & Hlookup''')]]%Hlookup''.
      + apply NoDupｰdrop. done.
      + apply NoDupｰtake. done.
      + apply (model۰validｰNoDup Hvalid Hlookup''').
    - intros class'' descr' [(-> & ->) | [(-> & ->) | (Hne1 & Hne2 & Hlookup''')]]%Hlookup''; [simpl; lia.. |].
      apply (model۰validｰseen Hvalid Hlookup''').
    - intros class'' descr' elt [(-> & ->) | [(-> & ->) | (Hne1 & Hne2 & Hlookup''')]]%Hlookup'' Helt; simpl in *.
      + rewrite decide_False.
        { intros Helt'. apply (NoDupｰelem_ofｰtakeｰdrop elts n elt); done. }
        apply (model۰validｰclasses Hvalid Hlookup), (elem_ofｰtakeｰdrop elts n). naive.
      + rewrite decide_True //.
      + assert (elt ∉ elts) as Helt'.
        { apply (model۰validｰother elt Hlookup Hlookup'''); done. }
        rewrite decide_False.
        { rewrite (elem_ofｰtakeｰdrop elts n) in Helt'. naive. }
        apply (model۰validｰclasses Hvalid Hlookup''' Helt).
    - intros class'' descr' elt [(-> & ->) | [(-> & ->) | (Hne1 & Hne2 & Hlookup''')]]%Hlookup'' Helt; simpl in *.
      + rewrite decide_False.
        { intros Helt'. apply (NoDupｰelem_ofｰtakeｰdrop elts n elt); done. }
        rewrite ?take_0 (model۰validｰseens Hvalid Hlookup).
        { apply (elem_ofｰtakeｰdrop elts n). naive. }
        rewrite !bool_decide_eq_false_2 //.
        intros Helt'. apply (NoDupｰelem_ofｰtakeｰdrop elts n elt); done.
      + rewrite decide_True // take_0 bool_decide_eq_false_2 //.
      + assert (elt ∉ elts) as Helt'.
        { apply (model۰validｰother elt Hlookup Hlookup'''); done. }
        rewrite decide_False.
        { rewrite (elem_ofｰtakeｰdrop elts n) in Helt'. naive. }
        apply (model۰validｰseens Hvalid Hlookup''' Helt).
    - intros class'' descr' i elt1 elt2 [(-> & ->) | [(-> & ->) | (Hne1 & Hne2 & Hlookup''')]]%Hlookup'' Hlookup1 Hlookup2; simpl in *.
      + rewrite lookup_drop in Hlookup1.
        rewrite lookup_drop Nat.add_succ_r in Hlookup2.
        apply (model۰validｰchain Hvalid Hlookup Hlookup1 Hlookup2).
      + apply lookup_take_Some in Hlookup1 as (Hlookup1 & _).
        apply lookup_take_Some in Hlookup2 as (Hlookup2 & _).
        apply (model۰validｰchain Hvalid Hlookup Hlookup1 Hlookup2).
      + apply (model۰validｰchain Hvalid Hlookup''' Hlookup1 Hlookup2).
  Qed.

  #[local] Lemma model۰validｰmake elt class :
    elt ∉ elements →
    descrs !! class = None →
    model۰valid
      ({[elt]} ∪ elements)
      (<[elt := elt]> prevs)
      (<[elt := elt]> nexts)
      (<[elt := class]> classes)
      (<[elt := false]> seens)
      (<[class := Descriptor [elt] 0]> descrs).
  Proof.
    intros Helt Hlookup.
    assert (
      ∀ class' descr elt',
      descrs !! class' = Some descr →
      elt' ∈ descr.(descriptor۰elts) →
      elt ≠ elt'
    ) as Hfresh.
    { intros class' descr elt' Hlookup' Helt' ->. apply Helt. eapply model۰validｰelement; done. }
    constructor.
    - apply links۰validｰmake; last done.
      apply (model۰validｰlinks Hvalid).
    - intros elt'.
      rewrite elem_of_union elem_of_singleton (model۰validｰelements Hvalid).
      setoid_rewrite lookup_insert_Some. split.
      + intros [-> | (class' & descr & Hlookup' & Helt')].
        * exists class, (Descriptor [elt] 0). set_solver.
        * exists class', descr. split; last done.
          right. split; last done. congruence.
      + intros (class' & descr & [(<- & <-) | (Hne & Hlookup')] & Helt').
        * left. set_solver.
        * right. naive.
    - intros class' descr [(<- & <-) | (Hne & Hlookup')]%lookup_insert_Some; first done.
      apply (model۰validｰnonempty Hvalid Hlookup').
    - intros class' descr [(<- & <-) | (Hne & Hlookup')]%lookup_insert_Some.
      + apply NoDup_singleton.
      + apply (model۰validｰNoDup Hvalid Hlookup').
    - intros class' descr [(<- & <-) | (Hne & Hlookup')]%lookup_insert_Some.
      + simpl. lia.
      + apply (model۰validｰseen Hvalid Hlookup').
    - intros class' descr elt' [(<- & <-) | (Hne & Hlookup')]%lookup_insert_Some Helt'.
      + apply list_elem_of_singleton in Helt' as ->.
        rewrite !fn_lookup_insert //.
      + rewrite !fn_lookup_insert_ne; first (eapply Hfresh; done).
        apply (model۰validｰclasses Hvalid Hlookup' Helt').
    - intros class' descr elt' [(<- & <-) | (Hne & Hlookup')]%lookup_insert_Some Helt'.
      + apply list_elem_of_singleton in Helt' as ->.
        rewrite fn_lookup_insert. symmetry.
        apply bool_decide_eq_false_2, not_elem_of_nil.
      + rewrite fn_lookup_insert_ne; first (eapply Hfresh; done).
        apply (model۰validｰseens Hvalid Hlookup' Helt').
    - intros class' descr i elt1 elt2 [(<- & <-) | (Hne & Hlookup')]%lookup_insert_Some Hlookup1 Hlookup2.
      + apply lookup_lt_Some in Hlookup2. simpl in Hlookup2. lia.
      + rewrite fn_lookup_insert_ne.
        { eapply Hfresh; first done. eapply list_elem_of_lookup_2. done. }
        apply (model۰validｰchain Hvalid Hlookup' Hlookup1 Hlookup2).
  Qed.

  #[local] Lemma model۰validｰadd {class descr} elt last :
    descrs !! class = Some descr →
    descr.(descriptor۰seen) = 0 →
    list.last descr.(descriptor۰elts) = Some last →
    elt ∉ elements →
    model۰valid
      ({[elt]} ∪ elements)
      (<[elt := last]> (<[nexts last := elt]> prevs))
      (<[last := elt]> (<[elt := nexts last]> nexts))
      (<[elt := class]> classes)
      (<[elt := false]> seens)
      (<[class := Descriptor (descr.(descriptor۰elts) ++ [elt]) 0]> descrs).
  Proof.
    intros Hlookup Hseen Hlast Helt.
    pose proof (model۰validｰNoDup Hvalid Hlookup) as Hnodup.
    assert (last ∈ descr.(descriptor۰elts)) as Hlast_elts.
    { apply last_Some_elem_of. done. }
    assert (
      ∀ class' descr elt',
      descrs !! class' = Some descr →
      elt' ∈ descr.(descriptor۰elts) →
      elt ≠ elt'
    ) as Hfresh.
    { intros class' descr' elt' Hlookup' Helt' ->. apply Helt. eapply model۰validｰelement; done. }
    constructor.
    - apply links۰validｰadd; [apply (model۰validｰlinks Hvalid) | done |].
      eapply model۰validｰelement; done.
    - intros elt'.
      rewrite elem_of_union elem_of_singleton (model۰validｰelements Hvalid).
      setoid_rewrite lookup_insert_Some. split.
      + intros [-> | (class' & descr' & Hlookup' & Helt')].
        * exists class, (Descriptor (descr.(descriptor۰elts) ++ [elt]) 0). set_solver.
        * destruct (decide (class' = class)) as [-> | Hne].
          -- simplify_eq.
             exists class, (Descriptor (descr.(descriptor۰elts) ++ [elt]) 0). set_solver.
          -- exists class', descr'. naive.
      + intros (class' & descr' & [(<- & <-) | (Hne & Hlookup')] & Helt').
        * simpl in Helt'. apply elem_of_app in Helt' as [Helt' | ->%list_elem_of_singleton].
          -- right. naive.
          -- left. done.
        * right. naive.
    - intros class' descr' [(<- & <-) | (Hne & Hlookup')]%lookup_insert_Some.
      + simpl. intros (_ & [=])%app_eq_nil.
      + apply (model۰validｰnonempty Hvalid Hlookup').
    - intros class' descr' [(<- & <-) | (Hne & Hlookup')]%lookup_insert_Some.
      + apply NoDup_app. split_and!; [done | | apply NoDup_singleton].
        intros elt' Helt' ->%list_elem_of_singleton. eapply Hfresh; done.
      + apply (model۰validｰNoDup Hvalid Hlookup').
    - intros class' descr' [(<- & <-) | (Hne & Hlookup')]%lookup_insert_Some.
      + simpl. lia.
      + apply (model۰validｰseen Hvalid Hlookup').
    - intros class' descr' elt' [(<- & <-) | (Hne & Hlookup')]%lookup_insert_Some Helt'.
      + simpl in Helt'. apply elem_of_app in Helt' as [Helt' | ->%list_elem_of_singleton].
        * rewrite fn_lookup_insert_ne; first (eapply Hfresh; done).
          apply (model۰validｰclasses Hvalid Hlookup Helt').
        * rewrite fn_lookup_insert //.
      + rewrite fn_lookup_insert_ne; first (eapply Hfresh; done).
        apply (model۰validｰclasses Hvalid Hlookup' Helt').
    - intros class' descr' elt' [(<- & <-) | (Hne & Hlookup')]%lookup_insert_Some Helt'.
      + transitivity false; last first.
        { symmetry. apply bool_decide_eq_false_2. simpl. rewrite ?take_0. apply not_elem_of_nil. }
        simpl in Helt'. apply elem_of_app in Helt' as [Helt' | ->%list_elem_of_singleton].
        * rewrite fn_lookup_insert_ne; first (eapply Hfresh; done).
          rewrite (model۰validｰseens Hvalid Hlookup Helt') Hseen.
          apply bool_decide_eq_false_2. rewrite ?take_0. apply not_elem_of_nil.
        * rewrite fn_lookup_insert //.
      + rewrite fn_lookup_insert_ne; first (eapply Hfresh; done).
        apply (model۰validｰseens Hvalid Hlookup' Helt').
    - intros class' descr' i elt1 elt2 [(<- & <-) | (Hne & Hlookup')]%lookup_insert_Some Hlookup1 Hlookup2.
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
          rewrite fn_lookup_insert_ne.
          { eapply Hfresh; first done. eapply list_elem_of_lookup_2. done. }
          apply (model۰validｰchain Hvalid Hlookup Hlookup1 Hlookup2).
        * apply list_lookup_singleton_Some in Hlookup2 as (Hi' & <-).
          assert (elt1 = last) as ->.
          { rewrite last_lookup in Hlast. pose proof Hlookup1 as ?%lookup_lt_Some.
            rewrite (_ : pred (length descr.(descriptor۰elts)) = i) in Hlast; first lia.
            congruence.
          }
          rewrite fn_lookup_insert //.
      + assert (elt1 ∈ descr'.(descriptor۰elts)) as Helt1.
        { eapply list_elem_of_lookup_2. done. }
        assert (elt1 ≠ last).
        { intros ->. apply (model۰validｰother last Hlookup Hlookup'); done. }
        rewrite !fn_lookup_insert_ne //; first (eapply Hfresh; done).
        apply (model۰validｰchain Hvalid Hlookup' Hlookup1 Hlookup2).
  Qed.
End model۰valid.

#[local] Definition descriptors۰part descrs part :=
  ∀ repr cl,
  part !! repr = Some cl ↔
    ∃ class descr,
    descrs !! class = Some descr ∧
    head descr.(descriptor۰elts) = Some repr ∧
    cl = descriptor۰set descr.

#[local] Lemma descriptors۰partｰexists descrs :
  ( ∀ class1 descr1 class2 descr2 repr,
    descrs !! class1 = Some descr1 →
    descrs !! class2 = Some descr2 →
    head descr1.(descriptor۰elts) = Some repr →
    head descr2.(descriptor۰elts) = Some repr →
    class1 = class2
  ) →
    ∃ part,
    descriptors۰part descrs part.
Proof.
  induction descrs as [| class descr descrs Hlookup IH] using map_ind.
  - intros _. exists ∅. intros repr cl.
    rewrite lookup_empty. split; first done.
    intros (class & descr & Hlookup & _). rewrite lookup_empty // in Hlookup.
  - intros Hheads.
    destruct IH as (part & Hpart).
    { intros class1 descr1 class2 descr2 repr Hlookup1 Hlookup2.
      apply Hheads; rewrite lookup_insert_ne //; congruence.
    }
    destruct (head descr.(descriptor۰elts)) as [repr |] eqn:Hhead.
    + exists (<[repr := descriptor۰set descr]> part).
      intros repr' cl. rewrite lookup_insert_Some Hpart.
      setoid_rewrite lookup_insert_Some. split.
      * intros [(<- & <-) | (Hne & class' & descr' & Hlookup' & Hhead' & ->)]; first naive.
        exists class', descr'. split_and!; try done.
        right. split; last done. congruence.
      * intros (class' & descr' & [(<- & <-) | (Hne & Hlookup')] & Hhead' & ->).
        -- left. naive.
        -- right. split; last naive.
           intros <-. apply Hne.
           apply (Hheads class descr class' descr' repr); try done.
           ++ apply lookup_insert_eq.
           ++ rewrite lookup_insert_ne //.
    + exists part.
      intros repr' cl. rewrite Hpart.
      setoid_rewrite lookup_insert_Some. split.
      * intros (class' & descr' & Hlookup' & Hhead' & ->).
        exists class', descr'. split_and!; try done.
        right. split; last done.
        intros <-. congruence.
      * intros (class' & descr' & [(<- & <-) | (Hne & Hlookup')] & Hhead' & ->).
        -- congruence.
        -- exists class', descr'. done.
Qed.

#[local] Lemma descriptors۰partｰlookup {descrs part repr cl} elt :
  descriptors۰part descrs part →
  part !! repr = Some cl →
  elt ∈ cl →
    ∃ class descr,
    descrs !! class = Some descr ∧
    head descr.(descriptor۰elts) = Some repr ∧
    cl = descriptor۰set descr ∧
    elt ∈ descr.(descriptor۰elts).
Proof.
  intros Hpart (class & descr & Hlookup & Hhead & ->)%Hpart Helt.
  exists class, descr. rewrite elem_of_list_to_set in Helt. done.
Qed.
#[local] Lemma descriptors۰partｰinsert {descrs part} class descr repr :
  descriptors۰part descrs part →
  head descr.(descriptor۰elts) = Some repr →
  ( ∀ descr',
    descrs !! class = Some descr' →
    head descr'.(descriptor۰elts) = Some repr
  ) →
  ( ∀ class' descr',
    descrs !! class' = Some descr' →
    class' ≠ class →
    head descr'.(descriptor۰elts) ≠ Some repr
  ) →
  descriptors۰part (<[class := descr]> descrs) (<[repr := descriptor۰set descr]> part).
Proof.
  intros Hpart Hhead Hclass Hother repr' cl.
  rewrite lookup_insert_Some Hpart.
  setoid_rewrite lookup_insert_Some. split.
  - intros [(<- & <-) | (Hne & class' & descr' & Hlookup' & Hhead' & ->)].
    + exists class, descr. naive.
    + exists class', descr'. split_and!; try done.
      right. split; last done.
      intros <-. pose proof (Hclass _ Hlookup'). congruence.
  - intros (class' & descr' & [(<- & <-) | (Hne & Hlookup')] & Hhead' & ->).
    + left. naive.
    + right. split.
      * intros <-. apply (Hother _ _ Hlookup'); [congruence | done].
      * exists class', descr'. done.
Qed.

Record record۰inv descrs0 X descrs split_list : Prop :=
  { record۰invｰdom :
      dom descrs = dom descrs0
  ; record۰invｰelts class descr0 descr :
      descrs0 !! class = Some descr0 →
      descrs !! class = Some descr →
        descriptor۰set descr = descriptor۰set descr0 ∧
        ( descr.(descriptor۰seen) = 0 →
          descr.(descriptor۰elts) = descr0.(descriptor۰elts)
        )
  ; record۰invｰseen class descr elt :
      descrs !! class = Some descr →
        elt ∈ take descr.(descriptor۰seen) descr.(descriptor۰elts) ↔
          elt ∈ descr.(descriptor۰elts) ∧
          elt ∈ X ∧
          length descr.(descriptor۰elts) ≠ 1
  ; record۰invｰNoDup :
      NoDup split_list
  ; record۰invｰsplit_list class :
      class ∈ split_list ↔
        ∃ descr,
        descrs !! class = Some descr ∧
        descr.(descriptor۰seen) ≠ 0
  }.
#[local] Arguments record۰invｰdom {_ _ _ _} _.
#[local] Arguments record۰invｰelts {_ _ _ _} _ {_ _ _}.
#[local] Arguments record۰invｰseen {_ _ _ _} _ {_ _} _ _.
#[local] Arguments record۰invｰNoDup {_ _ _ _} _.
#[local] Arguments record۰invｰsplit_list {_ _ _ _} _ _.

#[local] Lemma record۰invｰinit descrs :
  map_Forall (λ _ descr, descr.(descriptor۰seen) = 0) descrs →
  record۰inv descrs ∅ descrs [].
Proof.
  intros Hunseen.
  constructor.
  - done.
  - intros class descr0 descr Hlookup0 Hlookup. simplify_eq. naive.
  - intros class descr elt Hlookup.
    rewrite (Hunseen _ _ Hlookup) take_0. set_solver.
  - apply NoDup_nil_2.
  - intros class. split; first set_solver.
    intros (descr & Hlookup & Hseen).
    exfalso. apply Hseen, (Hunseen _ _ Hlookup).
Qed.

Section record۰inv.
  Context {elements prevs nexts classes seens descrs}.
  Context (Hvalid : model۰valid elements prevs nexts classes seens descrs).
  Context {descrs0 X split_list}.
  Context (Hinv : record۰inv descrs0 X descrs split_list).

  #[local] Lemma record۰invｰsingleton {class descr} elt :
    descrs !! class = Some descr →
    length descr.(descriptor۰elts) = 1 →
    elt ∈ descr.(descriptor۰elts) →
    record۰inv descrs0 ({[elt]} ∪ X) descrs split_list.
  Proof.
    intros Hlookup Hlength Helt.
    constructor; try apply Hinv.
    intros class' descr' elt' Hlookup'.
    rewrite (record۰invｰseen Hinv elt' Hlookup').
    destruct (decide (class' = class)) as [-> | Hne].
    - simplify_eq. rewrite Hlength. naive.
    - assert (elt' ∈ descr'.(descriptor۰elts) → elt' ≠ elt).
      { intros Helt' ->. apply (model۰validｰother Hvalid elt Hlookup Hlookup'); done. }
      set_solver.
  Qed.

  #[local] Lemma record۰invｰstep {class descr} split elt :
    descrs !! class = Some descr →
    descr.(descriptor۰elts) !! descr.(descriptor۰seen) = Some split →
    elt ∈ descr.(descriptor۰elts) →
    elt ∉ take descr.(descriptor۰seen) descr.(descriptor۰elts) →
    length descr.(descriptor۰elts) ≠ 1 →
    record۰inv descrs0 ({[elt]} ∪ X)
      (<[class := Descriptor (swap split elt <$> descr.(descriptor۰elts)) ˖descr.(descriptor۰seen)]> descrs)
      (if decide (descr.(descriptor۰seen) = 0) then class :: split_list else split_list).
  Proof.
    intros Hlookup Hlookup_split Helt Helt_seen Hlength.
    pose proof (model۰validｰNoDup Hvalid Hlookup) as Hnodup.
    assert (split ∈ descr.(descriptor۰elts)) as Hsplit.
    { eapply list_elem_of_lookup_2. done. }
    assert (split ∉ take descr.(descriptor۰seen) descr.(descriptor۰elts)) as Hsplit_seen.
    { rewrite elem_of_take. intros (i & Hlookup_i & Hi).
      opose proof* (NoDup_lookup _ i descr.(descriptor۰seen)); [done.. | lia].
    }
    assert (elt ∉ X) as Helt_X.
    { intros HX. apply Helt_seen, (record۰invｰseen Hinv elt Hlookup). done. }
    assert (
      take ˖descr.(descriptor۰seen) (swap split elt <$> descr.(descriptor۰elts)) =
      take descr.(descriptor۰seen) descr.(descriptor۰elts) ++ [elt]
    ) as Htake.
    { rewrite -fmap_take (take_S_r _ _ split) // fmap_app swapｰfmapｰid // /= swapｰl //. }
    constructor.
    - rewrite dom_insert_lookup_L //. apply (record۰invｰdom Hinv).
    - intros class' descr0 descr' Hlookup0 [(<- & <-) | (Hne & Hlookup')]%lookup_insert_Some.
      + destruct (record۰invｰelts Hinv Hlookup0 Hlookup) as (<- & _).
        split; last (simpl; lia).
        apply set_eq. intros elt'.
        rewrite /= !elem_of_list_to_set swapｰfmapｰelem_of //.
      + apply (record۰invｰelts Hinv Hlookup0 Hlookup').
    - intros class' descr' elt' [(<- & <-) | (Hne & Hlookup')]%lookup_insert_Some.
      + rewrite /= Htake elem_of_app list_elem_of_singleton (record۰invｰseen Hinv _ Hlookup).
        rewrite swapｰfmapｰelem_of // length_fmap.
        set_solver.
      + rewrite (record۰invｰseen Hinv elt' Hlookup').
        assert (elt' ∈ descr'.(descriptor۰elts) → elt' ≠ elt).
        { intros Helt' ->. apply (model۰validｰother Hvalid elt Hlookup Hlookup'); done. }
        set_solver.
    - destruct (decide (descr.(descriptor۰seen) = 0)) as [Hseen | Hseen].
      + apply NoDup_cons. split; last apply (record۰invｰNoDup Hinv).
        rewrite (record۰invｰsplit_list Hinv).
        intros (descr' & Hlookup' & Hseen'). simplify_eq.
      + apply (record۰invｰNoDup Hinv).
    - intros class'. setoid_rewrite lookup_insert_Some.
      assert (
        class' ∈ split_list ↔
          ∃ descr',
          descrs !! class' = Some descr' ∧
          descr'.(descriptor۰seen) ≠ 0
      ) as Hsplit_list by apply (record۰invｰsplit_list Hinv).
      destruct (decide (descr.(descriptor۰seen) = 0)) as [Hseen | Hseen].
      + rewrite elem_of_cons Hsplit_list.
        destruct (decide (class' = class)) as [-> | Hne]; first naive.
        split.
        * intros [-> | (descr' & Hlookup' & Hseen')]; naive.
        * intros (descr' & [(-> & <-) | (_ & Hlookup')] & Hseen'); naive.
      + rewrite Hsplit_list.
        destruct (decide (class' = class)) as [-> | Hne].
        * split; first naive.
          intros _. exists descr. done.
        * naive.
  Qed.
End record۰inv.

Record split۰inv descrs0 X descrs split_list : Prop :=
  { split۰invｰpending class :
      class ∈ split_list →
        ∃ descr0 descr,
        descrs0 !! class = Some descr0 ∧
        descrs !! class = Some descr ∧
        descr.(descriptor۰seen) ≠ 0 ∧
        descriptor۰set descr = descriptor۰set descr0 ∧
        ( ∀ elt,
          elt ∈ take descr.(descriptor۰seen) descr.(descriptor۰elts) ↔
            elt ∈ descr.(descriptor۰elts) ∧
            elt ∈ X
        )
  ; split۰invｰdone class descr :
      descrs !! class = Some descr →
      class ∉ split_list →
        descr.(descriptor۰seen) = 0 ∧
        ∃ class0 descr0,
        descrs0 !! class0 = Some descr0 ∧
        ( descriptor۰set descr = descriptor۰set descr0 ∩ X
        ∨ descriptor۰set descr = descriptor۰set descr0 ∖ X
        )
  ; split۰invｰcomplete class0 descr0 :
      descrs0 !! class0 = Some descr0 →
        class0 ∈ split_list ∨
        ∀ cl,
        (cl = descriptor۰set descr0 ∩ X ∨ cl = descriptor۰set descr0 ∖ X) →
        cl ≠ ∅ →
          ∃ class descr,
          descrs !! class = Some descr ∧
          class ∉ split_list ∧
          descriptor۰set descr = cl
  ; split۰invｰuntouched class0 descr0 :
      descrs0 !! class0 = Some descr0 →
      descriptor۰set descr0 ## X →
        ∃ descr,
        descrs !! class0 = Some descr ∧
        descr.(descriptor۰elts) = descr0.(descriptor۰elts)
  ; split۰invｰNoDup :
      NoDup split_list
  }.
#[local] Arguments split۰invｰpending {_ _ _ _} _ {_}.
#[local] Arguments split۰invｰdone {_ _ _ _} _ {_ _}.
#[local] Arguments split۰invｰcomplete {_ _ _ _} _ {_ _}.
#[local] Arguments split۰invｰuntouched {_ _ _ _} _ {_ _}.
#[local] Arguments split۰invｰNoDup {_ _ _ _} _.

Section split۰inv.
  Context {elements prevs nexts classes seens descrs}.
  Context (Hvalid : model۰valid elements prevs nexts classes seens descrs).

  #[local] Lemma split۰invｰinit {descrs0 X split_list} :
    record۰inv descrs0 X descrs split_list →
    split۰inv descrs0 X descrs split_list.
  Proof.
    intros Hinv.
    assert (
      ∀ class descr,
      descrs !! class = Some descr →
      class ∉ split_list →
        descr.(descriptor۰seen) = 0 ∧
        ( descriptor۰set descr ∩ X = ∅
        ∨ descriptor۰set descr ⊆ X
        )
    ) as Hunseen.
    { intros class descr Hlookup Hclass.
      assert (descr.(descriptor۰seen) = 0) as Hseen.
      { destruct (decide (descr.(descriptor۰seen) = 0)) as [? | Hseen]; first done.
        exfalso. apply Hclass, (record۰invｰsplit_list Hinv). naive.
      }
      split; first done.
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
      ∀ class descr,
      descrs !! class = Some descr →
        ∃ descr0,
        descrs0 !! class = Some descr0
    ) as Hdom.
    { intros class descr Hlookup.
      apply elem_of_dom. rewrite -(record۰invｰdom Hinv). apply elem_of_dom. done.
    }
    constructor.
    - intros class Hclass.
      apply (record۰invｰsplit_list Hinv) in Hclass as (descr & Hlookup & Hseen).
      destruct (Hdom _ _ Hlookup) as (descr0 & Hlookup0).
      exists descr0, descr. split_and!; try done.
      + apply (record۰invｰelts Hinv Hlookup0 Hlookup).
      + intros elt. rewrite (record۰invｰseen Hinv elt Hlookup).
        split; first naive.
        intros (Helt & HX). split_and!; try done.
        intros Hlength.
        pose proof (model۰validｰseen Hvalid Hlookup) as Hseen_le.
        opose proof* (proj1 (record۰invｰseen Hinv elt Hlookup)) as (_ & _ & Hlength').
        { rewrite take_ge //. lia. }
        done.
    - intros class descr Hlookup Hclass.
      destruct (Hunseen _ _ Hlookup Hclass) as (Hseen & Hpiece).
      destruct (Hdom _ _ Hlookup) as (descr0 & Hlookup0).
      split; first done.
      exists class, descr0. split; first done.
      destruct (record۰invｰelts Hinv Hlookup0 Hlookup) as (<- & _).
      destruct Hpiece; [right | left]; set_solver.
    - intros class0 descr0 Hlookup0.
      destruct (decide (class0 ∈ split_list)) as [Hclass | Hclass]; first naive.
      right. intros cl Hcl Hcl_ne.
      assert (is_Some (descrs !! class0)) as (descr & Hlookup).
      { apply elem_of_dom. rewrite (record۰invｰdom Hinv). apply elem_of_dom. done. }
      destruct (Hunseen _ _ Hlookup Hclass) as (Hseen & Hpiece).
      destruct (record۰invｰelts Hinv Hlookup0 Hlookup) as (Hset & _).
      exists class0, descr. split_and!; try done.
      destruct Hpiece; set_solver.
    - intros class0 descr0 Hlookup0 Hdisjoint.
      assert (is_Some (descrs !! class0)) as (descr & Hlookup).
      { apply elem_of_dom. rewrite (record۰invｰdom Hinv). apply elem_of_dom. done. }
      exists descr. split; first done.
      apply (record۰invｰelts Hinv Hlookup0 Hlookup).
      destruct (decide (descr.(descriptor۰seen) = 0)) as [? | Hseen]; first done.
      exfalso.
      destruct (record۰invｰelts Hinv Hlookup0 Hlookup) as (Hset & _).
      pose proof (model۰validｰseen Hvalid Hlookup) as Hseen_le.
      destruct (lookup_lt_is_Some_2 descr.(descriptor۰elts) 0) as (elt & Hlookup_elt); first lia.
      opose proof* (proj1 (record۰invｰseen Hinv elt Hlookup)) as (Helt & HX & _).
      { apply elem_of_take. exists 0. split; [done | lia]. }
      apply (Hdisjoint elt); last done.
      rewrite -Hset elem_of_list_to_set //.
    - apply (record۰invｰNoDup Hinv).
  Qed.

  #[local] Lemma split۰invｰreset {descrs0 X class split_list descr} :
    split۰inv descrs0 X descrs (class :: split_list) →
    descrs !! class = Some descr →
    descr.(descriptor۰seen) = length descr.(descriptor۰elts) →
    split۰inv descrs0 X (<[class := Descriptor descr.(descriptor۰elts) 0]> descrs) split_list.
  Proof.
    intros Hinv Hlookup Hseen.
    pose proof (split۰invｰNoDup Hinv) as (Hclass & Hnodup)%NoDup_cons.
    opose proof* (split۰invｰpending Hinv (class := class)) as (descr0 & descr_ & Hlookup0 & Hlookup_ & Hseen' & Hset & Htake); first set_solver.
    simplify_eq.
    rewrite take_ge in Htake; first lia.
    assert (descriptor۰set descr ⊆ X) as HX by set_solver.
    pose proof (model۰validｰnonempty Hvalid Hlookup) as Hnonempty.
    constructor.
    - intros class' Hclass'.
      destruct (split۰invｰpending Hinv (class := class')) as (descr0' & descr' & ?); first set_solver.
      exists descr0', descr'. rewrite lookup_insert_ne //. set_solver.
    - intros class' descr' [(<- & <-) | (Hne & Hlookup')]%lookup_insert_Some Hclass'.
      + split; first done.
        exists class, descr0. split; first done.
        left. set_solver.
      + apply (split۰invｰdone Hinv Hlookup'). set_solver.
    - intros class0 descr0' Hlookup0'.
      destruct (split۰invｰcomplete Hinv Hlookup0') as [[-> | Hclass0]%elem_of_cons | Hcomplete].
      + simplify_eq. right. intros cl [-> | ->] Hcl.
        * exists class, (Descriptor descr.(descriptor۰elts) 0).
          rewrite lookup_insert_eq. set_solver.
        * set_solver.
      + left. done.
      + right. intros cl Hcl Hcl_ne.
        destruct (Hcomplete cl Hcl Hcl_ne) as (class' & descr' & Hlookup' & Hclass' & <-).
        exists class', descr'.
        rewrite lookup_insert_ne; first set_solver.
        set_solver.
    - intros class0 descr0' Hlookup0' Hdisjoint.
      destruct (split۰invｰuntouched Hinv Hlookup0' Hdisjoint) as (descr' & Hlookup' & Helts).
      exists descr'. rewrite lookup_insert_ne //.
      intros ->. simplify_eq.
      destruct descr.(descriptor۰elts) as [| elt ?] eqn:Helts'; first done.
      apply (Hdisjoint elt); set_solver.
    - done.
  Qed.

  #[local] Lemma split۰invｰsplit {descrs0 X class split_list descr} class' :
    split۰inv descrs0 X descrs (class :: split_list) →
    descrs !! class = Some descr →
    descrs !! class' = None →
    descr.(descriptor۰seen) < length descr.(descriptor۰elts) →
    split۰inv descrs0 X
      ( <[class := Descriptor (drop descr.(descriptor۰seen) descr.(descriptor۰elts)) 0]> $
        <[class' := Descriptor (take descr.(descriptor۰seen) descr.(descriptor۰elts)) 0]> descrs
      )
      split_list.
  Proof.
    intros Hinv Hlookup Hlookup' Hseen_lt.
    pose proof (split۰invｰNoDup Hinv) as (Hclass & Hnodup)%NoDup_cons.
    opose proof* (split۰invｰpending Hinv (class := class)) as (descr0 & descr_ & Hlookup0 & Hlookup_ & Hseen & Hset & Htake); first set_solver.
    simplify_eq.
    pose proof (model۰validｰNoDup Hvalid Hlookup) as Hnodup_elts.
    destruct descr as [elts n]. simpl in *.
    assert (class' ≠ class) as Hne.
    { intros ->. congruence. }
    assert (class' ∉ split_list) as Hclass'.
    { intros Hclass'.
      destruct (split۰invｰpending Hinv (class := class')) as (? & ? & _ & ? & _); [set_solver | congruence].
    }
    assert (list_to_set (C := gset location) (take n elts) = descriptor۰set descr0 ∩ X) as Htake'.
    { rewrite -Hset. apply set_eq. intros elt. rewrite elem_of_intersection !elem_of_list_to_set Htake //. }
    assert (list_to_set (C := gset location) (drop n elts) = descriptor۰set descr0 ∖ X) as Hdrop'.
    { rewrite -Hset. apply set_eq. intros elt.
      rewrite elem_of_difference !elem_of_list_to_set.
      rewrite (elem_ofｰtakeｰdrop elts n) Htake.
      split; last naive.
      intros Helt. split; first naive.
      intros HX. apply (NoDupｰelem_ofｰtakeｰdrop elts n elt Hnodup_elts); last done.
      apply Htake. split; last done.
      rewrite (elem_ofｰtakeｰdrop elts n). naive.
    }
    assert (
      ∃ elt,
      elt ∈ take n elts
    ) as (elt & Helt).
    { destruct (lookup_lt_is_Some_2 elts 0) as (elt & Hlookup_elt); first lia.
      exists elt. apply elem_of_take. exists 0. split; [done | lia].
    }
    constructor.
    - intros class'' Hclass''.
      destruct (split۰invｰpending Hinv (class := class'')) as (descr0'' & descr'' & Hlookup0'' & Hlookup'' & ?); first set_solver.
      exists descr0'', descr''.
      rewrite !lookup_insert_ne; [congruence | set_solver | done].
    - intros class'' descr'' Hlookup'' Hclass''.
      rewrite !lookup_insert_Some in Hlookup''.
      destruct Hlookup'' as [(<- & <-) | (Hne1 & [(<- & <-) | (Hne2 & Hlookup'')])].
      + split; first done. exists class, descr0. naive.
      + split; first done. exists class, descr0. naive.
      + apply (split۰invｰdone Hinv Hlookup''). set_solver.
    - intros class0 descr0' Hlookup0'.
      destruct (split۰invｰcomplete Hinv Hlookup0') as [[-> | Hclass0]%elem_of_cons | Hcomplete].
      + simplify_eq. right. intros cl [-> | ->] Hcl.
        * exists class', (Descriptor (take n elts) 0).
          rewrite lookup_insert_ne // lookup_insert_eq. naive.
        * exists class, (Descriptor (drop n elts) 0).
          rewrite lookup_insert_eq. naive.
      + left. done.
      + right. intros cl Hcl Hcl_ne.
        destruct (Hcomplete cl Hcl Hcl_ne) as (class'' & descr'' & Hlookup'' & Hclass'' & <-).
        exists class'', descr''.
        assert (class'' ≠ class) by (intros ->; set_solver).
        assert (class'' ≠ class').
        { intros ->. congruence. }
        rewrite !lookup_insert_ne //. set_solver.
    - intros class0 descr0' Hlookup0' Hdisjoint'.
      destruct (split۰invｰuntouched Hinv Hlookup0' Hdisjoint') as (descr'' & Hlookup'' & Helts).
      exists descr''.
      assert (class0 ≠ class').
      { intros ->. congruence. }
      assert (class0 ≠ class).
      { intros ->. simplify_eq.
        apply Htake in Helt as (Helt & HX).
        apply (Hdisjoint' elt); last done.
        rewrite /= -Hset elem_of_list_to_set //.
      }
      rewrite !lookup_insert_ne //.
    - done.
  Qed.

  #[local] Lemma split۰invｰfinal {descrs0 part0 X part} :
    ( ∀ class0 descr0,
      descrs0 !! class0 = Some descr0 →
      descr0.(descriptor۰elts) ≠ []
    ) →
    descriptors۰part descrs0 part0 →
    descriptors۰part descrs part →
    split۰inv descrs0 X descrs [] →
      map_Forall (λ _ descr, descr.(descriptor۰seen) = 0) descrs ∧
      ( ∀ cl',
        cl' ∈ map_img (SA := gset (gset location)) part ↔
          cl' ≠ ∅ ∧
            ∃ repr cl,
            part0 !! repr = Some cl ∧
            ( cl' = cl ∩ X
            ∨ cl' = cl ∖ X
            )
      ) ∧
      ( ∀ repr cl,
        part0 !! repr = Some cl →
        cl ## X →
        part !! repr = Some cl
      ).
  Proof.
    intros Hnonempty0 Hpart0 Hpart Hinv. split_and!.
    - intros class descr Hlookup.
      apply (split۰invｰdone Hinv Hlookup). apply not_elem_of_nil.
    - intros cl'. rewrite elem_of_map_img. split.
      + intros (repr & (class & descr & Hlookup & Hhead & ->)%Hpart).
        destruct (split۰invｰdone Hinv Hlookup) as (_ & class0 & descr0 & Hlookup0 & Hcl); first apply not_elem_of_nil.
        split.
        * apply head_Some_elem_of in Hhead. set_solver.
        * destruct (headｰis_Some _ (Hnonempty0 _ _ Hlookup0)) as (repr0 & Hhead0).
          exists repr0, (descriptor۰set descr0). split; last done.
          apply Hpart0. naive.
      + intros (Hcl'_ne & repr0 & cl0 & (class0 & descr0 & Hlookup0 & Hhead0 & ->)%Hpart0 & Hcl').
        destruct (split۰invｰcomplete Hinv Hlookup0) as [Hclass | Hcomplete]; first set_solver.
        destruct (Hcomplete cl' Hcl' Hcl'_ne) as (class & descr & Hlookup & _ & <-).
        destruct (model۰validｰhead Hvalid Hlookup) as (repr & Hhead).
        exists repr. apply Hpart. naive.
    - intros repr cl (class0 & descr0 & Hlookup0 & Hhead0 & ->)%Hpart0 Hdisjoint.
      destruct (split۰invｰuntouched Hinv Hlookup0 Hdisjoint) as (descr & Hlookup & Helts).
      apply Hpart. exists class0, descr. rewrite Helts. naive.
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

  #[local] Definition descriptor۰model class descr : iProp Σ :=
    ∃ first last,
    ⌜head descr.(descriptor۰elts) = Some first⌝ ∗
    ⌜list.last descr.(descriptor۰elts) = Some last⌝ ∗
    class.[first] ↦ #first ∗
    class.[last] ↦ #last ∗
    class.[len] ↦ #(length descr.(descriptor۰elts)) ∗
    class.[split] ↦ #(default first (descr.(descriptor۰elts) !! descr.(descriptor۰seen))) ∗
    class.[split_len] ↦ #(if decide (descr.(descriptor۰seen) = length descr.(descriptor۰elts)) then 0 else descr.(descriptor۰seen)).
  #[local] Instance : CustomIpat "descriptor۰model" :=
    " ( %first{}
      & %last{}
      & %Hfirst{}
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
    [∗ map] class ↦ descr ∈ descrs,
      descriptor۰model class descr.
  #[local] Instance : CustomIpat "model'" :=
    " ( %Hvalid{}
      & Helements_auth{}
      & Hnodes{}
      & Hdescrs{}
      )
    ".

  Please Definition partition۰model γ part : iProp Σ :=
    ∃ elements prevs nexts classes seens descrs,
    ⌜descriptors۰part descrs part⌝ ∗
    ⌜map_Forall (λ _ descr, descr.(descriptor۰seen) = 0) descrs⌝ ∗
    model' γ elements prevs nexts classes seens descrs.
  #[local] Instance : CustomIpat "model" :=
    " ( %elements{}
      & %prevs{}
      & %nexts{}
      & %classes{}
      & %seens{}
      & %descrs{}
      & %Hpart{}
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

  #[local] Lemma nodes٠classｰspec {elements prevs nexts classes seens descrs class descr} elt :
    model۰valid elements prevs nexts classes seens descrs →
    descrs !! class = Some descr →
    elt ∈ descr.(descriptor۰elts) →
    {{{
      nodes elements prevs nexts classes seens
    }}}
      (#elt).{partition٠class_}
    {{{
      RET #class;
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

  #[local] Lemma descriptorsｰfresh descrs class v :
    ([∗ map] class ↦ descr ∈ descrs, descriptor۰model class descr) -∗
    class.[first] ↦ v -∗
    ⌜descrs !! class = None⌝.
  Proof.
    iIntros "Hdescrs Hclass_first".
    destruct (descrs !! class) as [descr |] eqn:Hlookup; last done.
    iDestruct (big_sepM_lookup with "Hdescrs") as "(:descriptor۰model =')"; first done.
    iDestruct (pointstoｰexclusive with "Hclass_first Hclass'_first") as %[].
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
    rewrite /model' /nodes !big_opS_empty !big_opM_empty.
    iFrame. iPureIntro. split_and!; [| apply map_Forall_empty | | done..].
    - intros repr cl. rewrite lookup_empty. split; first done.
      intros (class & descr & Hlookup & _). rewrite lookup_empty // in Hlookup.
    - constructor; try (intros *; rewrite lookup_empty; done).
      + intros elt. set_solver.
      + set_solver.
  Qed.
  Lemma partition۰modelｰvalid γ part :
    partition۰model γ part ⊢
    ⌜partition۰valid part⌝.
  Proof.
    iIntros "(:model)". iPureIntro. split.
    - intros repr cl (class & descr & Hlookup & Hhead & ->)%Hpart.
      rewrite elem_of_list_to_set. apply head_Some_elem_of. done.
    - intros repr1 cl1 repr2 cl2 (class1 & descr1 & Hlookup1 & Hhead1 & ->)%Hpart (class2 & descr2 & Hlookup2 & Hhead2 & ->)%Hpart Hne.
      apply elem_of_disjoint. intros elt Helt1%elem_of_list_to_set Helt2%elem_of_list_to_set.
      apply Hne.
      pose proof (model۰validｰdisjoint Hvalid elt Hlookup1 Hlookup2 Helt1 Helt2) as <-.
      congruence.
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
    iDestruct (elements۰elemｰvalid with "Helements_auth Helements_elem") as %(class & descr & Hlookup & Helt)%(model۰validｰelements Hvalid).
    destruct (model۰validｰhead Hvalid Hlookup) as (repr & Hhead).
    iExists repr, (descriptor۰set descr). iPureIntro. split.
    - apply Hpart. naive.
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
      wp۰apply (IH (elts1 ++ [elt]) with "[$Hnodes $HΨ $Hfn] HΦ"); [rewrite -assoc // | done..].
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
    iDestruct (descriptorsｰfresh with "Hdescrs Hclass_first") as %Hlookup.
    assert (
      ∀ class' descr',
      descrs !! class' = Some descr' →
      head descr'.(descriptor۰elts) ≠ Some elt
    ) as Hheads.
    { intros class' descr' Hlookup' Hhead%head_Some_elem_of.
      apply Helt. eapply (model۰validｰelement Hvalid); done.
    }
    iMod (elementsｰinsert elt with "Helements_auth") as "(Helements_auth & #Helements_elem)".
    iDestruct (nodesｰinsert elt elt elt class false with "Hnodes Helt_prev Helt_next Helt_class Helt_seen") as "Hnodes"; first done.

    iApply "HΦ".
    iSplitR.
    { iPureIntro.
      destruct (part !! elt) as [cl |] eqn:Hpart_lookup; last done.
      apply Hpart in Hpart_lookup as (class' & descr' & Hlookup' & Hhead & _).
      exfalso. apply (Hheads _ _ Hlookup' Hhead).
    }
    iSplitL; last iSteps.
    iExists _, _, _, _, _, (<[class := Descriptor [elt] 0]> descrs). iFrame.
    iSplitR.
    { iPureIntro.
      rewrite (_ : {[elt]} = descriptor۰set (Descriptor [elt] 0)); first set_solver.
      apply descriptors۰partｰinsert; [done | done | congruence |].
      intros class' descr' Hlookup' _. apply (Hheads _ _ Hlookup').
    }
    iSplitR. { iPureIntro. apply map_Forall_insert_2; done. }
    iSplitR. { iPureIntro. apply (model۰validｰmake Hvalid); done. }
    iApply (big_sepM_insert_2 with "[- Hdescrs] Hdescrs").
    iExists elt, elt. iSteps.
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

    destruct (descriptors۰partｰlookup elt Hpart Hpart_lookup Helt) as (class & descr & Hlookup & Hhead & -> & Helt').
    pose proof (Hunseen _ _ Hlookup) as Hseen. simpl in Hseen.

    wp۰rec.
    wp۰apply+ (nodes٠classｰspec elt Hvalid Hlookup Helt' with "Hnodes") as "Hnodes".
    wp۰apply+ (partition٠dllist٠createｰspec with "[//]") as (elt') "(Helt'_prev & Helt'_next & #Helt'_data & Helt'_class & Helt'_seen)".
    iDestruct (nodesｰfresh with "Hnodes Helt'_prev") as %Helt''.
    iDestruct (nodesｰinsert elt' elt' elt' class false with "Hnodes Helt'_prev Helt'_next Helt'_class Helt'_seen") as "Hnodes"; first done.
    iDestruct (big_sepM_insert_acc with "Hdescrs") as "((:descriptor۰model) & Hdescrs)"; first done.
    assert (first = repr) as -> by congruence.
    assert (last ∈ elements) as Hlast_elements.
    { eapply (model۰validｰelement Hvalid); first done. apply last_Some_elem_of. done. }
    assert (elt' ≠ last) by set_solver.
    wp۰apply+ (partition٠class_addｰspec with "[$Hnodes $Hclass_last $Hclass_len]") as "(Hnodes & Hclass_last & Hclass_len)".
    { set_solver. }
    { set_solver. }
    { rewrite fn_lookup_insert_ne //. apply elem_of_union_r, (model۰validｰnext Hvalid _ Hlast_elements). }
    rewrite fn_lookup_insert_ne //.
    iMod (elementsｰinsert elt' with "Helements_auth") as "(Helements_auth & #Helements_elem')".

    wp۰pures.
    iApply "HΦ".
    iSplitL; last iSteps.
    iExists ({[elt']} ∪ elements),
      (<[elt' := last]> (<[nexts last := elt']> prevs)),
      (<[last := elt']> (<[elt' := nexts last]> nexts)),
      (<[elt' := class]> classes),
      (<[elt' := false]> seens),
      (<[class := Descriptor (descr.(descriptor۰elts) ++ [elt']) 0]> descrs).
    iFrame "Helements_auth". iSplitR.
    { iPureIntro.
      rewrite (_ : descriptor۰set descr ∪ {[elt']} = descriptor۰set (Descriptor (descr.(descriptor۰elts) ++ [elt']) 0)).
      { rewrite /= list_to_set_app_L. set_solver. }
      apply descriptors۰partｰinsert; first done.
      - rewrite /= head_app Hhead //.
      - intros descr' Hlookup'. simplify_eq. done.
      - intros class' descr' Hlookup' Hne Hhead'. apply Hne.
        apply (model۰validｰdisjoint Hvalid repr Hlookup' Hlookup); apply head_Some_elem_of; done.
    }
    iSplitR. { iPureIntro. apply map_Forall_insert_2; done. }
    iSplitR. { iPureIntro. apply (model۰validｰadd Hvalid); done. }
    iSplitL "Hnodes".
    { iApply (nodesｰproper with "Hnodes"). intros x _.
      rewrite /insert /fn_insert. repeat case_decide; naive.
    }
    iApply "Hdescrs".
    iExists repr, elt'.
    rewrite /= head_app Hhead last_snoc length_app /= Hseen -!head_lookup head_app Hhead /=.
    pose proof (model۰validｰnonempty Hvalid Hlookup) as Hnonempty.
    assert (length descr.(descriptor۰elts) ≠ 0).
    { rewrite length_zero_iff_nil //. }
    rewrite Nat2Z.inj_add (decide_False (P := (0 = length _ + 1)%nat)); first lia.
    rewrite decide_False; first lia.
    iFrameSteps.
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

    destruct (descriptors۰partｰlookup elt1 Hpart Hpart_lookup_1 Helt1) as (class1 & descr1 & Hlookup1 & Hhead1 & -> & Helt1').
    destruct (descriptors۰partｰlookup elt2 Hpart Hpart_lookup_2 Helt2) as (class2 & descr2 & Hlookup2 & Hhead2 & -> & Helt2').

    wp۰rec.
    wp۰apply+ (nodes٠classｰspec elt2 Hvalid Hlookup2 Helt2' with "Hnodes") as "Hnodes".
    wp۰apply (nodes٠classｰspec elt1 Hvalid Hlookup1 Helt1' with "Hnodes") as "Hnodes".
    wp۰pures.
    rewrite (bool_decide_ext (class1 = class2) (repr1 = repr2)).
    { split.
      - intros <-. congruence.
      - intros <-.
        apply (model۰validｰdisjoint Hvalid repr1 Hlookup1 Hlookup2); apply head_Some_elem_of; done.
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

    destruct (descriptors۰partｰlookup elt Hpart Hpart_lookup Helt) as (class & descr & Hlookup & Hhead & -> & Helt').

    wp۰rec.
    wp۰apply+ (nodes٠classｰspec elt Hvalid Hlookup Helt' with "Hnodes") as "Hnodes".
    iDestruct (big_sepM_lookup_acc with "Hdescrs") as "((:descriptor۰model) & Hdescrs)"; first done.
    assert (first = repr) as -> by congruence.
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

    destruct (descriptors۰partｰlookup elt Hpart Hpart_lookup Helt) as (class & descr & Hlookup & Hhead & -> & Helt').

    wp۰rec.
    wp۰apply+ (nodes٠classｰspec elt Hvalid Hlookup Helt' with "Hnodes") as "Hnodes".
    iDestruct (big_sepM_lookup_acc with "Hdescrs") as "((:descriptor۰model) & Hdescrs)"; first done.
    wp۰load.
    iDestruct ("Hdescrs" with "[Hclass_first Hclass_last Hclass_len Hclass_split Hclass_split_len]") as "Hdescrs"; first iSteps.
    rewrite size_list_to_set; first apply (model۰validｰNoDup Hvalid Hlookup).
    iApply "HΦ".
    iFrameSteps.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [record₁]. *)

  #[local] Lemma partition٠record₁ｰspec γ descrs0 X elements prevs nexts classes seens descrs split_list elt v :
    record۰inv descrs0 X descrs split_list →
    {{{
      model' γ elements prevs nexts classes seens descrs ∗
      partition۰element γ elt v
    }}}
      partition٠record₁ (list۰to_val (#*ˡ split_list)) #elt
    {{{
      prevs' nexts' seens' descrs' split_list'
    , RET list۰to_val (#*ˡ split_list');
      model' γ elements prevs' nexts' classes seens' descrs' ∗
      ⌜record۰inv descrs0 ({[elt]} ∪ X) descrs' split_list'⌝
    }}}.
  Proof.
    iIntros "%Hinv %Φ ((:model') & (:element)) HΦ".

    iDestruct (elements۰elemｰvalid with "Helements_auth Helements_elem") as %(class & descr & Hlookup & Helt)%(model۰validｰelements Hvalid).
    pose proof (model۰validｰelement Hvalid Hlookup Helt) as Helt_elements.
    pose proof (model۰validｰNoDup Hvalid Hlookup) as Hnodup.
    pose proof (model۰validｰseen Hvalid Hlookup) as Hseen.
    iDestruct (big_sepM_insert_acc with "Hdescrs") as "((:descriptor۰model) & Hdescrs)"; first done.

    wp۰rec.
    wp۰apply+ (nodes٠classｰspec elt Hvalid Hlookup Helt with "Hnodes") as "Hnodes".
    wp۰apply+ (partition٠class_is_singletonｰspec with "Hclass_len") as "Hclass_len".
    destruct (decide (length descr.(descriptor۰elts) = 1)) as [Hlength | Hlength].

    - rewrite bool_decide_eq_true_2 //.
      wp۰pures.
      iDestruct ("Hdescrs" $! descr with "[Hclass_first Hclass_last Hclass_len Hclass_split Hclass_split_len]") as "Hdescrs"; first iFrameSteps.
      rewrite insert_id //.
      iApply ("HΦ" $! prevs nexts seens descrs split_list).
      iFrameSteps. iPureIntro.
      apply (record۰invｰsingleton Hvalid Hinv elt Hlookup Hlength Helt).

    - rewrite bool_decide_eq_false_2 //.
      wp۰apply+ (nodes٠seenｰspec with "Hnodes") as "Hnodes"; first done.
      rewrite (model۰validｰseens Hvalid Hlookup Helt).
      destruct (decide (elt ∈ take descr.(descriptor۰seen) descr.(descriptor۰elts))) as [Helt_seen | Helt_seen].

      + rewrite bool_decide_eq_true_2 //.
        wp۰pures.
        assert ({[elt]} ∪ X = X) as ->.
        { apply (record۰invｰseen Hinv elt Hlookup) in Helt_seen. set_solver. }
        iDestruct ("Hdescrs" $! descr with "[Hclass_first Hclass_last Hclass_len Hclass_split Hclass_split_len]") as "Hdescrs"; first iFrameSteps.
        rewrite insert_id //.
        iApply ("HΦ" $! prevs nexts seens descrs split_list).
        iFrameSteps.

      + rewrite bool_decide_eq_false_2 //.
        wp۰pures.
        assert (descr.(descriptor۰seen) < length descr.(descriptor۰elts)) as Hseen_lt.
        { destruct (decide (descr.(descriptor۰seen) < length descr.(descriptor۰elts))) as [? | Hge]; first done.
          rewrite take_ge in Helt_seen; [lia | done].
        }
        destruct (lookup_lt_is_Some_2 descr.(descriptor۰elts) descr.(descriptor۰seen)) as (split & Hlookup_split); first done.
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
        pose proof (record۰invｰstep Hvalid Hinv split elt Hlookup Hlookup_split Helt Helt_seen Hlength) as Hinv'.
        destruct (decide (split = last)) as [<- | Hsplit_last].

        * rewrite bool_decide_eq_true_2 //.
          assert (descr.(descriptor۰seen) = pred (length descr.(descriptor۰elts))) as Hseen_eq.
          { apply (NoDup_lookup descr.(descriptor۰elts) _ _ split); done. }
          assert (k = descr.(descriptor۰seen)) as ->.
          { apply lookup_lt_Some in Hlookup_k. lia. }
          simplify_eq.
          rewrite swapｰfmapｰdiag decide_False in Hinv'; first lia.
          wp۰pures. wp۰load. wp۰store. wp۰store. wp۰pures.
          iDestruct ("Hdescrs" $! (Descriptor descr.(descriptor۰elts) ˖descr.(descriptor۰seen)) with "[Hclass_first Hclass_last Hclass_len Hclass_split Hclass_split_len]") as "Hdescrs".
          { rewrite /descriptor۰model /= lookup_ge_None_2; first lia.
            rewrite decide_True; first lia.
            iFrameSteps.
          }
          iApply ("HΦ" $! prevs nexts (<[split := true]> seens) _ split_list).
          iFrameSteps. iPureIntro.
          apply (model۰validｰmark Hvalid split Hlookup Hlookup_split).

        * rewrite bool_decide_eq_false_2 //.
          assert (˖descr.(descriptor۰seen) < length descr.(descriptor۰elts)) as Hseen_lt'.
          { destruct (decide (˖descr.(descriptor۰seen) < length descr.(descriptor۰elts))) as [? | Hge]; first done.
            exfalso. apply Hsplit_last.
            rewrite (_ : pred (length descr.(descriptor۰elts)) = descr.(descriptor۰seen)) in Hlast_lookup; first lia.
            congruence.
          }
          destruct (lookup_lt_is_Some_2 descr.(descriptor۰elts) ˖descr.(descriptor۰seen)) as (split' & Hlookup_split'); first done.
          assert (2 ≤ length descr.(descriptor۰elts)) as Hlength2 by lia.
          assert (split = first ↔ descr.(descriptor۰seen) = 0) as Hrecord_class.
          { rewrite head_lookup in Hfirst. split.
            - intros ->. apply (NoDup_lookup descr.(descriptor۰elts) _ _ first); done.
            - intros Hzero. rewrite Hzero in Hlookup_split. congruence.
          }
          wp۰pures. wp۰load. wp۰pures.
          wp۰apply+ (partition٠class_swapｰspec with "[$Hnodes $Hclass_first $Hclass_last]") as "(Hnodes & Hclass_first & Hclass_last)".
          { apply (model۰validｰlinks Hvalid). }
          { apply (model۰validｰelement Hvalid Hlookup). eapply list_elem_of_lookup_2. done. }
          { done. }
          { apply (model۰validｰnextｰne Hvalid split Hlookup); first done.
            eapply list_elem_of_lookup_2. done.
          }
          { apply (model۰validｰnextｰne Hvalid elt Hlookup); done. }
          wp۰apply+ (nodes٠nextｰspec elt with "Hnodes") as "Hnodes"; first done.
          rewrite /= swapｰr (model۰validｰchain Hvalid Hlookup Hlookup_split Hlookup_split').
          wp۰store. wp۰load.
          rewrite decide_False; first lia.
          wp۰store. wp۰pures.
          iDestruct ("Hdescrs" $! (Descriptor (swap split elt <$> descr.(descriptor۰elts)) ˖descr.(descriptor۰seen)) with "[Hclass_first Hclass_last Hclass_len Hclass_split Hclass_split_len]") as "Hdescrs".
          { iExists (swap split elt first), (swap split elt last).
            rewrite /= head_lookup list_lookup_fmap -head_lookup Hfirst fmap_last Hlast.
            rewrite ?length_fmap list_lookup_fmap Hlookup_split' /=.
            rewrite decide_False; first (rewrite ?length_fmap; lia).
            rewrite Nat2Z.inj_succ -Z.add_1_r.
            iFrameSteps.
          }
          pose proof (model۰validｰswapｰmark Hvalid split elt Hlookup Hlookup_split Helt Helt_seen) as Hvalid'.
          destruct (decide (descr.(descriptor۰seen) = 0)) as [Hzero | Hzero].
          -- rewrite bool_decide_eq_true_2; first naive.
             wp۰pures.
             iApply ("HΦ" $! _ _ _ _ (class :: split_list)).
             iFrameSteps.
          -- rewrite bool_decide_eq_false_2; first naive.
             wp۰pures.
             iApply ("HΦ" $! _ _ _ _ split_list).
             iFrameSteps.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [record]. *)

  #[local] Lemma partition٠recordｰspec γ descrs0 elements prevs nexts classes seens descrs 𝑒𝑙𝑡𝑠 elts :
    list۰model' 𝑒𝑙𝑡𝑠 (#*ˡ elts) →
    record۰inv descrs0 ∅ descrs [] →
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
      ⌜record۰inv descrs0 (list_to_set elts) descrs' split_list⌝
    }}}.
  Proof.
    iIntros "%H𝑒𝑙𝑡𝑠 %Hinv %Φ (Hmodel & #Helts) HΦ".

    wp۰rec.
    wp۰apply (list٠foldlｰspec (λ i _ acc,
      ∃ prevs nexts seens descrs split_list,
      ⌜acc = list۰to_val (#*ˡ split_list)⌝ ∗
      model' γ elements prevs nexts classes seens descrs ∗
      ⌜record۰inv descrs0 (list_to_set (take i elts)) descrs split_list⌝
    )%I with "[Hmodel]") as (acc) "(%prevs' & %nexts' & %seens' & %descrs' & %split_list & -> & Hmodel & %Hinv')"; first done.
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

  #[local] Lemma partition٠split₁ｰspec γ descrs0 X elements prevs nexts classes seens descrs class split_list :
    split۰inv descrs0 X descrs (class :: split_list) →
    {{{
      model' γ elements prevs nexts classes seens descrs
    }}}
      partition٠split₁ #class
    {{{
      classes' seens' descrs'
    , RET ();
      model' γ elements prevs nexts classes' seens' descrs' ∗
      ⌜split۰inv descrs0 X descrs' split_list⌝
    }}}.
  Proof.
    iIntros "%Hinv %Φ (:model') HΦ".

    destruct (split۰invｰpending Hinv (class := class)) as (descr0 & descr & _ & Hlookup & Hseen & _ & Htake); first set_solver.
    pose proof (model۰validｰNoDup Hvalid Hlookup) as Hnodup.
    pose proof (model۰validｰseen Hvalid Hlookup) as Hseen_le.
    pose proof (λ i elt elt', @model۰validｰchain _ _ _ _ _ _ Hvalid _ _ i elt elt' Hlookup) as Hchain.
    assert (
      ∀ elt,
      elt ∈ descr.(descriptor۰elts) →
      elt ∈ elements
    ) as Hsubset.
    { intros elt Helt. apply (model۰validｰelement Hvalid Hlookup Helt). }
    destruct descr as [elts n]. simpl in *.
    iDestruct (big_sepM_delete with "Hdescrs") as "((:descriptor۰model) & Hdescrs)"; first done.
    cbn [descriptor۰elts descriptor۰seen].

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
      iApply ("HΦ" $! classes (λ elt, if decide (elt ∈ elts) then false else seens elt) (<[class := Descriptor elts 0]> descrs)).
      iSplitL.
      + iFrame. iSplitR.
        { iPureIntro. apply (model۰validｰreset Hvalid Hlookup). }
        iSplitL "Hnodes".
        { iApply (nodesｰproper with "Hnodes"). intros elt Helt.
          destruct (HΨ elt Helt) as (-> & ->). done.
        }
        iApply big_sepM_insert_delete. iFrame.
        rewrite /= -head_lookup Hfirst /=.
        rewrite decide_False; first lia.
        iFrame. done.
      + iPureIntro. apply (split۰invｰreset Hvalid Hinv Hlookup); done.

    - assert (n < length elts) as Hn' by lia.
      destruct (lookup_lt_is_Some_2 elts n) as (split & Hlookup_split); first done.
      destruct (lookup_lt_is_Some_2 elts (pred n)) as (prev & Hlookup_prev); first lia.
      assert (head (take n elts) = Some first) as Hfirst_take.
      { rewrite headｰtake //; lia. }
      assert (list.last (take n elts) = Some prev) as Hlast_take.
      { rewrite (_ : n = ˖(pred n)); first lia. apply lastｰtake. done. }
      assert (first ≠ split) as Hne_split.
      { intros ->. rewrite head_lookup in Hfirst.
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
      assert (class ≠ class') as Hne_classes.
      { intros ->. done. }
      assert (descrs !! class' = None) as Hlookup'.
      { rewrite lookup_delete_ne // in Hfresh. }
      wp۰apply+ (partition٠dllist٠iterｰspec (λ elts1 classes' seens',
        ⌜ ∀ elt,
          elt ∈ elements →
            classes' elt = (if decide (elt ∈ elts1) then class' else classes elt) ∧
            seens' elt = if decide (elt ∈ elts1) then false else seens elt
        ⌝
      )%I _ _ _ _ _ _ (take n elts) with "[$Hnodes]") as (classes' seens') "(Hnodes & %HΨ)".
      { apply NoDupｰtake. done. }
      { done. }
      { done. }
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
        (<[class := Descriptor (drop n elts) 0]> (<[class' := Descriptor (take n elts) 0]> descrs))
      ).
      iSplitL.
      + iFrame. iSplitR.
        { iPureIntro. apply (model۰validｰsplit Hvalid class' Hlookup Hlookup'). simpl. lia. }
        iSplitL "Hnodes".
        { iApply (nodesｰproper with "Hnodes"). intros elt Helt.
          destruct (HΨ elt Helt) as (-> & ->). done.
        }
        iApply big_sepM_insert_delete.
        rewrite delete_insert_ne //.
        assert (list.last (drop n elts) = Some last) as Hlast_drop.
        { rewrite lastｰdrop //. }
        iSplitL "Hclass_first Hclass_last Hclass_len Hclass_split Hclass_split_len".
        * iExists split, last.
          rewrite /= head_lookup length_drop decide_False; first lia.
          rewrite !lookup_drop Nat.add_0_r Hlookup_split /=.
          rewrite Nat2Z.inj_sub; first lia.
          iFrame. done.
        * iApply big_sepM_insert.
          { rewrite lookup_delete_ne //. }
          iFrame "Hdescrs".
          iExists first, prev.
          rewrite /= -head_lookup Hfirst_take length_take_le; first lia.
          rewrite decide_False; first lia.
          iFrame. done.
      + iPureIntro. apply (split۰invｰsplit Hvalid class' Hinv Hlookup); simpl; done.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [split]. *)

  #[local] Lemma partition٠splitｰspec γ descrs0 X elements prevs nexts classes seens descrs split_list :
    split۰inv descrs0 X descrs split_list →
    {{{
      model' γ elements prevs nexts classes seens descrs
    }}}
      partition٠split (list۰to_val (#*ˡ split_list))
    {{{
      classes' seens' descrs'
    , RET ();
      model' γ elements prevs nexts classes' seens' descrs' ∗
      ⌜split۰inv descrs0 X descrs' []⌝
    }}}.
  Proof.
    iIntros "%Hinv %Φ Hmodel HΦ".

    wp۰rec.
    wp۰apply (list٠iterｰspec (λ i _,
      ∃ classes seens descrs,
      model' γ elements prevs nexts classes seens descrs ∗
      ⌜split۰inv descrs0 X descrs (drop i split_list)⌝
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

    wp۰rec.
    wp۰apply+ (partition٠recordｰspec with "[Helements_auth Hnodes Hdescrs]") as (prevs' nexts' seens' descrs' split_list) "((:model' =') & %Hinv)".
    { done. }
    { apply record۰invｰinit. done. }
    { iFrame "∗ # %". }
    wp۰apply (partition٠splitｰspec with "[Helements_auth' Hnodes' Hdescrs']") as (classes'' seens'' descrs'') "((:model' ='') & %Hinv')".
    { apply (split۰invｰinit Hvalid' Hinv). }
    { iFrame "∗ %". }
    destruct (descriptors۰partｰexists descrs'') as (part' & Hpart').
    { intros class1 descr1 class2 descr2 repr Hlookup1 Hlookup2 Hhead1 Hhead2.
      refine (model۰validｰdisjoint Hvalid'' repr Hlookup1 Hlookup2 _ _); apply head_Some_elem_of; done.
    }
    opose proof* (split۰invｰfinal Hvalid'' _ Hpart Hpart' Hinv') as (Hunseen'' & Himg & Huntouched).
    { intros class0 descr0. apply (model۰validｰnonempty Hvalid). }
    iApply ("HΦ" $! part').
    iSplitL; last done.
    iExists _, _, _, _, _, descrs''. iFrame "∗ %".
  Qed.
End partition۰G.

Require zoo_data.partition__opaque.

Please opacify.
