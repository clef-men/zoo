Require Import zoo.prelude.
Require Import zoo.common.fin_maps.
Require Import zoo.base.
Require Export zoo_persistent.suf__code.
Require Import zoo_persistent.suf__types.
Require Import zoo_persistent.sstore_2.
Require Import zoo.options.

Implicit Type rank : Z.
Implicit Type elt repr parent : location.
Implicit Type t s descr : val.
Implicit Type reprs : gmap location location.
Implicit Type descrs : gmap location val.

Class SufG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] suf۰G۰sstore۰G :: Sstore2G Σ
  }.

Definition suf۰Σ :=
  #[sstore_2۰Σ
  ].
#[global] Instance subG𑁒suf۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG suf۰Σ Σ →
  SufG Σ.
Proof.
  solve_inG.
Qed.

Section unify.
  #[local] Definition unify_at repr1 repr2 repr :=
    if decide (repr = repr1) then
      repr2
    else
      repr.

  #[local] Lemma unify_at₁ repr1 repr2 :
    unify_at repr1 repr2 repr1 = repr2.
  Proof.
    rewrite /unify_at decide_True //.
  Qed.
  #[local] Lemma unify_at₂ repr1 repr2 repr :
    repr ≠ repr1 →
    unify_at repr1 repr2 repr = repr.
  Proof.
    intros.
    rewrite /unify_at decide_False //.
  Qed.

  #[local] Definition unify repr1 repr2 reprs :=
    unify_at repr1 repr2 <$> reprs.

  #[local] Lemma unify𑁒lookup₁ reprs repr1 repr2 elt :
    reprs !! elt = Some repr1 →
    unify repr1 repr2 reprs !! elt = Some repr2.
  Proof.
    intros Hreprs_lookup_elt.
    rewrite lookup_fmap Hreprs_lookup_elt /= unify_at₁ //.
  Qed.
  #[local] Lemma unify𑁒lookup₂ {reprs repr1 repr2 elt} repr :
    reprs !! elt = Some repr →
    repr ≠ repr1 →
    unify repr1 repr2 reprs !! elt = Some repr.
  Proof.
    intros Hreprs_lookup_elt ?.
    rewrite lookup_fmap Hreprs_lookup_elt /= unify_at₂ //.
  Qed.
  #[local] Lemma unify𑁒lookup₂' reprs repr1 repr2 :
    reprs !! repr2 = Some repr2 →
    repr1 ≠ repr2 →
    unify repr1 repr2 reprs !! repr2 = Some repr2.
  Proof.
    intros.
    apply unify𑁒lookup₂; done.
  Qed.
  #[local] Lemma dom𑁒unify repr1 repr2 reprs :
    dom (unify repr1 repr2 reprs) = dom reprs.
  Proof.
    apply dom_fmap_L.
  Qed.
End unify.

Opaque unify_at.
Opaque unify.

Section consistent.
  #[local] Definition consistent_at reprs elt repr descr :=
    ( ∃ rank,
      repr = elt ∧
      descr = ‘Root( #rank )%V
    ) ∨ (
      ∃ parent,
      elt ≠ repr ∧
      descr = ‘Link( #parent )%V ∧
      reprs !! parent = Some repr ∧
      reprs !! repr = Some repr
    ).
  #[local] Definition consistent reprs descrs :=
    map_Forall2 (consistent_at reprs) reprs descrs.

  #[local] Lemma consistent𑁒empty :
    consistent ∅ ∅.
  Proof.
    apply map_Forall2_empty.
  Qed.
  #[local] Lemma consistent𑁒lookup𑁒None {reprs descrs} elt :
    consistent reprs descrs →
    descrs !! elt = None →
    reprs !! elt = None.
  Proof.
    apply: map_Forall2𑁒lookup𑁒None𑁒r.
  Qed.
  #[local] Lemma consistent𑁒lookup𑁒Some {reprs descrs} elt repr :
    consistent reprs descrs →
    reprs !! elt = Some repr →
      ∃ descr,
      descrs !! elt = Some descr ∧
      consistent_at reprs elt repr descr.
  Proof.
    apply: map_Forall2𑁒lookup𑁒Some𑁒l.
  Qed.
  #[local] Lemma consistent𑁒insert {reprs descrs} elt :
    descrs !! elt = None →
    consistent reprs descrs →
    consistent
      (<[elt := elt]> reprs)
      (<[elt := ‘Root( 0 )%V]> descrs).
  Proof.
    rewrite /consistent /consistent_at.
    intros Hdescrs_lookup Hconsistent.
    eapply consistent𑁒lookup𑁒None in Hconsistent as Hresprs_lookup; last done.
    apply map_Forall2_insert_2; first naive_solver.
    eapply map_Forall2_impl; first done.
    intros elt' repr' descr' [| (parent & ? & -> & Hreprs_lookup_parent & Hreprs_lookup_repr)]; first auto.
    right. exists parent.
    rewrite !lookup_insert_ne //; congruence.
  Qed.
  #[local] Lemma consistent𑁒link𑁒repr {reprs descrs} elt repr :
    elt ≠ repr →
    reprs !! elt = Some repr →
    reprs !! repr = Some repr →
    consistent reprs descrs →
    consistent
      reprs
      (<[elt := ‘Link( #repr )%V]> descrs).
  Proof.
    rewrite /consistent.
    intros ? Hreprs_lookup_elt Hreprs_lookup_repr Hconsistent.
    eapply map_Forall2𑁒insert𑁒r; [done.. |].
    right. eauto.
  Qed.
  #[local] Lemma consistent𑁒link𑁒union {reprs descrs} repr1 repr2 :
    repr1 ≠ repr2 →
    reprs !! repr1 = Some repr1 →
    reprs !! repr2 = Some repr2 →
    consistent reprs descrs →
    consistent
      (unify repr1 repr2 reprs)
      (<[repr1 := ‘Link( #repr2 )%V]> descrs).
  Proof.
    rewrite /consistent.
    intros ? Hreprs_lookup_repr1 Hreprs_lookup_repr2 Hconsistent.
    apply map_Forall2𑁒alt in Hconsistent as (Hdom & Hconsistent).
    rewrite -map_Forall2𑁒fmap𑁒l map_Forall2𑁒alt.
    split.
    - apply elem_of_dom_2 in Hreprs_lookup_repr1.
      set_solver.
    - intros elt repr descr Hreprs_lookup_elt [(<- & <-) | (? & Hdescrs_lookup_elt)]%lookup_insert_Some. simplify.
      + right. exists repr2.
        rewrite unify_at₁ unify𑁒lookup₂' //.
      + destruct_decide (repr = repr1) as -> | ?.
        * rewrite unify_at₁.
          ospecialize* (Hconsistent elt); [done.. |].
          destruct Hconsistent as [| (parent & ? & -> & Hreprs_lookup_parent & Hreprs_lookup_repr1_)]; first naive_solver. simplify.
          right. exists parent.
          rewrite unify𑁒lookup₁ // unify𑁒lookup₂' //.
          naive_solver.
        * rewrite unify_at₂ //.
          ospecialize* (Hconsistent elt); [done.. |].
          destruct Hconsistent as [(rank & <- & ->)| (parent & ? & -> & Hreprs_lookup_parent & Hreprs_lookup_repr1_)].
          -- left. naive_solver.
          -- right. exists parent.
             rewrite !(unify𑁒lookup₂ repr) //.
  Qed.
  #[local] Lemma consistent𑁒update𑁒rank {reprs descrs} repr rank :
    reprs !! repr = Some repr →
    consistent reprs descrs →
    consistent
      reprs
      (<[repr := ‘Root( #rank )%V]> descrs).
  Proof.
    rewrite /consistent.
    intros Hreprs_lookup_repr Hconsistent.
    eapply map_Forall2𑁒insert𑁒r; [done.. |].
    left. eauto.
  Qed.
End consistent.

Opaque consistent_at.
Opaque consistent.

Section suf۰G.
  Context `{suf۰G : SufG Σ}.

  Definition suf۰model t reprs : iProp Σ :=
    ∃ descrs,
    sstore_2۰model t descrs ∗
    ⌜consistent reprs descrs⌝.
  #[local] Instance : CustomIpat "model" :=
    " ( %descrs{}
      & Hmodel{}
      & %Hconsistent{}
      )
    ".

  Definition suf۰snapshot s t reprs : iProp Σ :=
    ∃ descrs,
    sstore_2۰snapshot s t descrs ∗
    ⌜consistent reprs descrs⌝.
  #[local] Instance : CustomIpat "snapshot" :=
    " ( %descrs{}
      & Hsnapshot{}
      & %Hconsistent{}
      )
    ".

  #[global] Instance suf۰model𑁒timeless t reprs :
    Timeless (suf۰model t reprs).
  Proof.
    apply _.
  Qed.

  #[global] Instance suf۰snapshot𑁒persistent s t reprs :
    Persistent (suf۰snapshot s t reprs).
  Proof.
    apply _.
  Qed.

  Lemma suf۰model𑁒valid {t reprs} elt repr :
    reprs !! elt = Some repr →
    suf۰model t reprs ⊢
    ⌜reprs !! repr = Some repr⌝.
  Proof.
    iIntros "%Hreprs_lookup (:model)". iPureIntro.
    eapply consistent𑁒lookup𑁒Some in Hconsistent as (descr & Hdescrs_lookup & []); last done.
    all: naive_solver.
  Qed.
  Lemma suf۰model𑁒exclusive t reprs1 reprs2 :
    suf۰model t reprs1 -∗
    suf۰model t reprs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)".
    iApply (sstore_2۰model𑁒exclusive with "Hmodel1 Hmodel2").
  Qed.

  Lemma suf٠create𑁒spec :
    {{{
      True
    }}}
      suf٠create ()
    {{{
      t
    , RET t;
      suf۰model t ∅
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰apply (sstore_2٠create𑁒spec with "[//]").
    iSteps. iPureIntro. apply consistent𑁒empty.
  Qed.

  Lemma suf٠make𑁒spec t reprs :
    {{{
      suf۰model t reprs
    }}}
      suf٠make t
    {{{
      elt
    , RET #elt;
      suf۰model t (<[elt := elt]> reprs)
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".

    wp۰rec.
    wp۰apply+ (sstore_2٠ref𑁒spec with "Hmodel") as (elt) "(%Hdescrs_lookup & Hmodel)".

    eapply consistent𑁒insert in Hconsistent; last done.
    iSteps.
  Qed.

  Lemma suf٠repr𑁒spec {t reprs elt} repr :
    reprs !! elt = Some repr →
    {{{
      suf۰model t reprs
    }}}
      suf٠repr t #elt
    {{{
      RET #repr;
      suf۰model t reprs
    }}}.
  Proof.
    iLöb as "HLöb" forall (elt repr).

    iIntros "%Hreprs_lookup_elt %Φ (:model) HΦ".
    pose proof Hconsistent as (descr & Hdescrs_lookup & Hconsistent_at)%(consistent𑁒lookup𑁒Some elt repr); last done.

    wp۰rec.
    wp۰apply+ (sstore_2٠get𑁒spec with "Hmodel") as "Hmodel"; first done.

    destruct Hconsistent_at as [(rank & -> & ->) | (parent & ? & -> & Hreprs_lookup_parent & Hreprs_lookup_repr)]; wp۰pures; first iSteps.

    wp۰apply ("HLöb" $! parent with "[//] [$Hmodel //]") as "(:model =')".
    pose proof Hconsistent' as (descr' & Hdescrs'_lookup & _)%(consistent𑁒lookup𑁒Some elt repr); last done.

    wp۰apply+ (sstore_2٠set𑁒spec with "Hmodel'") as "Hmodel".
    { rewrite elem_of_dom //. }
    wp۰pures.

    apply (consistent𑁒link𑁒repr elt repr) in Hconsistent'; [| done..].
    iSteps.
  Qed.

  Lemma suf٠equiv𑁒spec {t reprs elt1} repr1 {elt2} repr2 :
    reprs !! elt1 = Some repr1 →
    reprs !! elt2 = Some repr2 →
    {{{
      suf۰model t reprs
    }}}
      suf٠equiv t #elt1 #elt2
    {{{
      RET #(bool_decide (repr1 = repr2));
      suf۰model t reprs
    }}}.
  Proof.
    iIntros "%Hreprs_lookup_elt1 %Hreprs_lookup_elt2 %Φ Hmodel HΦ".

    wp۰rec.
    wp۰apply+ (suf٠repr𑁒spec with "Hmodel") as "Hmodel"; first done.
    wp۰apply+ (suf٠repr𑁒spec with "Hmodel") as "Hmodel"; first done.
    iSteps.
  Qed.

  #[local] Lemma suf٠rank𑁒spec t reprs elt :
    reprs !! elt = Some elt →
    {{{
      suf۰model t reprs
    }}}
      suf٠rank t #elt
    {{{
      rank
    , RET #rank;
      suf۰model t reprs
    }}}.
  Proof.
    iIntros "%Hreprs_lookup_elt %Φ (:model) HΦ".
    pose proof Hconsistent as (descr & Hdescrs_lookup & Hconsistent_at)%(consistent𑁒lookup𑁒Some elt elt); last done.

    wp۰rec.
    wp۰apply+ (sstore_2٠get𑁒spec with "Hmodel") as "Hmodel"; first done.

    destruct Hconsistent_at as [(rank & _ & ->) | (parent & ? & -> & Hreprs_lookup_parent & Hreprs_lookup_repr)]; last done.
    iSteps.
  Qed.
  Definition suf۰union_condition reprs repr1 repr2 reprs' :=
    dom reprs = dom reprs' ∧
    ( ∀ elt repr,
      reprs !! elt = Some repr →
      repr ≠ repr1 →
      repr ≠ repr2 →
      reprs' !! elt = Some repr
    ) ∧
    ( ∃ repr12,
      (repr12 = repr1 ∨ repr12 = repr2) ∧
        ∀ elt repr,
        reprs !! elt = Some repr →
        repr = repr1 ∨ repr = repr2 →
        reprs' !! elt = Some repr12
    ).
  #[local] Lemma suf۰union_condition𑁒refl reprs repr :
    suf۰union_condition reprs repr repr reprs.
  Proof.
    split_and!; [done.. |].
    naive_solver.
  Qed.
  #[local] Lemma suf۰union_condition𑁒sym reprs repr1 repr2 reprs' :
    suf۰union_condition reprs repr1 repr2 reprs' →
    suf۰union_condition reprs repr2 repr1 reprs'.
  Proof.
    rewrite /suf۰union_condition.
    intros (Hdom & Hunchanged & (repr12 & Hchanged)).
    split_and!; auto.
    exists repr12. naive_solver.
  Qed.
  #[local] Lemma unify𑁒union_condition₁ reprs repr1 repr2 :
    repr1 ≠ repr2 →
    suf۰union_condition reprs repr1 repr2 (unify repr1 repr2 reprs).
  Proof.
    intros.
    split_and!.
    - rewrite dom𑁒unify //.
    - intros.
      apply unify𑁒lookup₂; done.
    - exists repr2. split; first auto.
      intros elt repr Hreprs_lookup_elt [-> | ->].
      + rewrite unify𑁒lookup₁ //.
      + rewrite (unify𑁒lookup₂ repr2) //.
  Qed.
  #[local] Lemma unify𑁒union_condition₂ reprs repr1 repr2 :
    repr1 ≠ repr2 →
    suf۰union_condition reprs repr2 repr1 (unify repr1 repr2 reprs).
  Proof.
    intros.
    apply suf۰union_condition𑁒sym, unify𑁒union_condition₁; done.
  Qed.
  #[local] Opaque suf۰union_condition.
  Lemma suf٠union𑁒spec {t reprs elt1} repr1 {elt2} repr2 :
    reprs !! elt1 = Some repr1 →
    reprs !! elt2 = Some repr2 →
    {{{
      suf۰model t reprs
    }}}
      suf٠union t #elt1 #elt2
    {{{
      reprs'
    , RET ();
      suf۰model t reprs' ∗
      ⌜suf۰union_condition reprs repr1 repr2 reprs'⌝
    }}}.
  Proof.
    iIntros "%Hreprs_lookup_elt1 %Hreprs_lookup_elt2 %Φ Hmodel HΦ".
    iDestruct (suf۰model𑁒valid elt1 with "Hmodel") as %Hreprs_lookup_repr1; first done.
    iDestruct (suf۰model𑁒valid elt2 with "Hmodel") as %Hreprs_lookup_repr2; first done.

    wp۰rec.
    wp۰apply+ (suf٠repr𑁒spec with "Hmodel") as "Hmodel"; first done.
    wp۰apply+ (suf٠rank𑁒spec with "Hmodel") as (rank1) "Hmodel"; first done.
    wp۰apply+ (suf٠repr𑁒spec with "Hmodel") as "Hmodel"; first done.
    wp۰apply+ (suf٠rank𑁒spec with "Hmodel") as (rank2) "(:model)"; first done.

    pose proof Hconsistent as (descr1 & Hdescrs_lookup_1 & Hconsistent_at_1)%(consistent𑁒lookup𑁒Some repr1 repr1); last done.
    pose proof Hconsistent as (descr2 & Hdescrs_lookup_2 & Hconsistent_at_2)%(consistent𑁒lookup𑁒Some repr2 repr2); last done.

    wp۰pures.
    case_bool_decide; first subst repr2.

    - iSteps. iPureIntro. apply suf۰union_condition𑁒refl.

    - wp۰pures.
      case_bool_decide; wp۰pures.

      + wp۰apply (sstore_2٠set𑁒spec with "Hmodel") as "Hmodel".
        { rewrite elem_of_dom //. }
        apply (consistent𑁒link𑁒union repr1 repr2) in Hconsistent; [| done..].

        iApply ("HΦ" $! (unify repr1 repr2 reprs)).
        iSteps. iPureIntro. apply unify𑁒union_condition₁. done.

      + wp۰apply (sstore_2٠set𑁒spec with "Hmodel") as "Hmodel".
        { rewrite elem_of_dom //. }
        apply (consistent𑁒link𑁒union repr2 repr1) in Hconsistent; [| done..].

        wp۰pures.
        case_bool_decide; wp۰pures.

        * wp۰apply (sstore_2٠set𑁒spec with "Hmodel") as "Hmodel".
          { apply dom_insert, elem_of_union_r, elem_of_dom. done. }
          eapply (consistent𑁒update𑁒rank repr1) in Hconsistent; last first.
          { rewrite unify𑁒lookup₂' //. }

          iApply ("HΦ" $! (unify repr2 repr1 reprs)).
          iSteps. iPureIntro. apply unify𑁒union_condition₂. done.

        * iApply ("HΦ" $! (unify repr2 repr1 reprs)).
          iSteps. iPureIntro. apply unify𑁒union_condition₂. done.
  Qed.

  Lemma suf٠capture𑁒spec t reprs :
    {{{
      suf۰model t reprs
    }}}
      suf٠capture t
    {{{
      s
    , RET s;
      suf۰model t reprs ∗
      suf۰snapshot s t reprs
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".

    wp۰apply (sstore_2٠capture𑁒spec with "Hmodel").
    iSteps.
  Qed.

  Lemma suf٠restore𑁒spec t reprs s reprs' :
    {{{
      suf۰model t reprs ∗
      suf۰snapshot s t reprs'
    }}}
      suf٠restore t s
    {{{
      RET ();
      suf۰model t reprs'
    }}}.
  Proof.
    iIntros "%Φ ((:model) & (:snapshot =')) HΦ".

    wp۰apply (sstore_2٠restore𑁒spec with "[$Hmodel $Hsnapshot']").
    iSteps.
  Qed.
End suf۰G.

Require zoo_persistent.suf__opaque.

#[global] Opaque suf۰model.
#[global] Opaque suf۰snapshot.
