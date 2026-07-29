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
#[global] Instance subGｰsuf۰Σ Σ `{zoo۰G : !ZooG Σ} :
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

  #[local] Lemma unifyｰlookup₁ reprs repr1 repr2 elt :
    reprs !! elt = Some repr1 →
    unify repr1 repr2 reprs !! elt = Some repr2.
  Proof.
    intros Hreprs_lookup_elt.
    rewrite lookup_fmap Hreprs_lookup_elt /= unify_at₁ //.
  Qed.
  #[local] Lemma unifyｰlookup₂ {reprs repr1 repr2 elt} repr :
    reprs !! elt = Some repr →
    repr ≠ repr1 →
    unify repr1 repr2 reprs !! elt = Some repr.
  Proof.
    intros Hreprs_lookup_elt ?.
    rewrite lookup_fmap Hreprs_lookup_elt /= unify_at₂ //.
  Qed.
  #[local] Lemma unifyｰlookup₂' reprs repr1 repr2 :
    reprs !! repr2 = Some repr2 →
    repr1 ≠ repr2 →
    unify repr1 repr2 reprs !! repr2 = Some repr2.
  Proof.
    intros.
    apply unifyｰlookup₂; done.
  Qed.
  #[local] Lemma domｰunify repr1 repr2 reprs :
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

  #[local] Lemma consistentｰempty :
    consistent ∅ ∅.
  Proof.
    apply map_Forall2_empty.
  Qed.
  #[local] Lemma consistentｰlookupｰNone {reprs descrs} elt :
    consistent reprs descrs →
    descrs !! elt = None →
    reprs !! elt = None.
  Proof.
    apply: map_Forall2ｰlookupｰNoneｰr.
  Qed.
  #[local] Lemma consistentｰlookupｰSome {reprs descrs} elt repr :
    consistent reprs descrs →
    reprs !! elt = Some repr →
      ∃ descr,
      descrs !! elt = Some descr ∧
      consistent_at reprs elt repr descr.
  Proof.
    apply: map_Forall2ｰlookupｰSomeｰl.
  Qed.
  #[local] Lemma consistentｰinsert {reprs descrs} elt :
    descrs !! elt = None →
    consistent reprs descrs →
    consistent
      (<[elt := elt]> reprs)
      (<[elt := ‘Root( 0 )%V]> descrs).
  Proof.
    rewrite /consistent /consistent_at.
    intros Hdescrs_lookup Hconsistent.
    eapply consistentｰlookupｰNone in Hconsistent as Hresprs_lookup; last done.
    apply map_Forall2_insert_2; first naive_solver.
    eapply map_Forall2_impl; first done.
    intros elt' repr' descr' [| (parent & ? & -> & Hreprs_lookup_parent & Hreprs_lookup_repr)]; first auto.
    right. exists parent.
    rewrite !lookup_insert_ne //; congruence.
  Qed.
  #[local] Lemma consistentｰlinkｰrepr {reprs descrs} elt repr :
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
    eapply map_Forall2ｰinsertｰr; [done.. |].
    right. eauto.
  Qed.
  #[local] Lemma consistentｰlinkｰunion {reprs descrs} repr1 repr2 :
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
    apply map_Forall2ｰalt in Hconsistent as (Hdom & Hconsistent).
    rewrite -map_Forall2ｰfmapｰl map_Forall2ｰalt.
    split.
    - apply elem_of_dom_2 in Hreprs_lookup_repr1.
      set_solver.
    - intros elt repr descr Hreprs_lookup_elt [(<- & <-) | (? & Hdescrs_lookup_elt)]%lookup_insert_Some. simplify.
      + right. exists repr2.
        rewrite unify_at₁ unifyｰlookup₂' //.
      + destruct_decide (repr = repr1) as -> | ?.
        * rewrite unify_at₁.
          ospecialize* (Hconsistent elt); [done.. |].
          destruct Hconsistent as [| (parent & ? & -> & Hreprs_lookup_parent & Hreprs_lookup_repr1_)]; first naive_solver. simplify.
          right. exists parent.
          rewrite unifyｰlookup₁ // unifyｰlookup₂' //.
          naive_solver.
        * rewrite unify_at₂ //.
          ospecialize* (Hconsistent elt); [done.. |].
          destruct Hconsistent as [(rank & <- & ->)| (parent & ? & -> & Hreprs_lookup_parent & Hreprs_lookup_repr1_)].
          -- left. naive_solver.
          -- right. exists parent.
             rewrite !(unifyｰlookup₂ repr) //.
  Qed.
  #[local] Lemma consistentｰupdateｰrank {reprs descrs} repr rank :
    reprs !! repr = Some repr →
    consistent reprs descrs →
    consistent
      reprs
      (<[repr := ‘Root( #rank )%V]> descrs).
  Proof.
    rewrite /consistent.
    intros Hreprs_lookup_repr Hconsistent.
    eapply map_Forall2ｰinsertｰr; [done.. |].
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

  #[global] Instance suf۰modelｰtimeless t reprs :
    Timeless (suf۰model t reprs).
  Proof.
    apply _.
  Qed.

  #[global] Instance suf۰snapshotｰpersistent s t reprs :
    Persistent (suf۰snapshot s t reprs).
  Proof.
    apply _.
  Qed.

  Lemma suf۰modelｰvalid {t reprs} elt repr :
    reprs !! elt = Some repr →
    suf۰model t reprs ⊢
    ⌜reprs !! repr = Some repr⌝.
  Proof.
    iIntros "%Hreprs_lookup (:model)". iPureIntro.
    eapply consistentｰlookupｰSome in Hconsistent as (descr & Hdescrs_lookup & []); last done.
    all: naive_solver.
  Qed.
  Lemma suf۰modelｰexclusive t reprs1 reprs2 :
    suf۰model t reprs1 -∗
    suf۰model t reprs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)".
    iApply (sstore_2۰modelｰexclusive with "Hmodel1 Hmodel2").
  Qed.

  Lemma suf٠createｰspec :
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

    wp۰apply (sstore_2٠createｰspec with "[//]").
    iSteps. iPureIntro. apply consistentｰempty.
  Qed.

  Lemma suf٠makeｰspec t reprs :
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
    wp۰apply+ (sstore_2٠refｰspec with "Hmodel") as (elt) "(%Hdescrs_lookup & Hmodel)".

    eapply consistentｰinsert in Hconsistent; last done.
    iSteps.
  Qed.

  Lemma suf٠reprｰspec {t reprs elt} repr :
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
    pose proof Hconsistent as (descr & Hdescrs_lookup & Hconsistent_at)%(consistentｰlookupｰSome elt repr); last done.

    wp۰rec.
    wp۰apply+ (sstore_2٠getｰspec with "Hmodel") as "Hmodel"; first done.

    destruct Hconsistent_at as [(rank & -> & ->) | (parent & ? & -> & Hreprs_lookup_parent & Hreprs_lookup_repr)]; wp۰pures; first iSteps.

    wp۰apply ("HLöb" $! parent with "[//] [$Hmodel //]") as "(:model =')".
    pose proof Hconsistent' as (descr' & Hdescrs'_lookup & _)%(consistentｰlookupｰSome elt repr); last done.

    wp۰apply+ (sstore_2٠setｰspec with "Hmodel'") as "Hmodel".
    { rewrite elem_of_dom //. }
    wp۰pures.

    apply (consistentｰlinkｰrepr elt repr) in Hconsistent'; [| done..].
    iSteps.
  Qed.

  Lemma suf٠equivｰspec {t reprs elt1} repr1 {elt2} repr2 :
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
    wp۰apply+ (suf٠reprｰspec with "Hmodel") as "Hmodel"; first done.
    wp۰apply+ (suf٠reprｰspec with "Hmodel") as "Hmodel"; first done.
    iSteps.
  Qed.

  #[local] Lemma suf٠rankｰspec t reprs elt :
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
    pose proof Hconsistent as (descr & Hdescrs_lookup & Hconsistent_at)%(consistentｰlookupｰSome elt elt); last done.

    wp۰rec.
    wp۰apply+ (sstore_2٠getｰspec with "Hmodel") as "Hmodel"; first done.

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
  #[local] Lemma suf۰union_conditionｰrefl reprs repr :
    suf۰union_condition reprs repr repr reprs.
  Proof.
    split_and!; [done.. |].
    naive_solver.
  Qed.
  #[local] Lemma suf۰union_conditionｰsym reprs repr1 repr2 reprs' :
    suf۰union_condition reprs repr1 repr2 reprs' →
    suf۰union_condition reprs repr2 repr1 reprs'.
  Proof.
    rewrite /suf۰union_condition.
    intros (Hdom & Hunchanged & (repr12 & Hchanged)).
    split_and!; auto.
    exists repr12. naive_solver.
  Qed.
  #[local] Lemma unifyｰunion_condition₁ reprs repr1 repr2 :
    repr1 ≠ repr2 →
    suf۰union_condition reprs repr1 repr2 (unify repr1 repr2 reprs).
  Proof.
    intros.
    split_and!.
    - rewrite domｰunify //.
    - intros.
      apply unifyｰlookup₂; done.
    - exists repr2. split; first auto.
      intros elt repr Hreprs_lookup_elt [-> | ->].
      + rewrite unifyｰlookup₁ //.
      + rewrite (unifyｰlookup₂ repr2) //.
  Qed.
  #[local] Lemma unifyｰunion_condition₂ reprs repr1 repr2 :
    repr1 ≠ repr2 →
    suf۰union_condition reprs repr2 repr1 (unify repr1 repr2 reprs).
  Proof.
    intros.
    apply suf۰union_conditionｰsym, unifyｰunion_condition₁; done.
  Qed.
  #[local] Opaque suf۰union_condition.
  Lemma suf٠unionｰspec {t reprs elt1} repr1 {elt2} repr2 :
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
    iDestruct (suf۰modelｰvalid elt1 with "Hmodel") as %Hreprs_lookup_repr1; first done.
    iDestruct (suf۰modelｰvalid elt2 with "Hmodel") as %Hreprs_lookup_repr2; first done.

    wp۰rec.
    wp۰apply+ (suf٠reprｰspec with "Hmodel") as "Hmodel"; first done.
    wp۰apply+ (suf٠rankｰspec with "Hmodel") as (rank1) "Hmodel"; first done.
    wp۰apply+ (suf٠reprｰspec with "Hmodel") as "Hmodel"; first done.
    wp۰apply+ (suf٠rankｰspec with "Hmodel") as (rank2) "(:model)"; first done.

    pose proof Hconsistent as (descr1 & Hdescrs_lookup_1 & Hconsistent_at_1)%(consistentｰlookupｰSome repr1 repr1); last done.
    pose proof Hconsistent as (descr2 & Hdescrs_lookup_2 & Hconsistent_at_2)%(consistentｰlookupｰSome repr2 repr2); last done.

    wp۰pures.
    case_bool_decide; first subst repr2.

    - iSteps. iPureIntro. apply suf۰union_conditionｰrefl.

    - wp۰pures.
      case_bool_decide; wp۰pures.

      + wp۰apply (sstore_2٠setｰspec with "Hmodel") as "Hmodel".
        { rewrite elem_of_dom //. }
        apply (consistentｰlinkｰunion repr1 repr2) in Hconsistent; [| done..].

        iApply ("HΦ" $! (unify repr1 repr2 reprs)).
        iSteps. iPureIntro. apply unifyｰunion_condition₁. done.

      + wp۰apply (sstore_2٠setｰspec with "Hmodel") as "Hmodel".
        { rewrite elem_of_dom //. }
        apply (consistentｰlinkｰunion repr2 repr1) in Hconsistent; [| done..].

        wp۰pures.
        case_bool_decide; wp۰pures.

        * wp۰apply (sstore_2٠setｰspec with "Hmodel") as "Hmodel".
          { apply dom_insert, elem_of_union_r, elem_of_dom. done. }
          eapply (consistentｰupdateｰrank repr1) in Hconsistent; last first.
          { rewrite unifyｰlookup₂' //. }

          iApply ("HΦ" $! (unify repr2 repr1 reprs)).
          iSteps. iPureIntro. apply unifyｰunion_condition₂. done.

        * iApply ("HΦ" $! (unify repr2 repr1 reprs)).
          iSteps. iPureIntro. apply unifyｰunion_condition₂. done.
  Qed.

  Lemma suf٠captureｰspec t reprs :
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

    wp۰apply (sstore_2٠captureｰspec with "Hmodel").
    iSteps.
  Qed.

  Lemma suf٠restoreｰspec t reprs s reprs' :
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

    wp۰apply (sstore_2٠restoreｰspec with "[$Hmodel $Hsnapshot']").
    iSteps.
  Qed.
End suf۰G.

Require zoo_persistent.suf__opaque.

#[global] Opaque suf۰model.
#[global] Opaque suf۰snapshot.
