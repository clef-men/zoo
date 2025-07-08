From zoo Require Import
  prelude.
From zoo.common Require Import
  fin_maps.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_persistent Require Export
  base
  puf__code.
From zoo_persistent Require Import
  puf__types
  pstore_2.
From zoo Require Import
  options.

Implicit Types rank : Z.
Implicit Types elt repr parent : location.
Implicit Types t s descr : val.
Implicit Types reprs : gmap location location.
Implicit Types descrs : gmap location val.

Class PufG Σ `{zoo_G : !ZooG Σ} := {
  #[local] puf_G_pstore_G :: Pstore2G Σ ;
}.

Definition puf_Σ := #[
  pstore_2_Σ
].
#[global] Instance subG_puf_Σ Σ `{zoo_G : !ZooG Σ} :
  subG puf_Σ Σ →
  PufG Σ.
Proof.
  solve_inG.
Qed.

Section puf_G.
  Context `{puf_G : PufG Σ}.

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

  Definition puf_model t reprs : iProp Σ :=
    ∃ descrs,
    pstore_2_model t descrs ∗
    ⌜consistent reprs descrs⌝.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %descrs{} &
      Hmodel{} &
      %Hconsistent{}
    )".

  Definition puf_snapshot s t reprs : iProp Σ :=
    ∃ descrs,
    pstore_2_snapshot s t descrs ∗
    ⌜consistent reprs descrs⌝.
  #[local] Instance : CustomIpatFormat "snapshot" :=
    "(
      %descrs{} &
      Hsnapshot{} &
      %Hconsistent{}
    )".

  #[global] Instance puf_model_timeless t reprs :
    Timeless (puf_model t reprs).
  Proof.
    apply _.
  Qed.
  #[global] Instance puf_snapshot_persistent s t reprs :
    Persistent (puf_snapshot s t reprs).
  Proof.
    apply _.
  Qed.

  #[local] Definition unify_at repr1 repr2 repr :=
    if decide (repr = repr1) then
      repr2
    else
      repr.

  #[local] Lemma unify_at_1 repr1 repr2 :
    unify_at repr1 repr2 repr1 = repr2.
  Proof.
    rewrite /unify_at decide_True //.
  Qed.
  #[local] Lemma unify_at_2 repr1 repr2 repr :
    repr ≠ repr1 →
    unify_at repr1 repr2 repr = repr.
  Proof.
    intros.
    rewrite /unify_at decide_False //.
  Qed.

  #[local] Definition unify repr1 repr2 reprs :=
    unify_at repr1 repr2 <$> reprs.

  #[local] Lemma unify_lookup_1 reprs repr1 repr2 elt :
    reprs !! elt = Some repr1 →
    unify repr1 repr2 reprs !! elt = Some repr2.
  Proof.
    intros Hreprs_lookup_elt.
    rewrite lookup_fmap Hreprs_lookup_elt /= unify_at_1 //.
  Qed.
  #[local] Lemma unify_lookup_2 {reprs repr1 repr2 elt} repr :
    reprs !! elt = Some repr →
    repr ≠ repr1 →
    unify repr1 repr2 reprs !! elt = Some repr.
  Proof.
    intros Hreprs_lookup_elt ?.
    rewrite lookup_fmap Hreprs_lookup_elt /= unify_at_2 //.
  Qed.
  #[local] Lemma unify_lookup_2' reprs repr1 repr2 :
    reprs !! repr2 = Some repr2 →
    repr1 ≠ repr2 →
    unify repr1 repr2 reprs !! repr2 = Some repr2.
  Proof.
    intros.
    apply unify_lookup_2; done.
  Qed.

  #[local] Lemma consistent_lookup_None {reprs descrs} elt :
    consistent reprs descrs →
    descrs !! elt = None →
    reprs !! elt = None.
  Proof.
    apply: map_Forall2_lookup_None_r.
  Qed.
  #[local] Lemma consistent_lookup_Some {reprs descrs} elt repr :
    consistent reprs descrs →
    reprs !! elt = Some repr →
      ∃ descr,
      descrs !! elt = Some descr ∧
      consistent_at reprs elt repr descr.
  Proof.
    apply: map_Forall2_lookup_Some_l.
  Qed.
  #[local] Lemma consistent_insert {reprs descrs} elt :
    descrs !! elt = None →
    consistent reprs descrs →
    consistent
      (<[elt := elt]> reprs)
      (<[elt := ‘Root( #0 )%V]> descrs).
  Proof.
    rewrite /consistent /consistent_at.
    intros Hdescrs_lookup Hconsistent.
    eapply consistent_lookup_None in Hconsistent as Hresprs_lookup; last done.
    apply map_Forall2_insert_2; first naive_solver.
    eapply map_Forall2_impl; first done.
    intros elt' repr' descr' [| (parent & ? & -> & Hreprs_lookup_parent & Hreprs_lookup_repr)]; first auto.
    right. exists parent.
    rewrite !lookup_insert_ne //; congruence.
  Qed.
  #[local] Lemma consistent_link_repr {reprs descrs} elt repr :
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
    eapply map_Forall2_insert_r; [done.. |].
    right. eauto.
  Qed.
  #[local] Lemma consistent_link_union {reprs descrs} repr1 repr2 :
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
    apply map_Forall2_alt in Hconsistent as (Hdom & Hconsistent).
    rewrite -map_Forall2_fmap_l map_Forall2_alt.
    split.
    - apply elem_of_dom_2 in Hreprs_lookup_repr1.
      set_solver.
    - intros elt repr descr Hreprs_lookup_elt [(<- & <-) | (? & Hdescrs_lookup_elt)]%lookup_insert_Some. simplify.
      + right. exists repr2.
        rewrite unify_at_1 unify_lookup_2' //.
      + destruct_decide (repr = repr1) as -> | ?.
        * rewrite unify_at_1.
          ospecialize* (Hconsistent elt); [done.. |].
          destruct Hconsistent as [| (parent & ? & -> & Hreprs_lookup_parent & Hreprs_lookup_repr1_)]; first naive_solver. simplify.
          right. exists parent.
          rewrite unify_lookup_1 // unify_lookup_2' //.
          naive_solver.
        * rewrite unify_at_2 //.
          ospecialize* (Hconsistent elt); [done.. |].
          destruct Hconsistent as [(rank & <- & ->)| (parent & ? & -> & Hreprs_lookup_parent & Hreprs_lookup_repr1_)].
          -- left. naive_solver.
          -- right. exists parent.
             rewrite !(unify_lookup_2 repr) //.
  Qed.
  #[local] Lemma consistent_update_rank {reprs descrs} repr rank :
    reprs !! repr = Some repr →
    consistent reprs descrs →
    consistent
      reprs
      (<[repr := ‘Root( #rank )%V]> descrs).
  Proof.
    rewrite /consistent.
    intros Hreprs_lookup_repr Hconsistent.
    eapply map_Forall2_insert_r; [done.. |].
    left. eauto.
  Qed.

  Lemma puf_model_valid {t reprs} elt repr :
    reprs !! elt = Some repr →
    puf_model t reprs ⊢
    ⌜reprs !! repr = Some repr⌝.
  Proof.
    iIntros "%Hreprs_lookup (:model)". iPureIntro.
    eapply consistent_lookup_Some in Hconsistent as (descr & Hdescrs_lookup & []); last done.
    all: naive_solver.
  Qed.
  Lemma puf_model_exclusive t reprs1 reprs2 :
    puf_model t reprs1 -∗
    puf_model t reprs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)".
    iApply (pstore_2_model_exclusive with "Hmodel1 Hmodel2").
  Qed.

  Lemma puf_create_spec :
    {{{
      True
    }}}
      puf_create ()
    {{{ t,
      RET t;
      puf_model t ∅
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_apply (pstore_2_create_spec with "[//]").
    iSteps.
  Qed.

  Lemma puf_make_spec t reprs :
    {{{
      puf_model t reprs
    }}}
      puf_make t
    {{{ elt,
      RET #elt;
      puf_model t (<[elt := elt]> reprs)
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".

    wp_rec.
    wp_smart_apply (pstore_2_ref_spec with "Hmodel") as (elt) "(%Hdescrs_lookup & Hmodel)".

    eapply consistent_insert in Hconsistent; last done.
    iSteps.
  Qed.

  #[local] Lemma puf_repr_spec {t reprs elt} repr :
    reprs !! elt = Some repr →
    {{{
      puf_model t reprs
    }}}
      puf_repr t #elt
    {{{
      RET #repr;
      puf_model t reprs
    }}}.
  Proof.
    iLöb as "HLöb" forall (elt repr).

    iIntros "%Hreprs_lookup_elt %Φ (:model) HΦ".
    pose proof Hconsistent as (descr & Hdescrs_lookup & Hconsistent_at)%(consistent_lookup_Some elt repr); last done.

    wp_rec.
    wp_smart_apply (pstore_2_get_spec with "Hmodel") as "Hmodel"; first done.

    destruct Hconsistent_at as [(rank & -> & ->) | (parent & ? & -> & Hreprs_lookup_parent & Hreprs_lookup_repr)]; wp_pures; first iSteps.

    wp_apply ("HLöb" $! parent with "[//] [$Hmodel //]") as "(:model =')".
    pose proof Hconsistent' as (descr' & Hdescrs'_lookup & _)%(consistent_lookup_Some elt repr); last done.

    wp_smart_apply (pstore_2_set_spec with "Hmodel'") as "Hmodel".
    { rewrite elem_of_dom //. }
    wp_pures.

    apply (consistent_link_repr elt repr) in Hconsistent'; [| done..].
    iSteps.
  Qed.

  Lemma puf_equiv_spec {t reprs elt1} repr1 {elt2} repr2 :
    reprs !! elt1 = Some repr1 →
    reprs !! elt2 = Some repr2 →
    {{{
      puf_model t reprs
    }}}
      puf_equiv t #elt1 #elt2
    {{{
      RET #(bool_decide (repr1 = repr2));
      puf_model t reprs
    }}}.
  Proof.
    iIntros "%Hreprs_lookup_elt1 %Hreprs_lookup_elt2 %Φ Hmodel HΦ".

    wp_rec.
    wp_smart_apply (puf_repr_spec with "Hmodel") as "Hmodel"; first done.
    wp_smart_apply (puf_repr_spec with "Hmodel") as "Hmodel"; first done.
    iSteps.
  Qed.

  #[local] Lemma puf_rank_spec t reprs elt :
    reprs !! elt = Some elt →
    {{{
      puf_model t reprs
    }}}
      puf_rank t #elt
    {{{ rank,
      RET #rank;
      puf_model t reprs
    }}}.
  Proof.
    iIntros "%Hreprs_lookup_elt %Φ (:model) HΦ".
    pose proof Hconsistent as (descr & Hdescrs_lookup & Hconsistent_at)%(consistent_lookup_Some elt elt); last done.

    wp_rec.
    wp_smart_apply (pstore_2_get_spec with "Hmodel") as "Hmodel"; first done.

    destruct Hconsistent_at as [(rank & _ & ->) | (parent & ? & -> & Hreprs_lookup_parent & Hreprs_lookup_repr)]; last done.
    iSteps.
  Qed.
  Definition puf_union_condition reprs repr1 repr2 reprs' :=
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
  #[local] Lemma puf_union_condition_refl reprs repr :
    puf_union_condition reprs repr repr reprs.
  Proof.
    split_and!; [done.. |].
    naive_solver.
  Qed.
  #[local] Lemma puf_union_condition_sym reprs repr1 repr2 reprs' :
    puf_union_condition reprs repr1 repr2 reprs' →
    puf_union_condition reprs repr2 repr1 reprs'.
  Proof.
    rewrite /puf_union_condition.
    intros (Hdom & Hunchanged & (repr12 & Hchanged)).
    split_and!; auto.
    exists repr12. naive_solver.
  Qed.
  #[local] Lemma unify_union_condition_1 reprs repr1 repr2 :
    repr1 ≠ repr2 →
    puf_union_condition reprs repr1 repr2 (unify repr1 repr2 reprs).
  Proof.
    intros.
    split_and!.
    - set_solver.
    - intros.
      apply unify_lookup_2; done.
    - exists repr2. split; first auto.
      intros elt repr Hreprs_lookup_elt [-> | ->].
      + rewrite unify_lookup_1 //.
      + rewrite (unify_lookup_2 repr2) //.
  Qed.
  #[local] Lemma unify_union_condition_2 reprs repr1 repr2 :
    repr1 ≠ repr2 →
    puf_union_condition reprs repr2 repr1 (unify repr1 repr2 reprs).
  Proof.
    intros.
    apply puf_union_condition_sym, unify_union_condition_1; done.
  Qed.
  #[local] Opaque puf_union_condition.
  Lemma puf_union_spec {t reprs elt1} repr1 {elt2} repr2 :
    reprs !! elt1 = Some repr1 →
    reprs !! elt2 = Some repr2 →
    {{{
      puf_model t reprs
    }}}
      puf_union t #elt1 #elt2
    {{{ reprs',
      RET ();
      puf_model t reprs' ∗
      ⌜puf_union_condition reprs repr1 repr2 reprs'⌝
    }}}.
  Proof.
    iIntros "%Hreprs_lookup_elt1 %Hreprs_lookup_elt2 %Φ Hmodel HΦ".
    iDestruct (puf_model_valid elt1 with "Hmodel") as %Hreprs_lookup_repr1; first done.
    iDestruct (puf_model_valid elt2 with "Hmodel") as %Hreprs_lookup_repr2; first done.

    wp_rec.
    wp_smart_apply (puf_repr_spec with "Hmodel") as "Hmodel"; first done.
    wp_smart_apply (puf_rank_spec with "Hmodel") as (rank1) "Hmodel"; first done.
    wp_smart_apply (puf_repr_spec with "Hmodel") as "Hmodel"; first done.
    wp_smart_apply (puf_rank_spec with "Hmodel") as (rank2) "(:model)"; first done.

    pose proof Hconsistent as (descr1 & Hdescrs_lookup_1 & Hconsistent_at_1)%(consistent_lookup_Some repr1 repr1); last done.
    pose proof Hconsistent as (descr2 & Hdescrs_lookup_2 & Hconsistent_at_2)%(consistent_lookup_Some repr2 repr2); last done.

    wp_pures.
    case_bool_decide; first subst repr2.

    - iSteps. iPureIntro. apply puf_union_condition_refl.

    - wp_pures.
      case_bool_decide; wp_pures.

      + wp_apply (pstore_2_set_spec with "Hmodel") as "Hmodel".
        { rewrite elem_of_dom //. }
        apply (consistent_link_union repr1 repr2) in Hconsistent; [| done..].

        iApply ("HΦ" $! (unify repr1 repr2 reprs)).
        iSteps. iPureIntro. apply unify_union_condition_1. done.

      + wp_apply (pstore_2_set_spec with "Hmodel") as "Hmodel".
        { rewrite elem_of_dom //. }
        apply (consistent_link_union repr2 repr1) in Hconsistent; [| done..].

        wp_pures.
        case_bool_decide; wp_pures.

        * wp_apply (pstore_2_set_spec with "Hmodel") as "Hmodel".
          { apply dom_insert, elem_of_union_r, elem_of_dom. done. }
          eapply (consistent_update_rank repr1) in Hconsistent; last first.
          { rewrite unify_lookup_2' //. }

          iApply ("HΦ" $! (unify repr2 repr1 reprs)).
          iSteps. iPureIntro. apply unify_union_condition_2. done.

        * iApply ("HΦ" $! (unify repr2 repr1 reprs)).
          iSteps. iPureIntro. apply unify_union_condition_2. done.
  Qed.

  Lemma puf_capture_spec t reprs :
    {{{
      puf_model t reprs
    }}}
      puf_capture t
    {{{ s,
      RET s;
      puf_model t reprs ∗
      puf_snapshot s t reprs
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".

    wp_apply (pstore_2_capture_spec with "Hmodel").
    iSteps.
  Qed.

  Lemma puf_restore_spec t reprs s reprs' :
    {{{
      puf_model t reprs ∗
      puf_snapshot s t reprs'
    }}}
      puf_restore t s
    {{{ s,
      RET s;
      puf_model t reprs'
    }}}.
  Proof.
    iIntros "%Φ ((:model) & (:snapshot =')) HΦ".

    wp_apply (pstore_2_restore_spec with "[$Hmodel $Hsnapshot']").
    iSteps.
  Qed.
End puf_G.

From zoo_persistent Require
  puf__opaque.

#[global] Opaque puf_model.
#[global] Opaque puf_snapshot.
