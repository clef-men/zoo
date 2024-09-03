From iris.base_logic Require Import
  lib.ghost_map.

From zoo Require Import
  prelude.
From zoo.common Require Import
  list
  fin_maps.
From zoo.iris.bi Require Import
  big_op.
From zoo.language Require Import
  notations
  diaframe.
From zoo.std Require Import
  xdeque.
From zoo.boxroot Require Export
  gc.
From zoo Require Import
  options.

Section list_to_set.
  Lemma list_to_set_delete `{Countable A} {l i} x :
    NoDup l →
    l !! i = Some x →
    list_to_set (C := gset A) (delete i l) ≡ list_to_set l ∖ {[x]}.
  Proof.
  Admitted.
End list_to_set.

Section list_to_map.
  Lemma list_to_map_zip_list_to_set `{Countable K} `{!Inhabited A} (m : gmap K A) (l : list K) :
    NoDup l →
    dom m ≡ list_to_set l →
    list_to_map (zip l ((λ x, m !!! x) <$> l)) = m.
  Proof.
    move: m. induction l as [| x l IH] => m.
    - intros _ ->%dom_empty_inv. done.
    - intros (Hx & Hnodup)%NoDup_cons Hdom.
      admit.
  Admitted.
End list_to_map.

Implicit Types l l_global root : location.
Implicit Types roots : list location.
Implicit Types v t global : val.
Implicit Types ω : gc_location.
Implicit Types map : gmap location gc_location.

Definition boxroot_init : val :=
  fun: <> =>
    let: "global" := xdeque_create () in
    gc_set_roots (fun: "fn" => xdeque_iter "global" "fn") #2%nat ;;
    "global".

Definition boxroot_create : val :=
  fun: "global" "v" =>
    let: "t" := { (), (), "v" } in
    xdeque_push_back "global" "t" ;;
    "t".

Definition boxroot_remove : val :=
  fun: "global" "t" =>
    xdeque_remove "t".

Definition boxroot_get : val :=
  fun: "t" =>
    "t".{xdeque_data}.

Definition boxroot_set : val :=
  fun: "t" "v" =>
    "t" <-{xdeque_data} "v".

Class BoxrootG Σ `{zoo_G : !ZooG Σ} := {
  #[local] boxroot_G_roots_G :: ghost_mapG Σ location gc_location ;
}.

Definition boxroot_Σ := #[
  ghost_mapΣ location gc_location
].
#[global] Instance subG_boxroot_Σ Σ `{zoo_G : !ZooG Σ} :
  subG boxroot_Σ Σ →
  BoxrootG Σ.
Proof.
  solve_inG.
Qed.

Section boxroot_G.
  Context `{boxroot_G : BoxrootG Σ}.

  #[local] Definition boxroot_roots_auth γ map :=
    ghost_map_auth γ 1 map.
  #[local] Definition boxroot_roots_elem γ root ω :=
    ghost_map_elem γ root (DfracOwn 1) ω.

  Definition boxroot_global global gc : iProp Σ :=
    ∃ l_global γ roots map,
    ⌜global = #l_global⌝ ∗
    meta l_global nroot γ ∗
    ⌜dom map ≡ list_to_set roots⌝ ∗
    boxroot_roots_auth γ map ∗
    xdeque_model global roots ∗
    [∗ map] root ↦ ω ∈ map,
      root.[xdeque_data] ↦root[gc] ω.

  Definition boxroot_model t global ω : iProp Σ :=
    ∃ root l_global γ,
    ⌜t = #root⌝ ∗
    ⌜global = #l_global⌝ ∗
    meta l_global nroot γ ∗
    boxroot_roots_elem γ root ω.

  #[local] Lemma boxroot_roots_alloc :
    ⊢ |==>
      ∃ γ,
      boxroot_roots_auth γ ∅.
  Proof.
    apply ghost_map_alloc_empty.
  Qed.
  #[local] Lemma boxroot_roots_lookup γ map root ω :
    boxroot_roots_auth γ map -∗
    boxroot_roots_elem γ root ω -∗
    ⌜map !! root = Some ω⌝.
  Proof.
    apply ghost_map_lookup.
  Qed.
  #[local] Lemma boxroot_roots_insert {γ map} root ω :
    map !! root = None →
    boxroot_roots_auth γ map ⊢ |==>
      boxroot_roots_auth γ (<[root := ω]> map) ∗
      boxroot_roots_elem γ root ω.
  Proof.
    iIntros "%Hlookup Hroots_auth".
    iApply (ghost_map_insert with "Hroots_auth"); first done.
  Qed.
  #[local] Lemma boxroot_roots_delete γ map root ω :
    boxroot_roots_auth γ map -∗
    boxroot_roots_elem γ root ω ==∗
      boxroot_roots_auth γ (delete root map).
  Proof.
    apply ghost_map_delete.
  Qed.
  #[local] Lemma boxroot_roots_update {γ map root ω} ω' :
    boxroot_roots_auth γ map -∗
    boxroot_roots_elem γ root ω ==∗
      boxroot_roots_auth γ (<[root := ω']> map) ∗
      boxroot_roots_elem γ root ω'.
  Proof.
    apply ghost_map_update.
  Qed.

  Lemma boxroot_init_spec gc Χ :
    {{{
      gc_model gc ∗
      gc_roots Χ
    }}}
      boxroot_init ()
    {{{ global,
      RET global;
      gc_model gc ∗
      gc_roots (boxroot_global global) ∗
      boxroot_global global gc
    }}}.
  Proof.
    iIntros "%Φ (Hgc & Hgc_roots) HΦ".
    wp_rec.
    wp_apply (xdeque_create_spec with "[//]") as (?) "((%l_global & -> & Hmeta) & Hroots)".
    iMod boxroot_roots_alloc as "(%γ & Hroots_auth)".
    iMod (meta_set _ _ γ with "Hmeta") as "#Hmeta"; first done.
    pose Χ' :=
      boxroot_global #l_global.
    pose (Ξ' roots ωs := (
      boxroot_roots_auth γ (list_to_map $ zip roots ωs) ∗
      xdeque_model #l_global roots
    )%I).
    wp_smart_apply (gc_set_roots_spec Χ' Ξ' with "[$Hgc $Hgc_roots]") as "(Hgc & Hgc_roots)".
    { clear gc Φ. iSplit; iModIntro.
      - iIntros "%gc". iSplit.
        + iIntros "(%_l_global & %_γ & %roots & %map & %Heq & #_Hmeta & %Hmap_dom & Hroots_auth & Hroots & Hmap)". injection Heq as <-.
          iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
          iDestruct (xdeque_model_NoDup with "Hroots") as %Hnodup.
          iExists roots, ((λ root, map !!! root) <$> roots). iSplitR "Hmap".
          * iFrame. rewrite list_to_map_zip_list_to_set //.
          * admit.
        + iIntros "(%roots & %ωs & (Hroots_auth & Hroots) & Hωs)".
          iDestruct (xdeque_model_NoDup with "Hroots") as %Hnodup.
          iDestruct (big_sepL2_alt with "Hωs") as "(%Hlength & Hωs)".
          iExists l_global, γ, roots, (list_to_map $ zip roots ωs). iSteps.
          * rewrite dom_list_to_map_L fst_zip //. lia.
          * rewrite big_sepM_list_to_map // fst_zip //. lia.
      - iIntros "%Ψ %roots %ωs %fn !> %Φ (HΨ & (Hroots_auth & Hroots) & #Hfn) HΦ".
        wp_smart_apply (xdeque_iter_spec Ψ with "[$HΨ $Hroots]"); iSteps.
    }
    wp_pures.
    iApply "HΦ". iFrame.
    iExists l_global, γ, [], ∅. iSteps. rewrite big_sepM_empty //.
  Admitted.

  Lemma boxroot_create_spec {gc global l} ω :
    ω ↦gc[gc] l →
    {{{
      boxroot_global global gc
    }}}
      boxroot_create global #l
    {{{ t,
      RET t;
      boxroot_global global gc ∗
      boxroot_model t global ω
    }}}.
  Proof.
    iIntros "%Hω %Φ (%l_global & %γ & %roots & %map & -> & #Hmeta & %Hmap_dom & Hroots_auth & Hroots & Hmap) HΦ".
    wp_rec.
    wp_block root as "(Hroot_prev & Hroot_next & Hroot & _)".
    (* iApply wp_fupd. *)
    wp_smart_apply (xdeque_push_back_spec with "[$Hroots $Hroot_prev $Hroot_next]") as "Hroots".
    iAssert ⌜map !! root = None⌝%I as %Hroot.
    { rewrite -eq_None_ne_Some. iIntros "%ω' %Hmap_lookup".
      iDestruct (big_sepM_lookup with "Hmap") as "(% & Hroot_ & _)"; first done.
      iApply (pointsto_exclusive with "Hroot Hroot_").
    }
    iMod (boxroot_roots_insert root ω with "Hroots_auth") as "(Hroots_auth & Hroots_elem)"; first done.
    wp_pures.
    iApply "HΦ". iFrame. iSplitR "Hroots_elem"; last iSteps.
    iExists l_global, γ, (roots ++ [root]), (<[root := ω]> map). iSteps.
    - iPureIntro. set_solver.
    - rewrite big_sepM_insert //. iSteps.
  Qed.

  Lemma boxroot_remove_spec gc global t ω :
    {{{
      boxroot_global global gc ∗
      boxroot_model t global ω
    }}}
      boxroot_remove global t
    {{{
      RET ();
      boxroot_global global gc
    }}}.
  Proof.
    iIntros "%Φ ((%l_global & %γ & %roots & %map & -> & #Hmeta & %Hmap_dom & Hroots_auth & Hroots & Hmap) & (%root & %_l_global & %_γ & -> & %Heq & _Hmeta & Hroots_elem)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    wp_rec.
    iApply wp_fupd.
    iDestruct (boxroot_roots_lookup with "Hroots_auth Hroots_elem") as "%Hmap_lookup".
    assert (∃ i, roots !! i = Some root) as (i & Hroots_lookup).
    { rewrite -elem_of_list_lookup -(elem_of_list_to_set (C := gset location)) -Hmap_dom elem_of_dom //. }
    iDestruct (xdeque_model_NoDup with "Hroots") as %Hnodup.
    wp_smart_apply (xdeque_remove_spec with "Hroots") as "Hroots"; first done.
    iMod (boxroot_roots_delete with "Hroots_auth Hroots_elem") as "Hroots_auth".
    iDestruct (big_sepM_delete with "Hmap") as "(Hroot & Hmap)"; first done.
    iApply "HΦ".
    iExists l_global, γ, (delete i roots), (delete root map). iSteps.
    iPureIntro. rewrite dom_delete_L list_to_set_delete //. set_solver.
  Qed.

  Lemma boxroot_get_spec gc global t ω :
    {{{
      boxroot_global global gc ∗
      boxroot_model t global ω
    }}}
      boxroot_get t
    {{{ l,
      RET #l;
      ⌜ω ↦gc[gc] l⌝ ∗
      boxroot_global global gc ∗
      boxroot_model t global ω
    }}}.
  Proof.
    iIntros "%Φ ((%l_global & %γ & %roots & %map & -> & #Hmeta & %Hmap_dom & Hroots_auth & Hroots & Hmap) & (%root & %_l_global & %_γ & -> & %Heq & _Hmeta & Hroots_elem)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    wp_rec.
    iDestruct (boxroot_roots_lookup with "Hroots_auth Hroots_elem") as %Hmap_lookup.
    iDestruct (big_sepM_lookup_acc with "Hmap") as "(Hroot & Hmap)"; first done.
    wp_apply (wp_load_gc_root with "Hroot"); first done.
    iSteps.
  Qed.

  Lemma boxroot_set_spec {gc global t ω'} ω l :
    ω ↦gc[gc] l →
    {{{
      boxroot_global global gc ∗
      boxroot_model t global ω'
    }}}
      boxroot_set t #l
    {{{
      RET ();
      boxroot_global global gc ∗
      boxroot_model t global ω
    }}}.
  Proof.
    iIntros "%Hω %Φ ((%l_global & %γ & %roots & %map & -> & #Hmeta & %Hmap_dom & Hroots_auth & Hroots & Hmap) & (%root & %_l_global & %_γ & -> & %Heq & _Hmeta & Hroots_elem)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    wp_rec.
    iDestruct (boxroot_roots_lookup with "Hroots_auth Hroots_elem") as %Hmap_lookup.
    iDestruct (big_sepM_insert_acc with "Hmap") as "(Hroot & Hmap)"; first done.
    iApply wp_fupd.
    wp_smart_apply (wp_store_gc_root with "Hroot") as "Hroot"; [done.. |].
    iMod (boxroot_roots_update ω with "Hroots_auth Hroots_elem") as "(Hroots_auth & Hroots_elem)".
    iApply "HΦ". iSplitR "Hroots_elem"; last iSteps.
    iExists l_global, γ, roots, (<[root := ω]> map). iSteps.
    iPureIntro. apply elem_of_dom_2 in Hmap_lookup. set_solver.
  Qed.
End boxroot_G.

#[global] Opaque boxroot_create.
#[global] Opaque boxroot_remove.
#[global] Opaque boxroot_get.
#[global] Opaque boxroot_set.

#[global] Opaque boxroot_global.
#[global] Opaque boxroot_model.
