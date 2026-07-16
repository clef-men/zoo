Require Import iris.base_logic.lib.ghost_map.

Require Import zoo.prelude.
Require Import zoo.common.list.
Require Import zoo.common.fin_maps.
Require Import zoo.iris.bi.big_op.
Require Import zoo.base.
Require Import zoo_std.xdeque.
Require Export zoo_boxroot.gc.
Require Import zoo.options.

Section list_to_set.
  Lemma list_to_set𑁒delete `{Countable A} {l i} x :
    NoDup l →
    l !! i = Some x →
    list_to_set (C := gset A) (delete i l) ≡ list_to_set l ∖ {[x]}.
  Proof.
  Admitted.
End list_to_set.

Section list_to_map.
  Lemma list_to_map𑁒zip𑁒list_to_set `{Countable K} `{!Inhabited A} (m : gmap K A) (l : list K) :
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
Implicit Types ω : gc۰location.
Implicit Types map : gmap location gc۰location.

Definition boxroot٠init : val :=
  fun: <> =>
    let: "global" := xdeque٠create () in
    gc٠set_roots (fun: "fn" => xdeque٠iter "fn" "global") #2%nat ;;
    "global".

Definition boxroot٠create : val :=
  fun: "global" "v" =>
    let: "t" := { (), (), "v" } in
    xdeque٠push_back "global" "t" ;;
    "t".

Definition boxroot٠remove : val :=
  fun: "global" "t" =>
    xdeque٠remove "t".

Definition boxroot٠get : val :=
  fun: "t" =>
    "t".{xdeque_data}.

Definition boxroot٠set : val :=
  fun: "t" "v" =>
    "t" <-{xdeque_data} "v".

Class BoxrootG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] boxroot۰G۰roots۰G :: ghost_mapG Σ location gc۰location
  }.

Definition boxroot۰Σ :=
  #[ghost_mapΣ location gc۰location
  ].
#[global] Instance subG𑁒boxroot۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG boxroot۰Σ Σ →
  BoxrootG Σ.
Proof.
  solve_inG.
Qed.

Section boxroot۰G.
  Context `{boxroot۰G : BoxrootG Σ}.

  #[local] Definition metadata :=
    gname.
  Implicit Types γ : metadata.

  #[local] Definition roots۰auth γ map :=
    ghost_map_auth γ 1 map.
  #[local] Definition roots۰elem γ root ω :=
    ghost_map_elem γ root (DfracOwn 1) ω.

  Definition boxroot۰global global gc : iProp Σ :=
    ∃ l_global γ roots map,
    ⌜global = #l_global⌝ ∗
    l_global ↪ γ ∗
    ⌜dom map ≡ list_to_set roots⌝ ∗
    roots۰auth γ map ∗
    xdeque۰model global roots ∗
    [∗ map] root ↦ ω ∈ map,
      root.[xdeque_data] ↦root[gc] ω.

  Definition boxroot۰model t global ω : iProp Σ :=
    ∃ root l_global γ,
    ⌜t = #root⌝ ∗
    ⌜global = #l_global⌝ ∗
    l_global ↪ γ ∗
    roots۰elem γ root ω.

  #[local] Lemma roots𑁒alloc :
    ⊢ |==>
      ∃ γ,
      roots۰auth γ ∅.
  Proof.
    apply ghost_map_alloc_empty.
  Qed.
  #[local] Lemma roots𑁒lookup γ map root ω :
    roots۰auth γ map -∗
    roots۰elem γ root ω -∗
    ⌜map !! root = Some ω⌝.
  Proof.
    apply ghost_map_lookup.
  Qed.
  #[local] Lemma roots𑁒insert {γ map} root ω :
    map !! root = None →
    roots۰auth γ map ⊢ |==>
      roots۰auth γ (<[root := ω]> map) ∗
      roots۰elem γ root ω.
  Proof.
    iIntros "%Hlookup Hroots_auth".
    iApply (ghost_map_insert with "Hroots_auth"); first done.
  Qed.
  #[local] Lemma roots𑁒delete γ map root ω :
    roots۰auth γ map -∗
    roots۰elem γ root ω ==∗
      roots۰auth γ (delete root map).
  Proof.
    apply ghost_map_delete.
  Qed.
  #[local] Lemma roots𑁒update {γ map root ω} ω' :
    roots۰auth γ map -∗
    roots۰elem γ root ω ==∗
      roots۰auth γ (<[root := ω']> map) ∗
      roots۰elem γ root ω'.
  Proof.
    apply ghost_map_update.
  Qed.

  Lemma boxroot٠init𑁒spec gc Χ :
    {{{
      gc۰model gc ∗
      gc۰roots Χ
    }}}
      boxroot٠init ()
    {{{
      global
    , RET global;
      gc۰model gc ∗
      gc۰roots (boxroot۰global global) ∗
      boxroot۰global global gc
    }}}.
  Proof.
    iIntros "%Φ (Hgc & Hgc_roots) HΦ".
    wp۰rec.
    wp۰apply (xdeque٠create𑁒spec with "[//]") as (?) "((%l_global & -> & Hmeta) & Hroots)".
    iMod roots𑁒alloc as "(%γ & Hroots_auth)".
    iMod (meta𑁒set γ with "Hmeta") as "#Hmeta"; first done.
    pose Χ' :=
      boxroot۰global #l_global.
    pose (Ξ' roots ωs := (
      roots۰auth γ (list_to_map $ zip roots ωs) ∗
      xdeque۰model #l_global roots
    )%I).
    wp۰apply+ (gc٠set_roots𑁒spec Χ' Ξ' with "[$Hgc $Hgc_roots]") as "(Hgc & Hgc_roots)".
    { clear gc Φ. iSplit; iModIntro.
      - iIntros "%gc". iSplit.
        + iIntros "(%_l_global & %_γ & %roots & %map & %Heq & #_Hmeta & %Hmap_dom & Hroots_auth & Hroots & Hmap)". injection Heq as <-.
          iDestruct (meta𑁒agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
          iDestruct (xdeque۰model𑁒NoDup with "Hroots") as %Hnodup.
          iExists roots, ((λ root, map !!! root) <$> roots). iSplitR "Hmap".
          * iFrame. rewrite list_to_map𑁒zip𑁒list_to_set //.
          * admit.
        + iIntros "(%roots & %ωs & (Hroots_auth & Hroots) & Hωs)".
          iDestruct (xdeque۰model𑁒NoDup with "Hroots") as %Hnodup.
          iDestruct (big_sepL2_alt with "Hωs") as "(%Hlength & Hωs)".
          iExists l_global, γ, roots, (list_to_map $ zip roots ωs). iSteps.
          * rewrite dom_list_to_map_L fst_zip //. lia.
          * rewrite big_sepM_list_to_map // fst_zip //. lia.
      - iIntros "%Ψ %roots %ωs %fn !> %Φ (HΨ & (Hroots_auth & Hroots) & #Hfn) HΦ".
        wp۰apply+ (xdeque٠iter𑁒spec Ψ with "[$HΨ $Hroots]"); iSteps.
    }
    wp۰pures.
    iApply "HΦ".
    iFrame. iExists l_global. rewrite big_sepM_empty. iSteps.
  Admitted.

  Lemma boxroot٠create𑁒spec {gc global l} ω :
    ω ↦gc[gc] l →
    {{{
      boxroot۰global global gc
    }}}
      boxroot٠create global #l
    {{{
      t
    , RET t;
      boxroot۰global global gc ∗
      boxroot۰model t global ω
    }}}.
  Proof.
    iIntros "%Hω %Φ (%l_global & %γ & %roots & %map & -> & #Hmeta & %Hmap_dom & Hroots_auth & Hroots & Hmap) HΦ".
    wp۰rec.
    wp۰block root as "(Hroot_prev & Hroot_next & Hroot & _)".
    (* iApply wp𑁒fupd. *)
    wp۰apply+ (xdeque٠push_back𑁒spec with "[$Hroots $Hroot_prev $Hroot_next]") as "Hroots".
    iAssert ⌜map !! root = None⌝%I as %Hroot.
    { rewrite -eq_None_ne_Some. iIntros "%ω' %Hmap_lookup".
      iDestruct (big_sepM_lookup with "Hmap") as "(% & Hroot_ & _)"; first done.
      iApply (pointsto𑁒exclusive with "Hroot Hroot_").
    }
    iMod (roots𑁒insert root ω with "Hroots_auth") as "(Hroots_auth & Hroots_elem)"; first done.
    wp۰pures.
    iApply "HΦ".
    iFrameSteps.
    - iPureIntro. set_solver.
    - rewrite big_sepM_insert //. iSteps.
  Qed.

  Lemma boxroot٠remove𑁒spec gc global t ω :
    {{{
      boxroot۰global global gc ∗
      boxroot۰model t global ω
    }}}
      boxroot٠remove global t
    {{{
      RET ();
      boxroot۰global global gc
    }}}.
  Proof.
    iIntros "%Φ ((%l_global & %γ & %roots & %map & -> & #Hmeta & %Hmap_dom & Hroots_auth & Hroots & Hmap) & (%root & %_l_global & %_γ & -> & %Heq & _Hmeta & Hroots_elem)) HΦ". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    wp۰rec.
    iApply wp𑁒fupd.
    iDestruct (roots𑁒lookup with "Hroots_auth Hroots_elem") as "%Hmap_lookup".
    assert (∃ i, roots !! i = Some root) as (i & Hroots_lookup).
    { rewrite -list_elem_of_lookup -(elem_of_list_to_set (C := gset location)) -Hmap_dom elem_of_dom //. }
    iDestruct (xdeque۰model𑁒NoDup with "Hroots") as %Hnodup.
    wp۰apply+ (xdeque٠remove𑁒spec with "Hroots") as "Hroots"; first done.
    iMod (roots𑁒delete with "Hroots_auth Hroots_elem") as "Hroots_auth".
    iDestruct (big_sepM_delete with "Hmap") as "(Hroot & Hmap)"; first done.
    iApply "HΦ".
    iExists l_global, γ, (delete i roots), (delete root map). iSteps.
    iPureIntro. rewrite dom_delete_L list_to_set𑁒delete //. set_solver.
  Qed.

  Lemma boxroot٠get𑁒spec gc global t ω :
    {{{
      boxroot۰global global gc ∗
      boxroot۰model t global ω
    }}}
      boxroot٠get t
    {{{
      l
    , RET #l;
      ⌜ω ↦gc[gc] l⌝ ∗
      boxroot۰global global gc ∗
      boxroot۰model t global ω
    }}}.
  Proof.
    iIntros "%Φ ((%l_global & %γ & %roots & %map & -> & #Hmeta & %Hmap_dom & Hroots_auth & Hroots & Hmap) & (%root & %_l_global & %_γ & -> & %Heq & _Hmeta & Hroots_elem)) HΦ". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    wp۰rec.
    iDestruct (roots𑁒lookup with "Hroots_auth Hroots_elem") as %Hmap_lookup.
    iDestruct (big_sepM_lookup_acc with "Hmap") as "(Hroot & Hmap)"; first done.
    wp۰apply (gc𑁒wp𑁒load𑁒root with "Hroot"); first done.
    iSteps.
  Qed.

  Lemma boxroot٠set𑁒spec {gc global t ω'} ω l :
    ω ↦gc[gc] l →
    {{{
      boxroot۰global global gc ∗
      boxroot۰model t global ω'
    }}}
      boxroot٠set t #l
    {{{
      RET ();
      boxroot۰global global gc ∗
      boxroot۰model t global ω
    }}}.
  Proof.
    iIntros "%Hω %Φ ((%l_global & %γ & %roots & %map & -> & #Hmeta & %Hmap_dom & Hroots_auth & Hroots & Hmap) & (%root & %_l_global & %_γ & -> & %Heq & _Hmeta & Hroots_elem)) HΦ". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    wp۰rec.
    iDestruct (roots𑁒lookup with "Hroots_auth Hroots_elem") as %Hmap_lookup.
    iDestruct (big_sepM_insert_acc with "Hmap") as "(Hroot & Hmap)"; first done.
    iApply wp𑁒fupd.
    wp۰apply+ (gc𑁒wp𑁒store𑁒root with "Hroot") as "Hroot"; [done.. |].
    iMod (roots𑁒update ω with "Hroots_auth Hroots_elem") as "(Hroots_auth & Hroots_elem)".
    iApply "HΦ".
    iSplitR "Hroots_elem"; last iSteps.
    iExists l_global, γ, roots, (<[root := ω]> map). iSteps.
    iPureIntro. apply elem_of_dom_2 in Hmap_lookup. set_solver.
  Qed.
End boxroot۰G.

#[global] Opaque boxroot٠create.
#[global] Opaque boxroot٠remove.
#[global] Opaque boxroot٠get.
#[global] Opaque boxroot٠set.

#[global] Opaque boxroot۰global.
#[global] Opaque boxroot۰model.
