(* Based on:
   https://github.com/backtracking/spds/blob/12e48dc9f5d169ab38a9b7887bb481621ab04331/parray.ml
*)

From iris.base_logic Require Import
  lib.ghost_map.

From zoo Require Import
  prelude.
From zoo.language Require Import
  notations
  diaframe.
From zoo.std Require Import
  array.
From zoo.persistent Require Export
  base.
From zoo Require Import
  options.

Implicit Types i : nat.
Implicit Types l root : location.
Implicit Types v t eq : val.
Implicit Types vs : list val.

#[local] Notation "'Root'" := (
  in_type "descr" 0
)(in custom zoo_tag
).
#[local] Notation "'Diff'" := (
  in_type "descr" 1
)(in custom zoo_tag
).

Definition parray_make : val :=
  fun: "sz" "v" =>
    ref ‘Root{ array_make "sz" "v" }.

#[local] Definition parray_reroot : val :=
  rec: "parray_reroot" "t" =>
    match: !"t" with
    | Root "arr" =>
        "arr"
    | Diff "i" "v" "t'" =>
        let: "arr" := "parray_reroot" "t'" in
        "t'" <- ‘Diff{ "i", array_unsafe_get "arr" "i", "t" } ;;
        array_unsafe_set "arr" "i" "v" ;;
        "t" <- ‘Root{ "arr" } ;;
        "arr"
    end.

Definition parray_get : val :=
  fun: "t" "i" =>
    array_unsafe_get (parray_reroot "t") "i".

Definition parray_set : val :=
  fun: "t" "eq" "i" "v" =>
    let: "arr" := parray_reroot "t" in
    let: "v'" := array_unsafe_get "arr" "i" in
    if: "eq" "v" "v'" then (
      "t"
    ) else (
      array_unsafe_set "arr" "i" "v" ;;
      let: "t'" := ref !"t" in
      "t" <- ‘Diff{ "i", "v'", "t'" } ;;
      "t'"
    ).

Class ParrayG Σ `{zoo_G : !ZooG Σ} := {
  parray_G_map_G : ghost_mapG Σ location (list val) ;
}.

Definition parray_Σ := #[
  ghost_mapΣ location (list val)
].
#[global] Instance subG_parray_Σ Σ `{zoo_G : !ZooG Σ} :
  subG parray_Σ Σ →
  ParrayG Σ.
Proof.
  solve_inG.
Qed.

Section parray_G.
  Context `{parray_G : ParrayG Σ}.

  Record parray_meta := {
    parray_meta_map : gname ;
    parray_meta_array : val ;
    parray_meta_size : nat ;
  }.
  Implicit Types γ : parray_meta.

  #[local] Definition parray_map_auth' γ_map map :=
    @ghost_map_auth _ _ _ _ _ parray_G_map_G γ_map 1 map.
  #[local] Definition parray_map_auth γ :=
    parray_map_auth' γ.(parray_meta_map).
  #[local] Definition parray_map_elem' γ_map l vs :=
    @ghost_map_elem _ _ _ _ _ parray_G_map_G γ_map l DfracDiscarded vs.
  #[local] Definition parray_map_elem γ :=
    parray_map_elem' γ.(parray_meta_map).

  #[local] Definition parray_inv_inner τ `{!iType _ τ} γ map root : iProp Σ :=
    parray_map_auth γ map ∗
    [∗ map] l ↦ vs ∈ map,
      ∃ descr,
      ⌜length vs = γ.(parray_meta_size)⌝ ∗
      l ↦ descr ∗
      if (decide (l = root)) then (
        ⌜descr = ’Root{ γ.(parray_meta_array) }⌝ ∗
        array_model γ.(parray_meta_array) (DfracOwn 1) vs ∗
        [∗ list] v ∈ vs, τ v
      ) else (
        ∃ i v l' vs',
        ⌜i < γ.(parray_meta_size) ∧ vs = <[i := v]> vs'⌝ ∗
        ⌜descr = ’Diff{ #i, v, #l' }⌝ ∗
        parray_map_elem γ l' vs' ∗
        τ v
      ).
  Definition parray_inv τ `{!iType _ τ} γ : iProp Σ :=
    ∃ map root,
    parray_inv_inner τ γ map root.

  Definition parray_model t γ vs : iProp Σ :=
    ∃ l,
    ⌜t = #l⌝ ∗
    parray_map_elem γ l vs.

  #[local] Instance parray_inv_inner_timeless τ `{!iType _ τ} γ map root :
    (∀ v, Timeless (τ v)) →
    Timeless (parray_inv_inner τ γ map root).
  Proof.
    rewrite /Timeless. iIntros "%Hτ (Hmap_auth & Hmap)".
    iSplitL "Hmap_auth".
    - iApply (timeless with "Hmap_auth").
    - unshelve iApply (timeless _ (Timeless := big_sepM_timeless _ _ _) with "Hmap").
      rewrite /Timeless. iIntros "%l %vs _ (%descr & >%Hvs_len & Hl & Hdescr)".
      iExists descr.
      iSplit; first iSteps.
      iSplitL "Hl"; first iApply (timeless with "Hl").
      case_decide as Hcase.
      + iDestruct "Hdescr" as "(>-> & Harr & Hvs)".
        iSplit; first iSteps.
        iSplitL "Harr"; first iApply (timeless with "Harr").
        unshelve iApply (timeless _ (Timeless := big_sepL_timeless _ _ _) with "Hvs").
        rewrite /Timeless. iIntros "%i %v _ Hv".
        iApply (Hτ with "Hv").
      + iDestruct "Hdescr" as "(%i & %v & %l' & %vs' & >(%Hi & %Hvs) & >-> & Hmap_elem' & Hv)".
        iExists i, v, l', vs'.
        iSplit; first iSteps.
        iSplit; first iSteps.
        iSplit; first iApply (timeless with "Hmap_elem'").
        iApply (Hτ with "Hv").
  Qed.
  #[global] Instance parray_inv_timeless τ `{!iType _ τ} γ :
    (∀ v, Timeless (τ v)) →
    Timeless (parray_inv τ γ).
  Proof.
    apply _.
  Qed.
  #[global] Instance parray_model_timeless t γ vs :
    Timeless (parray_model t γ vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance parray_model_persistent t γ vs :
    Persistent (parray_model t γ vs).
  Proof.
    apply _.
  Qed.

  #[local] Lemma parray_map_alloc root vs :
    ⊢ |==>
      ∃ γ_map,
      parray_map_auth' γ_map {[root := vs]} ∗
      parray_map_elem' γ_map root vs.
  Proof.
    iMod (@ghost_map_alloc _ _ _ _ _ parray_G_map_G {[root := vs]}) as "(%γ_map & Hmap_auth & Hmap_elem)".
    setoid_rewrite big_sepM_singleton.
    iMod (ghost_map_elem_persist with "Hmap_elem") as "Hmap_elem".
    iSteps.
  Qed.
  #[local] Lemma parray_map_lookup γ map l vs :
    parray_map_auth γ map -∗
    parray_map_elem γ l vs -∗
    ⌜map !! l = Some vs⌝.
  Proof.
    apply ghost_map_lookup.
  Qed.
  #[local] Lemma parray_map_insert {γ map} l vs :
    map !! l = None →
    parray_map_auth γ map ⊢ |==>
      parray_map_auth γ (<[l := vs]> map) ∗
      parray_map_elem γ l vs.
  Proof.
    iIntros "%Hlookup Hmap_auth".
    iMod (ghost_map_insert with "Hmap_auth") as "(Hmap_auth & Hmap_elem)"; first done.
    iMod (ghost_map_elem_persist with "Hmap_elem") as "Hmap_elem".
    iSteps.
  Qed.

  Lemma parray_make_spec τ `{!iType _ τ} (sz : Z) v :
    (0 ≤ sz)%Z →
    {{{
      τ v
    }}}
      parray_make #sz v
    {{{ t γ,
      RET t;
      parray_inv τ γ ∗
      parray_model t γ (replicate (Z.to_nat sz) v)
    }}}.
  Proof.
    iIntros "%Hsz %Φ #Hv HΦ".
    wp_rec.
    wp_smart_apply (array_make_spec with "[//]") as "%arr Harr"; first done.
    wp_alloc root as "Hroot".
    pose vs := replicate (Z.to_nat sz) v.
    iMod (parray_map_alloc root vs) as "(%γ_map & Hmap_auth & Hmap_elem)".
    pose γ := {|
      parray_meta_map := γ_map ;
      parray_meta_array := arr ;
      parray_meta_size := Z.to_nat sz ;
    |}.
    iApply ("HΦ" $! _ γ). iSplitR "Hmap_elem"; last iSteps. iExists {[root := vs]}, root. iFrame.
    iApply big_sepM_singleton.
    iExists _. rewrite replicate_length decide_True //. iSteps.
    iApply big_sepL_intro. iIntros "!> !>" (i ? (-> & Hi)%lookup_replicate) "//".
  Qed.

  #[local] Lemma parray_reroot_spec τ `{!iType _ τ} γ map root l vs :
    {{{
      parray_inv_inner τ γ map root ∗
      parray_map_elem γ l vs
    }}}
      parray_reroot #l
    {{{
      RET γ.(parray_meta_array);
      parray_inv_inner τ γ map l
    }}}.
  Proof.
    iLöb as "HLöb" forall (l vs).
    iIntros "%Φ ((Hmap_auth & Hmap) & #Hmap_elem) HΦ".
    wp_rec.
    iDestruct (parray_map_lookup with "Hmap_auth Hmap_elem") as %Hmap_lookup.
    iDestruct (big_sepM_lookup_acc with "Hmap") as "((%descr & %Hvs_len & Hl & Hdescr) & Hmap)"; first done.
    destruct (decide (l = root)) as [-> | Hcase1].
    { iDestruct "Hdescr" as "(-> & Harr & Hvs)". iSteps. }
    iDestruct "Hdescr" as "(%i & %v & %l' & %vs' & (%Hi & %Hvs) & -> & #Hmap_elem' & #Hv)".
    wp_load.
    iDestruct ("Hmap" with "[Hl Hv]") as "Hmap"; first iSteps.
    wp_smart_apply ("HLöb" with "[Hmap_auth Hmap]") as "(Hmap_auth & Hmap)"; first iSteps.
    wp_pures.
    iDestruct (parray_map_lookup with "Hmap_auth Hmap_elem'") as %Hmap_lookup'.
    iDestruct (big_sepM_delete with "Hmap") as "((%descr' & %Hvs'_len & Hl' & Hdescr') & Hmap)"; first done.
    rewrite decide_True //. iDestruct "Hdescr'" as "(-> & Harr & Hvs')".
    opose proof* (list_lookup_lookup_total_lt vs' i) as Hvs'_lookup; first lia.
    wp_apply (array_unsafe_get_spec i with "Harr") as "Harr"; [lia | | lia |]; first done.
    wp_store.
    wp_smart_apply (array_unsafe_set_spec with "Harr") as "Harr"; first lia.
    rewrite Nat2Z.id -Hvs.
    destruct (decide (l = l')) as [<- | Hcase2].
    - wp_store.
      iDestruct (big_sepM_delete with "[$Hmap Hl' Harr Hvs']") as "Hmap"; first done.
      { iExists _. rewrite decide_True //. clear Hvs. simplify. iSteps. }
      iSteps.
    - iDestruct (big_sepM_delete _ _ l with "Hmap") as "((%descr & _ & Hl & Hdescr) & Hmap)"; first rewrite lookup_delete_ne //.
      rewrite decide_False //. iDestruct "Hdescr" as "(%i'' & %w & %l'' & %vs'' & _ & -> & _ & _)".
      wp_store. wp_pures.
      iApply "HΦ". iFrame.
      iDestruct (big_sepL_insert_acc with "Hvs'") as "(Hvs'!!!i & Hvs')"; first done.
      iApply (big_sepM_delete _ _ l'); first done. iSplitL "Hl' Hvs'!!!i".
      { iExists _. rewrite decide_False //. iFrame. iSplitR; first iSteps. iExists i, (vs' !!! i), l, vs. iSteps.
        iPureIntro. rewrite Hvs list_insert_insert list_insert_id //.
      }
      iApply (big_sepM_delete _ _ l); first rewrite lookup_delete_ne //. iSplitL "Hl Harr Hvs'".
      { iExists _. rewrite decide_True //.
        iSpecialize ("Hvs'" $! v). rewrite -Hvs.
        iSteps.
      }
      iApply (big_sepM_impl with "Hmap"). clear. iIntros "!> !>" (l'' vs'' (Hl''1 & (Hl''2 & Hmap_lookup'')%lookup_delete_Some)%lookup_delete_Some) "(%descr'' & %Hvs''_len & Hl'' & Hdescr'')".
      iExists _. rewrite decide_False // decide_False //. iFrame. iSteps.
  Qed.

  Lemma parray_get_spec τ `{!iType _ τ} {t γ vs} {i : Z} v :
    (0 ≤ i)%Z →
    vs !! Z.to_nat i = Some v →
    {{{
      parray_inv τ γ ∗
      parray_model t γ vs
    }}}
      parray_get t #i
    {{{
      RET v;
      parray_inv τ γ
    }}}.
  Proof.
    iIntros "%Hi %Hvs_lookup %Φ ((%map & %root & Hinv) & (%l & -> & #Hmap_elem)) HΦ".
    wp_rec.
    wp_smart_apply (parray_reroot_spec τ with "[$Hinv $Hmap_elem]") as "(Hmap_auth & Hmap)".
    iDestruct (parray_map_lookup with "Hmap_auth Hmap_elem") as %Hmap_lookup.
    iDestruct (big_sepM_lookup_acc with "Hmap") as "((%descr & %Hvs_len & Hl & Hdescr) & Hmap)"; first done.
    rewrite decide_True //. iDestruct "Hdescr" as "(-> & Harr & Hvs)".
    wp_apply (array_unsafe_get_spec with "Harr"); [done.. |].
    setoid_rewrite decide_True at 1; last done. iSteps.
  Qed.

  Lemma parray_set_spec τ `{!iType _ τ} t γ vs eq (i : Z) v :
    (0 ≤ i < length vs)%Z →
    {{{
      parray_inv τ γ ∗
      parray_model t γ vs ∗
      ( ∀ v1 v2,
        τ v1 -∗
        τ v2 -∗
        WP eq v1 v2 {{ res,
          ⌜res = #(bool_decide (v1 = v2))⌝
        }}
      ) ∗
      τ v
    }}}
      parray_set t eq #i v
    {{{ t',
      RET t';
      parray_inv τ γ ∗
      parray_model t' γ (<[Z.to_nat i := v]> vs)
    }}}.
  Proof.
    iIntros "%Hi %Φ ((%map & %root & Hinv) & (%l & -> & #Hmap_elem) & Heq & #Hv) HΦ".
    Z_to_nat i. rewrite Nat2Z.id.
    wp_rec.
    wp_smart_apply (parray_reroot_spec with "[$Hinv //]") as "(Hmap_auth & Hmap)".
    iDestruct (parray_map_lookup with "Hmap_auth Hmap_elem") as %Hmap_lookup.
    iDestruct (big_sepM_delete _ _ l with "Hmap") as "((%descr & %Hvs_len & Hl & Hdescr) & Hmap)"; first done.
    rewrite decide_True //. iDestruct "Hdescr" as "(-> & Harr & Hvs)".
    opose proof* (list_lookup_lookup_total_lt vs i); first lia.
    wp_smart_apply (array_unsafe_get_spec i with "Harr") as "Harr"; [lia | done | lia |].
    iDestruct (big_sepL_insert_acc with "Hvs") as "(#Hvs!!!i & Hvs)"; first done.
    wp_smart_apply (wp_wand with "(Heq Hv Hvs!!!i)") as "% ->".
    wp_pures. case_bool_decide as Hcase; wp_pures.
    - iDestruct ("Hvs" with "Hv") as "Hvs".
      rewrite list_insert_id; first congruence.
      iDestruct (big_sepM_delete with "[Hl Harr Hvs $Hmap]") as "Hmap"; first done.
      { iExists _. rewrite decide_True //. iSteps. }
      iSteps.
    - wp_apply (array_unsafe_set_spec with "Harr") as "Harr"; first done. rewrite Nat2Z.id.
      wp_load. clear root. wp_alloc root as "Hroot". wp_store. wp_pures.
      iApply "HΦ".
      iAssert ⌜map !! root = None⌝%I as %Hmap_lookup_root.
      { rewrite -eq_None_ne_Some. iIntros "%vs_root %Hmap_lookup_root".
        iDestruct (pointsto_ne with "Hroot Hl") as %Hne.
        iDestruct (big_sepM_lookup _ _ root with "Hmap") as "(%descr & _ & Hroot_ & _)"; first rewrite lookup_delete_ne //.
        iDestruct (pointsto_ne with "Hroot Hroot_") as %[]. done.
      }
      set vs_root := <[i := v]> vs.
      iMod (parray_map_insert with "Hmap_auth") as "(Hmap_auth & #Hmap_elem_root)"; first done.
      iSplitR "Hmap_elem_root"; last iSteps. iExists (<[root := vs_root]> map), root. iFrame.
      iApply big_sepM_insert; first done. iSplitL "Hroot Harr Hvs".
      { iExists _. rewrite decide_True //. iSteps. rewrite insert_length //. }
      iApply (big_sepM_delete _ _ l); first done. iSplitL "Hl".
      { iExists _. rewrite decide_False; first congruence. iStep 2. iExists i, (vs !!! i), root, vs_root. iSteps.
        iPureIntro. rewrite /vs_root list_insert_insert list_insert_id //.
      }
      iApply (big_sepM_impl with "Hmap"). iIntros "!> !>" (l' vs'' (Hne & Hmap_lookup')%lookup_delete_Some) "(%descr' & %Hvs'_len & Hl' & Hdescr')".
      iExists _. rewrite decide_False // decide_False; first congruence. iFrame. iSteps.
  Qed.
End parray_G.

#[global] Opaque parray_make.
#[global] Opaque parray_get.
#[global] Opaque parray_set.

#[global] Opaque parray_inv.
#[global] Opaque parray_model.
