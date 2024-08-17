(* Based on:
   https://gitlab.com/basile.clement/store/-/blob/main/src/store.ml?ref_type=heads
*)

From iris.base_logic Require Import
  lib.ghost_map.

From zoo Require Import
  prelude.
From zoo.common Require Import
  list
  treemap.
From zoo.iris.base_logic Require Import
  lib.mono_map.
From zoo.language Require Import
  notations
  diaframe.
From zoo.std Require Import
  assert
  lst.
From zoo.persistent Require Export
  base
  pstore_2__code.
From zoo.persistent Require Import
  pstore_2__types.
From zoo Require Import
  options.

Implicit Types l r node cnode base root dst : location.
Implicit Types nodes : list location.
Implicit Types v t s : val.
Implicit Types σ : gmap location val.

Module raw.
  #[local] Definition generation :=
    nat.
  Implicit Types g : generation.

  #[local] Definition store :=
    gmap location (generation * val).
  Implicit Types ς : store.
  Implicit Types data : generation * val.

  #[local] Definition descriptor : Set :=
    generation * store.
  Implicit Types descr cnode_descr : descriptor.
  Implicit Types descrs : gmap location descriptor.

  Class PstoreG Σ `{zoo_G : !ZooG Σ} := {
    #[local] pstore_G_nodes_G :: ghost_mapG Σ location descriptor ;
  }.

  Definition pstore_Σ := #[
    ghost_mapΣ location descriptor
  ].
  #[global] Instance subG_pstore_Σ Σ `{zoo_G : !ZooG Σ} :
    subG pstore_Σ Σ →
    PstoreG Σ.
  Proof.
    solve_inG.
  Qed.

  Section pstore_G.
    Context `{pstore_G : PstoreG Σ}.

    #[local] Definition store_on σ0 ς :=
      ς ∪ (pair 0 <$> σ0).
    #[local] Definition store_generation g ς :=
      map_Forall (λ r data, data.1 ≤ g) ς.

    #[local] Definition descriptor_wf σ0 descr :=
      dom descr.2 ⊆ dom σ0 ∧
      store_generation descr.1 descr.2.

    #[local] Definition delta : Set :=
      location * (generation * val) * location.
    Implicit Types δ : delta.
    Implicit Types δs : list delta.
    Implicit Types path : list (list delta).
    #[local] Definition delta_ref δ :=
      δ.1.1.
    #[local] Definition delta_data δ :=
      δ.1.2.
    #[local] Definition delta_gen δ :=
      (delta_data δ).1.
    #[local] Definition delta_val δ :=
      (delta_data δ).2.
    #[local] Definition delta_node δ :=
      δ.2.

    #[local] Definition deltas_apply δs ς :=
      list_to_map δs.*1 ∪ ς.
    #[local] Fixpoint deltas_chain node δs dst : iProp Σ :=
      match δs with
      | [] =>
          ⌜node = dst⌝
      | δ :: δs =>
          node ↦ᵣ ’Diff( #(delta_ref δ), #(delta_gen δ), delta_val δ, #(delta_node δ) ) ∗
          deltas_chain (delta_node δ) δs dst
      end.

    #[local] Definition edge : Set :=
      location * list delta.
    Implicit Types ϵ : edge.
    Implicit Types ϵs : gmap location edge.

    #[local] Definition descriptors_auth γ descrs :=
      ghost_map_auth γ 1 descrs.
    #[local] Definition descriptors_elem γ cnode descr :=
      ghost_map_elem γ cnode DfracDiscarded descr.

    #[local] Definition cnode_model γ σ0 cnode descr ϵ ς : iProp Σ :=
      let cnode' := ϵ.1 in
      let δs := ϵ.2 in
      ⌜descriptor_wf σ0 descr⌝ ∗
      descriptors_elem γ cnode descr ∗
      ⌜NoDup $ delta_ref <$> δs⌝ ∗
      ⌜store_on σ0 descr.2 = store_on σ0 $ deltas_apply δs ς⌝ ∗
      deltas_chain cnode δs cnode'.
    Definition pstore_model t σ0 σ : iProp Σ :=
      ∃ l γ g root ς,
      ⌜t = #l⌝ ∗
      ⌜σ = snd <$> ς⌝ ∗
      meta l (nroot.@"impl") γ ∗
      l.[gen] ↦ #g ∗
      l.[root] ↦ #root ∗
      root ↦ᵣ §Root ∗
      ( [∗ map] r ↦ data ∈ store_on σ0 ς,
        r.[ref_gen] ↦ #data.1 ∗
        r.[ref_value] ↦ data.2
      ) ∗
      ⌜descriptor_wf σ0 (g, ς)⌝ ∗
      if decide (g = 0) then
        descriptors_auth γ ∅
      else
        ∃ descrs ϵs base descr δs,
        ⌜treemap_rooted ϵs base⌝ ∗
        descriptors_auth γ descrs ∗
        (* [base] cnode *)
        ⌜descrs !! base = Some descr⌝ ∗
        ⌜descr.1 < g⌝ ∗
        cnode_model γ σ0 base descr (root, δs) ς ∗
        ⌜δs = [] → ς = descr.2⌝ ∗
        ⌜Forall (λ δ, ∃ data, ς !! delta_ref δ = Some data ∧ data.1 = g) δs⌝ ∗
        (* other cnodes *)
        [∗ map] cnode ↦ descr; ϵ ∈ delete base descrs; ϵs,
          ∃ descr',
          ⌜descrs !! ϵ.1 = Some descr'⌝ ∗
          cnode_model γ σ0 cnode descr ϵ descr'.2.

    Definition pstore_snapshot s t σ : iProp Σ :=
      ∃ l γ g cnode descr,
      ⌜t = #l⌝ ∗
      ⌜s = (t, #g, #cnode)%V⌝ ∗
      ⌜σ = snd <$> descr.2⌝ ∗
      ⌜descr.1 ≤ g⌝ ∗
      meta l (nroot.@"impl") γ ∗
      descriptors_elem γ cnode descr.

    #[local] Instance deltas_chain_timeless node δs dst :
      Timeless (deltas_chain node δs dst).
    Proof.
      move: node. induction δs; apply _.
    Qed.
    #[global] Instance pstore_model_timeless t σ0 σ :
      Timeless (pstore_model t σ0 σ).
    Proof.
      rewrite /Timeless. iIntros "(%l & %γ & %g & H)".
      iExists l, γ, g.
      case_decide; iApply (timeless with "H").
    Qed.

    #[global] Instance pstore_snapshot_persistent s t σ :
      Persistent (pstore_snapshot s t σ).
    Proof.
      apply _.
    Qed.

    #[local] Lemma store_on_dom σ0 ς :
      dom (store_on σ0 ς) = dom σ0 ∪ dom ς.
    Proof.
      set_solver.
    Qed.
    #[local] Lemma store_on_dom' σ0 ς :
      dom ς ⊆ dom σ0 →
      dom (store_on σ0 ς) = dom σ0.
    Proof.
      set_solver.
    Qed.
    #[local] Lemma store_on_lookup {σ0 ς} r data :
      store_on σ0 ς !! r = Some data ↔
          ς !! r = Some data
        ∨ ς !! r = None ∧
          data.1 = 0 ∧
          σ0 !! r = Some data.2.
    Proof.
      destruct data as (g, v).
      rewrite lookup_union_Some_raw lookup_fmap_Some. naive_solver.
    Qed.
    #[local] Lemma store_on_lookup' {σ0 ς} r data :
      ς !! r = Some data →
      store_on σ0 ς !! r = Some data.
    Proof.
      apply lookup_union_Some_l.
    Qed.
    #[local] Lemma store_on_insert r data σ0 ς :
      store_on σ0 (<[r := data]> ς) = <[r := data]> (store_on σ0 ς).
    Proof.
      rewrite insert_union_l //.
    Qed.
    #[local] Lemma store_on_insert_support r v σ0 ς :
      σ0 !! r = None →
      dom ς ⊆ dom σ0 →
      store_on (<[r := v]> σ0) ς = <[r := (0, v)]> (store_on σ0 ς).
    Proof.
      intros Hr%not_elem_of_dom Hς_dom.
      assert (ς !! r = None).
      { apply not_elem_of_dom. set_solver. }
      rewrite insert_union_r // -fmap_insert //.
    Qed.
    #[local] Lemma store_on_deltas_apply σ0 δs ς :
      store_on σ0 (deltas_apply δs ς) = deltas_apply δs (store_on σ0 ς).
    Proof.
      rewrite /deltas_apply assoc //.
    Qed.

    #[local] Lemma store_generation_le {g ς} g' :
      g ≤ g' →
      store_generation g ς →
      store_generation g' ς.
    Proof.
      intros Hg Hς_gen.
      eapply map_Forall_impl; first done.
      naive_solver lia.
    Qed.
    #[local] Lemma store_generation_insert g ς r data :
      store_generation g ς →
      data.1 ≤ g →
      store_generation g (<[r := data]> ς).
    Proof.
      intros Hς_gen ?.
      apply map_Forall_insert_2; done.
    Qed.

    #[local] Lemma deltas_apply_nil ς :
      deltas_apply [] ς = ς.
    Proof.
      rewrite /deltas_apply list_to_map_nil left_id //.
    Qed.
    #[local] Lemma deltas_apply_cons δ δs ς :
      deltas_apply (δ :: δs) ς = <[delta_ref δ := delta_data δ]> (deltas_apply δs ς).
    Proof.
      destruct δ as ((r, data), suc).
      rewrite /deltas_apply list_to_map_cons insert_union_l //.
    Qed.
    #[local] Lemma deltas_apply_singleton δ ς :
      deltas_apply [δ] ς = <[delta_ref δ := delta_data δ]> ς.
    Proof.
      rewrite deltas_apply_cons deltas_apply_nil //.
    Qed.
    #[local] Lemma deltas_apply_app δs1 δs2 ς :
      deltas_apply (δs1 ++ δs2) ς = deltas_apply δs1 (deltas_apply δs2 ς).
    Proof.
      rewrite /deltas_apply fmap_app list_to_map_app assoc //.
    Qed.
    #[local] Lemma deltas_apply_snoc δs δ ς :
      deltas_apply (δs ++ [δ]) ς = deltas_apply δs (<[delta_ref δ := delta_data δ]> ς).
    Proof.
      rewrite deltas_apply_app deltas_apply_singleton //.
    Qed.
    #[local] Lemma deltas_apply_snoc' δs r data node ς :
      deltas_apply (δs ++ [(r, data, node)]) ς = deltas_apply δs (<[r := data]> ς).
    Proof.
      apply (deltas_apply_snoc _ (r, data, node)).
    Qed.
    #[local] Lemma deltas_apply_dom δs ς :
      dom (deltas_apply δs ς) = list_to_set (delta_ref <$> δs) ∪ dom ς.
    Proof.
      rewrite dom_union_L dom_list_to_map_L list_fmap_compose //.
    Qed.
    #[local] Lemma deltas_apply_lookup δs δ r data ς :
      NoDup (delta_ref <$> δs) →
      δ ∈ δs →
      r = delta_ref δ →
      data = delta_data δ →
      deltas_apply δs ς !! r = Some data.
    Proof.
      intros Hδs_nodup Hδ -> ->.
      apply lookup_union_Some_l, elem_of_list_to_map_1.
      - rewrite -list_fmap_compose //.
      - rewrite elem_of_list_fmap -surjective_pairing. eauto.
    Qed.
    #[local] Lemma deltas_apply_lookup' δs r data ς :
      NoDup (delta_ref <$> δs) →
      (r, data) ∈ δs.*1 →
      deltas_apply δs ς !! r = Some data.
    Proof.
      intros Hδs_nodup (((?, ?), ?) & [= <- <-] & Hδ)%elem_of_list_fmap.
      eapply deltas_apply_lookup; done.
    Qed.
    #[local] Lemma deltas_apply_lookup_ne r δs ς :
      NoDup (delta_ref <$> δs) →
      r ∉ (delta_ref <$> δs) →
      deltas_apply δs ς !! r = ς !! r.
    Proof.
      intros Hδs_nodup Hr.
      apply lookup_union_r, not_elem_of_list_to_map_1.
      rewrite -list_fmap_compose //.
    Qed.
    #[local] Lemma deltas_apply_permutation δs1 δs2 ς :
      NoDup (delta_ref <$> δs1) →
      δs1 ≡ₚ δs2 →
      deltas_apply δs1 ς = deltas_apply δs2 ς.
    Proof.
      intros. rewrite /deltas_apply (list_to_map_proper _ δs2.*1) //.
      { rewrite -list_fmap_compose //. }
      { f_equiv. done. }
    Qed.

    #[local] Lemma deltas_chain_cons src δ δs dst :
      src ↦ᵣ ’Diff( #(delta_ref δ), #(delta_gen δ), delta_val δ, #(delta_node δ) ) -∗
      deltas_chain (delta_node δ) δs dst -∗
        deltas_chain src (δ :: δs) dst.
    Proof.
      iSteps.
    Qed.
    #[local] Lemma deltas_chain_nil_inv src dst :
      deltas_chain src [] dst ⊢
      ⌜src = dst⌝.
    Proof.
      iSteps.
    Qed.
    #[local] Lemma deltas_chain_cons_inv src δ δs dst :
      deltas_chain src (δ :: δs) dst ⊢
        src ↦ᵣ ’Diff( #(delta_ref δ), #(delta_gen δ), delta_val δ, #(delta_node δ) ) ∗
        deltas_chain (delta_node δ) δs dst.
    Proof.
      iSteps.
    Qed.
    #[local] Lemma deltas_chain_snoc {src δs dst} r g v dst' :
      deltas_chain src δs dst -∗
      dst ↦ᵣ ’Diff( #r, #g, v, #dst' ) -∗
      deltas_chain src (δs ++ [(r, (g, v), dst')]) dst'.
    Proof.
      iInduction δs as [] "IH" forall (src); iSteps.
    Qed.
    #[local] Lemma deltas_chain_app_1 src δs1 δs2 dst :
      deltas_chain src (δs1 ++ δs2) dst ⊢
        let node := default src $ delta_node <$> last δs1 in
        deltas_chain src δs1 node ∗
        deltas_chain node δs2 dst.
    Proof.
      iIntros "Hδs".
      iInduction δs1 as [| δ1 δs1] "IH" forall (src); first iSteps.
      iDestruct "Hδs" as "(Hsrc & Hδs)".
      iDestruct ("IH" with "Hδs") as "(Hδs1 & Hδs2)".
      destruct δs1 as [| δ1' δs1]; first iSteps.
      rewrite last_cons_cons.
      assert (is_Some (last (δ1' :: δs1))) as (? & Heq).
      { rewrite last_is_Some //. }
      rewrite -> Heq in *. iSteps.
    Qed.
    #[local] Lemma deltas_chain_app_2 src δs1 node δs2 dst :
      deltas_chain src δs1 node -∗
      deltas_chain node δs2 dst -∗
      deltas_chain src (δs1 ++ δs2) dst.
    Proof.
      iIntros "Hδs1 Hδs2".
      iInduction δs1 as [] "IH" forall (src); last iSteps.
      iDestruct "Hδs1" as %<-. iSteps.
    Qed.
    #[local] Lemma deltas_chain_snoc_inv src δs δ dst :
      deltas_chain src (δs ++ [δ]) dst ⊢
        let node := default src $ delta_node <$> last δs in
        ⌜delta_node δ = dst⌝ ∗
        deltas_chain src δs node ∗
        node ↦ᵣ ’Diff( #(delta_ref δ), #(delta_gen δ), delta_val δ, #dst ).
    Proof.
      rewrite deltas_chain_app_1. iSteps.
    Qed.
    #[local] Lemma deltas_chain_lookup {src δs dst} i δ :
      δs !! i = Some δ →
      deltas_chain src δs dst ⊢
        deltas_chain src (take (S i) δs) (delta_node δ) ∗
        deltas_chain (delta_node δ) (drop (S i) δs) dst.
    Proof.
      iIntros "%δs_lookup Hδs".
      rewrite -{1}(take_drop (S i) δs).
      iDestruct (deltas_chain_app_1 with "Hδs") as "Hδs".
      rewrite {2 3}(take_S_r δs i δ) // last_snoc //.
    Qed.
    #[local] Lemma deltas_chain_lookup' {src δs dst} i δ :
      δs !! i = Some δ →
      deltas_chain src δs dst ⊢
        ∃ node,
        ⌜ if i is 0 then
            node = src
          else
            ∃ δ',
            δs !! pred i = Some δ' ∧
            delta_node δ' = node
        ⌝ ∗
        deltas_chain src (take i δs) node ∗
        node ↦ᵣ ’Diff( #(delta_ref δ), #(delta_gen δ), delta_val δ, #(delta_node δ) ) ∗
        deltas_chain (delta_node δ) (drop (S i) δs) dst.
    Proof.
      iIntros "%Hδs_lookup Hδs".
      iDestruct (deltas_chain_lookup with "Hδs") as "(Hδs1 & Hδs2)"; first done.
      rewrite (take_S_r δs i δ) //.
      destruct i; simpl; first iSteps.
      iDestruct (deltas_chain_snoc_inv with "Hδs1") as "(_ & Hδs1 & Hδ)".
      opose proof* (lookup_lt_is_Some_2 δs i) as (δ' & Hδs_lookup').
      { apply lookup_lt_Some in Hδs_lookup. lia. }
      rewrite {2 3}(take_S_r δs i δ') // last_snoc.
      iSteps.
    Qed.

    #[local] Definition descriptors_alloc root :
      ⊢ |==>
        ∃ γ,
        descriptors_auth γ ∅.
    Proof.
      iMod ghost_map_alloc as "(%γ & Hauth & _)".
      iSteps.
    Qed.
    #[local] Definition descriptors_lookup γ descrs cnode descr :
      descriptors_auth γ descrs -∗
      descriptors_elem γ cnode descr -∗
      ⌜descrs !! cnode = Some descr⌝.
    Proof.
      apply ghost_map_lookup.
    Qed.
    #[local] Lemma descriptors_insert {γ descrs} cnode descr :
      descrs !! cnode = None →
      descriptors_auth γ descrs ⊢ |==>
        descriptors_auth γ (<[cnode := descr]> descrs) ∗
        descriptors_elem γ cnode descr.
    Proof.
      iIntros "%Hdescrs_lookup Hauth".
      iMod (ghost_map_insert with "Hauth") as "($ & Helem)"; first done.
      iApply (ghost_map_elem_persist with "Helem").
    Qed.

    Lemma pstore_model_valid t σ0 σ :
      pstore_model t σ0 σ ⊢
      ⌜dom σ ⊆ dom σ0⌝.
    Proof.
      iIntros "(%l & %γ & %g & %root & %ς & -> & -> & #Hmeta & Hl_gen & Hl_root & Hroot & Hς & (%Hς_dom & %Hς_gen) & _)".
      rewrite dom_fmap //.
    Qed.

    Lemma pstore_create_spec :
      {{{ True }}}
        pstore_create ()
      {{{ t,
        RET t;
        (∃ l, ⌜t = #l⌝ ∗ meta_token l (↑nroot.@"user")) ∗
        pstore_model t ∅ ∅
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      wp_rec.
      wp_ref root as "Hroot".
      wp_block l as "Hmeta" "(Hl_gen & Hl_root & _)".

      iMod (descriptors_alloc root) as "(%γ & Hauth)".

      iDestruct (meta_token_difference _ (↑nroot.@"user") with "Hmeta") as "(Hmeta_user & Hmeta)"; first done.
      iDestruct (meta_token_difference _ (↑nroot.@"impl") with "Hmeta") as "(Hmeta & _)"; first solve_ndisj.
      iMod (meta_set with "Hmeta") as "Hmeta"; first done.

      iApply "HΦ".
      iStep. iExists l, γ, 0, root, ∅. iFrame. rewrite big_sepM_empty. iSteps.
    Qed.

    Lemma pstore_ref_spec t σ0 σ v :
      {{{
        pstore_model t σ0 σ
      }}}
        pstore_ref t v
      {{{ r,
        RET #r;
        ⌜σ0 !! r = None⌝ ∗
        pstore_model t (<[r := v]> σ0) σ
      }}}.
    Proof.
      iIntros "%Φ (%l & %γ & %g & %root & %ς & -> & -> & #Hmeta & Hl_gen & Hl_root & Hroot & Hς & (%Hς_dom & %Hς_gen) & Hmodel) HΦ".

      wp_rec. wp_block r as "(Hr_gen & Hr_value & _)".
      iAssert ⌜σ0 !! r = None⌝%I as %Hr.
      { rewrite -not_elem_of_dom. iIntros "%Hr".
        iDestruct (big_sepM_lookup with "Hς") as "(_Hr_gen & _)".
        { apply lookup_lookup_total_dom. rewrite store_on_dom' //. }
        iApply (pointsto_exclusive with "Hr_gen _Hr_gen").
      }
      iApply "HΦ".
      iSplitR; first iSteps. iExists l, γ, g, root, ς. iFrame "#∗". iStep 2.
      iSplitL "Hς Hr_gen Hr_value".
      { rewrite store_on_insert_support //.
        iApply (big_sepM_insert_2 with "[Hr_gen Hr_value] Hς").
        iSteps.
      }
      iSplitR. { iPureIntro. split; [set_solver | done]. }
      case_decide as Hg; first iSteps.
      iDecompose "Hmodel" as (descrs ϵs base descr δs Hϵs Hdescrs_lookup_base Hgen (Hstore_dom & Hstore_gen) Hδs_nodup Hδs Hδs_nil Hδs_gen) "Helem_base Hauth Hδs Hdescrs".
      iSteps; try iPureIntro.
      { set_solver. }
      { rewrite !store_on_insert_support //; last congruence.
        apply (f_equal dom) in Hδs. set_solver.
      } {
        iClear "Helem_base". clear dependent descr δs.
        iApply (big_sepM2_impl with "Hdescrs"). iIntros "!> !>" (cnode descr (cnode' & δs)) "%Hdescrs_lookup %Hϵs_lookup (%descr' & %Hdescrs_lookup' & ((%Hcnode_store_dom & %Hcnode_store_gen) & #Helem_cnode & %Hδs_nodup & %Hδs' & Hδs'))".
        simpl in *.
        iSteps; iPureIntro; first set_solver.
        rewrite !store_on_insert_support //; last congruence.
        apply (f_equal dom) in Hδs'. set_solver.
      }
    Qed.

    Lemma pstore_get_spec {t σ0 σ r} v :
      (σ ∪ σ0) !! r = Some v →
      {{{
        pstore_model t σ0 σ
      }}}
        pstore_get t #r
      {{{
        RET v;
        pstore_model t σ0 σ
      }}}.
    Proof.
      iIntros "%Hσ_lookup %Φ (%l & %γ & %g & %root & %ς & -> & -> & #Hmeta & Hl_gen & Hl_root & Hroot & Hς & (%Hς_dom & %Hς_gen) & Hmodel) HΦ".

      wp_rec.
      assert (∃ g_r, store_on σ0 ς !! r = Some (g_r, v)) as (g_r & Hς_lookup).
      { setoid_rewrite store_on_lookup.
        apply lookup_union_Some_raw in Hσ_lookup as [Hσ_lookup | (Hσ_lookup & Hσ0_lookup)].
        - apply lookup_fmap_Some in Hσ_lookup as ((g_r & _v) & ? & Hς_lookup).
          naive_solver.
        - rewrite lookup_fmap fmap_None in Hσ_lookup.
          naive_solver.
      }
      iDestruct (big_sepM_lookup_acc with "Hς") as "((Hr_gen & Hr_value) & Hς)"; first done.
      wp_load.
      iSteps.
    Qed.

    Lemma pstore_set_spec t σ0 σ r v :
      r ∈ dom σ0 →
      {{{
        pstore_model t σ0 σ
      }}}
        pstore_set t #r v
      {{{
        RET ();
        pstore_model t σ0 (<[r := v]> σ)
      }}}.
    Proof.
      iIntros "%Hr %Φ (%l & %γ & %g & %root & %ς & -> & -> & #Hmeta & Hl_gen & Hl_root & Hroot & Hς & (%Hς_dom & %Hς_gen) & Hmodel) HΦ".
      pose proof Hr as (w0 & Hσ0_lookup)%elem_of_dom.

      wp_rec. wp_load.
      assert (∃ g_r w, store_on σ0 ς !! r = Some (g_r, w) ∧ g_r ≤ g) as (g_r & w & Hς_lookup & Hg_r).
      { setoid_rewrite store_on_lookup.
        destruct (ς !! r) as [(g_r, w) |] eqn:Hς_lookup.
        - exists g_r, w. split; first naive_solver.
          opose proof* map_Forall_lookup_1; done.
        - exists 0, w0. split; first naive_solver. lia.
      }
      iDestruct (big_sepM_insert_acc with "Hς") as "((Hr_gen & Hr_value) & Hς)"; first done.
      wp_load. wp_pures.
      destruct (decide (g = 0)) as [-> | Hg].

      - assert (g_r = 0) as -> by lia.
        rewrite bool_decide_eq_true_2 //. wp_pures.
        wp_store.
        iDestruct ("Hς" $! (0, v) with "[$Hr_gen $Hr_value]") as "Hς".
        iApply "HΦ".
        iExists l, γ, 0, root, (<[r := (0, v)]> ς). iFrame "#∗". iStep.
        iSplitR. { rewrite fmap_insert //. }
        iSplitL. { rewrite insert_union_l //. }
        iPureIntro. split; first set_solver. apply map_Forall_insert_2; done.

      - destruct (decide (g = g_r)) as [<- | Hcase].

        + rewrite bool_decide_eq_true_2 //.
          wp_store.
          iDestruct ("Hς" $! (g, v) with "[$Hr_gen $Hr_value]") as "Hς".
          iApply "HΦ".
          iExists l, γ, g, root, (<[r := (g, v)]> ς). iFrame "#∗". iStep.
          iSplitR. { rewrite fmap_insert //. }
          iSplitL "Hς". { rewrite insert_union_l //. }
          iSplitR. { iPureIntro. split; first set_solver. apply map_Forall_insert_2; done. }
          rewrite decide_False //.
          iDecompose "Hmodel" as (descrs ϵs base descr δs Hϵs Hdescrs_lookup_base Hgen (Hstore_dom & Hstore_gen) Hδs_nodup Hδs Hδs_nil Hδs_gen) "Helem_base Hauth Hδs Hdescrs".
          iSteps; iPureIntro.
          { clear Hδs_nil Hδs_gen. generalize dependent ς.
            induction δs as [| ((r', (g', v')), node') δs IH] using rev_ind.
            all: intros ς Hς_dom Hς_gen Hς_lookup Hδs.
            - exfalso.
              rewrite deltas_apply_nil in Hδs.
              rewrite -Hδs store_on_lookup in Hς_lookup.
              destruct Hς_lookup as [Hstore_lookup |]; last naive_solver.
              opose proof* (map_Forall_lookup_1 _ descr.2); [done.. |].
              naive_solver lia.
            - rewrite deltas_apply_snoc /=.
              destruct (decide (r = r')) as [<- | Hr'].
              + rewrite deltas_apply_snoc /= in Hδs.
                rewrite insert_insert //.
              + rewrite insert_commute //.
                apply IH; simpl.
                * rewrite fmap_app NoDup_app in Hδs_nodup. naive_solver.
                * rewrite dom_insert union_subseteq singleton_subseteq_l.
                  split; last done.
                  apply (f_equal dom) in Hδs.
                  rewrite store_on_dom' // store_on_dom in Hδs.
                  rewrite Hδs deltas_apply_dom. set_solver.
                * apply map_Forall_insert_2; last done.
                  trans descr.1; last lia.
                  assert (store_on σ0 descr.2 !! r' = Some (g', v')) as [Hstore_lookup | (_ & ? & _)]%store_on_lookup.
                  { rewrite Hδs.
                    apply store_on_lookup', deltas_apply_lookup'; first done.
                    rewrite fmap_app. set_solver.
                  }
                  -- eapply map_Forall_lookup_1 in Hstore_gen; done.
                  -- simpl in *. lia.
                * rewrite /store_on -insert_union_l lookup_insert_ne //.
                * rewrite deltas_apply_snoc // in Hδs.
          } {
            intros ->. specialize (Hδs_nil eq_refl) as ->.
            exfalso.
            apply store_on_lookup in Hς_lookup as [].
            - opose proof* map_Forall_lookup_1; [done.. |].
              naive_solver lia.
            - naive_solver lia.
          } {
            eapply Forall_impl; first done. intros ((r', (g', v')), node) H.
            destruct (decide (r = r')) as [<- | Hr'].
            - rewrite lookup_insert. naive_solver.
            - rewrite lookup_insert_ne //.
          }

        + rewrite bool_decide_eq_false_2; first naive_solver. wp_pures.
          wp_ref root' as "Hroot'". do 2 wp_load. do 4 wp_store.
          iDestruct ("Hς" $! (g, v) with "[$Hr_gen $Hr_value]") as "Hς".
          iApply "HΦ".
          iExists l, γ, g, root', (<[r := (g, v)]> ς). iFrame "#∗". iStep.
          iSplitR. { rewrite fmap_insert //. }
          iSplitL "Hς". { rewrite insert_union_l //. }
          iSplitR. { iPureIntro. split; first set_solver. apply map_Forall_insert_2; done. }
          rewrite decide_False //.
          iDecompose "Hmodel" as (descrs ϵs base descr δs Hϵs Hdescrs_lookup_base Hgen (Hstore_dom & Hstore_gen) Hδs_nodup Hδs Hδs_nil Hδs_gen) "Helem_base Hauth Hδs Hdescrs".
          assert (r ∉ delta_ref <$> δs) as Hr_notin_δs.
          { intros (i & ((? & data) & -> & Hδs_lookup)%list_lookup_fmap_inv)%elem_of_list_lookup.
            opose proof* Forall_lookup_1 as H; [done.. |].
            apply store_on_lookup in Hς_lookup. naive_solver.
          }
          assert (store_on σ0 descr.2 !! r = Some (g_r, w)) as Hstore_lookup.
          { rewrite Hδs store_on_lookup deltas_apply_lookup_ne //.
            rewrite store_on_lookup // in Hς_lookup.
          }
          iDestruct (deltas_chain_snoc with "Hδs Hroot") as "Hδs".
          iExists _, _, _, _, (δs ++ [(r, (g_r, w), root')]). iSteps; iPureIntro.
          { rewrite fmap_app NoDup_app. split_and!; first done.
            - set_solver.
            - apply NoDup_singleton.
          } {
            rewrite deltas_apply_snoc insert_insert. cbn.
            erewrite <- deltas_apply_snoc'.
            rewrite (deltas_apply_permutation _ ((r, (g_r, w), root') :: δs)).
            { rewrite fmap_app NoDup_app. split_and!; first done.
              - cbn. set_solver.
              - apply NoDup_singleton.
            } {
              solve_Permutation.
            }
            rewrite deltas_apply_cons store_on_insert -Hδs insert_id //.
          } {
            intros []%symmetry%app_cons_not_nil.
          } {
            rewrite Forall_app Forall_singleton. split.
            - rewrite Forall_forall => δ Hδ. rewrite lookup_insert_ne.
              { rewrite elem_of_list_fmap in Hr_notin_δs. naive_solver. }
              rewrite Forall_forall in Hδs_gen. naive_solver.
            - rewrite lookup_insert. naive_solver.
          }
    Qed.

    Lemma pstore_capture_spec t σ0 σ :
      {{{
        pstore_model t σ0 σ
      }}}
        pstore_capture t
      {{{ s,
        RET s;
        pstore_model t σ0 σ ∗
        pstore_snapshot s t σ
      }}}.
    Proof.
      iIntros "%Φ (%l & %γ & %g & %root & %ς & -> & -> & #Hmeta & Hl_gen & Hl_root & Hroot & Hς & (%Hς_dom & %Hς_gen) & Hmodel) HΦ".

      wp_rec. wp_load. wp_store. wp_load. wp_pures.
      iApply "HΦ".
      case_decide as Hg; first subst.

      - pose descr := (0, ς).
        iMod (descriptors_insert root descr with "Hmodel") as "(Hauth & #Helem)"; first done.
        iSplitL; last first.
        { iSteps. iExists (0, ς). iSteps. }
        iExists l, γ, 1, root, ς. iFrame "#∗". iStep 2. iSplitR.
        { iPureIntro. split; first set_solver.
          eapply map_Forall_impl; first done. naive_solver.
        }
        iExists {[root := descr]}, ∅, root, descr, []. iSteps; try iPureIntro.
        { apply treemap_rooted_empty. }
        { rewrite lookup_insert //. }
        { rewrite NoDup_nil //. }
        { rewrite deltas_apply_nil //. }
        rewrite delete_singleton.
        iApply (big_sepM2_empty with "[//]").

      - iDecompose "Hmodel" as (descrs ϵs base descr δs Hϵs Hdescrs_lookup_base Hgen (Hstore_dom & Hstore_gen) Hδs_nodup Hδs Hδs_nil Hδs_gen) "Helem_base Hauth Hδs Hdescrs".
        destruct δs as [| δ δs]; simpl.

        + specialize (Hδs_nil eq_refl) as ->.
          iDestruct (deltas_chain_nil_inv with "Hδs") as %<-.
          iSplitL; iSteps.
          { iPureIntro. eapply map_Forall_impl; first done. naive_solver lia. }
          rewrite decide_False; first lia.
          iSteps.

        + iAssert ⌜ϵs !! base = None⌝%I as %Hϵs_lookup_base.
          { rewrite -eq_None_ne_Some. iIntros "%ϵ %Hϵs_lookup".
            iDestruct (big_sepM2_lookup_r with "Hdescrs") as "(%descr' & %Hdescrs_lookup & _)"; first done.
            rewrite lookup_delete // in Hdescrs_lookup.
          }
          iAssert ⌜descrs !! root = None⌝%I as %Hdescrs_lookup_root.
          { destruct (decide (root = base)) as [-> | Hcase].
            - iDestruct (deltas_chain_cons_inv with "Hδs") as "(Hbase & _)".
              iDestruct (pointsto_exclusive with "Hroot Hbase") as %[].
            - rewrite -eq_None_ne_Some. iIntros "%descr' %Hdescrs_lookup".
              iDestruct (big_sepM2_lookup_l with "Hdescrs") as ((cnode' & δs')) "(%Hϵs_lookup_root & %descr'' & _ & _ & _ & _ & _ & Hδs') /=".
              { rewrite lookup_delete_Some //. }
              destruct δs' as [| δ' δs'].
              + iDestruct (deltas_chain_nil_inv with "Hδs'") as %<-.
                opose proof* treemap_rooted_acyclic as []; done.
              + iDestruct (deltas_chain_cons_inv with "Hδs'") as "(_Hroot & _)".
                iApply (pointsto_exclusive with "Hroot _Hroot").
          }
          iAssert ⌜ϵs !! root = None⌝%I as %Hϵs_lookup_root.
          { iDestruct (big_sepM2_lookup_iff with "Hdescrs") as %H.
            iPureIntro.
            rewrite eq_None_not_Some -{}H. intros (_ & [])%lookup_delete_is_Some. congruence.
          }
          pose root_descr := (g, ς).
          iMod (descriptors_insert root root_descr with "Hauth") as "(Hauth & #Helem_root)"; first done.
          iSplitL; last first.
          { iSteps. iExists root_descr. iSteps. }
          iExists l, γ, (S g), root, ς. iFrame "#∗". iStep 3.
          iSplitR; first iSteps.
          set ϵ := (root, δ :: δs).
          iExists _, (<[base := ϵ]> ϵs), root, root_descr, []. iSteps; try iPureIntro.
          { eapply treemap_rooted_lift; [done.. | congruence]. }
          { rewrite lookup_insert //. }
          { rewrite NoDup_nil //. }
          { rewrite deltas_apply_nil //. }
          rewrite delete_insert //.
          iApply big_sepM2_delete_l; first done.
          iExists ϵ. iSteps.
          { rewrite lookup_insert //. }
          iExists root_descr. iSteps.
          { iPureIntro. rewrite lookup_insert //. }
          rewrite delete_insert //.
          iClear "Helem_base". clear dependent descr δs.
          iApply (big_sepM2_impl with "Hdescrs"). iIntros "!>" (cnode descr (cnode' & δs)) "%Hdescrs_lookup %Hϵs_lookup_cnode (%descr' & %Hdescrs_lookup' & ((%Hcnode_store_dom & %Hcnode_store_gen) & #Helem_cnode & %Hδs_nodup & %Hδs' & Hδs'))".
          simpl in *.
          iExists descr'. iSteps.
          rewrite lookup_insert_ne //. congruence.
    Qed.

    #[local] Definition pstore_collect_inv γ σ0 root ς descrs ϵs base descr δs : iProp Σ :=
      root ↦ᵣ §Root ∗
      ( [∗ map] r ↦ data ∈ store_on σ0 ς,
        r.[ref_gen] ↦ #data.1 ∗
        r.[ref_value] ↦ data.2
      ) ∗
      ⌜treemap_rooted ϵs base⌝ ∗
      descriptors_auth γ descrs ∗
      (* [base] cnode *)
      ⌜descrs !! base = Some descr⌝ ∗
      cnode_model γ σ0 base descr (root, δs) ς ∗
      ⌜δs = [] → ς = descr.2⌝ ∗
      (* other cnodes *)
      [∗ map] cnode ↦ descr; ϵ ∈ delete base descrs; ϵs,
        ∃ descr',
        ⌜descrs !! ϵ.1 = Some descr'⌝ ∗
        cnode_model γ σ0 cnode descr ϵ descr'.2.
    #[local] Lemma pstore_collect_spec_base_chain {γ σ0 root ς descrs ϵs base descr δs} i δ node acc :
      δs !! i = Some δ →
      delta_node δ = node →
      {{{
        pstore_collect_inv γ σ0 root ς descrs ϵs base descr δs
      }}}
        pstore_collect #node acc
      {{{ acc',
        RET (#root, acc');
        pstore_collect_inv γ σ0 root ς descrs ϵs base descr δs ∗
        plst_model acc' acc $ tail $
          (λ δ, #(delta_node δ)) <$> reverse (drop i δs)
      }}}.
    Proof.
      iLöb as "HLöb" forall (i δ node acc).

      iIntros "%Hδs_lookup %Hnode %Φ (Hroot & Hς & %Hϵs & Hauth & %Hdescrs_lookup_base & ((%Hstore_dom & %Hstore_gen) & #Helem_base & %Hδs_nodup & %Hδs & Hδs) & %Hδs_nil & Hdescrs) HΦ".
      simpl in *.

      wp_rec.
      iDestruct (deltas_chain_lookup i δ with "Hδs") as "(Hδs1 & Hδs2)"; first done.
      rewrite Hnode.
      destruct (drop (S i) δs) as [| δ' δs'] eqn:Hdrop_δs.

      - iDestruct (deltas_chain_nil_inv with "Hδs2") as %->.
        iDestruct (deltas_chain_app_2 with "Hδs1 Hδs2") as "Hδs".
        rewrite -Hdrop_δs take_drop (drop_S δs δ i) // Hdrop_δs /=.
        wp_load.
        iSteps.

      - iDestruct (deltas_chain_cons_inv with "Hδs2") as "(Hδ' & Hδs2)".
        wp_load.
        assert (δs !! S i = Some δ') as Hδs_lookup'.
        { rewrite -(take_drop (S i) δs) Hdrop_δs lookup_app_r take_length; first lia.
          rewrite Nat.min_l.
          { apply lookup_lt_Some in Hδs_lookup. lia. }
          rewrite Nat.sub_diag //.
        }
        assert (drop (S (S i)) δs = δs') as Hdrop_δs'.
        { erewrite drop_S in Hdrop_δs; [congruence | done]. }
        wp_smart_apply ("HLöb" $! (S i) δ' with "[//] [//] [- HΦ]") as (acc') "(Hinv & %Hacc')".
        { iDestruct (deltas_chain_cons with "Hδ' Hδs2") as "Hδs2".
          iDestruct (deltas_chain_app_2 with "Hδs1 Hδs2") as "Hδs".
          rewrite -Hdrop_δs take_drop. iSteps.
        }
        iSteps. iPureIntro.
        rewrite /plst_model' Hacc' -plst_to_val_singleton plst_to_val_app. f_equal.
        rewrite (drop_S δs δ i) // reverse_cons fmap_app /= Hnode tail_app //.
        rewrite Hdrop_δs reverse_cons fmap_app /=.
        symmetry. apply app_cons_not_nil.
    Qed.
    #[local] Definition pstore_collect_specification γ σ0 root ς descrs ϵs base descr δs : iProp Σ :=
      ∀ cnode cnode_descr path acc,
      {{{
        ⌜descrs !! cnode = Some cnode_descr⌝ ∗
        ⌜treemap_path ϵs base cnode path⌝ ∗
        pstore_collect_inv γ σ0 root ς descrs ϵs base descr δs
      }}}
        pstore_collect #cnode acc
      {{{ acc',
        RET (#root, acc');
        pstore_collect_inv γ σ0 root ς descrs ϵs base descr δs ∗
        plst_model acc' acc $ tail $
          ((λ δ, #(delta_node δ)) <$> reverse δs) ++
          ((λ δ, #(delta_node δ)) <$> reverse (concat path)) ++
          [ #cnode]
      }}}.
    #[local] Lemma pstore_collect_spec_chain {γ σ0 root ς descrs ϵs base descr δs} cnode ϵ i 𝝳 node path acc :
      ϵs !! cnode = Some ϵ →
      ϵ.2 !! i = Some 𝝳 →
      delta_node 𝝳 = node →
      treemap_path ϵs base ϵ.1 path →
      {{{
        pstore_collect_inv γ σ0 root ς descrs ϵs base descr δs ∗
        pstore_collect_specification γ σ0 root ς descrs ϵs base descr δs
      }}}
        pstore_collect #node acc
      {{{ acc',
        RET (#root, acc');
        pstore_collect_inv γ σ0 root ς descrs ϵs base descr δs ∗
        plst_model acc' acc $ tail $
          ((λ δ, #(delta_node δ)) <$> reverse δs) ++
          ((λ δ, #(delta_node δ)) <$> reverse (concat path)) ++
          ((λ δ, #(delta_node δ)) <$> reverse (drop i ϵ.2))
      }}}.
    Proof.
      destruct ϵ as (cnode', 𝝳s).

      iLöb as "HLöb" forall (i 𝝳 node acc).

      iIntros "%Hϵs_lookup %H𝝳s_lookup %Hnode %Hpath %Φ ((Hroot & Hς & %Hϵs & Hauth & %Hdescrs_lookup_base & ((%Hstore_dom & %Hstore_gen) & #Helem_base & %Hδs_nodup & %Hδs & Hδs) & %Hδs_nil & Hdescrs) & #Hspec) HΦ".
      simpl in *.

      iAssert (∃ descr, ⌜delete base descrs !! cnode = Some descr⌝)%I as "(%cnode_descr & %Hdescrs_lookup)".
      { iDestruct (big_sepM2_lookup_r with "Hdescrs") as "(% & % & _)"; first done.
        iSteps.
      }
      iDestruct (big_sepM2_lookup_acc with "Hdescrs") as "((%cnode_descr' & %Hdescrs_lookup' & (%Hcnode_store_dom & %Hcnode_store_gen) & #Helem_cnode & %H𝝳s_nodup & %H𝝳s & H𝝳s) & Hdescrs)"; [done.. |].
      iDestruct (deltas_chain_lookup i 𝝳 with "H𝝳s") as "(H𝝳s1 & H𝝳s2)"; first done.
      rewrite Hnode /=.
      destruct (drop (S i) 𝝳s) as [| 𝝳' 𝝳s'] eqn:Hdrop_𝝳s.

      - iDestruct (deltas_chain_nil_inv with "H𝝳s2") as %->.
        iDestruct (deltas_chain_app_2 with "H𝝳s1 H𝝳s2") as "H𝝳s".
        rewrite -Hdrop_𝝳s take_drop (drop_S 𝝳s 𝝳 i) // Hdrop_𝝳s /=.
        wp_apply ("Hspec" with "[- HΦ]") as (acc') "(Hinv & %Hacc')"; first iSteps.
        rewrite Hnode. iSteps.

      - iDestruct (deltas_chain_cons_inv with "H𝝳s2") as "(H𝝳' & H𝝳s2)".
        wp_rec. wp_load.
        assert (𝝳s !! S i = Some 𝝳') as H𝝳s_lookup'.
        { rewrite -(take_drop (S i) 𝝳s) Hdrop_𝝳s lookup_app_r take_length; first lia.
          rewrite Nat.min_l.
          { apply lookup_lt_Some in H𝝳s_lookup. lia. }
          rewrite Nat.sub_diag //.
        }
        assert (drop (S (S i)) 𝝳s = 𝝳s') as Hdrop_𝝳s'.
        { erewrite drop_S in Hdrop_𝝳s; [congruence | done]. }
        wp_smart_apply ("HLöb" $! (S i) 𝝳' with "[//] [//] [//] [//] [- HΦ]") as (acc') "(Hinv & %Hacc')".
        { iDestruct (deltas_chain_cons with "H𝝳' H𝝳s2") as "H𝝳s2".
          iDestruct (deltas_chain_app_2 with "H𝝳s1 H𝝳s2") as "H𝝳s".
          iFrame "Hspec".
          rewrite -Hdrop_𝝳s take_drop. iSteps.
        }
        iSteps. iPureIntro.
        rewrite /plst_model' Hacc' -plst_to_val_singleton plst_to_val_app. f_equal.
        rewrite (drop_S 𝝳s 𝝳 i) // reverse_cons fmap_app /= Hnode 2!(assoc _ _ _ [_]) -tail_app //.
        rewrite Hdrop_𝝳s reverse_cons fmap_app /= 2!assoc.
        symmetry. apply app_cons_not_nil.
    Qed.
    #[local] Lemma pstore_collect_spec {γ σ0 root ς descrs ϵs base descr δs} cnode cnode_descr path acc :
      descrs !! cnode = Some cnode_descr →
      treemap_path ϵs base cnode path →
      {{{
        pstore_collect_inv γ σ0 root ς descrs ϵs base descr δs
      }}}
        pstore_collect #cnode acc
      {{{ acc',
        RET (#root, acc');
        pstore_collect_inv γ σ0 root ς descrs ϵs base descr δs ∗
        plst_model acc' acc $ tail $
          ((λ δ, #(delta_node δ)) <$> reverse δs) ++
          ((λ δ, #(delta_node δ)) <$> reverse (concat path)) ++
          [ #cnode]
      }}}.
    Proof.
      iLöb as "HLöb" forall (cnode cnode_descr path acc).

      iIntros "%Hdescrs_lookup %Hpath %Φ (Hroot & Hς & %Hϵs & Hauth & %Hdescrs_lookup_base & ((%Hstore_dom & %Hstore_gen) & #Helem_base & %Hδs_nodup & %Hδs & Hδs) & %Hδs_nil & Hdescrs) HΦ".
      simpl in *.

      wp_rec.
      destruct (decide (cnode = base)) as [-> | Hcnode].

      - apply treemap_path_is_nil in Hpath as ->; last done.
        destruct δs as [| δ δs].

        + iDestruct (deltas_chain_nil_inv with "Hδs") as %<-.
          iSteps.

        + iDestruct (deltas_chain_cons_inv with "Hδs") as "(Hδ & Hδs)".
          wp_load.
          iDestruct (deltas_chain_cons with "Hδ Hδs") as "Hδs".
          wp_smart_apply (pstore_collect_spec_base_chain (δs := δ :: δs) 0 δ with "[- HΦ]") as (acc') "(Hinv & %Hacc')"; [done.. | |].
          { iFrame. iSteps. }
          iSteps. iPureIntro.
          rewrite /plst_model' Hacc' -plst_to_val_singleton plst_to_val_app. f_equal.
          rewrite -tail_app // reverse_cons fmap_app.
          symmetry. apply app_cons_not_nil.

      - apply treemap_path_is_cons in Hpath as (cnode' & 𝝳s & path' & -> & Hϵs_lookup & Hpath'); [| done..].
        assert (delete base descrs !! cnode = Some cnode_descr) as Hdelete_descrs_lookup.
        { rewrite lookup_delete_ne //. }
        iDestruct (big_sepM2_lookup_acc with "Hdescrs") as "((%cnode_descr' & %Hdescrs_lookup' & (%Hcnode_store_dom & %Hcnode_store_gen) & #Helem_cnode & %H𝝳s_nodup & %H𝝳s & H𝝳s) & Hdescrs)"; [done.. |].
        destruct 𝝳s as [| 𝝳 𝝳s].

        + iDestruct (deltas_chain_nil_inv with "H𝝳s") as %[= <-].
          opose proof* treemap_rooted_acyclic as []; done.

        + iDestruct (deltas_chain_cons_inv with "H𝝳s") as "(H𝝳 & H𝝳s)".
          wp_load.
          iDestruct (deltas_chain_cons with "H𝝳 H𝝳s") as "H𝝳s".
          wp_smart_apply (pstore_collect_spec_chain cnode _ 0 𝝳 with "[- HΦ]") as (acc') "(Hinv & %Hacc')"; [done.. | |].
          { iSplitL; first (iFrame; iSteps).
            iClear "Helem_cnode". clear.
            iIntros "%cnode %cnode_descr %path %acc !> %Φ (%Hdescrs_lookup & %Hpath & Hinv) HΦ".
            wp_apply ("HLöb" with "[//] [//] Hinv HΦ").
          }
          iSteps. iPureIntro.
          rewrite /plst_model' Hacc' -plst_to_val_singleton plst_to_val_app. f_equal.
          rewrite reverse_cons rev_append_rev rev_app_distr !rev_alt !fmap_app !assoc -tail_app //.
          symmetry. apply app_cons_not_nil.
    Qed.

    #[local] Definition pstore_revert_pre_1 γ σ0 root ς descrs ϵs base descr δs : iProp Σ :=
      ∃ v_root,
      root ↦ᵣ v_root ∗
      ( [∗ map] r ↦ data ∈ store_on σ0 ς,
        r.[ref_gen] ↦ #data.1 ∗
        r.[ref_value] ↦ data.2
      ) ∗
      ⌜treemap_rooted ϵs base⌝ ∗
      descriptors_auth γ descrs ∗
      (* [base] cnode *)
      ⌜descrs !! base = Some descr⌝ ∗
      cnode_model γ σ0 base descr (root, δs) ς ∗
      ⌜δs = [] → ς = descr.2⌝ ∗
      (* other cnodes *)
      [∗ map] cnode ↦ descr; ϵ ∈ delete base descrs; ϵs,
        ∃ descr',
        ⌜descrs !! ϵ.1 = Some descr'⌝ ∗
        cnode_model γ σ0 cnode descr ϵ descr'.2.
    #[local] Definition pstore_revert_pre_2 γ σ0 ς descrs ϵs base base_descr δs_base cnode cnode_descr δs_cnode node : iProp Σ :=
      ∃ v_node,
      node ↦ᵣ v_node ∗
      ( [∗ map] r ↦ data ∈ store_on σ0 ς,
        r.[ref_gen] ↦ #data.1 ∗
        r.[ref_value] ↦ data.2
      ) ∗
      ⌜treemap_rooted ϵs base⌝ ∗
      descriptors_auth γ descrs ∗
      (* [base] cnode *)
      ⌜descrs !! base = Some base_descr⌝ ∗
      cnode_model γ σ0 base base_descr (node, δs_base) ς ∗
      (* [cnode] cnode *)
      ⌜descrs !! cnode = Some cnode_descr⌝ ∗
      cnode_model γ σ0 cnode cnode_descr (node, δs_cnode) ς ∗
      (* other cnodes *)
      [∗ map] cnode ↦ descr; ϵ ∈ delete base $ delete cnode descrs; delete cnode ϵs,
        ∃ descr',
        ⌜descrs !! ϵ.1 = Some descr'⌝ ∗
        cnode_model γ σ0 cnode descr ϵ descr'.2.
    #[local] Definition pstore_revert_post γ σ0 descrs ϵs base descr : iProp Σ :=
      base ↦ᵣ §Root ∗
      ( [∗ map] r ↦ data ∈ store_on σ0 descr.2,
        r.[ref_gen] ↦ #data.1 ∗
        r.[ref_value] ↦ data.2
      ) ∗
      ⌜treemap_rooted ϵs base⌝ ∗
      descriptors_auth γ descrs ∗
      (* [base] cnode *)
      cnode_model γ σ0 base descr (base, []) descr.2 ∗
      (* other cnodes *)
      [∗ map] cnode ↦ descr; ϵ ∈ delete base descrs; ϵs,
        ∃ descr',
        ⌜descrs !! ϵ.1 = Some descr'⌝ ∗
        cnode_model γ σ0 cnode descr ϵ descr'.2.
    #[local] Lemma pstore_revert_spec_aux {γ σ0 ς descrs ϵs base base_descr δs_base cnode cnode_descr δs_cnode node} base' base_descr' path δs acc :
      descrs !! base' = Some base_descr' →
      treemap_path ϵs cnode base' path →
      ϵs !! cnode = Some (base, δs) →
      0 < length δs_cnode →
      NoDup (delta_ref <$> δs_cnode ++ δs_base) →
      lst_model' acc $ tail $
        ((λ δ, #(delta_node δ)) <$> reverse δs_cnode) ++
        ((λ δ, #(delta_node δ)) <$> reverse (concat path)) ++
        [ #base'] →
      {{{
        pstore_revert_pre_2 γ σ0 ς descrs ϵs base base_descr δs_base cnode cnode_descr δs_cnode node
      }}}
        pstore_revert #node acc
      {{{ ϵs,
        RET ();
        pstore_revert_post γ σ0 descrs ϵs base' base_descr'
      }}}.
    Proof.
      iLöb as "HLöb" forall (ς ϵs base base_descr δs_base cnode cnode_descr δs_cnode node path δs acc).

      iIntros (Hdescr_lookup_base' Hpath Hϵs_lookup_cnode Hδs_cnode_length Hnodup ->) "%Φ (%v_node & Hnode & Hς & %Hϵs & Hauth & %Hdescrs_lookup_base & ((%Hbase_store_dom & %Hbase_store_gen) & #Helem_base & %Hδs_base_nodup & %Hδs_base & Hδs_base) & %Hdescrs_lookup_cnode & ((%Hcnode_store_dom & %Hcnode_store_gen) & #Helem_cnode & %Hδs_cnode_nodup & %Hδs_cnode & Hδs_cnode) & Hdescrs) HΦ".

      destruct (rev_elim δs_cnode) as [-> | (δs_cnode_ & ((r1, (g1, v1)), _node) & ->)]; first naive_solver lia.
      simpl in *.
      iDestruct (deltas_chain_snoc_inv with "Hδs_cnode") as "(%Hnode & Hδs_cnode & Hδ)".
      simplify.

      wp_rec.
      destruct (rev_elim δs_cnode_) as [-> | (δs_cnode & ((r2, (g2, v2)), node') & ->)].

      - iDestruct (deltas_chain_nil_inv with "Hδs_cnode") as %->.
        simpl in *.
        destruct (rev_elim path) as [-> | (path' & δs_cnode' & ->)]; simpl.

        + apply treemap_path_nil_inv in Hpath as <-.
          wp_load.
          wp_smart_apply assert_spec; first rewrite bool_decide_eq_true_2 //.
          assert (∃ data, store_on σ0 ς !! r1 = Some data) as ((g1', v1') & Hς_lookup).
          { apply elem_of_dom.
            apply (f_equal dom) in Hδs_cnode.
            set_solver.
          }
          iDestruct (big_sepM_insert_acc with "Hς") as "((Hr_gen & Hr_value) & Hς)"; first done.
          do 2 wp_load. do 3 wp_store. wp_pures. wp_rec. wp_store.
          iDestruct ("Hς" with "[$Hr_gen $Hr_value]") as "Hς".
          rewrite deltas_apply_singleton store_on_insert in Hδs_cnode.
          rewrite -Hδs_cnode.
          set δs_base' := δs_base ++ [(r1, (g1', v1'), base')].
          opose proof* (treemap_reroot_rooted _ _ δs_base') as Hϵs'; [done.. |].
          iApply "HΦ".
          simplify. iSteps; try iPureIntro.
          { apply NoDup_nil_2. }
          { rewrite deltas_apply_nil //. }
          { rewrite -{2}(insert_id (delete base' descrs) base base_descr).
            { rewrite lookup_delete_ne //.
              eapply (treemap_rooted_acyclic (tree := ϵs)); done.
            }
            rewrite -insert_delete_insert.
            iApply (big_sepM2_insert_2 with "[- Hdescrs] Hdescrs").
            iSteps; try iPureIntro.
            { rewrite /δs_base' -Permutation_cons_append //. }
            { rewrite Hδs_base (store_on_deltas_apply _ _ base_descr'.2) Hδs_cnode.
              rewrite (deltas_apply_permutation δs_base' (δs_base ++ [(r1, (g1', v1'), base')])) //.
              { rewrite /δs_base' -Permutation_cons_append //. }
              rewrite deltas_apply_snoc insert_insert insert_id // store_on_deltas_apply //.
            } {
              iApply (deltas_chain_snoc with "Hδs_base Hnode").
            }
          }

        + pose proof Hpath as (cnode' & Hpath' & (? & Hϵs_lookup_cnode' & ->%treemap_path_nil_inv)%treemap_path_cons_inv)%treemap_path_app_inv.
          rewrite concat_app reverse_app fmap_app /= right_id.
          assert (cnode' ≠ cnode).
          { eapply treemap_rooted_acyclic; done. }
          assert (cnode' ≠ base).
          { pose proof Hϵs as ?%treemap_rooted_root. congruence. }
          iDestruct (big_sepM2_delete_r with "Hdescrs") as "(%cnode_descr' & %Hdescrs_lookup_cnode' & (%cnode_descr_ & %Hdescrs_lookup_cnode_ & ((%cnode_descr_dom' & %cnode_descr_gen') & #Helem_cnode' & %Hδs_cnode'_nodup & %Hδs_cnode' & Hδs_cnode')) & Hdescrs)".
          { rewrite lookup_delete_ne //. }
          simpl in *.
          rewrite Hdescrs_lookup_cnode in Hdescrs_lookup_cnode_. injection Hdescrs_lookup_cnode_ as <-.
          destruct (rev_elim δs_cnode') as [-> | (δs_cnode'' & ((r2, (g2, v2)), cnode_) & ->)].
          { iDestruct (deltas_chain_nil_inv with "Hδs_cnode'") as %<-.
            opose proof* treemap_rooted_acyclic as []; done.
          }
          rewrite reverse_snoc. cbn.
          iDestruct (deltas_chain_snoc_inv with "Hδs_cnode'") as "(%Hcnode & Hδs_cnode' & Hδ')".
          simpl in Hcnode. subst cnode_.
          wp_load.
          iDestruct (deltas_chain_snoc with "Hδs_cnode' Hδ'") as "Hδs_cnode'".
          wp_smart_apply assert_spec; first rewrite bool_decide_eq_true_2 //.
          assert (∃ data, store_on σ0 ς !! r1 = Some data) as ((g1', v1') & Hς_lookup).
          { apply elem_of_dom.
            apply (f_equal dom) in Hδs_cnode.
            set_solver.
          }
          iDestruct (big_sepM_insert_acc with "Hς") as "((Hr_gen & Hr_value) & Hς)"; first done.
          do 2 wp_load. do 3 wp_store.
          iDestruct ("Hς" $! (g1, v1) with "[$Hr_gen $Hr_value]") as "Hς".
          rewrite deltas_apply_singleton store_on_insert in Hδs_cnode.
          rewrite -Hδs_cnode.
          set δs_base' := δs_base ++ [(r1, (g1', v1'), cnode)].
          set ϵs' := treemap_reroot ϵs base cnode δs_base'.
          opose proof* (treemap_reroot_rooted cnode _ δs_base') as Hϵs'; [done.. |].
          wp_smart_apply ("HLöb" $! _ ϵs' cnode cnode_descr [] cnode' cnode_descr' (δs_cnode'' ++ [_]) with "[] [] [] [] [] [] [- HΦ]"); try iPureIntro; try done.
          { eapply treemap_reroot_path; done. }
          { rewrite lookup_insert_ne // lookup_delete_ne //. }
          { rewrite app_length /=. lia. }
          { rewrite right_id //. }
          { rewrite reverse_snoc assoc //. }
          iSteps; try iPureIntro.
          { apply NoDup_nil_2. }
          { rewrite deltas_apply_nil //. }
          { do 2 rewrite lookup_delete_ne // in Hdescrs_lookup_cnode'. }
          { rewrite (delete_commute _ cnode' base) (delete_commute _ cnode cnode') delete_insert_ne //.
            rewrite -{2}(insert_delete (delete cnode' $ delete cnode descrs) base base_descr).
            { rewrite lookup_delete_ne // lookup_delete_ne //.
              eapply (treemap_rooted_acyclic (tree := ϵs)); done.
            }
            iApply (big_sepM2_insert_2 with "[- Hdescrs] Hdescrs").
            iSteps; try iPureIntro.
            { rewrite /δs_base' -Permutation_cons_append //. }
            { rewrite Hδs_base (store_on_deltas_apply _ _ cnode_descr.2) Hδs_cnode.
              rewrite (deltas_apply_permutation δs_base' (δs_base ++ [(r1, (g1', v1'), cnode)])) //.
              { rewrite /δs_base' -Permutation_cons_append //. }
              rewrite deltas_apply_snoc insert_insert insert_id // store_on_deltas_apply //.
            } {
              iApply (deltas_chain_snoc with "Hδs_base Hnode").
            }
          }

      - rewrite 2!reverse_snoc.
        iDestruct (deltas_chain_snoc_inv with "Hδs_cnode") as "(_ & Hδs_cnode & Hδ')".
        rewrite !last_snoc. cbn.
        wp_load.
        wp_smart_apply assert_spec; first rewrite bool_decide_eq_true_2 //.
        assert (∃ data, store_on σ0 ς !! r1 = Some data) as ((g1', v1') & Hς_lookup).
        { apply elem_of_dom.
          rewrite deltas_apply_snoc in Hδs_cnode.
          apply (f_equal dom) in Hδs_cnode.
          set_solver.
        }
        iDestruct (big_sepM_insert_acc with "Hς") as "((Hr_gen & Hr_value) & Hς)"; first done.
        do 2 wp_load. do 3 wp_store.
        iDestruct ("Hς" $! (g1, v1) with "[$Hr_gen $Hr_value]") as "Hς".
        rewrite -store_on_insert.
        iDestruct (deltas_chain_snoc with "Hδs_base Hnode") as "Hδs_base".
        iDestruct (deltas_chain_snoc with "Hδs_cnode Hδ'") as "Hδs_cnode".
        set ς' := <[r1 := (g1, v1)]> ς.
        set δs_base' := δs_base ++ [(r1, (g1', v1'), node')].
        set δs_cnode' := δs_cnode ++ [(r2, (g2, v2), node')].
        wp_smart_apply ("HLöb" $! ς' _ base base_descr δs_base' cnode cnode_descr δs_cnode' with "[] [] [] [] [] [] [- HΦ]"); try iPureIntro; try done.
        { rewrite app_length /=. lia. }
        { rewrite -assoc (comm _ [_]) assoc fmap_app in Hnodup.
          rewrite /δs_cnode' /δs_base' assoc fmap_app //.
        }
        { rewrite reverse_app //. }
        iSteps; try iPureIntro.
        { rewrite -assoc fmap_app in Hnodup.
          apply NoDup_app in Hnodup as (_ & _ & Hnodup).
          rewrite /δs_base' Permutation_app_comm //.
        } {
          rewrite deltas_apply_snoc insert_insert store_on_deltas_apply store_on_insert insert_id // -store_on_deltas_apply //.
        } {
          rewrite -assoc fmap_app in Hnodup.
          apply NoDup_app in Hnodup as (Hnodup & _ & _).
          done.
        } {
          rewrite /ς' -(deltas_apply_snoc' _ _ _ node) //.
        }
    Qed.
    #[local] Lemma pstore_revert_spec {γ σ0 root ς descrs ϵs base base_descr δs} base' base_descr' path acc :
      descrs !! base' = Some base_descr' →
      treemap_path ϵs base base' path →
      lst_model' acc $ tail $
        ((λ δ, #(delta_node δ)) <$> reverse δs) ++
        ((λ δ, #(delta_node δ)) <$> reverse (concat path)) ++
        [ #base'] →
      {{{
        pstore_revert_pre_1 γ σ0 root ς descrs ϵs base base_descr δs
      }}}
        pstore_revert #root acc
      {{{ ϵs,
        RET ();
        pstore_revert_post γ σ0 descrs ϵs base' base_descr'
      }}}.
    Proof.
      iLöb as "HLöb" forall (root ς δs acc).

      iIntros (Hdescrs_lookup_base' Hpath ->) "%Φ (%v_root & Hroot & Hς & %Hϵs & Hauth & %Hdescrs_lookup_base & ((%Hstore_dom & %Hstore_gen) & #Helem_base & %Hδs_nodup & %Hδs & Hδs) & %Hδs_nil & Hdescrs) HΦ".
      simpl in *.

      destruct (rev_elim δs) as [-> | (δs' & ((r1, (g1, v1)), _root) & ->)].

      - iDestruct (deltas_chain_nil_inv with "Hδs") as %<-.
        specialize (Hδs_nil eq_refl) as ->.
        destruct (rev_elim path) as [-> | (path' & δs_cnode & ->)]; simpl.

        + apply treemap_path_nil_inv in Hpath as ->.
          assert (base_descr' = base_descr) as -> by congruence.
          wp_rec.
          iSteps.

        + apply treemap_path_app_inv in Hpath as (cnode & Hpath' & (? & Hϵs_lookup_cnode & ->%treemap_path_nil_inv)%treemap_path_cons_inv).
          iDestruct (big_sepM2_delete_r with "Hdescrs") as "(%cnode_descr & %Hdescrs_lookup_cnode & (%_base_descr & %Hdescrs_lookup_base_ & ((%Hcnode_store_dom & %Hcnode_store_gen) & #Helem_cnode & %Hδs_cnode_nodup & %Hδs_cnode & Hδs_cnode)) & Hdescrs)"; first done.
          simpl in Hdescrs_lookup_base_. assert (_base_descr = base_descr) as -> by congruence.
          assert (cnode ≠ base) as Hcnode.
          { intros ->.
            opose proof* treemap_rooted_acyclic as []; done.
          }
          iAssert ⌜0 < length δs_cnode⌝%I as %Hδs_cnode_length.
          { destruct δs_cnode; last iSteps.
            iDestruct (deltas_chain_nil_inv with "Hδs_cnode") as %?. done.
          }
          rewrite lookup_delete_ne // in Hdescrs_lookup_cnode.
          rewrite delete_commute.
          wp_apply (pstore_revert_spec_aux (δs_base := []) (δs_cnode := δs_cnode) base' with "[- HΦ]"); try done.
          { rewrite right_id //. }
          { rewrite concat_app reverse_app fmap_app -assoc /= right_id //. }
          { iSteps. }

      - iDestruct (deltas_chain_snoc_inv with "Hδs") as "(%Heq & Hδs & Hδ)".
        simpl in Heq. subst _root.
        rewrite reverse_snoc. cbn.
        wp_rec.
        destruct (rev_elim δs') as [-> | (δs & ((r2, (g2, v2)), node) & ->)].

        + destruct (rev_elim path) as [-> | (path' & δs_cnode & ->)]; simpl.

          * apply treemap_path_nil_inv in Hpath as ->.
            assert (base_descr' = base_descr) as -> by congruence.
            wp_load.
            wp_smart_apply assert_spec; first rewrite bool_decide_eq_true_2 //.
            assert (∃ data, store_on σ0 ς !! r1 = Some data) as ((g1', v1') & Hς_lookup).
            { apply elem_of_dom.
              rewrite deltas_apply_snoc in Hδs.
              apply (f_equal dom) in Hδs.
              set_solver.
            }
            iDestruct (big_sepM_insert_acc with "Hς") as "((Hr_gen & Hr_value) & Hς)"; first done.
            do 2 wp_load. do 3 wp_store. wp_pures. wp_rec. wp_store.
            iDestruct ("Hς" $! (g1, v1) with "[$Hr_gen $Hr_value]") as "Hς".
            rewrite deltas_apply_singleton store_on_insert in Hδs.
            rewrite -Hδs.
            iSteps; iPureIntro.
            { apply NoDup_nil_2. }
            { rewrite deltas_apply_nil //. }

          * apply treemap_path_app_inv in Hpath as (cnode & Hpath' & (? & Hϵs_lookup_cnode & ->%treemap_path_nil_inv)%treemap_path_cons_inv).
            iDestruct (big_sepM2_delete_r with "Hdescrs") as "(%cnode_descr & %Hdescrs_lookup_cnode & (%_base_descr & %Hdescrs_lookup_base_ & ((%Hcnode_store_dom & %Hcnode_store_gen) & #Helem_cnode & %Hδs_cnode_nodup & %Hδs_cnode & Hδs_cnode)) & Hdescrs)"; first done.
            simpl in Hdescrs_lookup_base_. assert (_base_descr = base_descr) as -> by congruence.
            assert (cnode ≠ base) as Hcnode.
            { intros ->.
              opose proof* treemap_rooted_acyclic as []; done.
            }
            destruct (rev_elim δs_cnode) as [->| (δs_cnode' & ((r2, (g2, v2)), _base) & ->)].
            { iDestruct (deltas_chain_nil_inv with "Hδs_cnode") as %?. done. }
            iDestruct (deltas_chain_snoc_inv with "Hδs_cnode") as "(%Heq & Hδs_cnode & Hδ')".
            simpl in Heq. subst _base.
            rewrite concat_app reverse_app fmap_app /= right_id reverse_app /=.
            wp_load.
            iDestruct (deltas_chain_snoc with "Hδs_cnode Hδ'") as "Hδs_cnode". cbn.
            wp_smart_apply assert_spec; first rewrite bool_decide_eq_true_2 //.
            assert (∃ data, store_on σ0 ς !! r1 = Some data) as ((g1', v1') & Hς_lookup).
            { apply elem_of_dom.
              rewrite deltas_apply_snoc in Hδs.
              apply (f_equal dom) in Hδs.
              set_solver.
            }
            iDestruct (big_sepM_insert_acc with "Hς") as "((Hr_gen & Hr_value) & Hς)"; first done.
            do 2 wp_load. do 3 wp_store.
            iDestruct ("Hς" $! (g1, v1) with "[$Hr_gen $Hr_value]") as "Hς".
            rewrite lookup_delete_ne // in Hdescrs_lookup_cnode.
            rewrite deltas_apply_singleton store_on_insert in Hδs.
            rewrite -Hδs delete_commute.
            wp_smart_apply (pstore_revert_spec_aux (δs_base := []) (δs_cnode := δs_cnode' ++ [_]) base' with "[- HΦ]"); try done.
            { rewrite app_length /=. lia. }
            { rewrite right_id //. }
            { rewrite reverse_app fmap_app -assoc //. }
            { iSteps; try iPureIntro.
              { apply NoDup_nil_2. }
              { rewrite deltas_apply_nil //. }
            }

        + rewrite last_snoc reverse_snoc /=.
          iDestruct (deltas_chain_snoc_inv with "Hδs") as "(_ & Hδs & Hδ')".
          wp_load.
          iDestruct (deltas_chain_snoc with "Hδs Hδ'") as "Hδs". cbn.
          wp_smart_apply assert_spec; first rewrite bool_decide_eq_true_2 //.
          assert (∃ data, store_on σ0 ς !! r1 = Some data) as ((g1', v1') & Hς_lookup).
          { apply elem_of_dom.
            rewrite deltas_apply_snoc in Hδs.
            apply (f_equal dom) in Hδs.
            set_solver.
          }
          iDestruct (big_sepM_insert_acc with "Hς") as "((Hr_gen & Hr_value) & Hς)"; first done.
          do 2 wp_load. do 3 wp_store.
          iDestruct ("Hς" $! (g1, v1) with "[$Hr_gen $Hr_value]") as "Hς".
          rewrite -store_on_insert.
          wp_smart_apply ("HLöb" $! node _ (δs ++ [((r2, (g2, v2)), node)]) with "[%] [%] [%] [- HΦ]"); try done.
          { rewrite reverse_app fmap_app -assoc //. }
          { iSteps; iPureIntro.
            { rewrite fmap_app in Hδs_nodup.
              apply NoDup_app in Hδs_nodup as (Hnodup & _ & _).
              done.
            }
            { erewrite <- deltas_apply_snoc'. done. }
            { intros []%symmetry%app_cons_not_nil. }
          }
    Qed.

    #[local] Lemma pstore_reroot_spec {γ σ0 root ς descrs ϵs base descr δs} base' descr' path :
      descrs !! base' = Some descr' →
      treemap_path ϵs base base' path →
      {{{
        pstore_collect_inv γ σ0 root ς descrs ϵs base descr δs
      }}}
        pstore_reroot #base'
      {{{ ϵs,
        RET ();
        pstore_revert_post γ σ0 descrs ϵs base' descr'
      }}}.
    Proof.
      iIntros "%Hdescrs_lookup_base' %Hpath %Φ Hinv HΦ".

      wp_rec.
      wp_apply (pstore_collect_spec with "Hinv") as (acc) "(Hinv & %Hacc)"; [done.. |].
      wp_smart_apply (pstore_revert_spec with "[Hinv] HΦ"); [done.. |].
      iDestruct "Hinv" as "(Hroot & Hς & %Hϵs & Hauth & %Hdescrs_lookup_base & ((%Hstore_dom & %Hstore_gen) & #Helem_base & %Hδs_nodup & %Hδs & Hδs) & %Hδs_nil & Hdescrs)".
      iSteps.
    Qed.

    Lemma pstore_restore_spec t σ0 σ s σ' :
      {{{
        pstore_model t σ0 σ ∗
        pstore_snapshot s t σ'
      }}}
        pstore_restore t s
      {{{
        RET ();
        pstore_model t σ0 σ'
      }}}.
    Proof.
      iIntros "%Φ ((%l & %γ & %g & %root & %ς & -> & -> & #Hmeta & Hl_gen & Hl_root & Hroot & Hς & (%Hς_dom & %Hς_gen) & Hmodel) & (%_l & %_γ & %g' & %base' & %descr' & %Heq & -> & -> & %Hg' & #_Hmeta & #Helem_base')) HΦ". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

      wp_rec. wp_pures. rewrite bool_decide_eq_true_2 //. wp_pures.
      case_decide as Hg.
      { iDestruct (descriptors_lookup with "Hmodel Helem_base'") as %[]%lookup_empty_Some. }
      iDecompose "Hmodel" as (descrs ϵs base descr δs Hϵs Hdescrs_lookup_base Hgen (Hstore_dom & Hstore_gen) Hδs_nodup Hδs Hδs_nil Hδs_gen) "Helem_base Hauth Hδs Hdescrs".
      iDestruct (descriptors_lookup with "Hauth Helem_base'") as %Hdescrs_lookup_base'.
      destruct (decide (base' = root)) as [-> | Hbase'].

      - destruct (decide (root = base)) as [-> | Hroot]; last first.
        { assert (delete base descrs !! root = Some descr') as Hdelete_descrs_lookup_root.
          { rewrite lookup_delete_ne //. }
          iAssert (∃ ϵ, ⌜ϵs !! root = Some ϵ⌝)%I as "(%ϵ & %Hϵs_lookup_root)".
          { iDestruct (big_sepM2_lookup_l with "Hdescrs") as "(% & % & _)"; first done.
            iSteps.
          }
          iDestruct (big_sepM2_lookup_acc with "Hdescrs") as "((%root_descr & %Hdescrs_lookup_root & (%Hroot_store_dom & %Hroot_store_gen) & #Helem_root & %Hδs'_nodup & %Hδs' & Hδs') & Hdescrs)"; [done.. |].
          destruct ϵ.2 as [| δ δs'] eqn:Hδ.
          { iDestruct (deltas_chain_nil_inv with "Hδs'") as %?.
            opose proof* treemap_rooted_acyclic as []; done.
          }
          iDestruct (deltas_chain_cons_inv with "Hδs'") as "(Hδ & Hδs')".
          iDestruct (pointsto_exclusive with "Hroot Hδ") as %[].
        }
        assert (descr = descr') as <- by congruence.
        destruct δs as [| δ δs]; last first.
        { iDestruct (deltas_chain_cons_inv with "Hδs") as "(Hδ & _)".
          iDestruct (pointsto_exclusive with "Hroot Hδ") as %[].
        }
        specialize (Hδs_nil eq_refl) as ->.
        iSteps. rewrite decide_False //. iSteps.

      - destruct (decide (base' = base)) as [-> | Hbase'_].

        + assert (descr = descr') as <- by congruence.
          destruct δs as [| δ δs].
          { iDestruct (deltas_chain_nil_inv with "Hδs") as %?. done. }
          iDestruct (deltas_chain_cons_inv with "Hδs") as "(Hδ & Hδs)".
          wp_load.
          iDestruct (deltas_chain_cons with "Hδ Hδs") as "Hδs".
          wp_smart_apply (pstore_reroot_spec with "[- Hl_gen Hl_root HΦ]") as (ϵs') "(Hbase & Hstore & %Hϵs' & Hauth & Hdescr & Hdescrs)"; first done.
          { apply treemap_path_nil. }
          { iFrame "#∗". iSteps. }
          do 2 wp_store.
          iApply "HΦ".
          iExists l, γ, (S g'), base, descr.2. unshelve iStep 8.
          { iPureIntro. eapply store_generation_le; last done. lia. }
          iExists descrs, ϵs', base, descr, []. iSteps.

        + assert (delete base descrs !! base' = Some descr') as Hdelete_descrs_lookup_base'.
          { rewrite lookup_delete_ne //. }
          iAssert (∃ ϵ, ⌜ϵs !! base' = Some ϵ⌝)%I as "(%ϵ & %Hϵs_lookup_base')".
          { iDestruct (big_sepM2_lookup_l with "Hdescrs") as "(% & % & _)"; first done.
            iSteps.
          }
          iDestruct (big_sepM2_lookup_acc with "Hdescrs") as "((%cnode_descr & %Hdescrs_lookup_cnode & (%Hcnode_store_dom & %Hcnode_store_gen) & #Helem_cnode & %Hδs'_nodup & %Hδs' & Hδs') & Hdescrs)"; [done.. |].
          destruct ϵ.2 as [| δ δs'] eqn:Hδ.
          { iDestruct (deltas_chain_nil_inv with "Hδs'") as %?.
            opose proof* treemap_rooted_acyclic as []; done.
          }
          iDestruct (deltas_chain_cons_inv with "Hδs'") as "(Hδ & Hδs')".
          wp_load. wp_pures.
          iDestruct (deltas_chain_cons with "Hδ Hδs'") as "Hδs'".
          rewrite <- Hδ in *. clear Hδ δ δs'.
          opose proof* treemap_rooted_path as (path & Hpath); [done.. |].
          wp_smart_apply (pstore_reroot_spec (descrs := descrs) with "[- Hl_gen Hl_root HΦ]") as (ϵs') "(Hbase' & Hstore' & %Hϵs' & Hauth & Hdescr' & Hdescrs)"; [done.. | |].
          { iFrame "#∗". iSteps. }
          do 2 wp_store.
          iApply "HΦ".
          iExists l, γ, (S g'), base', descr'.2. unshelve iStep 8.
          { iPureIntro. eapply store_generation_le; last done. lia. }
          iExists descrs, ϵs', base', descr', []. iSteps.
    Qed.
  End pstore_G.

  #[global] Opaque pstore_model.
  #[global] Opaque pstore_snapshot.
End raw.

#[global] Opaque pstore_create.
#[global] Opaque pstore_ref.
#[global] Opaque pstore_get.
#[global] Opaque pstore_set.
#[global] Opaque pstore_capture.
#[global] Opaque pstore_restore.

Class PstoreG Σ `{zoo_G : !ZooG Σ} := {
  #[local] pstore_G_raw_G :: raw.PstoreG Σ ;
  #[local] pstore_G_support_G :: MonoMapG Σ location val ;
}.

Definition pstore_Σ := #[
  raw.pstore_Σ ;
  mono_map_Σ location val
].
Lemma subG_pstore_Σ Σ `{zoo_G : !ZooG Σ} :
  subG pstore_Σ Σ →
  PstoreG Σ.
Proof.
  solve_inG.
Qed.

Section pstore_G.
  Context `{pstore_G : PstoreG Σ}.

  Definition pstore_model t σ : iProp Σ :=
    ∃ l γ σ0 ς,
    ⌜t = #l⌝ ∗
    ⌜σ ⊆ ς ∪ σ0⌝ ∗
    meta l (nroot.@"user") γ ∗
    mono_map_auth γ (DfracOwn 1) σ0 ∗
    raw.pstore_model t σ0 ς.

  Definition pstore_snapshot s t σ : iProp Σ :=
    ∃ l γ σ0 ς,
    ⌜t = #l⌝ ∗
    ⌜σ ⊆ ς ∪ σ0⌝ ∗
    meta l (nroot.@"user") γ ∗
    mono_map_lb γ σ0 ∗
    raw.pstore_snapshot s t ς.

  (*
  #[global] Instance pstore_model_timeless t σ :
    Timeless (pstore_model t σ).
  Proof.
    apply _.
  Qed.
   *)

  #[global] Instance pstore_snapshot_persistent s t σ :
    Persistent (pstore_snapshot s t σ).
  Proof.
    apply _.
  Qed.

  Lemma pstore_create_spec :
    {{{ True }}}
      pstore_create ()
    {{{ t,
      RET t;
      pstore_model t ∅
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    iApply wp_fupd.
    wp_apply (raw.pstore_create_spec with "[//]") as (t) "((%l & -> & Hmeta) & Ht)".
    iMod mono_map_alloc as "(%γ & Hauth)".
    iMod (meta_set with "Hmeta") as "Hmeta"; first done.
    iSteps. iExists ∅, ∅. iSteps.
  Qed.

  Lemma pstore_ref_spec t σ v :
    {{{
      pstore_model t σ
    }}}
      pstore_ref t v
    {{{ r,
      RET #r;
      ⌜σ !! r = None⌝ ∗
      pstore_model t (<[r := v]> σ)
    }}}.
  Proof.
    iIntros "%Φ (%l & %γ & %σ0 & %ς & -> & %Hσ & #Hmeta & Hauth & Ht) HΦ".
    iDestruct (raw.pstore_model_valid with "Ht") as %Hς_dom.
    iApply wp_fupd.
    wp_apply (raw.pstore_ref_spec with "Ht") as (r) "(%Hσ0_lookup & Ht)".
    assert (ς !! r = None) as Hς_lookup.
    { rewrite -!not_elem_of_dom in Hσ0_lookup |- *. set_solver. }
    assert (σ !! r = None) as Hσ_lookup.
    { eapply lookup_weaken_None; last done. apply lookup_union_None_2; done. }
    iMod (mono_map_insert with "Hauth") as "Hauth"; first done.
    iApply "HΦ".
    iStep. iExists l, γ, (<[r := v]> σ0), ς. iSteps. iPureIntro.
    rewrite -insert_union_r //. apply insert_mono. done.
  Qed.

  Lemma pstore_get_spec {t σ r} v :
    σ !! r = Some v →
    {{{
      pstore_model t σ
    }}}
      pstore_get t #r
    {{{
      RET v;
      pstore_model t σ
    }}}.
  Proof.
    iIntros "%Hσ_lookup %Φ (%l & %γ & %σ0 & %ς & -> & %Hσ & #Hmeta & Hauth & Ht) HΦ".
    wp_apply (raw.pstore_get_spec with "Ht") as "Ht".
    { eapply lookup_weaken; done. }
    iSteps.
  Qed.

  Lemma pstore_set_spec t σ r v :
    r ∈ dom σ →
    {{{
      pstore_model t σ
    }}}
      pstore_set t #r v
    {{{
      RET ();
      pstore_model t (<[r := v]> σ)
    }}}.
  Proof.
    iIntros "%Hr %Φ (%l & %γ & %σ0 & %ς & -> & %Hσ & #Hmeta & Hauth & Ht) HΦ".
    iDestruct (raw.pstore_model_valid with "Ht") as %Hς_dom.
    wp_apply (raw.pstore_set_spec with "Ht") as "Ht".
    { apply subseteq_dom in Hσ. set_solver. }
    iApply "HΦ".
    iExists l, γ, σ0, (<[r := v]> ς). iSteps. iPureIntro.
    rewrite -insert_union_l. apply insert_mono. done.
  Qed.

  Lemma pstore_capture_spec t σ :
    {{{
      pstore_model t σ
    }}}
      pstore_capture t
    {{{ s,
      RET s;
      pstore_model t σ ∗
      pstore_snapshot s t σ
    }}}.
  Proof.
    iIntros "%Φ (%l & %γ & %σ0 & %ς & -> & %Hσ & #Hmeta & Hauth & Ht) HΦ".
    iDestruct (mono_map_lb_get with "Hauth") as "#Hlb".
    wp_apply (raw.pstore_capture_spec with "Ht") as (s) "(Ht & Hs)".
    iSteps.
  Qed.

  Lemma pstore_restore_spec t σ s σ' :
    {{{
      pstore_model t σ ∗
      pstore_snapshot s t σ'
    }}}
      pstore_restore t s
    {{{
      RET ();
      pstore_model t σ'
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & %σ0 & %ς & -> & %Hσ & #Hmeta & Hauth & Ht) & (%_l & %_γ & %σ0' & %ς' & %Heq & %Hσ' & _Hmeta & #Hlb & Hs)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    wp_apply (raw.pstore_restore_spec with "[$Ht $Hs]") as "Ht".
    iDestruct (mono_map_lb_valid with "Hauth Hlb") as %Hσ0'.
    iApply "HΦ".
    iExists l, γ, σ0, ς'. iSteps. iPureIntro.
    trans (ς' ∪ σ0'); first done. apply map_union_mono_l. done.
  Qed.
End pstore_G.

#[global] Opaque pstore_model.
#[global] Opaque pstore_snapshot.
