From iris.base_logic Require Import
  lib.ghost_map.

From zoo Require Import
  prelude.
From zoo.iris.bi Require Import
  big_op.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  array.
From zoo_persistent Require Export
  base
  parray__code.
From zoo_persistent Require Import
  parray__types.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types node root : location.
Implicit Types v t equal : val.
Implicit Types vs : list val.
Implicit Types nodes : gmap location (list val).

Class ParrayG Σ `{zoo_G : !ZooG Σ} := {
  parray_G_nodes_G : ghost_mapG Σ location (list val) ;
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
  Context τ `{!iType (iProp Σ) τ}.

  Record metadata := {
    metadata_size : nat ;
    metadata_data : val ;
    metadata_nodes : gname ;
  }.
  Implicit Types γ : metadata.

  #[local] Definition nodes_auth' γ_nodes :=
    @ghost_map_auth _ _ _ _ _ parray_G_nodes_G γ_nodes 1.
  #[local] Definition nodes_auth γ :=
    nodes_auth' γ.(metadata_nodes).
  #[local] Definition nodes_elem' γ_nodes node :=
    @ghost_map_elem _ _ _ _ _ parray_G_nodes_G γ_nodes node DfracDiscarded.
  #[local] Definition nodes_elem γ :=
    nodes_elem' γ.(metadata_nodes).

  #[local] Definition node_model γ node vs : iProp Σ :=
    ∃ (i : nat) v node' vs',
    node ↦ᵣ ‘Diff( #i, v, #node' ) ∗
    τ v ∗
    nodes_elem γ node' vs' ∗
    ⌜length vs = γ.(metadata_size)⌝ ∗
    ⌜i < γ.(metadata_size)⌝ ∗
    ⌜vs = <[i := v]> vs'⌝.
  #[local] Instance : CustomIpatFormat "node_model" :=
    "(
      %i_{node} &
      %v_{node} &
      %node{='} &
      %vs_node{='} &
      H{node}{_{suff}} &
      #Hv_{node} &
      #Hnodes_elem_node{='} &
      % &
      % &
      %Hvs_{node}
    )".
  #[local] Definition inv' γ nodes root : iProp Σ :=
    ∃ vs_root,
    nodes_auth γ nodes ∗
    root ↦ᵣ ‘Root( γ.(metadata_data) ) ∗
    array_model γ.(metadata_data) (DfracOwn 1) vs_root ∗
    ⌜nodes !! root = Some vs_root⌝ ∗
    ⌜length vs_root = γ.(metadata_size)⌝ ∗
    ([∗ list] v ∈ vs_root, τ v) ∗
    [∗ map] node ↦ vs ∈ delete root nodes,
      node_model γ node vs.
  #[local] Instance : CustomIpatFormat "inv'" :=
    "(
      %vs_{root} &
      Hnodes_auth &
      H{root} &
      Hdata &
      %Hnodes_lookup_{root} &
      % &
      #Hvs_{root} &
      Hnodes
    )".
  Definition parray_inv γ : iProp Σ :=
    ∃ nodes root,
    inv' γ nodes root.
  #[local] Instance : CustomIpatFormat "inv" :=
    "(
      %nodes &
      %{root} &
      (:inv')
    )".

  Definition parray_model t γ vs : iProp Σ :=
    ∃ node,
    ⌜t = #node⌝ ∗
    nodes_elem γ node vs.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %node &
      -> &
      #Hnodes_elem_node
    )".

  #[global] Instance parray_inv_timeless γ :
    (∀ v, Timeless (τ v)) →
    Timeless (parray_inv γ).
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

  #[local] Lemma nodes_alloc root vs :
    ⊢ |==>
      ∃ γ_nodes,
      nodes_auth' γ_nodes {[root := vs]} ∗
      nodes_elem' γ_nodes root vs.
  Proof.
    iMod (@ghost_map_alloc _ _ _ _ _ parray_G_nodes_G {[root := vs]}) as "(%γ_nodes & Hnodes_auth & Hnodes_elem)".
    rewrite big_sepM_singleton.
    iMod (ghost_map_elem_persist with "Hnodes_elem") as "Hnodes_elem".
    iSteps.
  Qed.
  #[local] Lemma nodes_lookup γ nodes node vs :
    nodes_auth γ nodes -∗
    nodes_elem γ node vs -∗
    ⌜nodes !! node = Some vs⌝.
  Proof.
    apply ghost_map_lookup.
  Qed.
  #[local] Lemma nodes_insert {γ nodes} node vs :
    nodes !! node = None →
    nodes_auth γ nodes ⊢ |==>
      nodes_auth γ (<[node := vs]> nodes) ∗
      nodes_elem γ node vs.
  Proof.
    iIntros "%Hlookup Hnodes_auth".
    iMod (ghost_map_insert with "Hnodes_auth") as "(Hnodes_auth & Hnodes_elem)"; first done.
    iMod (ghost_map_elem_persist with "Hnodes_elem") as "Hnodes_elem".
    iSteps.
  Qed.

  Lemma parray_make_spec (sz : Z) v :
    (0 ≤ sz)%Z →
    {{{
      τ v
    }}}
      parray_make #sz v
    {{{ t γ,
      RET t;
      parray_inv γ ∗
      parray_model t γ (replicate ₊sz v)
    }}}.
  Proof.
    iIntros "%Hsz %Φ #Hv HΦ".

    wp_rec.
    wp_smart_apply (array_unsafe_make_spec with "[//]") as "%data Hdata"; first done.
    wp_ref root as "Hroot".

    iMod (nodes_alloc root (replicate ₊sz v)) as "(%γ_nodes & Hnodes_auth & Hnodes_elem)".

    pose γ := {|
      metadata_size := ₊sz ;
      metadata_data := data ;
      metadata_nodes := γ_nodes ;
    |}.

    iApply ("HΦ" $! _ γ).
    iModIntro. iFrame.
    rewrite lookup_insert length_replicate delete_singleton big_sepM_empty.
    rewrite big_op.big_sepL_replicate -big_sepL_intro.
    auto 10.
  Qed.

  #[local] Definition reroot_inv γ nodes root vs_root : iProp Σ :=
    ∃ descr_root,
    nodes_auth γ nodes ∗
    root ↦ᵣ descr_root ∗
    array_model γ.(metadata_data) (DfracOwn 1) vs_root ∗
    ⌜length vs_root = γ.(metadata_size)⌝ ∗
    ([∗ list] v ∈ vs_root, τ v) ∗
    [∗ map] node ↦ vs ∈ delete root nodes,
      node_model γ node vs.
  #[local] Instance : CustomIpatFormat "reroot_inv" :=
    "(
      %descr_{root} &
      Hnodes_auth &
      H{root} &
      Hdata &
      % &
      #Hvs_{root} &
      Hnodes
    )".
  #[local] Lemma parray_reroot_0_spec {γ nodes root node} vs :
    {{{
      inv' γ nodes root ∗
      nodes_elem γ node vs
    }}}
      parray_reroot_0 #node
    {{{
      RET γ.(metadata_data);
      reroot_inv γ nodes node vs
    }}}.
  Proof.
    iLöb as "HLöb" forall (node vs).

    iIntros "%Φ ((:inv') & #Hnodes_elem_node) HΦ".

    wp_rec.
    destruct (decide (node = root)) as [-> | Hnode].

    - iDestruct (nodes_lookup with "Hnodes_auth Hnodes_elem_node") as %Hnodes_lookup_root_. simplify.
      iSteps.

    - iDestruct (nodes_lookup with "Hnodes_auth Hnodes_elem_node") as %Hnodes_lookup_node.
      iDestruct (big_sepM_lookup_acc with "Hnodes") as "((:node_model =1) & Hnodes)".
      { rewrite lookup_delete_ne //. }
      wp_load.

      wp_smart_apply ("HLöb" $! node1 vs_node1 with "[- HΦ]") as "(:reroot_inv root=node1)"; first iFrameSteps.

      destruct (lookup_lt_is_Some_2 vs_node1 i_node) as (v & Hvs_node1_lookup); first lia.
      wp_smart_apply (array_unsafe_get_spec with "Hdata") as "Hdata"; [lia | done | lia |].
      wp_store.
      wp_smart_apply (array_unsafe_set_spec with "Hdata") as "Hdata"; first lia.
      rewrite Nat2Z.id -Hvs_node.
      wp_pures.

      iDestruct (big_sepL_insert i_node with "Hvs_node1 Hv_node") as "Hvs"; first lia.
      rewrite -Hvs_node.

      iDestruct (nodes_lookup with "Hnodes_auth Hnodes_elem_node1") as %Hnodes_lookup_node1.
      iDestruct (big_sepM_delete_2 with "Hnodes [$Hnode1]") as "Hnodes"; first done.
      { iDestruct (big_sepL_lookup with "Hvs_node1") as "$"; first done.
        iSteps. iPureIntro.
        rewrite Hvs_node list_insert_insert list_insert_id //.
      }
      iClear "Hv_node". clear dependent i_node v_node.
      iDestruct (big_sepM_delete_1 node with "Hnodes") as "((:node_model =2) & Hnodes)"; first done.

      iSteps.
  Qed.
  #[local] Lemma parray_reroot_spec γ node vs :
    {{{
      parray_inv γ ∗
      nodes_elem γ node vs
    }}}
      parray_reroot #node
    {{{ nodes,
      RET γ.(metadata_data);
      inv' γ nodes node
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & #Hnodes_elem_node) HΦ".

    wp_rec.
    destruct (decide (node = root)) as [-> | Hnode]; first iSteps.

    iDestruct (nodes_lookup with "Hnodes_auth Hnodes_elem_node") as %Hnodes_lookup_node.
    iDestruct (big_sepM_lookup_acc with "Hnodes") as "((:node_model) & Hnodes)".
    { rewrite lookup_delete_ne //. }
    wp_load.

    wp_smart_apply (parray_reroot_0_spec vs with "[- HΦ]") as "(:reroot_inv root=node)"; first iFrameSteps.
    iSteps.
  Qed.

  Lemma parray_get_spec {t γ vs} i v :
    (0 ≤ i)%Z →
    vs !! ₊i = Some v →
    {{{
      parray_inv γ ∗
      parray_model t γ vs
    }}}
      parray_get t #i
    {{{
      RET v;
      parray_inv γ
    }}}.
  Proof.
    iIntros "% %Hvs_lookup %Φ (Hinv & (:model)) HΦ".

    wp_rec.
    wp_smart_apply (parray_reroot_spec with "[$Hinv $Hnodes_elem_node]") as (nodes) "(:inv' root=node)".

    iDestruct (nodes_lookup with "Hnodes_auth Hnodes_elem_node") as %Hnodes_lookup_node_. simplify.
    wp_smart_apply (array_unsafe_get_spec with "Hdata") as "Hdata"; [done.. |].

    iStepFrameSteps.
  Qed.

  Lemma parray_set_spec t γ vs equal i v :
    (0 ≤ i < length vs)%Z →
    {{{
      parray_inv γ ∗
      parray_model t γ vs ∗
      ( ∀ v1 v2,
        τ v1 -∗
        τ v2 -∗
        WP equal v1 v2 {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          ⌜if b then v1 = v2 else True⌝
        }}
      ) ∗
      τ v
    }}}
      parray_set t equal #i v
    {{{ t',
      RET t';
      parray_inv γ ∗
      parray_model t' γ (<[₊i := v]> vs)
    }}}.
  Proof.
    iIntros "% %Φ (Hinv & (:model) & Hequal & #Hv) HΦ".

    wp_rec.
    wp_smart_apply (parray_reroot_spec with "[$Hinv $Hnodes_elem_node]") as (nodes) "(:inv' root=node)".

    iDestruct (nodes_lookup with "Hnodes_auth Hnodes_elem_node") as %Hnodes_lookup_node_. simplify.
    destruct (lookup_lt_is_Some_2 vs_node ₊i) as (w & Hvs_node_lookup); first lia.
    wp_smart_apply (array_unsafe_get_spec with "Hdata") as "Hdata"; [done.. |].

    iDestruct (big_sepL_lookup with "Hvs_node") as "#Hw"; first done.
    wp_smart_apply (wp_wand with "(Hequal Hv Hw)") as (res) "(%b & -> & %Hb)".
    destruct b; first subst w; wp_pures.

    - rewrite list_insert_id //.
      iStepFrameSteps.

    - wp_apply (array_unsafe_set_spec with "Hdata") as "Hdata"; first done.
      wp_load.
      wp_ref root as "Hroot".
      wp_store. wp_pures.

      iAssert ⌜nodes !! root = None⌝%I as %Hnodes_lookup_root.
      { rewrite -eq_None_ne_Some. iIntros "%vs_root %Hnodes_lookup_root".
        iDestruct (pointsto_ne with "Hroot Hnode") as %?.
        iDestruct (big_sepM_lookup _ _ root with "Hnodes") as "(:node_model node=root suff=)".
        { rewrite lookup_delete_ne //. congruence. }
        iApply (pointsto_exclusive with "Hroot Hroot_").
      }

      set vs_root := <[₊i := v]> vs_node.
      iDestruct (big_sepL_insert ₊i with "Hvs_node Hv") as "Hvs_root"; first lia.
      iMod (nodes_insert root vs_root with "Hnodes_auth") as "(Hnodes_auth & #Hnodes_elem_root)"; first done.
      iDestruct (big_sepM_insert_delete_2 with "Hnodes [Hnode]") as "Hnodes".
      { iExists ₊i, w, root, vs_root. iSteps; iPureIntro.
        - rewrite Z2Nat.id //.
        - rewrite list_insert_insert list_insert_id //.
      }
      iEval (rewrite insert_id //) in "Hnodes".
      rewrite -{2}(delete_insert nodes root vs_root) //.
      iStepFrameSteps; iPureIntro.
      { rewrite lookup_insert //. }
      { rewrite /vs_root. simpl_length. }
  Qed.
End parray_G.

#[global] Opaque parray_make.
#[global] Opaque parray_get.
#[global] Opaque parray_set.

#[global] Opaque parray_inv.
#[global] Opaque parray_model.
