From iris.base_logic Require Import
  lib.ghost_map.

From zoo Require Import
  prelude.
From zoo.common Require Import
  countable.
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
  parray_2__code.
From zoo_persistent Require Import
  parray_2__types.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types l node root : location.
Implicit Types v t s equal : val.
Implicit Types vs : list val.
Implicit Types nodes : gmap location (list val).

Class Parray2G Σ `{zoo_G : !ZooG Σ} := {
  parray_2_G_nodes_G : ghost_mapG Σ location (list val) ;
}.

Definition parray_2_Σ := #[
  ghost_mapΣ location (list val)
].
#[global] Instance subG_parray_2_Σ Σ `{zoo_G : !ZooG Σ} :
  subG parray_2_Σ Σ →
  Parray2G Σ.
Proof.
  solve_inG.
Qed.

Section parray_2_G.
  Context `{parray_2_G : Parray2G Σ}.
  Context τ `{!iType (iProp Σ) τ}.

  Record metadata := {
    metadata_equal : val;
    metadata_size : nat ;
    metadata_data : val ;
    metadata_nodes : gname ;
  }.
  Implicit Types γ : metadata.

  #[local] Instance metadata_eq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[local] Instance metadata_countable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition nodes_auth' γ_nodes :=
    @ghost_map_auth _ _ _ _ _ parray_2_G_nodes_G γ_nodes 1.
  #[local] Definition nodes_auth γ :=
    nodes_auth' γ.(metadata_nodes).
  #[local] Definition nodes_elem' γ_nodes node :=
    @ghost_map_elem _ _ _ _ _ parray_2_G_nodes_G γ_nodes node DfracDiscarded.
  #[local] Definition nodes_elem γ :=
    nodes_elem' γ.(metadata_nodes).

  Definition equal_model equal : iProp Σ :=
    □ ∀ v1 v2,
      τ v1 -∗
      τ v2 -∗
      WP equal v1 v2 {{ res,
        ∃ b,
        ⌜res = #b⌝ ∗
        ⌜if b then v1 = v2 else True⌝
      }}.

  #[local] Definition node_model γ node vs : iProp Σ :=
    ∃ (i : nat) v node' vs',
    node ↦ᵣ ‘Diff( #i, v, #node' ) ∗
    τ v ∗
    nodes_elem γ node' vs' ∗
    ⌜length vs = γ.(metadata_size)⌝ ∗
    ⌜i < γ.(metadata_size)⌝ ∗
    ⌜vs = <[i := v]> vs'⌝.
  #[local] Instance : CustomIpatFormat "node_model" :=
    " ( %i_{node} &
        %v_{node} &
        %node{;'} &
        %vs_node{;'} &
        H{node}{_{!}} &
        #Hv_{node} &
        #Hnodes_elem_node{;'} &
        % &
        % &
        %Hvs_{node}
      )
    ".

  #[local] Definition model' γ nodes root vs_root : iProp Σ :=
    nodes_auth γ nodes ∗
    root ↦ᵣ §Root ∗
    array_model γ.(metadata_data) (DfracOwn 1) vs_root ∗
    nodes_elem γ root vs_root ∗
    ⌜length vs_root = γ.(metadata_size)⌝ ∗
    ([∗ list] v ∈ vs_root, τ v) ∗
    [∗ map] node ↦ vs ∈ delete root nodes,
      node_model γ node vs.
  #[local] Instance : CustomIpatFormat "model'" :=
    " ( Hnodes_auth{_{}} &
        H{root}{} &
        Hdata{_{}} &
        #Hnodes_elem_{root}{_{}} &
        % &
        #Hvs_{root}{_{}} &
        Hnodes{_{}}
      )
    ".
  Definition parray_2_model t vs : iProp Σ :=
    ∃ l γ nodes root,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[equal] ↦□ γ.(metadata_equal) ∗
    l.[data] ↦□ γ.(metadata_data) ∗
    l.[root] ↦ #root ∗
    equal_model γ.(metadata_equal) ∗
    model' γ nodes root vs.
  #[local] Instance : CustomIpatFormat "model" :=
    " ( %l{} &
        %γ{} &
        %nodes{} &
        %root{} &
        {%Heq{};->} &
        #Hmeta{_{}} &
        #Hl_equal{_{}} &
        #Hl_data{_{}} &
        Hl_root{_{}} &
        #Hequal{_{}} &
        (:model' {//})
      )
    ".

  Definition parray_2_snapshot s t vs : iProp Σ :=
    ∃ node l γ,
    ⌜s = #node⌝ ∗
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    nodes_elem γ node vs.
  #[local] Instance : CustomIpatFormat "snapshot" :=
    " ( %node &
        %l_ &
        %γ_ &
        -> &
        %Heq &
        #Hmeta_ &
        #Hnodes_elem_node
      )
    ".

  #[global] Instance parray_2_snapshot_persistent s t vs :
    Persistent (parray_2_snapshot s t vs).
  Proof.
    apply _.
  Qed.

  #[local] Lemma nodes_alloc root vs :
    ⊢ |==>
      ∃ γ_nodes,
      nodes_auth' γ_nodes {[root := vs]} ∗
      nodes_elem' γ_nodes root vs.
  Proof.
    iMod (@ghost_map_alloc _ _ _ _ _ parray_2_G_nodes_G {[root := vs]}) as "(%γ_nodes & Hnodes_auth & Hnodes_elem)".
    rewrite big_sepM_singleton.
    iMod (ghost_map_elem_persist with "Hnodes_elem") as "Hnodes_elem".
    iSteps.
  Qed.
  #[local] Lemma nodes_elem_lookup γ nodes node vs :
    nodes_auth γ nodes -∗
    nodes_elem γ node vs -∗
    ⌜nodes !! node = Some vs⌝.
  Proof.
    apply ghost_map_lookup.
  Qed.
  #[local] Lemma nodes_elem_agree γ node vs1 vs2 :
    nodes_elem γ node vs1 -∗
    nodes_elem γ node vs2 -∗
    ⌜vs1 = vs2⌝.
  Proof.
    apply ghost_map_elem_agree.
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

  Lemma parray_2_model_exclusive t vs1 vs2 :
    parray_2_model t vs1 -∗
    parray_2_model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iApply (pointsto_exclusive with "Hl_root_1 Hl_root_2").
  Qed.

  Lemma parray_2_make_spec equal (sz : Z) v :
    (0 ≤ sz)%Z →
    {{{
      equal_model equal ∗
      τ v
    }}}
      parray_2_make equal #sz v
    {{{ t,
      RET t;
      parray_2_model t (replicate ₊sz v)
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hequal & #Hv) HΦ".

    wp_rec.
    wp_smart_apply (array_unsafe_make_spec with "[//]") as "%data Hdata"; first done.
    wp_ref root as "Hroot".
    wp_block l as "Hmeta" "(Hl_equal & Hl_data & Hl_root & _)".
    iMod (pointsto_persist with "Hl_equal") as "#Hl_equal".
    iMod (pointsto_persist with "Hl_data") as "#Hl_data".

    iMod (nodes_alloc root (replicate ₊sz v)) as "(%γ_nodes & Hnodes_auth & #Hnodes_elem)".

    pose γ := {|
      metadata_equal := equal ;
      metadata_size := ₊sz ;
      metadata_data := data ;
      metadata_nodes := γ_nodes ;
    |}.
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iModIntro. iFrame "#∗".
    rewrite length_replicate delete_singleton_eq big_sepM_empty.
    rewrite big_sepL.big_sepL_replicate -big_sepL_intro.
    auto 10.
  Qed.

  Lemma parray_2_get_spec {t vs} i v :
    (0 ≤ i)%Z →
    vs !! ₊i = Some v →
    {{{
      parray_2_model t vs
    }}}
      parray_2_get t #i
    {{{
      RET v;
      parray_2_model t vs
    }}}.
  Proof.
    iIntros "% %Hvs_lookup %Φ (:model) HΦ".

    wp_rec. wp_load.
    wp_apply (array_unsafe_get_spec with "Hdata") as "Hdata"; [done.. |].

    iApply "HΦ".
    iFrame "#∗". iSteps.
  Qed.

  Lemma parray_2_set_spec t vs i v :
    (0 ≤ i < length vs)%Z →
    {{{
      parray_2_model t vs ∗
      τ v
    }}}
      parray_2_set t #i v
    {{{
      RET ();
      parray_2_model t (<[₊i := v]> vs)
    }}}.
  Proof.
    iIntros "% %Φ ((:model) & #Hv) HΦ".

    wp_rec. wp_load.

    destruct (lookup_lt_is_Some_2 vs ₊i) as (w & Hvs_lookup); first lia.
    wp_smart_apply (array_unsafe_get_spec with "Hdata") as "Hdata"; [lia | done.. |].

    wp_load.

    iDestruct (big_sepL_lookup with "Hvs_root") as "#Hw"; first done.
    wp_apply (wp_wand with "(Hequal Hv Hw)") as (res) "(%b & -> & %Hb)".
    destruct b; first subst w; wp_pures.

    - iApply "HΦ".
      rewrite list_insert_id //. iFrame "#∗". iSteps.

    - wp_ref root' as "Hroot'".
      wp_load. do 2 wp_store. wp_load.
      iApply wp_fupd.
      wp_apply (array_unsafe_set_spec with "Hdata") as "Hdata"; first done.

      iAssert ⌜nodes !! root' = None⌝%I as %Hnodes_lookup_root'.
      { rewrite -eq_None_ne_Some. iIntros "%vs_root' %Hnodes_lookup_root'".
        iDestruct (pointsto_ne with "Hroot Hroot'") as %?.
        iDestruct (big_sepM_lookup _ _ root' with "Hnodes") as "(:node_model node=root' !=)".
        { rewrite lookup_delete_ne //. congruence. }
        iApply (pointsto_exclusive with "Hroot' Hroot'_").
      }

      iApply "HΦ".
      set vs' := <[₊i := v]> vs.
      iDestruct (big_sepL_insert ₊i with "Hvs_root Hv") as "Hvs_root'"; first lia.
      iDestruct (nodes_elem_lookup with "Hnodes_auth Hnodes_elem_root") as %Hnodes_lookup_root.
      iMod (nodes_insert root' vs' with "Hnodes_auth") as "(Hnodes_auth & #Hnodes_elem_root')"; first done.
      iDestruct (big_sepM_delete_2 with "Hnodes [Hroot]") as "Hnodes"; first done.
      { iExists ₊i, w, root', vs'. iSteps; iPureIntro.
        - rewrite Z2Nat.id //. lia.
        - rewrite list_insert_insert_eq list_insert_id //.
      }
      rewrite -{2}(delete_insert_id nodes root' vs') //.
      iFrame "#∗". iSteps. iPureIntro.
      rewrite /vs'. simpl_length.
  Qed.

  Lemma parray_2_capture_spec t vs :
    {{{
      parray_2_model t vs
    }}}
      parray_2_capture t
    {{{ s,
      RET s;
      parray_2_model t vs ∗
      parray_2_snapshot s t vs
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".

    wp_rec. wp_load.

    iApply "HΦ".
    iFrame "#∗". iSteps.
  Qed.

  #[local] Definition restore_inv γ nodes root vs_root : iProp Σ :=
    ∃ descr_root,
    nodes_auth γ nodes ∗
    root ↦ᵣ descr_root ∗
    array_model γ.(metadata_data) (DfracOwn 1) vs_root ∗
    ⌜length vs_root = γ.(metadata_size)⌝ ∗
    ([∗ list] v ∈ vs_root, τ v) ∗
    [∗ map] node ↦ vs ∈ delete root nodes,
      node_model γ node vs.
  #[local] Instance : CustomIpatFormat "restore_inv" :=
    " ( %descr_{root} &
        Hnodes_auth &
        H{root} &
        Hdata &
        % &
        #Hvs_{root} &
        Hnodes
      )
    ".
  #[local] Lemma parray_2_restore_0_spec {γ nodes root vs_root node} vs :
    {{{
      model' γ nodes root vs_root ∗
      nodes_elem γ node vs
    }}}
      parray_2_restore_0 γ.(metadata_data) #node
    {{{
      RET ();
      restore_inv γ nodes node vs
    }}}.
  Proof.
    iLöb as "HLöb" forall (node vs).

    iIntros "%Φ ((:model') & #Hnodes_elem_node) HΦ".
    iDestruct (nodes_elem_lookup with "Hnodes_auth Hnodes_elem_node") as %Hnodes_lookup_node.

    wp_rec.
    destruct_decide (node = root) as -> | Hnode.

    - iDestruct (nodes_elem_agree with "Hnodes_elem_node Hnodes_elem_root") as %<-.
      iSteps.

    - iDestruct (big_sepM_lookup_acc with "Hnodes") as "((:node_model =1) & Hnodes)".
      { rewrite lookup_delete_ne //. }
      wp_load.

      wp_smart_apply ("HLöb" $! node1 vs_node1 with "[- HΦ]") as "(:restore_inv root=node1)"; first iFrameSteps.

      destruct (lookup_lt_is_Some_2 vs_node1 i_node) as (v & Hvs_node1_lookup); first lia.
      wp_smart_apply (array_unsafe_get_spec with "Hdata") as "Hdata"; [lia | done | lia |].
      wp_store.
      wp_smart_apply (array_unsafe_set_spec with "Hdata") as "Hdata"; first lia.
      rewrite Nat2Z.id -Hvs_node.

      iDestruct (big_sepL_insert i_node with "Hvs_node1 Hv_node") as "Hvs"; first lia.
      rewrite -Hvs_node.

      iDestruct (nodes_elem_lookup with "Hnodes_auth Hnodes_elem_node1") as %Hnodes_lookup_node1.
      iDestruct (big_sepM_delete_2 with "Hnodes [$Hnode1]") as "Hnodes"; first done.
      { iDestruct (big_sepL_lookup with "Hvs_node1") as "$"; first done.
        iSteps. iPureIntro.
        rewrite Hvs_node list_insert_insert_eq list_insert_id //.
      }
      iClear "Hv_node". clear dependent i_node v_node.
      iDestruct (big_sepM_delete_1 node with "Hnodes") as "((:node_model =2) & Hnodes)"; first done.

      iSteps.
  Qed.
  Lemma parray_2_restore_spec t vs s vs' :
    {{{
      parray_2_model t vs ∗
      parray_2_snapshot s t vs'
    }}}
      parray_2_restore t s
    {{{
      RET ();
      parray_2_model t vs'
    }}}.
  Proof.
    iIntros "%Φ ((:model) & (:snapshot)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (nodes_elem_lookup with "Hnodes_auth Hnodes_elem_node") as %Hnodes_lookup_node.

    wp_rec.
    destruct_decide (node = root) as -> | Hnode.

    - wp_load. wp_pures.

      iApply "HΦ".
      iDestruct (nodes_elem_agree with "Hnodes_elem_node Hnodes_elem_root") as %->.
      iFrame "#∗". iSteps.

    - iDestruct (big_sepM_lookup_acc with "Hnodes") as "((:node_model) & Hnodes)".
      { rewrite lookup_delete_ne //. }
      wp_load.

      wp_load.
      wp_smart_apply (parray_2_restore_0_spec vs' with "[- Hl_root HΦ]") as "(:restore_inv root=node)"; first iFrameSteps.
      do 2 wp_store.

      iApply "HΦ".
      iFrame "#∗". iSteps.
  Qed.
End parray_2_G.

From zoo_persistent Require
  parray_2__opaque.

#[global] Opaque parray_2_model.
#[global] Opaque parray_2_snapshot.
