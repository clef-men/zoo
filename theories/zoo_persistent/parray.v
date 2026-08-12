Require Import iris.base_logic.lib.ghost_map.

Require Import zoo.prelude.
Require Import zoo.iris.bi.big_op.
Require Import zoo.base.
Require Export zoo_persistent.parray__code.
Require Import zoo_persistent.parray__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type node root : location.
Implicit Type v t equal : val.
Implicit Type vs : list val.
Implicit Type nodes : gmap location (list val).

Class ParrayG Σ `{zoo۰G : !ZooG Σ} :=
  { parray۰G۰nodes۰G : ghost_mapG Σ location (list val)
  }.

Definition parray۰Σ :=
  #[ghost_mapΣ location (list val)
  ].
#[global] Instance subGｰparray۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG parray۰Σ Σ →
  ParrayG Σ.
Proof.
  solve_inG.
Qed.

Section parray۰G.
  Context `{parray۰G : ParrayG Σ}.
  Context τ `{!iType (iProp Σ) τ}.

  Record metadata :=
    { metadata۰equal : val
    ; metadata۰size : nat
    ; metadata۰data : val
    ; metadata۰nodes : gname
    }.
  Implicit Type γ : metadata.

  #[local] Definition nodes۰auth' γ_nodes :=
    @ghost_map_auth _ _ _ _ _ parray۰G۰nodes۰G γ_nodes 1.
  #[local] Definition nodes۰auth γ :=
    nodes۰auth' γ.(metadata۰nodes).
  #[local] Definition nodes۰elem' γ_nodes node :=
    @ghost_map_elem _ _ _ _ _ parray۰G۰nodes۰G γ_nodes node DfracDiscarded.
  #[local] Definition nodes۰elem γ :=
    nodes۰elem' γ.(metadata۰nodes).

  Definition equal۰model equal : iProp Σ :=
    □ ∀ v1 v2,
      τ v1 -∗
      τ v2 -∗
      WP equal v1 v2 {{ res,
        ∃ b,
        ⌜res = #b⌝ ∗
        ⌜if b then v1 = v2 else True⌝
      }}.

  #[local] Definition node۰model γ node vs : iProp Σ :=
    ∃ (i : nat) v node' vs',
    node ↦ᵣ ‘Diff( #i, v, #node' ) ∗
    τ v ∗
    nodes۰elem γ node' vs' ∗
    ⌜length vs = γ.(metadata۰size)⌝ ∗
    ⌜i < γ.(metadata۰size)⌝ ∗
    ⌜vs = <[i := v]> vs'⌝.
  #[local] Instance : CustomIpat "node۰model" :=
    " ( %i_{node}
      & %v_{node}
      & %node{;'}
      & %vs_node{;'}
      & H{node}{_{!}}
      & #Hv_{node}
      & #Hnodes_elem_node{;'}
      & %
      & %
      & %Hvs_{node}
      )
    ".

  #[local] Definition inv' γ nodes root : iProp Σ :=
    ∃ vs_root,
    equal۰model γ.(metadata۰equal) ∗
    nodes۰auth γ nodes ∗
    root ↦ᵣ ‘Root( γ.(metadata۰equal), γ.(metadata۰data) ) ∗
    array۰model γ.(metadata۰data) (DfracOwn 1) vs_root ∗
    nodes۰elem γ root vs_root ∗
    ⌜length vs_root = γ.(metadata۰size)⌝ ∗
    ([∗ list] v ∈ vs_root, τ v) ∗
    [∗ map] node ↦ vs ∈ delete root nodes,
      node۰model γ node vs.
  #[local] Instance : CustomIpat "inv'" :=
    " ( %vs_{root}{_{}}
      & #Hequal{_{}}
      & Hnodes_auth{_{}}
      & H{root}{}
      & Hdata{_{}}
      & #Hnodes_elem_{root}{_{}}{_{!}}
      & %
      & #Hvs_{root}{_{}}
      & Hnodes{_{}}
      )
    ".
  Definition parray۰inv γ : iProp Σ :=
    ∃ nodes root,
    inv' γ nodes root.
  #[local] Instance : CustomIpat "inv" :=
    " ( %nodes{}
      & %{root}{}
      & (:inv')
      )
    ".

  Definition parray۰model t γ vs : iProp Σ :=
    ∃ node,
    ⌜t = #node⌝ ∗
    nodes۰elem γ node vs.
  #[local] Instance : CustomIpat "model" :=
    " ( %node
      & ->
      & #Hnodes_elem_node
      )
    ".

  #[global] Instance parray۰modelｰpersistent t γ vs :
    Persistent (parray۰model t γ vs).
  Proof.
    apply _.
  Qed.

  #[local] Lemma nodesｰalloc root vs :
    ⊢ |==>
      ∃ γ_nodes,
      nodes۰auth' γ_nodes {[root := vs]} ∗
      nodes۰elem' γ_nodes root vs.
  Proof.
    iMod (@ghost_map_alloc _ _ _ _ _ parray۰G۰nodes۰G {[root := vs]}) as "(%γ_nodes & Hnodes_auth & Hnodes_elem)".
    rewrite big_sepM_singleton.
    iMod (ghost_map_elem_persist with "Hnodes_elem") as "Hnodes_elem".
    iSteps.
  Qed.
  #[local] Lemma nodes۰authｰexclusive γ nodes1 nodes2 :
    nodes۰auth γ nodes1 -∗
    nodes۰auth γ nodes2 -∗
    False.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (ghost_map_auth_valid_2 with "Hauth1 Hauth2") as %(? & _). done.
  Qed.
  #[local] Lemma nodes۰elemｰlookup γ nodes node vs :
    nodes۰auth γ nodes -∗
    nodes۰elem γ node vs -∗
    ⌜nodes !! node = Some vs⌝.
  Proof.
    apply ghost_map_lookup.
  Qed.
  #[local] Lemma nodes۰elemｰagree γ node vs1 vs2 :
    nodes۰elem γ node vs1 -∗
    nodes۰elem γ node vs2 -∗
    ⌜vs1 = vs2⌝.
  Proof.
    apply ghost_map_elem_agree.
  Qed.
  #[local] Lemma nodesｰinsert {γ nodes} node vs :
    nodes !! node = None →
    nodes۰auth γ nodes ⊢ |==>
      nodes۰auth γ (<[node := vs]> nodes) ∗
      nodes۰elem γ node vs.
  Proof.
    iIntros "%Hlookup Hnodes_auth".
    iMod (ghost_map_insert with "Hnodes_auth") as "(Hnodes_auth & Hnodes_elem)"; first done.
    iMod (ghost_map_elem_persist with "Hnodes_elem") as "Hnodes_elem".
    iSteps.
  Qed.

  Lemma parray۰invｰexclusive γ :
    parray۰inv γ -∗
    parray۰inv γ -∗
    False.
  Proof.
    iIntros "(:inv =1) (:inv =2)". simp.
    iApply (nodes۰authｰexclusive with "Hnodes_auth_1 Hnodes_auth_2").
  Qed.

  Lemma parray٠makeｰspec equal (sz : Z) v :
    (0 ≤ sz)%Z →
    {{{
      equal۰model equal ∗
      τ v
    }}}
      parray٠make equal #sz v
    {{{
      t γ
    , RET t;
      parray۰inv γ ∗
      parray۰model t γ (replicate ₊sz v)
    }}}.
  Proof.
    iIntros "%Hsz %Φ (#Hequal & #Hv) HΦ".

    wp۰rec.
    wp۰apply+ (array٠unsafe_makeｰspec with "[//]") as "%data Hdata"; first done.
    wp۰ref root as "Hroot".

    iMod (nodesｰalloc root (replicate ₊sz v)) as "(%γ_nodes & Hnodes_auth & #Hnodes_elem)".

    pose γ :=
      {|metadata۰equal := equal
      ; metadata۰size := ₊sz
      ; metadata۰data := data
      ; metadata۰nodes := γ_nodes
      |}.

    iApply ("HΦ" $! _ γ).
    iModIntro. iFrame "#∗".
    rewrite length_replicate delete_singleton_eq big_sepM_empty.
    rewrite big_sepLｰreplicate -big_sepL_intro.
    iFrame "#∗" => //.
  Qed.

  #[local] Definition reroot۰inv γ nodes root vs_root : iProp Σ :=
    ∃ descr_root,
    nodes۰auth γ nodes ∗
    root ↦ᵣ descr_root ∗
    array۰model γ.(metadata۰data) (DfracOwn 1) vs_root ∗
    ⌜length vs_root = γ.(metadata۰size)⌝ ∗
    ([∗ list] v ∈ vs_root, τ v) ∗
    [∗ map] node ↦ vs ∈ delete root nodes,
      node۰model γ node vs.
  #[local] Instance : CustomIpat "reroot۰inv" :=
    " ( %descr_{root}
      & Hnodes_auth
      & H{root}
      & Hdata
      & %
      & #Hvs_{root}
      & Hnodes
      )
    ".
  #[local] Lemma parray٠reroot₁ｰspec {γ nodes root node} vs :
    {{{
      inv' γ nodes root ∗
      nodes۰elem γ node vs
    }}}
      parray٠reroot₁ #node
    {{{
      RET (γ.(metadata۰equal), γ.(metadata۰data));
      reroot۰inv γ nodes node vs
    }}}.
  Proof.
    iLöb as "HLöb" forall (node vs).

    iIntros "%Φ ((:inv') & #Hnodes_elem_node) HΦ".
    iDestruct (nodes۰elemｰlookup with "Hnodes_auth Hnodes_elem_node") as %Hnodes_lookup_node.

    wp۰rec.
    destruct_decide (node = root) as -> | Hnode.

    - iDestruct (nodes۰elemｰagree with "Hnodes_elem_node Hnodes_elem_root") as %<-.
      iSteps.

    - iDestruct (big_sepM_lookup_acc with "Hnodes") as "((:node۰model =1) & Hnodes)".
      { rewrite lookup_delete_ne //. }
      wp۰load.

      wp۰apply+ ("HLöb" $! node1 vs_node1 with "[- HΦ]") as "(:reroot۰inv root=node1)".
      { iFrame "∗#". iSteps. }

      destruct (lookup_lt_is_Some_2 vs_node1 i_node) as (v & Hvs_node1_lookup); first lia.
      wp۰apply+ (array٠unsafe_getｰspec with "Hdata") as "Hdata"; [lia | done | lia |].
      wp۰store.
      wp۰apply+ (array٠unsafe_setｰspec with "Hdata") as "Hdata"; first lia.
      rewrite Nat2Z.id -Hvs_node.
      wp۰pures.

      iDestruct (big_sepLｰinsert i_node with "Hvs_node1 Hv_node") as "Hvs"; first lia.
      rewrite -Hvs_node.

      iDestruct (nodes۰elemｰlookup with "Hnodes_auth Hnodes_elem_node1") as %Hnodes_lookup_node1.
      iDestruct (big_sepMｰdelete₂ with "Hnodes [$Hnode1]") as "Hnodes"; first done.
      { iDestruct (big_sepL_lookup with "Hvs_node1") as "$"; first done.
        iSteps. iPureIntro.
        rewrite Hvs_node list_insert_insert_eq list_insert_id //.
      }
      iClear "Hv_node". clear dependent i_node v_node.
      iDestruct (big_sepMｰdelete₁ node with "Hnodes") as "((:node۰model =2) & Hnodes)"; first done.

      iSteps.
  Qed.
  #[local] Lemma parray٠rerootｰspec γ node vs :
    {{{
      parray۰inv γ ∗
      nodes۰elem γ node vs
    }}}
      parray٠reroot #node
    {{{
      nodes
    , RET (γ.(metadata۰equal),γ.(metadata۰data));
      inv' γ nodes node
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & #Hnodes_elem_node) HΦ".
    iDestruct (nodes۰elemｰlookup with "Hnodes_auth Hnodes_elem_node") as %Hnodes_lookup_node.

    wp۰rec.
    destruct_decide (node = root) as -> | Hnode.

    - iStep 16. iFrame "∗#" => //.

    - iDestruct (big_sepM_lookup_acc with "Hnodes") as "((:node۰model) & Hnodes)".
      { rewrite lookup_delete_ne //. }
      wp۰load.

      wp۰apply+ (parray٠reroot₁ｰspec vs with "[- HΦ]") as "(:reroot۰inv root=node)".
      { iFrame "∗#". iSteps. }

      iStep 16. iFrame "∗#" => //.
  Qed.

  Lemma parray٠getｰspec {t γ vs} i v :
    (0 ≤ i)%Z →
    vs !! ₊i = Some v →
    {{{
      parray۰inv γ ∗
      parray۰model t γ vs
    }}}
      parray٠get t #i
    {{{
      RET v;
      parray۰inv γ
    }}}.
  Proof.
    iIntros "% %Hvs_lookup %Φ (Hinv & (:model)) HΦ".

    wp۰rec.

    wp۰apply+ (parray٠rerootｰspec with "[$]") as (nodes) "(:inv' root=node !=)".
    iDestruct (nodes۰elemｰagree with "Hnodes_elem_node Hnodes_elem_node_") as %<-.

    wp۰apply+ (array٠unsafe_getｰspec with "Hdata") as "Hdata"; [done.. |].

    iApply "HΦ".
    iFrame "#∗" => //.
  Qed.

  Lemma parray٠setｰspec t γ vs i v :
    (0 ≤ i < length vs)%Z →
    {{{
      parray۰inv γ ∗
      parray۰model t γ vs ∗
      τ v
    }}}
      parray٠set t #i v
    {{{
      t'
    , RET t';
      parray۰inv γ ∗
      parray۰model t' γ (<[₊i := v]> vs)
    }}}.
  Proof.
    iIntros "% %Φ (Hinv & (:model) & #Hv) HΦ".

    wp۰rec.

    wp۰apply+ (parray٠rerootｰspec with "[$Hinv $Hnodes_elem_node]") as (nodes) "(:inv' root=node !=)".
    iDestruct (nodes۰elemｰagree with "Hnodes_elem_node Hnodes_elem_node_") as %<-.

    destruct (lookup_lt_is_Some_2 vs ₊i) as (w & Hvs_node_lookup); first lia.
    wp۰apply+ (array٠unsafe_getｰspec with "Hdata") as "Hdata"; [lia | done.. |].

    iDestruct (big_sepL_lookup with "Hvs_node") as "#Hw"; first done.
    wp۰apply+ (wpｰwand with "(Hequal Hv Hw)") as (res) "(%b & -> & %Hb)".
    destruct b; first subst w; wp۰pures.

    - rewrite list_insert_id //.
      iApply "HΦ".
      iFrame "∗#" => //.

    - wp۰apply (array٠unsafe_setｰspec with "Hdata") as "Hdata"; first done.
      wp۰load.
      wp۰ref root as "Hroot".
      wp۰store. wp۰pures.

      iAssert ⌜nodes !! root = None⌝%I as %Hnodes_lookup_root.
      { rewrite -eq_None_ne_Some. iIntros "%vs_root %Hnodes_lookup_root".
        iDestruct (pointstoｰne with "Hroot Hnode") as %?.
        iDestruct (big_sepM_lookup _ _ root with "Hnodes") as "(:node۰model node=root !=)".
        { rewrite lookup_delete_ne //. congruence. }
        iApply (pointstoｰexclusive with "Hroot Hroot_").
      }

      set vs' := <[₊i := v]> vs.
      iDestruct (big_sepLｰinsert ₊i with "Hvs_node Hv") as "Hvs_root"; first lia.
      iDestruct (nodes۰elemｰlookup with "Hnodes_auth Hnodes_elem_node") as %Hnodes_lookup_node.
      iMod (nodesｰinsert root vs' with "Hnodes_auth") as "(Hnodes_auth & #Hnodes_elem_root)"; first done.
      iDestruct (big_sepMｰdelete₂ with "Hnodes [Hnode]") as "Hnodes"; first done.
      { iExists ₊i, w, root, vs'. iSteps; iPureIntro.
        - rewrite Z2Nat.id //. lia.
        - rewrite list_insert_insert_eq list_insert_id //.
      }
      rewrite -{2}(delete_insert_id nodes root vs') //.

      iApply "HΦ".
      iFrame "∗#". iSteps. iPureIntro.
      rewrite /vs'. simp_length.
  Qed.
End parray۰G.

Require zoo_persistent.parray__opaque.

#[global] Opaque parray۰inv.
#[global] Opaque parray۰model.
