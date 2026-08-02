Require Import iris.base_logic.lib.ghost_map.

Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.iris.bi.big_op.
Require Import zoo.base.
Require Export zoo_persistent.sarray__code.
Require Import zoo_persistent.sarray__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type l node root : location.
Implicit Type v t s equal : val.
Implicit Type vs : list val.
Implicit Type nodes : gmap location (list val).

Class SarrayG Σ `{zoo۰G : !ZooG Σ} :=
  { sarray۰G۰nodes۰G : ghost_mapG Σ location (list val)
  }.

Definition sarray۰Σ :=
  #[ghost_mapΣ location (list val)
  ].
#[global] Instance subGｰsarray۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG sarray۰Σ Σ →
  SarrayG Σ.
Proof.
  solve_inG.
Qed.

Section sarray۰G.
  Context `{sarray۰G : SarrayG Σ}.
  Context τ `{!iType (iProp Σ) τ}.

  Record metadata :=
    { metadata۰equal : val
    ; metadata۰size : nat
    ; metadata۰data : val
    ; metadata۰nodes : gname
    }.
  Implicit Type γ : metadata.

  #[local] Instance metadataｰeq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[local] Instance metadataｰcountable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition nodes۰auth' γ_nodes :=
    @ghost_map_auth _ _ _ _ _ sarray۰G۰nodes۰G γ_nodes 1.
  #[local] Definition nodes۰auth γ :=
    nodes۰auth' γ.(metadata۰nodes).
  #[local] Definition nodes۰elem' γ_nodes node :=
    @ghost_map_elem _ _ _ _ _ sarray۰G۰nodes۰G γ_nodes node DfracDiscarded.
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

  #[local] Definition model' γ nodes root vs_root : iProp Σ :=
    nodes۰auth γ nodes ∗
    root ↦ᵣ §Root ∗
    array۰model γ.(metadata۰data) (DfracOwn 1) vs_root ∗
    nodes۰elem γ root vs_root ∗
    ⌜length vs_root = γ.(metadata۰size)⌝ ∗
    ([∗ list] v ∈ vs_root, τ v) ∗
    [∗ map] node ↦ vs ∈ delete root nodes,
      node۰model γ node vs.
  #[local] Instance : CustomIpat "model'" :=
    " ( Hnodes_auth{_{}}
      & H{root}{}
      & Hdata{_{}}
      & #Hnodes_elem_{root}{_{}}
      & %
      & #Hvs_{root}{_{}}
      & Hnodes{_{}}
      )
    ".
  Definition sarray۰model t vs : iProp Σ :=
    ∃ l γ nodes root,
    ⌜t = #l⌝ ∗
    l ↪ γ ∗
    l.[equal] ↦□ γ.(metadata۰equal) ∗
    l.[data] ↦□ γ.(metadata۰data) ∗
    l.[root] ↦ #root ∗
    equal۰model γ.(metadata۰equal) ∗
    model' γ nodes root vs.
  #[local] Instance : CustomIpat "model" :=
    " ( %l{}
      & %γ{}
      & %nodes{}
      & %root{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & #Hl_equal{_{}}
      & #Hl_data{_{}}
      & Hl_root{_{}}
      & #Hequal{_{}}
      & (:model')
      )
    ".

  Definition sarray۰snapshot s t vs : iProp Σ :=
    ∃ node l γ,
    ⌜s = #node⌝ ∗
    ⌜t = #l⌝ ∗
    l ↪ γ ∗
    nodes۰elem γ node vs.
  #[local] Instance : CustomIpat "snapshot" :=
    " ( %node
      & %l_
      & %γ_
      & ->
      & %Heq
      & #Hmeta_
      & #Hnodes_elem_node
      )
    ".

  #[global] Instance sarray۰snapshotｰpersistent s t vs :
    Persistent (sarray۰snapshot s t vs).
  Proof.
    apply _.
  Qed.

  #[local] Lemma nodesｰalloc root vs :
    ⊢ |==>
      ∃ γ_nodes,
      nodes۰auth' γ_nodes {[root := vs]} ∗
      nodes۰elem' γ_nodes root vs.
  Proof.
    iMod (@ghost_map_alloc _ _ _ _ _ sarray۰G۰nodes۰G {[root := vs]}) as "(%γ_nodes & Hnodes_auth & Hnodes_elem)".
    rewrite big_sepM_singleton.
    iMod (ghost_map_elem_persist with "Hnodes_elem") as "Hnodes_elem".
    iSteps.
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

  Lemma sarray۰modelｰexclusive t vs1 vs2 :
    sarray۰model t vs1 -∗
    sarray۰model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iApply (pointstoｰexclusive with "Hl_root_1 Hl_root_2").
  Qed.

  Lemma sarray٠makeｰspec equal (sz : Z) v :
    (0 ≤ sz)%Z →
    {{{
      equal۰model equal ∗
      τ v
    }}}
      sarray٠make equal #sz v
    {{{
      t
    , RET t;
      sarray۰model t (replicate ₊sz v)
    }}}.
  Proof.
    iIntros "%Hsz %Φ (Hequal & #Hv) HΦ".

    wp۰rec.
    wp۰apply+ (array٠unsafe_makeｰspec with "[//]") as "%data Hdata"; first done.
    wp۰ref root as "Hroot".
    wp۰block l as "Hmeta" "(Hl_equal & Hl_data & Hl_root & _)".
    iMod (pointstoｰpersist with "Hl_equal") as "#Hl_equal".
    iMod (pointstoｰpersist with "Hl_data") as "#Hl_data".

    iMod (nodesｰalloc root (replicate ₊sz v)) as "(%γ_nodes & Hnodes_auth & #Hnodes_elem)".

    pose γ :=
      {|metadata۰equal := equal
      ; metadata۰size := ₊sz
      ; metadata۰data := data
      ; metadata۰nodes := γ_nodes
      |}.
    iMod (metaｰset γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iModIntro. iFrame "#∗".
    rewrite length_replicate delete_singleton_eq big_sepM_empty.
    rewrite big_sepLｰreplicate -big_sepL_intro.
    auto 10.
  Qed.

  Lemma sarray٠getｰspec {t vs} i v :
    (0 ≤ i)%Z →
    vs !! ₊i = Some v →
    {{{
      sarray۰model t vs
    }}}
      sarray٠get t #i
    {{{
      RET v;
      sarray۰model t vs
    }}}.
  Proof.
    iIntros "% %Hvs_lookup %Φ (:model) HΦ".

    wp۰rec. wp۰load.
    wp۰apply (array٠unsafe_getｰspec with "Hdata") as "Hdata"; [done.. |].

    iApply "HΦ".
    iFrame "#∗". iSteps.
  Qed.

  Lemma sarray٠setｰspec t vs i v :
    (0 ≤ i < length vs)%Z →
    {{{
      sarray۰model t vs ∗
      τ v
    }}}
      sarray٠set t #i v
    {{{
      RET ();
      sarray۰model t (<[₊i := v]> vs)
    }}}.
  Proof.
    iIntros "% %Φ ((:model) & #Hv) HΦ".

    wp۰rec. wp۰load.

    destruct (lookup_lt_is_Some_2 vs ₊i) as (w & Hvs_lookup); first lia.
    wp۰apply+ (array٠unsafe_getｰspec with "Hdata") as "Hdata"; [lia | done.. |].

    wp۰load.

    iDestruct (big_sepL_lookup with "Hvs_root") as "#Hw"; first done.
    wp۰apply (wpｰwand with "(Hequal Hv Hw)") as (res) "(%b & -> & %Hb)".
    destruct b; first subst w; wp۰pures.

    - iApply "HΦ".
      rewrite list_insert_id //. iFrame "#∗". iSteps.

    - wp۰ref root' as "Hroot'".
      wp۰load. do 2 wp۰store. wp۰load.
      iApply wpｰfupd.
      wp۰apply (array٠unsafe_setｰspec with "Hdata") as "Hdata"; first done.

      iAssert ⌜nodes !! root' = None⌝%I as %Hnodes_lookup_root'.
      { rewrite -eq_None_ne_Some. iIntros "%vs_root' %Hnodes_lookup_root'".
        iDestruct (pointstoｰne with "Hroot Hroot'") as %?.
        iDestruct (big_sepM_lookup _ _ root' with "Hnodes") as "(:node۰model node=root' !=)".
        { rewrite lookup_delete_ne //. congruence. }
        iApply (pointstoｰexclusive with "Hroot' Hroot'_").
      }

      iApply "HΦ".
      set vs' := <[₊i := v]> vs.
      iDestruct (big_sepLｰinsert ₊i with "Hvs_root Hv") as "Hvs_root'"; first lia.
      iDestruct (nodes۰elemｰlookup with "Hnodes_auth Hnodes_elem_root") as %Hnodes_lookup_root.
      iMod (nodesｰinsert root' vs' with "Hnodes_auth") as "(Hnodes_auth & #Hnodes_elem_root')"; first done.
      iDestruct (big_sepMｰdelete₂ with "Hnodes [Hroot]") as "Hnodes"; first done.
      { iExists ₊i, w, root', vs'. iSteps; iPureIntro.
        - rewrite Z2Nat.id //. lia.
        - rewrite list_insert_insert_eq list_insert_id //.
      }
      rewrite -{2}(delete_insert_id nodes root' vs') //.
      iFrame "#∗". iSteps. iPureIntro.
      rewrite /vs'. simpl_length.
  Qed.

  Lemma sarray٠captureｰspec t vs :
    {{{
      sarray۰model t vs
    }}}
      sarray٠capture t
    {{{
      s
    , RET s;
      sarray۰model t vs ∗
      sarray۰snapshot s t vs
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".

    wp۰rec. wp۰load.

    iApply "HΦ".
    iFrame "#∗". iSteps.
  Qed.

  #[local] Definition restore۰inv γ nodes root vs_root : iProp Σ :=
    ∃ descr_root,
    nodes۰auth γ nodes ∗
    root ↦ᵣ descr_root ∗
    array۰model γ.(metadata۰data) (DfracOwn 1) vs_root ∗
    ⌜length vs_root = γ.(metadata۰size)⌝ ∗
    ([∗ list] v ∈ vs_root, τ v) ∗
    [∗ map] node ↦ vs ∈ delete root nodes,
      node۰model γ node vs.
  #[local] Instance : CustomIpat "restore۰inv" :=
    " ( %descr_{root}
      & Hnodes_auth
      & H{root}
      & Hdata
      & %
      & #Hvs_{root}
      & Hnodes
      )
    ".
  #[local] Lemma sarray٠restore₁ｰspec {γ nodes root vs_root node} vs :
    {{{
      model' γ nodes root vs_root ∗
      nodes۰elem γ node vs
    }}}
      sarray٠restore₁ γ.(metadata۰data) #node
    {{{
      RET ();
      restore۰inv γ nodes node vs
    }}}.
  Proof.
    iLöb as "HLöb" forall (node vs).

    iIntros "%Φ ((:model') & #Hnodes_elem_node) HΦ".
    iDestruct (nodes۰elemｰlookup with "Hnodes_auth Hnodes_elem_node") as %Hnodes_lookup_node.

    wp۰rec.
    destruct_decide (node = root) as -> | Hnode.

    - iDestruct (nodes۰elemｰagree with "Hnodes_elem_node Hnodes_elem_root") as %<-.
      iSteps.

    - iDestruct (big_sepM_lookup_acc with "Hnodes") as "((:node۰model =1) & Hnodes)".
      { rewrite lookup_delete_ne //. }
      wp۰load.

      wp۰apply+ ("HLöb" $! node1 vs_node1 with "[- HΦ]") as "(:restore۰inv root=node1)"; first iFrameSteps.

      destruct (lookup_lt_is_Some_2 vs_node1 i_node) as (v & Hvs_node1_lookup); first lia.
      wp۰apply+ (array٠unsafe_getｰspec with "Hdata") as "Hdata"; [lia | done | lia |].
      wp۰store.
      wp۰apply+ (array٠unsafe_setｰspec with "Hdata") as "Hdata"; first lia.
      rewrite Nat2Z.id -Hvs_node.

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
  Lemma sarray٠restoreｰspec t vs s vs' :
    {{{
      sarray۰model t vs ∗
      sarray۰snapshot s t vs'
    }}}
      sarray٠restore t s
    {{{
      RET ();
      sarray۰model t vs'
    }}}.
  Proof.
    iIntros "%Φ ((:model) & (:snapshot)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (nodes۰elemｰlookup with "Hnodes_auth Hnodes_elem_node") as %Hnodes_lookup_node.

    wp۰rec.
    destruct_decide (node = root) as -> | Hnode.

    - wp۰load. wp۰pures.

      iApply "HΦ".
      iDestruct (nodes۰elemｰagree with "Hnodes_elem_node Hnodes_elem_root") as %->.
      iFrame "#∗". iSteps.

    - iDestruct (big_sepM_lookup_acc with "Hnodes") as "((:node۰model) & Hnodes)".
      { rewrite lookup_delete_ne //. }
      wp۰load.

      wp۰load.
      wp۰apply+ (sarray٠restore₁ｰspec vs' with "[- Hl_root HΦ]") as "(:restore۰inv root=node)"; first iFrameSteps.
      do 2 wp۰store.

      iApply "HΦ".
      iFrame "#∗". iSteps.
  Qed.
End sarray۰G.

Require zoo_persistent.sarray__opaque.

#[global] Opaque sarray۰model.
#[global] Opaque sarray۰snapshot.
