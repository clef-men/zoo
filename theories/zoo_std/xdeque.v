From zoo Require Import
  prelude.
From zoo.common Require Import
  option
  list.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  xdeque__types
  xdeque__code.
From zoo_std Require Import
  option
  xdlchain.
From zoo Require Import
  options.

Implicit Types l node : location.
Implicit Types nodes : list location.
Implicit Types fn : val.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition xdeque_model t nodes : iProp Σ :=
    ∃ l,
    ⌜t = #l⌝ ∗
    l.[xdeque_prev] ↦ from_option #@{location} t (last nodes) ∗
    l.[xdeque_next] ↦ from_option #@{location} t (head nodes) ∗
    xdlchain t nodes t.

  #[global] Instance xdeque_model_timeless t nodes :
    Timeless (xdeque_model t nodes).
  Proof.
    apply _.
  Qed.

  Lemma xdeque_model_exclusive t nodes1 nodes2 :
    xdeque_model t nodes1 -∗
    xdeque_model t nodes2 -∗
    False.
  Proof.
    iIntros "(%l1 & %Heq1 & Hprev1 & _) (%l2 & %Heq2 & Hprev2 & _)". simplify.
    iApply (pointsto_exclusive with "Hprev1 Hprev2").
  Qed.

  Lemma xdeque_model_NoDup t nodes :
    xdeque_model t nodes ⊢
    ⌜NoDup nodes⌝.
  Proof.
    iIntros "(%l & -> & _ & _ & Hnodes)".
    iApply (xdlchain_NoDup with "Hnodes").
  Qed.

  Lemma xdeque_create_spec :
    {{{
      True
    }}}
      xdeque_create ()
    {{{ t,
      RET t;
      (∃ l, ⌜t = #l⌝ ∗ meta_token l ⊤) ∗
      xdeque_model t []
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma xdeque_is_empty_spec t nodes :
    {{{
      xdeque_model t nodes
    }}}
      xdeque_is_empty t
    {{{
      RET #(bool_decide (nodes = []%list));
      xdeque_model t nodes
    }}}.
  Proof.
    iIntros "%Φ (%l & -> & Hprev & Hnext & Hnodes) HΦ".
    wp_rec. wp_load.
    destruct nodes as [| node nodes] => /=; wp_pures.
    - rewrite bool_decide_eq_true_2 //. iSteps.
    - case_bool_decide; last iSteps.
      subst.
      iDestruct (xdlchain_cons_1 with "Hnodes") as "(Hnode_prev & _)"; first done.
      iDestruct (pointsto_exclusive with "Hprev Hnode_prev") as %[].
  Qed.

  #[local] Lemma xdeque_link_spec node1 v1 node2 v2 :
    {{{
      node1.[xdeque_next] ↦ v1 ∗
      node2.[xdeque_prev] ↦ v2
    }}}
      xdeque_link #node1 #node2
    {{{
      RET ();
      node1.[xdeque_next] ↦ #node2 ∗
      node2.[xdeque_prev] ↦ #node1
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma xdeque_push_front_spec t nodes node prev next :
    {{{
      xdeque_model t nodes ∗
      node.[xdeque_prev] ↦ prev ∗
      node.[xdeque_next] ↦ next
    }}}
      xdeque_push_front t #node
    {{{
      RET ();
      xdeque_model t (node :: nodes)
    }}}.
  Proof.
    iIntros "%Φ ((%l & -> & Hprev & Hnext & Hnodes) & Hnode_prev & Hnode_next) HΦ".
    wp_rec. wp_load. wp_rec.
    wp_smart_apply (xdeque_link_spec with "[$Hnext $Hnode_prev]") as "(Hnext & Hnode_prev)".
    wp_pures.
    destruct nodes as [| node' nodes] => /=.
    - wp_apply (xdeque_link_spec with "[$Hnode_next $Hprev]") as "(Hnode_next & Hprev)".
      iSteps.
      iApply (xdlchain_cons_2 _ _ [] with "Hnode_prev Hnode_next").
      iApply xdlchain_nil.
    - iDestruct (xdlchain_cons_1 with "Hnodes") as "(Hnode'_prev & Hnode'_next & Hnodes)"; first done.
      wp_apply (xdeque_link_spec with "[$Hnode_next $Hnode'_prev]") as "(Hnode_next & Hnode'_prev)".
      iSteps.
      iApply (xdlchain_cons_2 _ _ (node' :: nodes) with "Hnode_prev Hnode_next").
      iApply (xdlchain_cons_2 with "Hnode'_prev Hnode'_next Hnodes").
  Qed.

  Lemma xdeque_push_back_spec t nodes node prev next :
    {{{
      xdeque_model t nodes ∗
      node.[xdeque_prev] ↦ prev ∗
      node.[xdeque_next] ↦ next
    }}}
      xdeque_push_back t #node
    {{{
      RET ();
      xdeque_model t (nodes ++ [node])
    }}}.
  Proof.
    iIntros "%Φ ((%l & -> & Hprev & Hnext & Hnodes) & Hnode_prev & Hnode_next) HΦ".
    wp_rec. wp_load. wp_rec. wp_pures.
    destruct nodes as [| node' nodes _] using rev_ind => /=.
    - wp_apply (xdeque_link_spec with "[$Hnext $Hnode_prev]") as "(Hnext & Hnode_prev)".
      wp_smart_apply (xdeque_link_spec with "[$Hnode_next $Hprev]") as "(Hnode_next & Hprev)".
      iSteps.
      iApply (xdlchain_cons_2 _ _ [] with "Hnode_prev Hnode_next").
      iApply xdlchain_nil.
    - rewrite last_snoc /=.
      iDestruct (xdlchain_snoc_1 with "Hnodes") as "(Hnodes & Hnode'_prev & Hnode'_next)"; first done.
      wp_apply (xdeque_link_spec with "[$Hnode'_next $Hnode_prev]") as "(Hnode'_next & Hnode_prev)".
      wp_smart_apply (xdeque_link_spec with "[$Hnode_next $Hprev]") as "(Hnode_next & Hprev)".
      iSteps; [iPureIntro.. |].
      + rewrite last_snoc //.
      + rewrite -assoc head_snoc_snoc //.
      + iApply (xdlchain_snoc_2 _ (nodes ++ [node']) with "[Hnodes Hnode'_prev Hnode'_next] [Hnode_prev] Hnode_next"); last rewrite last_snoc //.
        iApply (xdlchain_snoc_2 with "Hnodes Hnode'_prev Hnode'_next").
  Qed.

  Lemma xdeque_pop_front_spec t nodes :
    {{{
      xdeque_model t nodes
    }}}
      xdeque_pop_front t
    {{{
      RET (#@{location} <$> head nodes : option val) : val;
      xdeque_model t (tail nodes)
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp_rec.
    wp_apply (xdeque_is_empty_spec with "Hmodel") as "(%l & -> & Hprev & Hnext & Hnodes)".
    case_bool_decide.
    - subst. iSteps.
    - wp_load.
      destruct nodes as [| node nodes] => //=.
      iDestruct (xdlchain_cons_1 with "Hnodes") as "(Hnode_prev & Hnode_next & Hnodes)"; first done.
      wp_load. wp_pures.
      destruct nodes as [| node' nodes] => /=.
      + wp_apply (xdeque_link_spec with "[$Hnext $Hprev]") as "(Hnext & Hprev)".
        iSteps.
      + iDestruct (xdlchain_cons_1 with "Hnodes") as "(Hnode'_prev & Hnode'_next & Hnodes)"; first done.
      wp_apply (xdeque_link_spec with "[$Hnext $Hnode'_prev]") as "(Hnext & Hnode'_prev)".
      iSteps.
      iApply (xdlchain_cons_2 with "Hnode'_prev Hnode'_next Hnodes").
  Qed.

  Lemma xdeque_pop_back_spec t nodes :
    {{{
      xdeque_model t nodes
    }}}
      xdeque_pop_back t
    {{{ o,
      RET (#@{location} <$> o : option val) : val;
      match o with
      | None =>
          ⌜nodes = []⌝ ∗
          xdeque_model t []
      | Some node =>
          ∃ nodes',
          ⌜nodes = nodes' ++ [node]⌝ ∗
          xdeque_model t nodes'
      end
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp_rec.
    wp_apply (xdeque_is_empty_spec with "Hmodel") as "(%l & -> & Hprev & Hnext & Hnodes)".
    case_bool_decide; wp_pures.
    - subst.
      iApply ("HΦ" $! None).
      iSteps.
    - wp_load.
      destruct nodes as [| node1 nodes _] using rev_ind => //=.
      rewrite last_snoc /=.
      iDestruct (xdlchain_snoc_1 with "Hnodes") as "(Hnodes & Hnode1_prev & Hnode1_next)"; first done.
      wp_load.
      destruct nodes as [| node2 nodes _] using rev_ind => /=.
      + wp_smart_apply (xdeque_link_spec with "[$Hnext $Hprev]") as "(Hnext & Hprev)".
        wp_pures.
        iApply ("HΦ" $! (Some _)).
        iExists []. iSteps.
      + rewrite last_snoc.
        iDestruct (xdlchain_snoc_1 with "Hnodes") as "(Hnodes & Hnode2_prev & Hnode2_next)"; first done.
        wp_smart_apply (xdeque_link_spec with "[$Hnode2_next $Hprev]") as "(Hnode2_next & Hprev)".
        wp_pures.
        iApply ("HΦ" $! (Some _)).
        iSteps; first iPureIntro.
        * rewrite last_snoc //.
        * rewrite -assoc head_snoc_snoc //.
        * iApply (xdlchain_snoc_2 with "Hnodes Hnode2_prev Hnode2_next").
  Qed.

  Lemma xdeque_remove_spec {t nodes} i node :
    nodes !! i = Some node →
    {{{
      xdeque_model t nodes
    }}}
      xdeque_remove #node
    {{{
      RET ();
      xdeque_model t (delete i nodes)
    }}}.
  Proof.
    iIntros "%Hlookup %Φ (%l & -> & Hprev & Hnext & Hnodes) HΦ".
    wp_rec.
    wp_apply (xdlchain_prev_spec_lookup with "Hnodes") as "Hnodes"; first done.
    wp_smart_apply (xdlchain_next_spec_lookup with "Hnodes") as "Hnodes"; first done.
    wp_pures. wp_rec. wp_pures.
    iDestruct (xdlchain_lookup with "Hnodes") as "(Hnodes1 & Hnode_prev & Hnode_next & Hnodes2)"; first done.

    set nodes1 := take i nodes.
    set nodes2 := drop (S i) nodes.
    set nodes' := nodes1 ++ nodes2.

    wp_bind (_ <-{xdeque_next} _)%E.
    wp_apply (wp_wand (λ res,
      ⌜res = ()%V⌝ ∗
      l.[xdeque_next] ↦ from_option #@{location} #l (head nodes') ∗
      xdlchain #l nodes1 (from_option #@{location} #l $ head nodes2)
    )%I with "[Hnext Hnodes1]") as (res) "(-> & Hnext & Hnodes1)".
    { destruct nodes1 as [| node1 nodes1' _] eqn:Hnodes1 using rev_ind => /=; first iSteps.
      rewrite last_snoc /=.
      iDestruct (xdlchain_snoc_1 with "Hnodes1") as "(Hnodes1 & Hnode1_prev & Hnode1_next)"; first done.
      wp_store.
      iDestruct (xdlchain_snoc_2 with "Hnodes1 Hnode1_prev Hnode1_next") as "Hnodes1".
      iSteps. iPureIntro.
      rewrite -(take_drop i nodes) -/nodes1 /nodes' Hnodes1 -!assoc !head_app_cons //.
    }

    wp_smart_apply (wp_wand (λ res,
      ⌜res = ()%V⌝ ∗
      l.[xdeque_prev] ↦ from_option #@{location} #l (last nodes') ∗
      xdlchain (from_option #@{location} #l $ last nodes1) nodes2 #l
    )%I with "[Hprev Hnodes2]") as (res) "(-> & Hprev & Hnodes2)".
    { destruct nodes2 as [| node2 nodes2'] eqn:Hnodes2 => /=.
      - rewrite right_id in nodes' |- *. iSteps.
      - iDestruct (xdlchain_cons_1 with "Hnodes2") as "(Hnode2_prev & Hnode2_next & Hnodes2)"; first done.
        wp_store.
        iDestruct (xdlchain_cons_2 with "Hnode2_prev Hnode2_next Hnodes2") as "Hnodes2".
        iSteps. iPureIntro.
        rewrite -(take_drop (S i) nodes) -/nodes2 /nodes' Hnodes2 !last_app_cons //.
    }

    iDestruct (xdlchain_app_2 with "Hnodes1 Hnodes2") as "Hnodes".
    rewrite /nodes' -delete_take_drop. iSteps.
  Qed.

  #[local] Lemma xdeque_iter_aux_spec Ψ i fn l nodes node :
    (nodes ++ [l]) !! i = Some node →
    {{{
      ▷ Ψ (take i nodes) ∗
      xdeque_model #l nodes ∗
      □ (
        ∀ nodes_done node nodes_todo,
        ⌜nodes = nodes_done ++ node :: nodes_todo⌝ -∗
        Ψ nodes_done -∗
        WP fn #node {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (nodes_done ++ [#node])
        }}
      )
    }}}
      xdeque_iter_aux fn #l #node
    {{{
      RET ();
      xdeque_model #l nodes ∗
      Ψ nodes
    }}}.
  Proof.
    iIntros "%Hlookup %Φ (HΨ & (%_l & %Heq & Hprev & Hnext & Hnodes) & #Hfn) HΦ". injection Heq as <-.
    iLöb as "HLöb" forall (i node Hlookup).
    wp_rec. wp_pures.
    destruct (Z.lt_trichotomy i (length nodes)) as [Hi | [Hi | Hi]].
    - rewrite lookup_app_l in Hlookup; first lia.
      iDestruct (xdlchain_lookup_acc with "Hnodes") as "(Hnode_prev & Hnode_next & Hnodes)"; first done.
      iAssert ⌜node ≠ l⌝%I as %Hnode.
      { iIntros "->".
        iApply (pointsto_exclusive with "Hnode_prev Hprev").
      }
      rewrite bool_decide_eq_false_2 //.
      wp_smart_apply (wp_wand with "(Hfn [%] HΨ)") as (res) "(-> & HΨ)".
      { erewrite take_drop_middle => //. }
      wp_load.
      iEval (rewrite from_option_default).
      wp_apply ("HLöb" $! (S i) with "[%] [HΨ] Hprev Hnext (Hnodes Hnode_prev Hnode_next) HΦ").
      { rewrite head_drop.
        destruct (nodes !! S i) as [node' |] eqn:Hlookup'.
        - erewrite lookup_app_l_Some => //.
        - apply length_lookup_last in Hlookup'; last done.
          rewrite list_lookup_middle //.
      } {
        erewrite take_S_r => //.
      }
    - rewrite list_lookup_middle in Hlookup; first lia. simplify.
      rewrite bool_decide_eq_true_2 // firstn_all2 //. iSteps.
    - rewrite list_lookup_alt length_app /= in Hlookup. lia.
  Qed.
  Lemma xdeque_iter_spec Ψ fn t nodes :
    {{{
      ▷ Ψ [] ∗
      xdeque_model t nodes ∗
      □ (
        ∀ nodes_done node nodes_todo,
        ⌜nodes = nodes_done ++ node :: nodes_todo⌝ -∗
        Ψ nodes_done -∗
        WP fn #node {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (nodes_done ++ [#node])
        }}
      )
    }}}
      xdeque_iter fn t
    {{{
      RET ();
      xdeque_model t nodes ∗
      Ψ nodes
    }}}.
  Proof.
    iIntros "%Φ (HΨ & (%l & -> & Hprev & Hnext & Hnodes) & #Hfn) HΦ".
    wp_rec. wp_load.
    iEval (rewrite from_option_default).
    wp_apply (xdeque_iter_aux_spec Ψ 0 with "[-HΦ] HΦ").
    { destruct nodes; done. }
    iSteps.
  Qed.
End zoo_G.

#[global] Opaque xdeque_create.
#[global] Opaque xdeque_is_empty.
#[global] Opaque xdeque_push_front.
#[global] Opaque xdeque_push_back.
#[global] Opaque xdeque_pop_front.
#[global] Opaque xdeque_pop_back.
#[global] Opaque xdeque_remove.
#[global] Opaque xdeque_iter.

#[global] Opaque xdeque_model.
