Require Import zoo.prelude.
Require Import zoo.common.option.
Require Import zoo.common.list.
Require Import zoo.base.
Require Export zoo_std.xdeque__types.
Require Export zoo_std.xdeque__code.
Require Import zoo_std.option.
Require Import zoo_std.xdlchain.
Require Import zoo.options.

Implicit Types l node : location.
Implicit Types nodes : list location.
Implicit Types fn : val.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Definition xdeque۰model t nodes : iProp Σ :=
    ∃ l,
    ⌜t = #l⌝ ∗
    l.[xdeque_prev] ↦ from_option #@{location} t (last nodes) ∗
    l.[xdeque_next] ↦ from_option #@{location} t (head nodes) ∗
    xdlchain t nodes t.

  #[global] Instance xdeque۰model𑁒timeless t nodes :
    Timeless (xdeque۰model t nodes).
  Proof.
    apply _.
  Qed.

  Lemma xdeque۰model𑁒exclusive t nodes1 nodes2 :
    xdeque۰model t nodes1 -∗
    xdeque۰model t nodes2 -∗
    False.
  Proof.
    iIntros "(%l1 & %Heq1 & Hprev1 & _) (%l2 & %Heq2 & Hprev2 & _)". simplify.
    iApply (pointsto𑁒exclusive with "Hprev1 Hprev2").
  Qed.

  Lemma xdeque۰model𑁒NoDup t nodes :
    xdeque۰model t nodes ⊢
    ⌜NoDup nodes⌝.
  Proof.
    iIntros "(%l & -> & _ & _ & Hnodes)".
    iApply (xdlchain𑁒NoDup with "Hnodes").
  Qed.

  Lemma xdeque٠create𑁒spec :
    {{{
      True
    }}}
      xdeque٠create ()
    {{{
      t
    , RET t;
      (∃ l, ⌜t = #l⌝ ∗ meta_token l ⊤) ∗
      xdeque۰model t []
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma xdeque٠is_empty𑁒spec t nodes :
    {{{
      xdeque۰model t nodes
    }}}
      xdeque٠is_empty t
    {{{
      RET #(bool_decide (nodes = []%list));
      xdeque۰model t nodes
    }}}.
  Proof.
    iIntros "%Φ (%l & -> & Hprev & Hnext & Hnodes) HΦ".
    wp۰rec. wp۰load.
    destruct nodes as [| node nodes] => /=; wp۰pures.
    - rewrite bool_decide_eq_true_2 //. iSteps.
    - case_bool_decide; last iSteps.
      subst.
      iDestruct (xdlchain𑁒cons₁ with "Hnodes") as "(Hnode_prev & _)"; first done.
      iDestruct (pointsto𑁒exclusive with "Hprev Hnode_prev") as %[].
  Qed.

  #[local] Lemma xdeque٠link𑁒spec node1 v1 node2 v2 :
    {{{
      node1.[xdeque_next] ↦ v1 ∗
      node2.[xdeque_prev] ↦ v2
    }}}
      xdeque٠link #node1 #node2
    {{{
      RET ();
      node1.[xdeque_next] ↦ #node2 ∗
      node2.[xdeque_prev] ↦ #node1
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma xdeque٠push_front𑁒spec t nodes node prev next :
    {{{
      xdeque۰model t nodes ∗
      node.[xdeque_prev] ↦ prev ∗
      node.[xdeque_next] ↦ next
    }}}
      xdeque٠push_front t #node
    {{{
      RET ();
      xdeque۰model t (node :: nodes)
    }}}.
  Proof.
    iIntros "%Φ ((%l & -> & Hprev & Hnext & Hnodes) & Hnode_prev & Hnode_next) HΦ".
    wp۰rec. wp۰load. wp۰rec.
    wp۰apply+ (xdeque٠link𑁒spec with "[$Hnext $Hnode_prev]") as "(Hnext & Hnode_prev)".
    wp۰pures.
    destruct nodes as [| node' nodes] => /=.
    - wp۰apply (xdeque٠link𑁒spec with "[$Hnode_next $Hprev]") as "(Hnode_next & Hprev)".
      iSteps.
      iApply (xdlchain𑁒cons₂ _ _ [] with "Hnode_prev Hnode_next").
      iApply xdlchain𑁒nil.
    - iDestruct (xdlchain𑁒cons₁ with "Hnodes") as "(Hnode'_prev & Hnode'_next & Hnodes)"; first done.
      wp۰apply (xdeque٠link𑁒spec with "[$Hnode_next $Hnode'_prev]") as "(Hnode_next & Hnode'_prev)".
      iSteps.
      iApply (xdlchain𑁒cons₂ _ _ (node' :: nodes) with "Hnode_prev Hnode_next").
      iApply (xdlchain𑁒cons₂ with "Hnode'_prev Hnode'_next Hnodes").
  Qed.

  Lemma xdeque٠push_back𑁒spec t nodes node prev next :
    {{{
      xdeque۰model t nodes ∗
      node.[xdeque_prev] ↦ prev ∗
      node.[xdeque_next] ↦ next
    }}}
      xdeque٠push_back t #node
    {{{
      RET ();
      xdeque۰model t (nodes ++ [node])
    }}}.
  Proof.
    iIntros "%Φ ((%l & -> & Hprev & Hnext & Hnodes) & Hnode_prev & Hnode_next) HΦ".
    wp۰rec. wp۰load. wp۰rec. wp۰pures.
    destruct nodes as [| node' nodes _] using rev_ind => /=.
    - wp۰apply (xdeque٠link𑁒spec with "[$Hnext $Hnode_prev]") as "(Hnext & Hnode_prev)".
      wp۰apply+ (xdeque٠link𑁒spec with "[$Hnode_next $Hprev]") as "(Hnode_next & Hprev)".
      iSteps.
      iApply (xdlchain𑁒cons₂ _ _ [] with "Hnode_prev Hnode_next").
      iApply xdlchain𑁒nil.
    - rewrite last_snoc /=.
      iDestruct (xdlchain𑁒snoc₁ with "Hnodes") as "(Hnodes & Hnode'_prev & Hnode'_next)"; first done.
      wp۰apply (xdeque٠link𑁒spec with "[$Hnode'_next $Hnode_prev]") as "(Hnode'_next & Hnode_prev)".
      wp۰apply+ (xdeque٠link𑁒spec with "[$Hnode_next $Hprev]") as "(Hnode_next & Hprev)".
      iSteps; [iPureIntro.. |].
      + rewrite last_snoc //.
      + rewrite -assoc head_snoc_snoc //.
      + iApply (xdlchain𑁒snoc₂ _ (nodes ++ [node']) with "[Hnodes Hnode'_prev Hnode'_next] [Hnode_prev] Hnode_next"); last rewrite last_snoc //.
        iApply (xdlchain𑁒snoc₂ with "Hnodes Hnode'_prev Hnode'_next").
  Qed.

  Lemma xdeque٠pop_front𑁒spec t nodes :
    {{{
      xdeque۰model t nodes
    }}}
      xdeque٠pop_front t
    {{{
      RET #*@{location} $ head nodes : option val;
      xdeque۰model t (tail nodes)
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp۰rec.
    wp۰apply (xdeque٠is_empty𑁒spec with "Hmodel") as "(%l & -> & Hprev & Hnext & Hnodes)".
    case_bool_decide.
    - subst. iSteps.
    - wp۰load.
      destruct nodes as [| node nodes] => //=.
      iDestruct (xdlchain𑁒cons₁ with "Hnodes") as "(Hnode_prev & Hnode_next & Hnodes)"; first done.
      wp۰load. wp۰pures.
      destruct nodes as [| node' nodes] => /=.
      + wp۰apply (xdeque٠link𑁒spec with "[$Hnext $Hprev]") as "(Hnext & Hprev)".
        iSteps.
      + iDestruct (xdlchain𑁒cons₁ with "Hnodes") as "(Hnode'_prev & Hnode'_next & Hnodes)"; first done.
      wp۰apply (xdeque٠link𑁒spec with "[$Hnext $Hnode'_prev]") as "(Hnext & Hnode'_prev)".
      iSteps.
      iApply (xdlchain𑁒cons₂ with "Hnode'_prev Hnode'_next Hnodes").
  Qed.

  Lemma xdeque٠pop_back𑁒spec t nodes :
    {{{
      xdeque۰model t nodes
    }}}
      xdeque٠pop_back t
    {{{
      o
    , RET #*@{location} o : option val;
      match o with
      | None =>
          ⌜nodes = []⌝ ∗
          xdeque۰model t []
      | Some node =>
          ∃ nodes',
          ⌜nodes = nodes' ++ [node]⌝ ∗
          xdeque۰model t nodes'
      end
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp۰rec.
    wp۰apply (xdeque٠is_empty𑁒spec with "Hmodel") as "(%l & -> & Hprev & Hnext & Hnodes)".
    case_bool_decide; wp۰pures.
    - subst.
      iApply ("HΦ" $! None).
      iSteps.
    - wp۰load.
      destruct nodes as [| node1 nodes _] using rev_ind => //=.
      rewrite last_snoc /=.
      iDestruct (xdlchain𑁒snoc₁ with "Hnodes") as "(Hnodes & Hnode1_prev & Hnode1_next)"; first done.
      wp۰load.
      destruct nodes as [| node2 nodes _] using rev_ind => /=.
      + wp۰apply+ (xdeque٠link𑁒spec with "[$Hnext $Hprev]") as "(Hnext & Hprev)".
        wp۰pures.
        iApply ("HΦ" $! (Some _)).
        iExists []. iSteps.
      + rewrite last_snoc.
        iDestruct (xdlchain𑁒snoc₁ with "Hnodes") as "(Hnodes & Hnode2_prev & Hnode2_next)"; first done.
        wp۰apply+ (xdeque٠link𑁒spec with "[$Hnode2_next $Hprev]") as "(Hnode2_next & Hprev)".
        wp۰pures.
        iApply ("HΦ" $! (Some _)).
        iSteps; first iPureIntro.
        * rewrite last_snoc //.
        * rewrite -assoc head_snoc_snoc //.
        * iApply (xdlchain𑁒snoc₂ with "Hnodes Hnode2_prev Hnode2_next").
  Qed.

  Lemma xdeque٠remove𑁒spec {t nodes} i node :
    nodes !! i = Some node →
    {{{
      xdeque۰model t nodes
    }}}
      xdeque٠remove #node
    {{{
      RET ();
      xdeque۰model t (delete i nodes)
    }}}.
  Proof.
    iIntros "%Hlookup %Φ (%l & -> & Hprev & Hnext & Hnodes) HΦ".
    wp۰rec.
    wp۰apply (xdlchain٠prev𑁒spec𑁒lookup with "Hnodes") as "Hnodes"; first done.
    wp۰apply+ (xdlchain٠next𑁒spec𑁒lookup with "Hnodes") as "Hnodes"; first done.
    wp۰pures. wp۰rec. wp۰pures.
    iDestruct (xdlchain𑁒lookup with "Hnodes") as "(Hnodes1 & Hnode_prev & Hnode_next & Hnodes2)"; first done.

    set nodes1 := take i nodes.
    set nodes2 := drop ˖i nodes.
    set nodes' := nodes1 ++ nodes2.

    wp۰bind (_ <-{xdeque_next} _)%E.
    wp۰apply (wp𑁒wand (λ res,
      ⌜res = ()%V⌝ ∗
      l.[xdeque_next] ↦ from_option #@{location} #l (head nodes') ∗
      xdlchain #l nodes1 (from_option #@{location} #l $ head nodes2)
    )%I with "[Hnext Hnodes1]") as (res) "(-> & Hnext & Hnodes1)".
    { destruct nodes1 as [| node1 nodes1' _] eqn:Hnodes1 using rev_ind => /=; first iSteps.
      rewrite last_snoc /=.
      iDestruct (xdlchain𑁒snoc₁ with "Hnodes1") as "(Hnodes1 & Hnode1_prev & Hnode1_next)"; first done.
      wp۰store.
      iDestruct (xdlchain𑁒snoc₂ with "Hnodes1 Hnode1_prev Hnode1_next") as "Hnodes1".
      iSteps. iPureIntro.
      rewrite -(take_drop i nodes) -/nodes1 /nodes' Hnodes1 -!assoc !head𑁒app𑁒cons //.
    }

    wp۰apply+ (wp𑁒wand (λ res,
      ⌜res = ()%V⌝ ∗
      l.[xdeque_prev] ↦ from_option #@{location} #l (last nodes') ∗
      xdlchain (from_option #@{location} #l $ last nodes1) nodes2 #l
    )%I with "[Hprev Hnodes2]") as (res) "(-> & Hprev & Hnodes2)".
    { destruct nodes2 as [| node2 nodes2'] eqn:Hnodes2 => /=.
      - rewrite right_id in nodes' |- *. iSteps.
      - iDestruct (xdlchain𑁒cons₁ with "Hnodes2") as "(Hnode2_prev & Hnode2_next & Hnodes2)"; first done.
        wp۰store.
        iDestruct (xdlchain𑁒cons₂ with "Hnode2_prev Hnode2_next Hnodes2") as "Hnodes2".
        iSteps. iPureIntro.
        rewrite -(take_drop ˖i nodes) -/nodes2 /nodes' Hnodes2 !last_app_cons //.
    }

    iDestruct (xdlchain𑁒app₂ with "Hnodes1 Hnodes2") as "Hnodes".
    rewrite /nodes' -delete_take_drop. iSteps.
  Qed.

  #[local] Lemma xdeque٠iter_aux𑁒spec Ψ i fn l nodes node :
    (nodes ++ [l]) !! i = Some node →
    {{{
      ▷ Ψ (take i nodes) ∗
      xdeque۰model #l nodes ∗
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
      xdeque٠iter_aux fn #l #node
    {{{
      RET ();
      xdeque۰model #l nodes ∗
      Ψ nodes
    }}}.
  Proof.
    iIntros "%Hlookup %Φ (HΨ & (%_l & %Heq & Hprev & Hnext & Hnodes) & #Hfn) HΦ". injection Heq as <-.
    iLöb as "HLöb" forall (i node Hlookup).
    wp۰rec. wp۰pures.
    destruct (Z.lt_trichotomy i (length nodes)) as [Hi | [Hi | Hi]].
    - rewrite lookup_app_l in Hlookup; first lia.
      iDestruct (xdlchain𑁒lookup𑁒acc with "Hnodes") as "(Hnode_prev & Hnode_next & Hnodes)"; first done.
      iAssert ⌜node ≠ l⌝%I as %Hnode.
      { iIntros "->".
        iApply (pointsto𑁒exclusive with "Hnode_prev Hprev").
      }
      rewrite bool_decide_eq_false_2 //.
      wp۰apply+ (wp𑁒wand with "(Hfn [%] HΨ)") as (res) "(-> & HΨ)".
      { erewrite take_drop_middle => //. }
      wp۰load.
      iEval (rewrite from_option𑁒default).
      wp۰apply ("HLöb" $! ˖i with "[%] [HΨ] Hprev Hnext (Hnodes Hnode_prev Hnode_next) HΦ").
      { rewrite head𑁒drop.
        destruct (nodes !! ˖i) as [node' |] eqn:Hlookup'.
        - erewrite lookup_app_l_Some => //.
        - apply length𑁒lookup𑁒last in Hlookup'; last done.
          rewrite list_lookup_middle //.
      } {
        erewrite take_S_r => //.
      }
    - rewrite list_lookup_middle in Hlookup; first lia. simplify.
      rewrite bool_decide_eq_true_2 // firstn_all2 //. iSteps.
    - rewrite list_lookup_alt length_app /= in Hlookup. lia.
  Qed.
  Lemma xdeque٠iter𑁒spec Ψ fn t nodes :
    {{{
      ▷ Ψ [] ∗
      xdeque۰model t nodes ∗
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
      xdeque٠iter fn t
    {{{
      RET ();
      xdeque۰model t nodes ∗
      Ψ nodes
    }}}.
  Proof.
    iIntros "%Φ (HΨ & (%l & -> & Hprev & Hnext & Hnodes) & #Hfn) HΦ".
    wp۰rec. wp۰load.
    iEval (rewrite from_option𑁒default).
    wp۰apply (xdeque٠iter_aux𑁒spec Ψ 0 with "[-HΦ] HΦ").
    { destruct nodes; done. }
    iSteps.
  Qed.
End zoo۰G.

Require zoo_std.xdeque__opaque.

#[global] Opaque xdeque۰model.
