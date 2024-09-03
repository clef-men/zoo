From zoo Require Import
  prelude.
From zoo.common Require Import
  option
  list.
From zoo.language Require Import
  notations
  diaframe.
From zoo.std Require Export
  base.
From zoo.std Require Import
  option
  xdlchain.
From zoo Require Import
  options.

Implicit Types l node : location.
Implicit Types nodes : list location.
Implicit Types fn : val.

Notation "'xdeque_prev'" := (
  in_type "xdlchain" 0
)(in custom zoo_field
).
Notation "'xdeque_next'" := (
  in_type "xdlchain" 1
)(in custom zoo_field
).
Notation "'xdeque_data'" := (
  in_type "xdlchain" 2
)(in custom zoo_field
).

Definition xdeque_create : val :=
  fun: <> =>
    let: "t" := Alloc #0 #2 in
    "t" <-{xdeque_prev} "t" ;;
    "t" <-{xdeque_next} "t" ;;
    "t".

Definition xdeque_is_empty : val :=
  fun: "t" =>
    "t".{xdeque_next} = "t".

#[local] Definition xdeque_insert : val :=
  fun: "prev" "node" "next" =>
    "node" <-{xdeque_prev} "prev" ;;
    "node" <-{xdeque_next} "next" ;;
    "prev" <-{xdeque_next} "node" ;;
    "next" <-{xdeque_prev} "node".

Definition xdeque_push_front : val :=
  fun: "t" "front" =>
    xdeque_insert "t" "front" "t".{xdeque_next}.

Definition xdeque_push_back : val :=
  fun: "t" "back" =>
    xdeque_insert "t".{xdeque_prev} "back" "t".

Definition xdeque_pop_front : val :=
  fun: "t" =>
    if: xdeque_is_empty "t" then (
      §None
    ) else (
      let: "old_front" := "t".{xdeque_next} in
      let: "front" := "old_front".{xdeque_next} in
      "front" <-{xdeque_prev} "t" ;;
      "t" <-{xdeque_next} "front" ;;
      ‘Some( "old_front" )
    ).

Definition xdeque_pop_back : val :=
  fun: "t" =>
    if: xdeque_is_empty "t" then (
      §None
    ) else (
      let: "old_back" := "t".{xdeque_prev} in
      let: "back" := "old_back".{xdeque_prev} in
      "t" <-{xdeque_prev} "back" ;;
      "back" <-{xdeque_next} "t" ;;
      ‘Some( "old_back" )
    ).

Definition xdeque_remove : val :=
  fun: "node" =>
    let: "prev" := "node".{xdeque_prev} in
    let: "next" := "node".{xdeque_next} in
    "prev" <-{xdeque_next} "next" ;;
    "next" <-{xdeque_prev} "prev".

#[local] Definition xdeque_iter_aux : val :=
  rec: "xdeque_iter_aux" "t" "fn" "node" =>
    if: "node" = "t" then (
      ()
    ) else (
      "fn" "node" ;;
      "xdeque_iter_aux" "t" "fn" "node".{xdeque_next}
    ).
Definition xdeque_iter : val :=
  fun: "t" "fn" =>
    xdeque_iter_aux "t" "fn" "t".{xdeque_next}.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition xdeque_model t nodes : iProp Σ :=
    ∃ l,
    ⌜t = #l⌝ ∗
    l.[xdeque_prev] ↦ from_option #@{location} t (last nodes) ∗
    l.[xdeque_next] ↦ from_option #@{location} t (head nodes) ∗
    xdlchain_model t nodes t.

  #[global] Instance xdeque_model_timeless t nodes :
    Timeless (xdeque_model t nodes).
  Proof.
    apply _.
  Qed.

  Lemma xdeque_model_NoDup t nodes :
    xdeque_model t nodes ⊢
    ⌜NoDup nodes⌝.
  Proof.
    iIntros "(%l & -> & _ & _ & Hnodes)".
    iApply (xdlchain_model_NoDup with "Hnodes").
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
      RET #(bool_decide (nodes = []));
      xdeque_model t nodes
    }}}.
  Proof.
    iIntros "%Φ (%l & -> & Hprev & Hnext & Hnodes) HΦ".
    wp_rec. wp_load.
    destruct nodes as [| node nodes] => /=; wp_pures.
    - rewrite bool_decide_eq_true_2 //. iSteps.
    - case_bool_decide; last iSteps.
      subst.
      iDestruct (xdlchain_model_cons_1 with "Hnodes") as "(Hnode_prev & _)"; first done.
      iDestruct (pointsto_exclusive with "Hprev Hnode_prev") as %[].
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
    wp_rec. wp_load. wp_rec. do 2 wp_store. wp_store. wp_pures.
    destruct nodes as [| node' nodes] => /=.
    - iSteps.
      iApply (xdlchain_model_cons_2 _ _ [] with "Hnode_prev Hnode_next").
      iApply xdlchain_model_nil.
    - iDestruct (xdlchain_model_cons_1 with "Hnodes") as "(Hnode'_prev & Hnode'_next & Hnodes)"; first done.
      wp_store.
      iSteps.
      iApply (xdlchain_model_cons_2 _ _ (node' :: nodes) with "Hnode_prev Hnode_next").
      iApply (xdlchain_model_cons_2 with "Hnode'_prev Hnode'_next Hnodes").
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
    wp_rec. wp_load. wp_rec. do 2 wp_store. wp_pures.
    destruct (rev_elim nodes) as [-> | (nodes' & node' & ->)] => /=.
    - iSteps.
      iApply (xdlchain_model_cons_2 _ _ [] with "Hnode_prev Hnode_next").
      iApply xdlchain_model_nil.
    - rewrite last_snoc /=.
      iDestruct (xdlchain_model_snoc_1 with "Hnodes") as "(Hnodes & Hnode'_prev & Hnode'_next)"; first done.
      wp_store.
      iSteps; [iPureIntro.. |].
      + rewrite last_snoc //.
      + rewrite -assoc head_snoc_snoc //.
      + iApply (xdlchain_model_snoc_2 _ (nodes' ++ [node']) with "[Hnodes Hnode'_prev Hnode'_next] [Hnode_prev] Hnode_next"); last rewrite last_snoc //.
        iApply (xdlchain_model_snoc_2 with "Hnodes Hnode'_prev Hnode'_next").
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
      iDestruct (xdlchain_model_cons_1 with "Hnodes") as "(Hnode_prev & Hnode_next & Hnodes)"; first done.
      wp_load. wp_pures.
      destruct nodes as [| node' nodes] => /=; first iSteps.
      iDestruct (xdlchain_model_cons_1 with "Hnodes") as "(Hnode'_prev & Hnode'_next & Hnodes)"; first done.
      do 2 wp_store.
      iSteps.
      iApply (xdlchain_model_cons_2 with "Hnode'_prev Hnode'_next Hnodes").
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
      destruct (rev_elim nodes) as [-> | (nodes' & node & ->)] => //=.
      rewrite last_snoc /=.
      iDestruct (xdlchain_model_snoc_1 with "Hnodes") as "(Hnodes & Hnode_prev & Hnode_next)"; first done.
      wp_load. wp_store.
      destruct (rev_elim nodes') as [-> | (nodes'' & node' & ->)] => /=.
      + wp_store. wp_pures.
        iApply ("HΦ" $! (Some _)).
        iExists []. iSteps.
      + rewrite last_snoc.
        iDestruct (xdlchain_model_snoc_1 with "Hnodes") as "(Hnodes & Hnode'_prev & Hnode'_next)"; first done.
        wp_store. wp_pures.
        iApply ("HΦ" $! (Some _)).
        iSteps; first iPureIntro.
        * rewrite last_snoc //.
        * rewrite -assoc head_snoc_snoc //.
        * iApply (xdlchain_model_snoc_2 with "Hnodes Hnode'_prev Hnode'_next").
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
    wp_pures.
    iDestruct (xdlchain_model_lookup with "Hnodes") as "(Hnodes1 & Hnode_prev & Hnode_next & Hnodes2)"; first done.
    set nodes1 := take i nodes.
    set nodes2 := drop (S i) nodes.
    set nodes' := nodes1 ++ nodes2.
    wp_bind (Store _ _ _).
    wp_apply (wp_wand _ _ (λ res,
      ⌜res = ()%V⌝ ∗
      l.[xdeque_next] ↦ from_option #@{location} #l (head nodes') ∗
      xdlchain_model #l nodes1 (from_option #@{location} #l $ head nodes2)
    )%I with "[Hnext Hnodes1]") as (res) "(-> & Hnext & Hnodes1)".
    { destruct (rev_elim nodes1) as [-> | (nodes1' & node1 & Hnodes1)] => /=; first iSteps.
      rewrite Hnodes1 last_snoc /=.
      iDestruct (xdlchain_model_snoc_1 with "Hnodes1") as "(Hnodes1 & Hnode1_prev & Hnode1_next)"; first done.
      wp_store.
      iDestruct (xdlchain_model_snoc_2 with "Hnodes1 Hnode1_prev Hnode1_next") as "Hnodes1".
      iSteps. iPureIntro.
      rewrite -(take_drop i nodes) -/nodes1 /nodes' Hnodes1 -!assoc !head_app_cons //.
    }
    wp_pures.
    wp_apply (wp_wand _ _ (λ res,
      ⌜res = ()%V⌝ ∗
      l.[xdeque_prev] ↦ from_option #@{location} #l (last nodes') ∗
      xdlchain_model (from_option #@{location} #l $ last nodes1) nodes2 #l
    )%I with "[Hprev Hnodes2]") as (res) "(-> & Hprev & Hnodes2)".
    { destruct nodes2 as [| node2 nodes2'] eqn:Hnodes2 => /=.
      - rewrite right_id in nodes' |- *. iSteps.
      - iDestruct (xdlchain_model_cons_1 with "Hnodes2") as "(Hnode2_prev & Hnode2_next & Hnodes2)"; first done.
        wp_store.
        iDestruct (xdlchain_model_cons_2 with "Hnode2_prev Hnode2_next Hnodes2") as "Hnodes2".
        iSteps. iPureIntro.
        rewrite -(take_drop (S i) nodes) -/nodes2 /nodes' Hnodes2 !last_app_cons //.
    }
    iDestruct (xdlchain_model_app_2 with "Hnodes1 Hnodes2") as "Hnodes".
    rewrite /nodes' -delete_take_drop. iSteps.
  Qed.

  #[local] Lemma xdeque_iter_aux_spec Ψ i node l nodes fn :
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
      xdeque_iter_aux #l fn #node
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
      iDestruct (xdlchain_model_lookup_acc with "Hnodes") as "(Hnode_prev & Hnode_next & Hnodes)"; first done.
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
        - apply lookup_last_length in Hlookup'; last done.
          rewrite list_lookup_middle //.
      } {
        erewrite take_S_r => //.
      }
    - rewrite list_lookup_middle in Hlookup; first lia. simplify.
      rewrite bool_decide_eq_true_2 // firstn_all2 //. iSteps.
    - rewrite list_lookup_alt app_length /= in Hlookup. lia.
  Qed.
  Lemma xdeque_iter_spec Ψ t nodes fn :
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
      xdeque_iter t fn
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
