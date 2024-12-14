From zoo Require Import
  prelude.
From zoo.common Require Import
  list.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  xchain__types.
From zoo Require Import
  options.

Implicit Types node : location.
Implicit Types nodes : list location.
Implicit Types v next dst : val.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Fixpoint xchain nodes dst : iProp Σ :=
    match nodes with
    | [] =>
        True
    | node :: nodes =>
        match nodes with
        | [] =>
            node.[xchain_next] ↦ dst
        | node' :: _ =>
            node.[xchain_next] ↦ #node' ∗
            xchain nodes dst
        end
    end.
  #[global] Arguments xchain !_ _ / : assert.

  #[global] Instance xchain_timeless nodes dst :
    Timeless (xchain nodes dst).
  Proof.
    induction nodes as [| ? []]; apply _.
  Qed.

  Lemma xchain_nil dst :
    ⊢ xchain [] dst.
  Proof.
    iSteps.
  Qed.

  Lemma xchain_singleton node dst :
    xchain [node] dst ⊣⊢
    node.[xchain_next] ↦ dst.
  Proof.
    iSteps.
  Qed.
  Lemma xchain_singleton_1 node dst :
    xchain [node] dst ⊢
    node.[xchain_next] ↦ dst.
  Proof.
    iSteps.
  Qed.
  Lemma xchain_singleton_2 node dst :
    node.[xchain_next] ↦ dst ⊢
    xchain [node] dst.
  Proof.
    iSteps.
  Qed.

  Lemma xchain_cons nodes node nodes' dst :
    nodes = node :: nodes' →
    xchain nodes dst ⊣⊢
      node.[xchain_next] ↦ from_option #@{location} dst (head nodes') ∗
      xchain nodes' dst.
  Proof.
    destruct nodes'; iSteps.
  Qed.
  Lemma xchain_cons_1 nodes node nodes' dst :
    nodes = node :: nodes' →
    xchain nodes dst ⊢
      node.[xchain_next] ↦ from_option #@{location} dst (head nodes') ∗
      xchain nodes' dst.
  Proof.
    intros. rewrite xchain_cons //.
  Qed.
  Lemma xchain_cons_2 node nodes dst :
    node.[xchain_next] ↦ from_option #@{location} dst (head nodes) -∗
    xchain nodes dst -∗
    xchain (node :: nodes) dst.
  Proof.
    rewrite (xchain_cons (node :: nodes)) //. iSteps.
  Qed.

  Lemma xchain_app nodes nodes1 nodes2 dst :
    nodes = nodes1 ++ nodes2 →
    xchain nodes dst ⊣⊢
      xchain nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xchain nodes2 dst.
  Proof.
    intros ->.
    iInduction nodes1 as [| node1 [| node1' nodes1]] "IH".
    - iSteps.
    - destruct nodes2; iSteps.
    - iSplit.
      + iIntros "($ & H)".
        iApply ("IH" with "H").
      + iIntros "(($ & H1) & H2)".
        iApply ("IH" with "[$H1 $H2]").
  Qed.
  Lemma xchain_app_1 nodes nodes1 nodes2 dst :
    nodes = nodes1 ++ nodes2 →
    xchain nodes dst ⊢
      xchain nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xchain nodes2 dst.
  Proof.
    intros. rewrite xchain_app //.
  Qed.
  Lemma xchain_app_2 nodes1 nodes2 dst :
    xchain nodes1 (from_option #@{location} dst (head nodes2)) -∗
    xchain nodes2 dst -∗
    xchain (nodes1 ++ nodes2) dst.
  Proof.
    rewrite (xchain_app (nodes1 ++ nodes2)) //. iSteps.
  Qed.

  Lemma xchain_snoc nodes nodes' node dst :
    nodes = nodes' ++ [node] →
    xchain nodes dst ⊣⊢
      xchain nodes' #node ∗
      node.[xchain_next] ↦ dst.
  Proof.
    intros. rewrite xchain_app //.
  Qed.
  Lemma xchain_snoc_1 nodes nodes' node dst :
    nodes = nodes' ++ [node] →
    xchain nodes dst ⊢
      xchain nodes' #node ∗
      node.[xchain_next] ↦ dst.
  Proof.
    intros. rewrite xchain_snoc //.
  Qed.
  Lemma xchain_snoc_2 nodes node dst :
    xchain nodes #node -∗
    node.[xchain_next] ↦ dst -∗
    xchain (nodes ++ [node]) dst.
  Proof.
    rewrite (xchain_snoc (nodes ++ [node])) //. iSteps.
  Qed.

  Lemma xchain_lookup {nodes} i node dst :
    nodes !! i = Some node →
    xchain nodes dst ⊣⊢
      xchain (take i nodes) #node ∗
      node.[xchain_next] ↦ from_option #@{location} dst (nodes !! S i) ∗
      xchain (drop (S i) nodes) dst.
  Proof.
    intros Hlookup.
    pose proof Hlookup as Hnodes%take_drop_middle.
    rewrite -{1}Hnodes xchain_app // (xchain_cons (node :: _)) // head_drop //.
  Qed.
  Lemma xchain_lookup_1 {nodes} i node dst :
    nodes !! i = Some node →
    xchain nodes dst ⊢
      xchain (take i nodes) #node ∗
      node.[xchain_next] ↦ from_option #@{location} dst (nodes !! S i) ∗
      xchain (drop (S i) nodes) dst.
  Proof.
    intros. rewrite xchain_lookup //.
  Qed.
  Lemma xchain_lookup_2 {nodes} i node next dst :
    nodes !! i = Some node →
    next = from_option #@{location} dst (nodes !! S i) →
    xchain (take i nodes) #node -∗
    node.[xchain_next] ↦ next -∗
    xchain (drop (S i) nodes) dst -∗
    xchain nodes dst.
  Proof.
    intros. rewrite (@xchain_lookup nodes) //. iSteps.
  Qed.

  Lemma xchain_lookup_acc {nodes} i node dst :
    nodes !! i = Some node →
    xchain nodes dst ⊢
      node.[xchain_next] ↦ from_option #@{location} dst (nodes !! S i) ∗
      ( node.[xchain_next] ↦ from_option #@{location} dst (nodes !! S i) -∗
        xchain nodes dst
      ).
  Proof.
    intros. rewrite xchain_lookup //. iSteps.
  Qed.

  Lemma xchain_exclusive nodes dst1 dst2 :
    0 < length nodes →
    xchain nodes dst1 -∗
    xchain nodes dst2 -∗
    False.
  Proof.
    iIntros "% H1 H2".
    destruct nodes as [| ? []]; first naive_solver lia.
    2: iDestruct "H1" as "(H1 & _)".
    2: iDestruct "H2" as "(H2 & _)".
    all: iApply (pointsto_exclusive with "H1 H2").
  Qed.

  Lemma xchain_NoDup nodes dst :
    xchain nodes dst ⊢
    ⌜NoDup nodes⌝.
  Proof.
    rewrite NoDup_alt.
    iIntros "H %i1 %i2 %node %Hlookup_1 %Hlookup_2".
    destruct (decide (i1 = i2)) as [| Hne]; [done | iExFalso].
    assert (nodes !! (i1 `min` i2) = Some node) as Hlookup_min.
    { destruct (Nat.min_spec i1 i2) as [(_ & ->) | (_ & ->)]; done. }
    assert (nodes !! (i1 `max` i2) = Some node) as Hlookup_max.
    { destruct (Nat.max_spec i1 i2) as [(_ & ->) | (_ & ->)]; done. }
    iDestruct (xchain_lookup (i1 `min` i2) with "H") as "(_ & Hnode_1 & H)"; first done.
    iDestruct (xchain_lookup (i1 `max` i2 - i1 `min` i2 - 1) node with "H") as "(_ & Hnode_2 & _)".
    { rewrite lookup_drop -Hlookup_max. f_equal. lia. }
    iApply (pointsto_exclusive with "Hnode_1 Hnode_2").
  Qed.

  Lemma xchain_next_spec {nodes node} nodes' dst E :
    nodes = node :: nodes' →
    {{{
      xchain nodes dst
    }}}
      (#node).{xchain_next} @ E
    {{{
      RET from_option #@{location} dst (head nodes');
      xchain nodes dst
    }}}.
  Proof.
    iIntros (->) "%Φ H HΦ".
    destruct nodes'; iSteps.
  Qed.
  Lemma xchain_next_spec_lookup {nodes} i node dst E :
    nodes !! i = Some node →
    {{{
      xchain nodes dst
    }}}
      (#node).{xchain_next} @ E
    {{{
      RET from_option #@{location} dst (nodes !! S i);
      xchain nodes dst
    }}}.
  Proof.
    intros Hlookup.
    setoid_rewrite xchain_lookup_acc at 1; last done.
    iSteps.
  Qed.

  Lemma xchain_set_next_spec {nodes node} nodes' dst v E :
    nodes = node :: nodes' →
    {{{
      xchain nodes dst
    }}}
      (#node) <-{xchain_next} v @ E
    {{{
      RET ();
      xchain [node] v ∗
      xchain nodes' dst
    }}}.
  Proof.
    iIntros (->) "%Φ H HΦ".
    destruct nodes'; iSteps.
  Qed.
  Lemma xchain_set_next_spec_lookup {nodes} i node dst v E :
    nodes !! i = Some node →
    {{{
      xchain nodes dst
    }}}
      #node <-{xchain_next} v @ E
    {{{
      RET ();
      xchain (take (S i) nodes) v ∗
      xchain (drop (S i) nodes) dst
    }}}.
  Proof.
    intros Hlookup.
    setoid_rewrite xchain_lookup at 1; last done.
    iIntros "%Φ (H1 & Hnode & H2) HΦ".
    wp_store.
    iDestruct (xchain_snoc_2 with "H1 Hnode") as "H1".
    rewrite -take_S_r //. iSteps.
  Qed.
End zoo_G.

#[global] Opaque xchain.
