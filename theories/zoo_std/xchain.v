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

  Fixpoint xchain dq nodes dst : iProp Σ :=
    match nodes with
    | [] =>
        True
    | node :: nodes =>
        match nodes with
        | [] =>
            node.[xchain_next] ↦{dq} dst
        | node' :: _ =>
            node.[xchain_next] ↦{dq} #node' ∗
            xchain dq nodes dst
        end
    end.
  #[global] Arguments xchain _ !_ _ / : assert.

  #[global] Instance xchain_timeless dq nodes dst :
    Timeless (xchain dq nodes dst).
  Proof.
    induction nodes as [| ? []]; apply _.
  Qed.
  #[global] Instance xchain_persistent nodes dst :
    Persistent (xchain DfracDiscarded nodes dst).
  Proof.
    induction nodes as [| ? []]; apply _.
  Qed.

  Lemma xchain_nil dst :
    ⊢ xchain (DfracOwn 1) [] dst.
  Proof.
    iSteps.
  Qed.

  Lemma xchain_singleton dq node dst :
    xchain dq [node] dst ⊣⊢
    node.[xchain_next] ↦{dq} dst.
  Proof.
    iSteps.
  Qed.
  Lemma xchain_singleton_1 dq node dst :
    xchain dq [node] dst ⊢
    node.[xchain_next] ↦{dq} dst.
  Proof.
    iSteps.
  Qed.
  Lemma xchain_singleton_2 dq node dst :
    node.[xchain_next] ↦{dq} dst ⊢
    xchain dq [node] dst.
  Proof.
    iSteps.
  Qed.

  Lemma xchain_cons {dq} nodes node nodes' dst :
    nodes = node :: nodes' →
    xchain dq nodes dst ⊣⊢
      node.[xchain_next] ↦{dq} from_option #@{location} dst (head nodes') ∗
      xchain dq nodes' dst.
  Proof.
    destruct nodes'; iSteps.
  Qed.
  Lemma xchain_cons' {dq} node nodes dst :
    xchain dq (node :: nodes) dst ⊣⊢
      node.[xchain_next] ↦{dq} from_option #@{location} dst (head nodes) ∗
      xchain dq nodes dst.
  Proof.
    rewrite xchain_cons //.
  Qed.
  Lemma xchain_cons_1 {dq} nodes node nodes' dst :
    nodes = node :: nodes' →
    xchain dq nodes dst ⊢
      node.[xchain_next] ↦{dq} from_option #@{location} dst (head nodes') ∗
      xchain dq nodes' dst.
  Proof.
    intros.
    rewrite xchain_cons //.
  Qed.
  Lemma xchain_cons_1' {dq} node nodes dst :
    xchain dq (node :: nodes) dst ⊢
      node.[xchain_next] ↦{dq} from_option #@{location} dst (head nodes) ∗
      xchain dq nodes dst.
  Proof.
    rewrite xchain_cons //.
  Qed.
  Lemma xchain_cons_2 dq node nodes dst :
    node.[xchain_next] ↦{dq} from_option #@{location} dst (head nodes) -∗
    xchain dq nodes dst -∗
    xchain dq (node :: nodes) dst.
  Proof.
    rewrite (xchain_cons (node :: nodes)) //. iSteps.
  Qed.

  Lemma xchain_app {dq} nodes nodes1 nodes2 dst :
    nodes = nodes1 ++ nodes2 →
    xchain dq nodes dst ⊣⊢
      xchain dq nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xchain dq nodes2 dst.
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
  Lemma xchain_app' {dq} nodes1 nodes2 dst :
    xchain dq (nodes1 ++ nodes2) dst ⊣⊢
      xchain dq nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xchain dq nodes2 dst.
  Proof.
    rewrite xchain_app //.
  Qed.
  Lemma xchain_app_1 {dq} nodes nodes1 nodes2 dst :
    nodes = nodes1 ++ nodes2 →
    xchain dq nodes dst ⊢
      xchain dq nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xchain dq nodes2 dst.
  Proof.
    intros.
    rewrite xchain_app //.
  Qed.
  Lemma xchain_app_1' {dq} nodes1 nodes2 dst :
    xchain dq (nodes1 ++ nodes2) dst ⊢
      xchain dq nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xchain dq nodes2 dst.
  Proof.
    rewrite xchain_app //.
  Qed.
  Lemma xchain_app_2 dq nodes1 nodes2 dst :
    xchain dq nodes1 (from_option #@{location} dst (head nodes2)) -∗
    xchain dq nodes2 dst -∗
    xchain dq (nodes1 ++ nodes2) dst.
  Proof.
    rewrite (xchain_app (nodes1 ++ nodes2)) //. iSteps.
  Qed.

  Lemma xchain_snoc {dq} nodes nodes' node dst :
    nodes = nodes' ++ [node] →
    xchain dq nodes dst ⊣⊢
      xchain dq nodes' #node ∗
      node.[xchain_next] ↦{dq} dst.
  Proof.
    intros.
    rewrite xchain_app //.
  Qed.
  Lemma xchain_snoc' {dq} nodes node dst :
    xchain dq (nodes ++ [node]) dst ⊣⊢
      xchain dq nodes #node ∗
      node.[xchain_next] ↦{dq} dst.
  Proof.
    rewrite xchain_snoc //.
  Qed.
  Lemma xchain_snoc_1 {dq} nodes nodes' node dst :
    nodes = nodes' ++ [node] →
    xchain dq nodes dst ⊢
      xchain dq nodes' #node ∗
      node.[xchain_next] ↦{dq} dst.
  Proof.
    intros.
    rewrite xchain_snoc //.
  Qed.
  Lemma xchain_snoc_1' {dq} nodes node dst :
    xchain dq (nodes ++ [node]) dst ⊢
      xchain dq nodes #node ∗
      node.[xchain_next] ↦{dq} dst.
  Proof.
    rewrite xchain_snoc_1 //.
  Qed.
  Lemma xchain_snoc_2 dq nodes node dst :
    xchain dq nodes #node -∗
    node.[xchain_next] ↦{dq} dst -∗
    xchain dq (nodes ++ [node]) dst.
  Proof.
    rewrite (xchain_snoc (nodes ++ [node])) //. iSteps.
  Qed.

  Lemma xchain_lookup {dq nodes} i node dst :
    nodes !! i = Some node →
    xchain dq nodes dst ⊣⊢
      xchain dq (take i nodes) #node ∗
      node.[xchain_next] ↦{dq} from_option #@{location} dst (nodes !! S i) ∗
      xchain dq (drop (S i) nodes) dst.
  Proof.
    intros Hlookup.
    pose proof Hlookup as Hnodes%take_drop_middle.
    rewrite -{1}Hnodes xchain_app // (xchain_cons (node :: _)) // head_drop //.
  Qed.
  Lemma xchain_lookup_1 {dq nodes} i node dst :
    nodes !! i = Some node →
    xchain dq nodes dst ⊢
      xchain dq (take i nodes) #node ∗
      node.[xchain_next] ↦{dq} from_option #@{location} dst (nodes !! S i) ∗
      xchain dq (drop (S i) nodes) dst.
  Proof.
    intros.
    rewrite xchain_lookup //.
  Qed.
  Lemma xchain_lookup_2 {dq nodes} i node next dst :
    nodes !! i = Some node →
    next = from_option #@{location} dst (nodes !! S i) →
    xchain dq (take i nodes) #node -∗
    node.[xchain_next] ↦{dq} next -∗
    xchain dq (drop (S i) nodes) dst -∗
    xchain dq nodes dst.
  Proof.
    intros. subst.
    rewrite (@xchain_lookup _ nodes) //. iSteps.
  Qed.
  Lemma xchain_lookup_acc {dq nodes} i node dst :
    nodes !! i = Some node →
    xchain dq nodes dst ⊢
      node.[xchain_next] ↦{dq} from_option #@{location} dst (nodes !! S i) ∗
      ( node.[xchain_next] ↦{dq} from_option #@{location} dst (nodes !! S i) -∗
        xchain dq nodes dst
      ).
  Proof.
    intros. rewrite xchain_lookup //. iSteps.
  Qed.

  Lemma xchain_last {dq nodes dst} node :
    last nodes = Some node →
    xchain dq nodes dst ⊣⊢
      xchain dq (removelast nodes) #node ∗
      node.[xchain_next] ↦{dq} dst.
  Proof.
    intros.
    rewrite {1}(last_removelast nodes node) // xchain_snoc' //.
  Qed.
  Lemma xchain_last_acc {dq nodes dst} node :
    last nodes = Some node →
    xchain dq nodes dst ⊢
      node.[xchain_next] ↦{dq} dst ∗
      ( ∀ dst,
        node.[xchain_next] ↦{dq} dst -∗
        xchain dq nodes dst
      ).
  Proof.
    intros.
    setoid_rewrite (@xchain_last _ nodes); [| done..].
    iSteps.
  Qed.

  Lemma xchain_valid dq nodes dst :
    0 < length nodes →
    xchain dq nodes dst ⊢
    ⌜✓ dq⌝.
  Proof.
    intros Hvs.
    destruct nodes as [| node nodes]; first naive_solver lia.
    destruct nodes.
    1: iIntros "Hnode".
    2: iIntros "(Hnode & _)".
    all: iApply (pointsto_valid with "Hnode").
  Qed.
  Lemma xchain_combine nodes dq1 dst1 dq2 dst2 :
    0 < length nodes →
    xchain dq1 nodes dst1 -∗
    xchain dq2 nodes dst2 -∗
      ⌜dst1 = dst2⌝ ∗
      xchain (dq1 ⋅ dq2) nodes dst1.
  Proof.
    iInduction nodes as [| node1 nodes] "IH"; first iSteps.
    iIntros "% H1 H2".
    iDestruct (xchain_cons_1' with "H1") as "(Hnode_1 & H1)".
    iDestruct (xchain_cons_1' with "H2") as "(Hnode_2 & H2)".
    iDestruct (pointsto_agree with "Hnode_1 Hnode_2") as %?.
    iDestruct (pointsto_combine with "Hnode_1 Hnode_2") as "(-> & Hnode)".
    destruct nodes as [| node2 nodes].
    - simplify. iSteps.
    - iDestruct ("IH" with "[%] H1 H2") as "(-> & H)".
      { simpl. lia. }
      iSteps.
  Qed.
  Lemma xchain_valid_2 nodes dq1 dst1 dq2 dst2 :
    0 < length nodes →
    xchain dq1 nodes dst1 -∗
    xchain dq2 nodes dst2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜dst1 = dst2⌝.
  Proof.
    iIntros "% H1 H2".
    iDestruct (xchain_combine with "H1 H2") as "(-> & H)"; first done.
    iDestruct (xchain_valid with "H") as "$"; first done.
    iSteps.
  Qed.
  Lemma xchain_agree nodes dq1 dst1 dq2 dst2 :
    0 < length nodes →
    xchain dq1 nodes dst1 -∗
    xchain dq2 nodes dst2 -∗
    ⌜dst1 = dst2⌝.
  Proof.
    iIntros "% H1 H2".
    iDestruct (xchain_combine with "H1 H2") as "($ & _)"; first done.
  Qed.
  Lemma xchain_dfrac_ne dq1 nodes1 dst1 dq2 nodes2 dst2 :
    0 < length nodes1 →
    ¬ ✓ (dq1 ⋅ dq2) →
    xchain dq1 nodes1 dst1 -∗
    xchain dq2 nodes2 dst2 -∗
    ⌜nodes1 ≠ nodes2⌝.
  Proof.
    iIntros "% % H1 H2" (->).
    iDestruct (xchain_valid_2 with "H1 H2") as %?; naive_solver.
  Qed.
  Lemma xchain_ne nodes1 dst1 dq2 nodes2 dst2 :
    0 < length nodes1 →
    xchain (DfracOwn 1) nodes1 dst1 -∗
    xchain dq2 nodes2 dst2 -∗
    ⌜nodes1 ≠ nodes2⌝.
  Proof.
    intros.
    iApply xchain_dfrac_ne; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma xchain_exclusive nodes dst1 dq2 dst2 :
    0 < length nodes →
    xchain (DfracOwn 1) nodes dst1 -∗
    xchain dq2 nodes dst2 -∗
    False.
  Proof.
    iIntros "% H1 H2".
    iDestruct (xchain_ne with "H1 H2") as %?; done.
  Qed.
  Lemma xchain_persist dq nodes dst :
    xchain dq nodes dst ⊢ |==>
    xchain DfracDiscarded nodes dst.
  Proof.
    iInduction nodes as [| node nodes] "IH"; first iSteps.
    rewrite !xchain_cons'.
    iIntros "(Hnode & H)".
    iMod (pointsto_persist with "Hnode") as "$".
    iApply ("IH" with "H").
  Qed.

  Lemma xchain_NoDup nodes dst :
    xchain (DfracOwn 1) nodes dst ⊢
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

  Lemma xchain_next_spec {dq nodes dst node} nodes' E :
    nodes = node :: nodes' →
    {{{
      xchain dq nodes dst
    }}}
      (#node).{xchain_next} @ E
    {{{
      RET from_option #@{location} dst (head nodes');
      xchain dq nodes dst
    }}}.
  Proof.
    iIntros (->) "%Φ H HΦ".
    destruct nodes'; iSteps.
  Qed.
  Lemma xchain_next_spec_lookup {dq nodes dst} i node E :
    nodes !! i = Some node →
    {{{
      xchain dq nodes dst
    }}}
      (#node).{xchain_next} @ E
    {{{
      RET from_option #@{location} dst (nodes !! S i);
      xchain dq nodes dst
    }}}.
  Proof.
    intros Hlookup.
    setoid_rewrite xchain_lookup_acc at 1; last done.
    iSteps.
  Qed.
  Lemma xchain_next_spec_last dq nodes dst node E :
    last nodes = Some node →
    {{{
      xchain dq nodes dst
    }}}
      (#node).{xchain_next} @ E
    {{{
      RET dst;
      xchain dq nodes dst
    }}}.
  Proof.
    intros.
    setoid_rewrite xchain_last_acc at 1; last done.
    iSteps.
  Qed.

  Lemma xchain_set_next_spec {nodes dst node} nodes' v E :
    nodes = node :: nodes' →
    {{{
      xchain (DfracOwn 1) nodes dst
    }}}
      (#node) <-{xchain_next} v @ E
    {{{
      RET ();
      xchain (DfracOwn 1) [node] v ∗
      xchain (DfracOwn 1) nodes' dst
    }}}.
  Proof.
    iIntros (->) "%Φ H HΦ".
    destruct nodes'; iSteps.
  Qed.
  Lemma xchain_set_next_spec_lookup {nodes dst} i node v E :
    nodes !! i = Some node →
    {{{
      xchain (DfracOwn 1) nodes dst
    }}}
      #node <-{xchain_next} v @ E
    {{{
      RET ();
      xchain (DfracOwn 1) (take (S i) nodes) v ∗
      xchain (DfracOwn 1) (drop (S i) nodes) dst
    }}}.
  Proof.
    intros Hlookup.
    setoid_rewrite xchain_lookup at 1; last done.
    iIntros "%Φ (H1 & Hnode & H2) HΦ".
    wp_store.
    iDestruct (xchain_snoc_2 with "H1 Hnode") as "H1".
    rewrite -take_S_r //. iSteps.
  Qed.
  Lemma xchain_set_next_spec_last nodes dst node v E :
    last nodes = Some node →
    {{{
      xchain (DfracOwn 1) nodes dst
    }}}
      #node <-{xchain_next} v @ E
    {{{
      RET ();
      xchain (DfracOwn 1) nodes v
    }}}.
  Proof.
    intros.
    setoid_rewrite xchain_last_acc at 1; last done.
    iSteps.
  Qed.
  Lemma xchain_set_next_spec_last' {nodes dst node} node' dst' E :
    last nodes = Some node →
    {{{
      xchain (DfracOwn 1) nodes dst ∗
      node'.[xchain_next] ↦ dst'
    }}}
      #node <-{xchain_next} #node' @ E
    {{{
      RET ();
      xchain (DfracOwn 1) (nodes ++ [node']) dst'
    }}}.
  Proof.
    intros.
    setoid_rewrite xchain_last_acc at 1; last done.
    rewrite xchain_snoc'.
    iSteps.
  Qed.
End zoo_G.

From zoo_std Require xchain__opaque.

#[global] Opaque xchain.
