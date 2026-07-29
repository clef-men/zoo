Require Import zoo.prelude.
Require Import zoo.common.list.
Require Import zoo.base.
Require Export zoo_std.xchain__types.
Require Import zoo.options.

Implicit Type node : location.
Implicit Type nodes : list location.
Implicit Type v next dst : val.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

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

  #[global] Instance xchainｰtimeless dq nodes dst :
    Timeless (xchain dq nodes dst).
  Proof.
    induction nodes as [| ? []]; apply _.
  Qed.

  #[global] Instance xchainｰpersistent nodes dst :
    Persistent (xchain DfracDiscarded nodes dst).
  Proof.
    induction nodes as [| ? []]; apply _.
  Qed.

  Lemma xchainｰnil dst :
    ⊢ xchain (DfracOwn 1) [] dst.
  Proof.
    iSteps.
  Qed.

  Lemma xchainｰsingleton dq node dst :
    xchain dq [node] dst ⊣⊢
    node.[xchain_next] ↦{dq} dst.
  Proof.
    iSteps.
  Qed.
  Lemma xchainｰsingleton₁ dq node dst :
    xchain dq [node] dst ⊢
    node.[xchain_next] ↦{dq} dst.
  Proof.
    iSteps.
  Qed.
  Lemma xchainｰsingleton₂ dq node dst :
    node.[xchain_next] ↦{dq} dst ⊢
    xchain dq [node] dst.
  Proof.
    iSteps.
  Qed.

  Lemma xchainｰcons {dq} nodes node nodes' dst :
    nodes = node :: nodes' →
    xchain dq nodes dst ⊣⊢
      node.[xchain_next] ↦{dq} from_option #@{location} dst (head nodes') ∗
      xchain dq nodes' dst.
  Proof.
    destruct nodes'; iSteps.
  Qed.
  Lemma xchainｰcons' {dq} node nodes dst :
    xchain dq (node :: nodes) dst ⊣⊢
      node.[xchain_next] ↦{dq} from_option #@{location} dst (head nodes) ∗
      xchain dq nodes dst.
  Proof.
    rewrite xchainｰcons //.
  Qed.
  Lemma xchainｰcons₁ {dq} nodes node nodes' dst :
    nodes = node :: nodes' →
    xchain dq nodes dst ⊢
      node.[xchain_next] ↦{dq} from_option #@{location} dst (head nodes') ∗
      xchain dq nodes' dst.
  Proof.
    intros.
    rewrite xchainｰcons //.
  Qed.
  Lemma xchainｰcons₁' {dq} node nodes dst :
    xchain dq (node :: nodes) dst ⊢
      node.[xchain_next] ↦{dq} from_option #@{location} dst (head nodes) ∗
      xchain dq nodes dst.
  Proof.
    rewrite xchainｰcons //.
  Qed.
  Lemma xchainｰcons₂ dq node nodes dst :
    node.[xchain_next] ↦{dq} from_option #@{location} dst (head nodes) -∗
    xchain dq nodes dst -∗
    xchain dq (node :: nodes) dst.
  Proof.
    rewrite (xchainｰcons (node :: nodes)) //. iSteps.
  Qed.

  Lemma xchainｰapp {dq} nodes nodes1 nodes2 dst :
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
  Lemma xchainｰapp' {dq} nodes1 nodes2 dst :
    xchain dq (nodes1 ++ nodes2) dst ⊣⊢
      xchain dq nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xchain dq nodes2 dst.
  Proof.
    rewrite xchainｰapp //.
  Qed.
  Lemma xchainｰapp₁ {dq} nodes nodes1 nodes2 dst :
    nodes = nodes1 ++ nodes2 →
    xchain dq nodes dst ⊢
      xchain dq nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xchain dq nodes2 dst.
  Proof.
    intros.
    rewrite xchainｰapp //.
  Qed.
  Lemma xchainｰapp₁' {dq} nodes1 nodes2 dst :
    xchain dq (nodes1 ++ nodes2) dst ⊢
      xchain dq nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xchain dq nodes2 dst.
  Proof.
    rewrite xchainｰapp //.
  Qed.
  Lemma xchainｰapp₂ dq nodes1 nodes2 dst :
    xchain dq nodes1 (from_option #@{location} dst (head nodes2)) -∗
    xchain dq nodes2 dst -∗
    xchain dq (nodes1 ++ nodes2) dst.
  Proof.
    rewrite (xchainｰapp (nodes1 ++ nodes2)) //. iSteps.
  Qed.

  Lemma xchainｰsnoc {dq} nodes nodes' node dst :
    nodes = nodes' ++ [node] →
    xchain dq nodes dst ⊣⊢
      xchain dq nodes' #node ∗
      node.[xchain_next] ↦{dq} dst.
  Proof.
    intros.
    rewrite xchainｰapp //.
  Qed.
  Lemma xchainｰsnoc' {dq} nodes node dst :
    xchain dq (nodes ++ [node]) dst ⊣⊢
      xchain dq nodes #node ∗
      node.[xchain_next] ↦{dq} dst.
  Proof.
    rewrite xchainｰsnoc //.
  Qed.
  Lemma xchainｰsnoc₁ {dq} nodes nodes' node dst :
    nodes = nodes' ++ [node] →
    xchain dq nodes dst ⊢
      xchain dq nodes' #node ∗
      node.[xchain_next] ↦{dq} dst.
  Proof.
    intros.
    rewrite xchainｰsnoc //.
  Qed.
  Lemma xchainｰsnoc₁' {dq} nodes node dst :
    xchain dq (nodes ++ [node]) dst ⊢
      xchain dq nodes #node ∗
      node.[xchain_next] ↦{dq} dst.
  Proof.
    rewrite xchainｰsnoc₁ //.
  Qed.
  Lemma xchainｰsnoc₂ dq nodes node dst :
    xchain dq nodes #node -∗
    node.[xchain_next] ↦{dq} dst -∗
    xchain dq (nodes ++ [node]) dst.
  Proof.
    rewrite (xchainｰsnoc (nodes ++ [node])) //. iSteps.
  Qed.

  Lemma xchainｰlookup {dq nodes} i node dst :
    nodes !! i = Some node →
    xchain dq nodes dst ⊣⊢
      xchain dq (take i nodes) #node ∗
      node.[xchain_next] ↦{dq} from_option #@{location} dst (nodes !! ˖i) ∗
      xchain dq (drop ˖i nodes) dst.
  Proof.
    intros Hlookup.
    pose proof Hlookup as Hnodes%take_drop_middle.
    rewrite -{1}Hnodes xchainｰapp // (xchainｰcons (node :: _)) // headｰdrop //.
  Qed.
  Lemma xchainｰlookup₁ {dq nodes} i node dst :
    nodes !! i = Some node →
    xchain dq nodes dst ⊢
      xchain dq (take i nodes) #node ∗
      node.[xchain_next] ↦{dq} from_option #@{location} dst (nodes !! ˖i) ∗
      xchain dq (drop ˖i nodes) dst.
  Proof.
    intros.
    rewrite xchainｰlookup //.
  Qed.
  Lemma xchainｰlookup₂ {dq nodes} i node next dst :
    nodes !! i = Some node →
    next = from_option #@{location} dst (nodes !! ˖i) →
    xchain dq (take i nodes) #node -∗
    node.[xchain_next] ↦{dq} next -∗
    xchain dq (drop ˖i nodes) dst -∗
    xchain dq nodes dst.
  Proof.
    intros. subst.
    rewrite (@xchainｰlookup _ nodes) //. iSteps.
  Qed.
  Lemma xchainｰlookupｰacc {dq nodes} i node dst :
    nodes !! i = Some node →
    xchain dq nodes dst ⊢
      node.[xchain_next] ↦{dq} from_option #@{location} dst (nodes !! ˖i) ∗
      ( node.[xchain_next] ↦{dq} from_option #@{location} dst (nodes !! ˖i) -∗
        xchain dq nodes dst
      ).
  Proof.
    intros. rewrite xchainｰlookup //. iSteps.
  Qed.

  Lemma xchainｰlast {dq nodes dst} node :
    last nodes = Some node →
    xchain dq nodes dst ⊣⊢
      xchain dq (removelast nodes) #node ∗
      node.[xchain_next] ↦{dq} dst.
  Proof.
    intros.
    rewrite {1}(lastｰremovelast nodes node) // xchainｰsnoc' //.
  Qed.
  Lemma xchainｰlastｰacc {dq nodes dst} node :
    last nodes = Some node →
    xchain dq nodes dst ⊢
      node.[xchain_next] ↦{dq} dst ∗
      ( ∀ dst,
        node.[xchain_next] ↦{dq} dst -∗
        xchain dq nodes dst
      ).
  Proof.
    intros.
    setoid_rewrite (@xchainｰlast _ nodes); [| done..].
    iSteps.
  Qed.

  Lemma xchainｰvalid dq nodes dst :
    0 < length nodes →
    xchain dq nodes dst ⊢
    ⌜✓ dq⌝.
  Proof.
    intros Hvs.
    destruct nodes as [| node nodes]; first naive_solver lia.
    destruct nodes.
    1: iIntros "Hnode".
    2: iIntros "(Hnode & _)".
    all: iApply (pointstoｰvalid with "Hnode").
  Qed.
  Lemma xchainｰcombine nodes dq1 dst1 dq2 dst2 :
    0 < length nodes →
    xchain dq1 nodes dst1 -∗
    xchain dq2 nodes dst2 -∗
      ⌜dst1 = dst2⌝ ∗
      xchain (dq1 ⋅ dq2) nodes dst1.
  Proof.
    iInduction nodes as [| node1 nodes] "IH"; first iSteps.
    iIntros "% H1 H2".
    iDestruct (xchainｰcons₁' with "H1") as "(Hnode_1 & H1)".
    iDestruct (xchainｰcons₁' with "H2") as "(Hnode_2 & H2)".
    iDestruct (pointstoｰagree with "Hnode_1 Hnode_2") as %?.
    iDestruct (pointstoｰcombine with "Hnode_1 Hnode_2") as "(-> & Hnode)".
    destruct nodes as [| node2 nodes].
    - simplify. iSteps.
    - iDestruct ("IH" with "[%] H1 H2") as "(-> & H)".
      { simpl. lia. }
      iSteps.
  Qed.
  Lemma xchainｰvalidｰ2 nodes dq1 dst1 dq2 dst2 :
    0 < length nodes →
    xchain dq1 nodes dst1 -∗
    xchain dq2 nodes dst2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜dst1 = dst2⌝.
  Proof.
    iIntros "% H1 H2".
    iDestruct (xchainｰcombine with "H1 H2") as "(-> & H)"; first done.
    iDestruct (xchainｰvalid with "H") as "$"; first done.
    iSteps.
  Qed.
  Lemma xchainｰagree nodes dq1 dst1 dq2 dst2 :
    0 < length nodes →
    xchain dq1 nodes dst1 -∗
    xchain dq2 nodes dst2 -∗
    ⌜dst1 = dst2⌝.
  Proof.
    iIntros "% H1 H2".
    iDestruct (xchainｰcombine with "H1 H2") as "($ & _)"; first done.
  Qed.
  Lemma xchainｰdfracｰne dq1 nodes1 dst1 dq2 nodes2 dst2 :
    0 < length nodes1 →
    ¬ ✓ (dq1 ⋅ dq2) →
    xchain dq1 nodes1 dst1 -∗
    xchain dq2 nodes2 dst2 -∗
    ⌜nodes1 ≠ nodes2⌝.
  Proof.
    iIntros "% % H1 H2" (->).
    iDestruct (xchainｰvalidｰ2 with "H1 H2") as %?; naive_solver.
  Qed.
  Lemma xchainｰne nodes1 dst1 dq2 nodes2 dst2 :
    0 < length nodes1 →
    xchain (DfracOwn 1) nodes1 dst1 -∗
    xchain dq2 nodes2 dst2 -∗
    ⌜nodes1 ≠ nodes2⌝.
  Proof.
    intros.
    iApply xchainｰdfracｰne; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma xchainｰexclusive nodes dst1 dq2 dst2 :
    0 < length nodes →
    xchain (DfracOwn 1) nodes dst1 -∗
    xchain dq2 nodes dst2 -∗
    False.
  Proof.
    iIntros "% H1 H2".
    iDestruct (xchainｰne with "H1 H2") as %?; done.
  Qed.
  Lemma xchainｰpersist dq nodes dst :
    xchain dq nodes dst ⊢ |==>
    xchain DfracDiscarded nodes dst.
  Proof.
    iInduction nodes as [| node nodes] "IH"; first iSteps.
    rewrite !xchainｰcons'.
    iIntros "(Hnode & H)".
    iMod (pointstoｰpersist with "Hnode") as "$".
    iApply ("IH" with "H").
  Qed.

  Lemma xchainｰNoDup nodes dst :
    xchain (DfracOwn 1) nodes dst ⊢
    ⌜NoDup nodes⌝.
  Proof.
    rewrite NoDup_alt.
    iIntros "H %i1 %i2 %node %Hlookup_1 %Hlookup_2".
    destruct_decide (i1 = i2) as ? | Hne; [done | iExFalso].
    assert (nodes !! (i1 `min` i2) = Some node) as Hlookup_min.
    { destruct (Nat.min_spec i1 i2) as [(_ & ->) | (_ & ->)]; done. }
    assert (nodes !! (i1 `max` i2) = Some node) as Hlookup_max.
    { destruct (Nat.max_spec i1 i2) as [(_ & ->) | (_ & ->)]; done. }
    iDestruct (xchainｰlookup (i1 `min` i2) with "H") as "(_ & Hnode_1 & H)"; first done.
    iDestruct (xchainｰlookup (i1 `max` i2 - i1 `min` i2 - 1) node with "H") as "(_ & Hnode_2 & _)".
    { rewrite lookup_drop -Hlookup_max. f_equal. lia. }
    iApply (pointstoｰexclusive with "Hnode_1 Hnode_2").
  Qed.

  Lemma xchain٠nextｰspec {dq nodes dst node} nodes' E :
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
  Lemma xchain٠nextｰspecｰlookup {dq nodes dst} i node E :
    nodes !! i = Some node →
    {{{
      xchain dq nodes dst
    }}}
      (#node).{xchain_next} @ E
    {{{
      RET from_option #@{location} dst (nodes !! ˖i);
      xchain dq nodes dst
    }}}.
  Proof.
    intros Hlookup.
    setoid_rewrite xchainｰlookupｰacc at 1; last done.
    iSteps.
  Qed.
  Lemma xchain٠nextｰspecｰlast dq nodes dst node E :
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
    setoid_rewrite xchainｰlastｰacc at 1; last done.
    iSteps.
  Qed.

  Lemma xchain٠set_nextｰspec {nodes dst node} nodes' v E :
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
  Lemma xchain٠set_nextｰspecｰlookup {nodes dst} i node v E :
    nodes !! i = Some node →
    {{{
      xchain (DfracOwn 1) nodes dst
    }}}
      #node <-{xchain_next} v @ E
    {{{
      RET ();
      xchain (DfracOwn 1) (take ˖i nodes) v ∗
      xchain (DfracOwn 1) (drop ˖i nodes) dst
    }}}.
  Proof.
    intros Hlookup.
    setoid_rewrite xchainｰlookup at 1; last done.
    iIntros "%Φ (H1 & Hnode & H2) HΦ".
    wp۰store.
    iDestruct (xchainｰsnoc₂ with "H1 Hnode") as "H1".
    rewrite -take_S_r //. iSteps.
  Qed.
  Lemma xchain٠set_nextｰspecｰlast nodes dst node v E :
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
    setoid_rewrite xchainｰlastｰacc at 1; last done.
    iSteps.
  Qed.
  Lemma xchain٠set_nextｰspecｰlast' {nodes dst node} node' dst' E :
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
    setoid_rewrite xchainｰlastｰacc at 1; last done.
    rewrite xchainｰsnoc'.
    iSteps.
  Qed.
End zoo۰G.

Require zoo_std.xchain__opaque.

#[global] Opaque xchain.
