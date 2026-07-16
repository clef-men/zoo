Require Import zoo.prelude.
Require Import zoo.common.list.
Require Import zoo.base.
Require Export zoo_std.xchain__types.
Require Import zoo.options.

Implicit Types node : location.
Implicit Types nodes : list location.
Implicit Types v next dst : val.

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

  #[global] Instance xchain𑁒timeless dq nodes dst :
    Timeless (xchain dq nodes dst).
  Proof.
    induction nodes as [| ? []]; apply _.
  Qed.

  #[global] Instance xchain𑁒persistent nodes dst :
    Persistent (xchain DfracDiscarded nodes dst).
  Proof.
    induction nodes as [| ? []]; apply _.
  Qed.

  Lemma xchain𑁒nil dst :
    ⊢ xchain (DfracOwn 1) [] dst.
  Proof.
    iSteps.
  Qed.

  Lemma xchain𑁒singleton dq node dst :
    xchain dq [node] dst ⊣⊢
    node.[xchain_next] ↦{dq} dst.
  Proof.
    iSteps.
  Qed.
  Lemma xchain𑁒singleton₁ dq node dst :
    xchain dq [node] dst ⊢
    node.[xchain_next] ↦{dq} dst.
  Proof.
    iSteps.
  Qed.
  Lemma xchain𑁒singleton₂ dq node dst :
    node.[xchain_next] ↦{dq} dst ⊢
    xchain dq [node] dst.
  Proof.
    iSteps.
  Qed.

  Lemma xchain𑁒cons {dq} nodes node nodes' dst :
    nodes = node :: nodes' →
    xchain dq nodes dst ⊣⊢
      node.[xchain_next] ↦{dq} from_option #@{location} dst (head nodes') ∗
      xchain dq nodes' dst.
  Proof.
    destruct nodes'; iSteps.
  Qed.
  Lemma xchain𑁒cons' {dq} node nodes dst :
    xchain dq (node :: nodes) dst ⊣⊢
      node.[xchain_next] ↦{dq} from_option #@{location} dst (head nodes) ∗
      xchain dq nodes dst.
  Proof.
    rewrite xchain𑁒cons //.
  Qed.
  Lemma xchain𑁒cons₁ {dq} nodes node nodes' dst :
    nodes = node :: nodes' →
    xchain dq nodes dst ⊢
      node.[xchain_next] ↦{dq} from_option #@{location} dst (head nodes') ∗
      xchain dq nodes' dst.
  Proof.
    intros.
    rewrite xchain𑁒cons //.
  Qed.
  Lemma xchain𑁒cons₁' {dq} node nodes dst :
    xchain dq (node :: nodes) dst ⊢
      node.[xchain_next] ↦{dq} from_option #@{location} dst (head nodes) ∗
      xchain dq nodes dst.
  Proof.
    rewrite xchain𑁒cons //.
  Qed.
  Lemma xchain𑁒cons₂ dq node nodes dst :
    node.[xchain_next] ↦{dq} from_option #@{location} dst (head nodes) -∗
    xchain dq nodes dst -∗
    xchain dq (node :: nodes) dst.
  Proof.
    rewrite (xchain𑁒cons (node :: nodes)) //. iSteps.
  Qed.

  Lemma xchain𑁒app {dq} nodes nodes1 nodes2 dst :
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
  Lemma xchain𑁒app' {dq} nodes1 nodes2 dst :
    xchain dq (nodes1 ++ nodes2) dst ⊣⊢
      xchain dq nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xchain dq nodes2 dst.
  Proof.
    rewrite xchain𑁒app //.
  Qed.
  Lemma xchain𑁒app₁ {dq} nodes nodes1 nodes2 dst :
    nodes = nodes1 ++ nodes2 →
    xchain dq nodes dst ⊢
      xchain dq nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xchain dq nodes2 dst.
  Proof.
    intros.
    rewrite xchain𑁒app //.
  Qed.
  Lemma xchain𑁒app₁' {dq} nodes1 nodes2 dst :
    xchain dq (nodes1 ++ nodes2) dst ⊢
      xchain dq nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xchain dq nodes2 dst.
  Proof.
    rewrite xchain𑁒app //.
  Qed.
  Lemma xchain𑁒app₂ dq nodes1 nodes2 dst :
    xchain dq nodes1 (from_option #@{location} dst (head nodes2)) -∗
    xchain dq nodes2 dst -∗
    xchain dq (nodes1 ++ nodes2) dst.
  Proof.
    rewrite (xchain𑁒app (nodes1 ++ nodes2)) //. iSteps.
  Qed.

  Lemma xchain𑁒snoc {dq} nodes nodes' node dst :
    nodes = nodes' ++ [node] →
    xchain dq nodes dst ⊣⊢
      xchain dq nodes' #node ∗
      node.[xchain_next] ↦{dq} dst.
  Proof.
    intros.
    rewrite xchain𑁒app //.
  Qed.
  Lemma xchain𑁒snoc' {dq} nodes node dst :
    xchain dq (nodes ++ [node]) dst ⊣⊢
      xchain dq nodes #node ∗
      node.[xchain_next] ↦{dq} dst.
  Proof.
    rewrite xchain𑁒snoc //.
  Qed.
  Lemma xchain𑁒snoc₁ {dq} nodes nodes' node dst :
    nodes = nodes' ++ [node] →
    xchain dq nodes dst ⊢
      xchain dq nodes' #node ∗
      node.[xchain_next] ↦{dq} dst.
  Proof.
    intros.
    rewrite xchain𑁒snoc //.
  Qed.
  Lemma xchain𑁒snoc₁' {dq} nodes node dst :
    xchain dq (nodes ++ [node]) dst ⊢
      xchain dq nodes #node ∗
      node.[xchain_next] ↦{dq} dst.
  Proof.
    rewrite xchain𑁒snoc₁ //.
  Qed.
  Lemma xchain𑁒snoc₂ dq nodes node dst :
    xchain dq nodes #node -∗
    node.[xchain_next] ↦{dq} dst -∗
    xchain dq (nodes ++ [node]) dst.
  Proof.
    rewrite (xchain𑁒snoc (nodes ++ [node])) //. iSteps.
  Qed.

  Lemma xchain𑁒lookup {dq nodes} i node dst :
    nodes !! i = Some node →
    xchain dq nodes dst ⊣⊢
      xchain dq (take i nodes) #node ∗
      node.[xchain_next] ↦{dq} from_option #@{location} dst (nodes !! ˖i) ∗
      xchain dq (drop ˖i nodes) dst.
  Proof.
    intros Hlookup.
    pose proof Hlookup as Hnodes%take_drop_middle.
    rewrite -{1}Hnodes xchain𑁒app // (xchain𑁒cons (node :: _)) // head𑁒drop //.
  Qed.
  Lemma xchain𑁒lookup₁ {dq nodes} i node dst :
    nodes !! i = Some node →
    xchain dq nodes dst ⊢
      xchain dq (take i nodes) #node ∗
      node.[xchain_next] ↦{dq} from_option #@{location} dst (nodes !! ˖i) ∗
      xchain dq (drop ˖i nodes) dst.
  Proof.
    intros.
    rewrite xchain𑁒lookup //.
  Qed.
  Lemma xchain𑁒lookup₂ {dq nodes} i node next dst :
    nodes !! i = Some node →
    next = from_option #@{location} dst (nodes !! ˖i) →
    xchain dq (take i nodes) #node -∗
    node.[xchain_next] ↦{dq} next -∗
    xchain dq (drop ˖i nodes) dst -∗
    xchain dq nodes dst.
  Proof.
    intros. subst.
    rewrite (@xchain𑁒lookup _ nodes) //. iSteps.
  Qed.
  Lemma xchain𑁒lookup𑁒acc {dq nodes} i node dst :
    nodes !! i = Some node →
    xchain dq nodes dst ⊢
      node.[xchain_next] ↦{dq} from_option #@{location} dst (nodes !! ˖i) ∗
      ( node.[xchain_next] ↦{dq} from_option #@{location} dst (nodes !! ˖i) -∗
        xchain dq nodes dst
      ).
  Proof.
    intros. rewrite xchain𑁒lookup //. iSteps.
  Qed.

  Lemma xchain𑁒last {dq nodes dst} node :
    last nodes = Some node →
    xchain dq nodes dst ⊣⊢
      xchain dq (removelast nodes) #node ∗
      node.[xchain_next] ↦{dq} dst.
  Proof.
    intros.
    rewrite {1}(last𑁒removelast nodes node) // xchain𑁒snoc' //.
  Qed.
  Lemma xchain𑁒last𑁒acc {dq nodes dst} node :
    last nodes = Some node →
    xchain dq nodes dst ⊢
      node.[xchain_next] ↦{dq} dst ∗
      ( ∀ dst,
        node.[xchain_next] ↦{dq} dst -∗
        xchain dq nodes dst
      ).
  Proof.
    intros.
    setoid_rewrite (@xchain𑁒last _ nodes); [| done..].
    iSteps.
  Qed.

  Lemma xchain𑁒valid dq nodes dst :
    0 < length nodes →
    xchain dq nodes dst ⊢
    ⌜✓ dq⌝.
  Proof.
    intros Hvs.
    destruct nodes as [| node nodes]; first naive_solver lia.
    destruct nodes.
    1: iIntros "Hnode".
    2: iIntros "(Hnode & _)".
    all: iApply (pointsto𑁒valid with "Hnode").
  Qed.
  Lemma xchain𑁒combine nodes dq1 dst1 dq2 dst2 :
    0 < length nodes →
    xchain dq1 nodes dst1 -∗
    xchain dq2 nodes dst2 -∗
      ⌜dst1 = dst2⌝ ∗
      xchain (dq1 ⋅ dq2) nodes dst1.
  Proof.
    iInduction nodes as [| node1 nodes] "IH"; first iSteps.
    iIntros "% H1 H2".
    iDestruct (xchain𑁒cons₁' with "H1") as "(Hnode_1 & H1)".
    iDestruct (xchain𑁒cons₁' with "H2") as "(Hnode_2 & H2)".
    iDestruct (pointsto𑁒agree with "Hnode_1 Hnode_2") as %?.
    iDestruct (pointsto𑁒combine with "Hnode_1 Hnode_2") as "(-> & Hnode)".
    destruct nodes as [| node2 nodes].
    - simplify. iSteps.
    - iDestruct ("IH" with "[%] H1 H2") as "(-> & H)".
      { simpl. lia. }
      iSteps.
  Qed.
  Lemma xchain𑁒valid𑁒2 nodes dq1 dst1 dq2 dst2 :
    0 < length nodes →
    xchain dq1 nodes dst1 -∗
    xchain dq2 nodes dst2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜dst1 = dst2⌝.
  Proof.
    iIntros "% H1 H2".
    iDestruct (xchain𑁒combine with "H1 H2") as "(-> & H)"; first done.
    iDestruct (xchain𑁒valid with "H") as "$"; first done.
    iSteps.
  Qed.
  Lemma xchain𑁒agree nodes dq1 dst1 dq2 dst2 :
    0 < length nodes →
    xchain dq1 nodes dst1 -∗
    xchain dq2 nodes dst2 -∗
    ⌜dst1 = dst2⌝.
  Proof.
    iIntros "% H1 H2".
    iDestruct (xchain𑁒combine with "H1 H2") as "($ & _)"; first done.
  Qed.
  Lemma xchain𑁒dfrac𑁒ne dq1 nodes1 dst1 dq2 nodes2 dst2 :
    0 < length nodes1 →
    ¬ ✓ (dq1 ⋅ dq2) →
    xchain dq1 nodes1 dst1 -∗
    xchain dq2 nodes2 dst2 -∗
    ⌜nodes1 ≠ nodes2⌝.
  Proof.
    iIntros "% % H1 H2" (->).
    iDestruct (xchain𑁒valid𑁒2 with "H1 H2") as %?; naive_solver.
  Qed.
  Lemma xchain𑁒ne nodes1 dst1 dq2 nodes2 dst2 :
    0 < length nodes1 →
    xchain (DfracOwn 1) nodes1 dst1 -∗
    xchain dq2 nodes2 dst2 -∗
    ⌜nodes1 ≠ nodes2⌝.
  Proof.
    intros.
    iApply xchain𑁒dfrac𑁒ne; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma xchain𑁒exclusive nodes dst1 dq2 dst2 :
    0 < length nodes →
    xchain (DfracOwn 1) nodes dst1 -∗
    xchain dq2 nodes dst2 -∗
    False.
  Proof.
    iIntros "% H1 H2".
    iDestruct (xchain𑁒ne with "H1 H2") as %?; done.
  Qed.
  Lemma xchain𑁒persist dq nodes dst :
    xchain dq nodes dst ⊢ |==>
    xchain DfracDiscarded nodes dst.
  Proof.
    iInduction nodes as [| node nodes] "IH"; first iSteps.
    rewrite !xchain𑁒cons'.
    iIntros "(Hnode & H)".
    iMod (pointsto𑁒persist with "Hnode") as "$".
    iApply ("IH" with "H").
  Qed.

  Lemma xchain𑁒NoDup nodes dst :
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
    iDestruct (xchain𑁒lookup (i1 `min` i2) with "H") as "(_ & Hnode_1 & H)"; first done.
    iDestruct (xchain𑁒lookup (i1 `max` i2 - i1 `min` i2 - 1) node with "H") as "(_ & Hnode_2 & _)".
    { rewrite lookup_drop -Hlookup_max. f_equal. lia. }
    iApply (pointsto𑁒exclusive with "Hnode_1 Hnode_2").
  Qed.

  Lemma xchain٠next𑁒spec {dq nodes dst node} nodes' E :
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
  Lemma xchain٠next𑁒spec𑁒lookup {dq nodes dst} i node E :
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
    setoid_rewrite xchain𑁒lookup𑁒acc at 1; last done.
    iSteps.
  Qed.
  Lemma xchain٠next𑁒spec𑁒last dq nodes dst node E :
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
    setoid_rewrite xchain𑁒last𑁒acc at 1; last done.
    iSteps.
  Qed.

  Lemma xchain٠set_next𑁒spec {nodes dst node} nodes' v E :
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
  Lemma xchain٠set_next𑁒spec𑁒lookup {nodes dst} i node v E :
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
    setoid_rewrite xchain𑁒lookup at 1; last done.
    iIntros "%Φ (H1 & Hnode & H2) HΦ".
    wp۰store.
    iDestruct (xchain𑁒snoc₂ with "H1 Hnode") as "H1".
    rewrite -take_S_r //. iSteps.
  Qed.
  Lemma xchain٠set_next𑁒spec𑁒last nodes dst node v E :
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
    setoid_rewrite xchain𑁒last𑁒acc at 1; last done.
    iSteps.
  Qed.
  Lemma xchain٠set_next𑁒spec𑁒last' {nodes dst node} node' dst' E :
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
    setoid_rewrite xchain𑁒last𑁒acc at 1; last done.
    rewrite xchain𑁒snoc'.
    iSteps.
  Qed.
End zoo۰G.

Require zoo_std.xchain__opaque.

#[global] Opaque xchain.
