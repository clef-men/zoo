Require Import zoo.prelude.
Require Import zoo.common.list.
Require Import zoo.base.
Require Export zoo_std.xdlchain__code.
Require Import zoo_std.xdlchain__types.
Require Import zoo.options.

Implicit Type node : location.
Implicit Type nodes : list location.
Implicit Type v next prev src dst : val.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Fixpoint xdlchain src nodes dst : iProp Σ :=
    match nodes with
    | [] =>
        True
    | node :: nodes =>
        node.[prev] ↦ src ∗
        match nodes with
        | [] =>
            node.[next] ↦ dst
        | node' :: _ =>
            node.[next] ↦ #node' ∗
            xdlchain #node nodes dst
        end
    end.
  #[global] Arguments xdlchain _ !_ _ / : assert.

  #[global] Instance xdlchainｰtimeless src nodes dst :
    Timeless (xdlchain src nodes dst).
  Proof.
    move: src. induction nodes as [| ? []]; apply _.
  Qed.

  Lemma xdlchainｰnil src dst :
    ⊢ xdlchain src [] dst.
  Proof.
    iSteps.
  Qed.

  Lemma xdlchainｰsingleton src node dst :
    xdlchain src [node] dst ⊣⊢
      node.[prev] ↦ src ∗
      node.[next] ↦ dst.
  Proof.
    iSteps.
  Qed.
  Lemma xdlchainｰsingleton₁ src node dst :
    xdlchain src [node] dst ⊢
      node.[prev] ↦ src ∗
      node.[next] ↦ dst.
  Proof.
    iSteps.
  Qed.
  Lemma xdlchainｰsingleton₂ src node dst :
    node.[prev] ↦ src -∗
    node.[next] ↦ dst -∗
    xdlchain src [node] dst.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma xdlchainｰconsｰunfold {src} node nodes dst :
    xdlchain src (node :: nodes) dst ⊣⊢
      node.[prev] ↦ src ∗
      match nodes with
      | [] =>
          node.[next] ↦ dst
      | node' :: _ =>
          node.[next] ↦ #node' ∗
          xdlchain #node nodes dst
      end.
  Proof.
    done.
  Qed.

  Lemma xdlchainｰcons {src} nodes node nodes' dst :
    nodes = node :: nodes' →
    xdlchain src nodes dst ⊣⊢
      node.[prev] ↦ src ∗
      node.[next] ↦ from_option #@{location} dst (head nodes') ∗
      xdlchain #node nodes' dst.
  Proof.
    destruct nodes'; iSteps.
  Qed.
  Lemma xdlchainｰcons₁ {src} nodes node nodes' dst :
    nodes = node :: nodes' →
    xdlchain src nodes dst ⊢
      node.[prev] ↦ src ∗
      node.[next] ↦ from_option #@{location} dst (head nodes') ∗
      xdlchain #node nodes' dst.
  Proof.
    intros. rewrite xdlchainｰcons //.
  Qed.
  Lemma xdlchainｰcons₂ src node nodes dst :
    node.[prev] ↦ src -∗
    node.[next] ↦ from_option #@{location} dst (head nodes) -∗
    xdlchain #node nodes dst -∗
    xdlchain src (node :: nodes) dst.
  Proof.
    rewrite (xdlchainｰcons (node :: nodes)) //. iSteps.
  Qed.

  Lemma xdlchainｰapp {src} nodes nodes1 nodes2 dst :
    nodes = nodes1 ++ nodes2 →
    xdlchain src nodes dst ⊣⊢
      xdlchain src nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xdlchain (from_option #@{location} src (last nodes1)) nodes2 dst.
  Proof.
    intros ->.
    iInduction nodes1 as [| node1 [| node1' nodes1]] "IH" forall (src).
    - iSteps.
    - destruct nodes2; iSteps.
    - iSplit.
      + rewrite /= -!xdlchainｰconsｰunfold lastｰcons'.
        iIntros "($ & $ & H)".
        iApply ("IH" with "H").
      + rewrite /= -!xdlchainｰconsｰunfold lastｰcons'.
        iIntros "(($ & $ & H1) & H2)".
        iApply ("IH" with "[$H1 $H2]").
  Qed.
  Lemma xdlchainｰapp₁ {src} nodes nodes1 nodes2 dst :
    nodes = nodes1 ++ nodes2 →
    xdlchain src nodes dst ⊢
      xdlchain src nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xdlchain (from_option #@{location} src (last nodes1)) nodes2 dst.
  Proof.
    intros. rewrite xdlchainｰapp //.
  Qed.
  Lemma xdlchainｰapp₂ src nodes1 nodes2 dst :
    xdlchain src nodes1 (from_option #@{location} dst (head nodes2)) -∗
    xdlchain (from_option #@{location} src (last nodes1)) nodes2 dst -∗
    xdlchain src (nodes1 ++ nodes2) dst.
  Proof.
    rewrite (xdlchainｰapp (nodes1 ++ nodes2)) //. iSteps.
  Qed.

  Lemma xdlchainｰsnoc {src} nodes nodes' node dst :
    nodes = nodes' ++ [node] →
    xdlchain src nodes dst ⊣⊢
      xdlchain src nodes' #node ∗
      node.[prev] ↦ from_option #@{location} src (last nodes') ∗
      node.[next] ↦ dst.
  Proof.
    intros. rewrite xdlchainｰapp //.
  Qed.
  Lemma xdlchainｰsnoc₁ {src} nodes nodes' node dst :
    nodes = nodes' ++ [node] →
    xdlchain src nodes dst ⊢
      xdlchain src nodes' #node ∗
      node.[prev] ↦ from_option #@{location} src (last nodes') ∗
      node.[next] ↦ dst.
  Proof.
    intros. rewrite xdlchainｰsnoc //.
  Qed.
  Lemma xdlchainｰsnoc₂ src nodes node dst :
    xdlchain src nodes #node -∗
    node.[prev] ↦ from_option #@{location} src (last nodes) -∗
    node.[next] ↦ dst -∗
    xdlchain src (nodes ++ [node]) dst.
  Proof.
    rewrite (xdlchainｰsnoc (nodes ++ [node])) //. iSteps.
  Qed.

  Lemma xdlchainｰlast {src nodes} node dst :
    last nodes = Some node →
    xdlchain src nodes dst ⊢
      ∃ nodes',
      ⌜nodes = nodes' ++ [node]⌝ ∗
      xdlchain src nodes' #node ∗
      node.[prev] ↦ from_option #@{location} src (last nodes') ∗
      node.[next] ↦ dst.
  Proof.
    iIntros ((nodes' & ->)%last_Some) "H".
    iExists nodes'. iStep.
    iApply (xdlchainｰsnoc₁ with "H"); first done.
  Qed.

  Lemma xdlchainｰlookup {src nodes} i node dst :
    nodes !! i = Some node →
    xdlchain src nodes dst ⊣⊢
      xdlchain src (take i nodes) #node ∗
      node.[prev] ↦ from_option #@{location} src (last $ take i nodes) ∗
      node.[next] ↦ from_option #@{location} dst (head $ drop ˖i nodes) ∗
      xdlchain #node (drop ˖i nodes) dst.
  Proof.
    intros Hlookup.
    pose proof Hlookup as Hnodes%take_drop_middle.
    rewrite -{1}Hnodes xdlchainｰapp // (xdlchainｰcons (node :: _)) //.
  Qed.
  Lemma xdlchainｰlookup₁ {src nodes} i node dst :
    nodes !! i = Some node →
    xdlchain src nodes dst ⊢
      xdlchain src (take i nodes) #node ∗
      node.[prev] ↦ from_option #@{location} src (last $ take i nodes) ∗
      node.[next] ↦ from_option #@{location} dst (head $ drop ˖i nodes) ∗
      xdlchain #node (drop ˖i nodes) dst.
  Proof.
    intros. rewrite xdlchainｰlookup //.
  Qed.
  Lemma xdlchainｰlookup₂ {src nodes} i node prev next dst :
    nodes !! i = Some node →
    prev = from_option #@{location} src (last $ take i nodes) →
    next = from_option #@{location} dst (head $ drop ˖i nodes) →
    xdlchain src (take i nodes) #node -∗
    node.[prev] ↦ prev -∗
    node.[next] ↦ next -∗
    xdlchain #node (drop ˖i nodes) dst -∗
    xdlchain src nodes dst.
  Proof.
    intros. rewrite (@xdlchainｰlookup _ nodes) //. iSteps.
  Qed.

  Lemma xdlchainｰlookupｰacc {src nodes} i node dst :
    nodes !! i = Some node →
    xdlchain src nodes dst ⊢
      node.[prev] ↦ from_option #@{location} src (last $ take i nodes) ∗
      node.[next] ↦ from_option #@{location} dst (head $ drop ˖i nodes) ∗
      ( node.[prev] ↦ from_option #@{location} src (last $ take i nodes) -∗
        node.[next] ↦ from_option #@{location} dst (head $ drop ˖i nodes) -∗
        xdlchain src nodes dst
      ).
  Proof.
    intros. rewrite xdlchainｰlookup //. iSteps.
  Qed.

  Lemma xdlchainｰexclusive src1 src2 nodes dst1 dst2 :
    0 < length nodes →
    xdlchain src1 nodes dst1 -∗
    xdlchain src2 nodes dst2 -∗
    False.
  Proof.
    iIntros "% H1 H2".
    destruct nodes as [| ? []]; first naive_solver lia.
    1: iDestruct "H1" as "(H1 & _)".
    1: iDestruct "H2" as "(H2 & _)".
    2: iDestruct "H1" as "(_ & H1 & _)".
    2: iDestruct "H2" as "(_ & H2 & _)".
    all: iApply (pointstoｰexclusive with "H1 H2").
  Qed.

  Lemma xdlchainｰNoDup src nodes dst :
    xdlchain src nodes dst ⊢
    ⌜NoDup nodes⌝.
  Proof.
    rewrite NoDup_alt.
    iIntros "H %i1 %i2 %node %Hlookup_1 %Hlookup_2".
    destruct_decide (i1 = i2) as ? | Hne; [done | iExFalso].
    assert (nodes !! (i1 `min` i2) = Some node) as Hlookup_min.
    { destruct (Nat.min_spec i1 i2) as [(_ & ->) | (_ & ->)]; done. }
    assert (nodes !! (i1 `max` i2) = Some node) as Hlookup_max.
    { destruct (Nat.max_spec i1 i2) as [(_ & ->) | (_ & ->)]; done. }
    iDestruct (xdlchainｰlookup (i1 `min` i2) with "H") as "(_ & _ & Hnext_1 & H)"; first done.
    iDestruct (xdlchainｰlookup (i1 `max` i2 - i1 `min` i2 - 1) node with "H") as "(_ & _ & Hnext_2 & _)".
    { rewrite lookup_drop -Hlookup_max. f_equal. lia. }
    iApply (pointstoｰexclusive with "Hnext_1 Hnext_2").
  Qed.

  Lemma xdlchain٠prevｰspec {src nodes node} nodes' dst E :
    nodes = node :: nodes' →
    {{{
      xdlchain src nodes dst
    }}}
      (#node).{prev} @ E
    {{{
      RET src;
      xdlchain src nodes dst
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma xdlchain٠prevｰspecｰlookup {src nodes} i node dst E :
    nodes !! i = Some node →
    {{{
      xdlchain src nodes dst
    }}}
      (#node).{prev} @ E
    {{{
      RET from_option #@{location} src (last $ take i nodes);
      xdlchain src nodes dst
    }}}.
  Proof.
    intros Hlookup.
    setoid_rewrite xdlchainｰlookupｰacc at 1; last done.
    iSteps.
  Qed.
  Lemma xdlchain٠prevｰspecｰhead {src nodes} node dst E :
    head nodes = Some node →
    {{{
      xdlchain src nodes dst
    }}}
      (#node).{prev} @ E
    {{{
      RET src;
      xdlchain src nodes dst
    }}}.
  Proof.
    intros (nodes' & ->)%head_Some.
    eapply xdlchain٠prevｰspec. done.
  Qed.

  Lemma xdlchain٠nextｰspec {src nodes node} nodes' dst E :
    nodes = node :: nodes' →
    {{{
      xdlchain src nodes dst
    }}}
      (#node).{next} @ E
    {{{
      RET from_option #@{location} dst (head nodes');
      xdlchain src nodes dst
    }}}.
  Proof.
    iIntros (->) "%Φ H HΦ".
    destruct nodes'; iSteps.
  Qed.
  Lemma xdlchain٠nextｰspecｰlookup {src nodes} i node dst E :
    nodes !! i = Some node →
    {{{
      xdlchain src nodes dst
    }}}
      (#node).{next} @ E
    {{{
      RET from_option #@{location} dst (head $ drop ˖i nodes);
      xdlchain src nodes dst
    }}}.
  Proof.
    intros Hlookup.
    setoid_rewrite xdlchainｰlookupｰacc at 1; last done.
    iSteps.
  Qed.
  Lemma xdlchain٠nextｰspecｰlast {src nodes} node dst E :
    last nodes = Some node →
    {{{
      xdlchain src nodes dst
    }}}
      (#node).{next} @ E
    {{{
      RET dst;
      xdlchain src nodes dst
    }}}.
  Proof.
    iIntros (Hnode) "%Φ H HΦ".
    wp۰apply (xdlchain٠nextｰspecｰlookup (pred (length nodes)) with "H").
    { rewrite -last_lookup //. }
    rewrite skipn_all2; first lia.
    iSteps.
  Qed.

  Lemma xdlchain٠set_prevｰspec {src nodes node} nodes' dst v E :
    nodes = node :: nodes' →
    {{{
      xdlchain src nodes dst
    }}}
      #node <-{prev} v @ E
    {{{
      RET ();
      xdlchain v nodes dst
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma xdlchain٠set_prevｰspecｰlookup {src nodes} i node dst v E :
    nodes !! i = Some node →
    {{{
      xdlchain src nodes dst
    }}}
      #node <-{prev} v @ E
    {{{
      RET ();
      xdlchain src (take i nodes) #node ∗
      xdlchain v (drop i nodes) dst
    }}}.
  Proof.
    intros Hlookup.
    setoid_rewrite xdlchainｰlookup at 1; last done.
    iIntros "%Φ (H1 & Hprev & Hnext & H2) HΦ".
    wp۰store.
    iDestruct (xdlchainｰcons₂ with "Hprev Hnext H2") as "H2".
    rewrite -drop_S //. iSteps.
  Qed.
  Lemma xdlchain٠set_prevｰspecｰhead {src nodes} node dst v E :
    head nodes = Some node →
    {{{
      xdlchain src nodes dst
    }}}
      #node <-{prev} v @ E
    {{{
      RET ();
      xdlchain v nodes dst
    }}}.
  Proof.
    intros (nodes' & ->)%head_Some.
    eapply xdlchain٠set_prevｰspec. done.
  Qed.

  Lemma xdlchain٠set_nextｰspec {src nodes node} nodes' dst v E :
    nodes = node :: nodes' →
    {{{
      xdlchain src nodes dst
    }}}
      #node <-{next} v @ E
    {{{
      RET ();
      xdlchain src [node] v ∗
      xdlchain #node nodes' dst
    }}}.
  Proof.
    iIntros (->) "%Φ H HΦ".
    destruct nodes'; iSteps.
  Qed.
  Lemma xdlchain٠set_nextｰspecｰlookup {src nodes} i node dst v E :
    nodes !! i = Some node →
    {{{
      xdlchain src nodes dst
    }}}
      #node <-{next} v @ E
    {{{
      RET ();
      xdlchain src (take ˖i nodes) v ∗
      xdlchain #node (drop ˖i nodes) dst
    }}}.
  Proof.
    intros Hlookup.
    setoid_rewrite xdlchainｰlookup at 1; last done.
    iIntros "%Φ (H1 & Hprev & Hnext & H2) HΦ".
    wp۰store.
    iDestruct (xdlchainｰsnoc₂ with "H1 Hprev Hnext") as "H1".
    rewrite -take_S_r //. iSteps.
  Qed.
  Lemma xdlchain٠set_nextｰspecｰlast {src nodes} node dst v E :
    last nodes = Some node →
    {{{
      xdlchain src nodes dst
    }}}
      #node <-{next} v @ E
    {{{
      RET ();
      xdlchain src nodes v
    }}}.
  Proof.
    iIntros (Hnode) "%Φ H HΦ".
    wp۰apply (xdlchain٠set_nextｰspecｰlookup (pred (length nodes)) with "H").
    { rewrite -last_lookup //. }
    rewrite firstn_all2; first lia.
    iSteps.
  Qed.
End zoo۰G.

Require zoo_std.xdlchain__opaque.

#[global] Opaque xdlchain.
