Require Import zoo.prelude.
Require Import zoo.common.list.
Require Import zoo.base.
Require Export zoo_std.xdlchain__types.
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
        node.[xdlchain_prev] ↦ src ∗
        match nodes with
        | [] =>
            node.[xdlchain_next] ↦ dst
        | node' :: _ =>
            node.[xdlchain_next] ↦ #node' ∗
            xdlchain #node nodes dst
        end
    end.
  #[global] Arguments xdlchain _ !_ _ / : assert.

  #[global] Instance xdlchain𑁒timeless src nodes dst :
    Timeless (xdlchain src nodes dst).
  Proof.
    move: src. induction nodes as [| ? []]; apply _.
  Qed.

  Lemma xdlchain𑁒nil src dst :
    ⊢ xdlchain src [] dst.
  Proof.
    iSteps.
  Qed.

  Lemma xdlchain𑁒singleton src node dst :
    xdlchain src [node] dst ⊣⊢
      node.[xdlchain_prev] ↦ src ∗
      node.[xdlchain_next] ↦ dst.
  Proof.
    iSteps.
  Qed.
  Lemma xdlchain𑁒singleton₁ src node dst :
    xdlchain src [node] dst ⊢
      node.[xdlchain_prev] ↦ src ∗
      node.[xdlchain_next] ↦ dst.
  Proof.
    iSteps.
  Qed.
  Lemma xdlchain𑁒singleton₂ src node dst :
    node.[xdlchain_prev] ↦ src -∗
    node.[xdlchain_next] ↦ dst -∗
    xdlchain src [node] dst.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma xdlchain𑁒cons𑁒unfold {src} node nodes dst :
    xdlchain src (node :: nodes) dst ⊣⊢
      node.[xdlchain_prev] ↦ src ∗
      match nodes with
      | [] =>
          node.[xdlchain_next] ↦ dst
      | node' :: _ =>
          node.[xdlchain_next] ↦ #node' ∗
          xdlchain #node nodes dst
      end.
  Proof.
    done.
  Qed.

  Lemma xdlchain𑁒cons {src} nodes node nodes' dst :
    nodes = node :: nodes' →
    xdlchain src nodes dst ⊣⊢
      node.[xdlchain_prev] ↦ src ∗
      node.[xdlchain_next] ↦ from_option #@{location} dst (head nodes') ∗
      xdlchain #node nodes' dst.
  Proof.
    destruct nodes'; iSteps.
  Qed.
  Lemma xdlchain𑁒cons₁ {src} nodes node nodes' dst :
    nodes = node :: nodes' →
    xdlchain src nodes dst ⊢
      node.[xdlchain_prev] ↦ src ∗
      node.[xdlchain_next] ↦ from_option #@{location} dst (head nodes') ∗
      xdlchain #node nodes' dst.
  Proof.
    intros. rewrite xdlchain𑁒cons //.
  Qed.
  Lemma xdlchain𑁒cons₂ src node nodes dst :
    node.[xdlchain_prev] ↦ src -∗
    node.[xdlchain_next] ↦ from_option #@{location} dst (head nodes) -∗
    xdlchain #node nodes dst -∗
    xdlchain src (node :: nodes) dst.
  Proof.
    rewrite (xdlchain𑁒cons (node :: nodes)) //. iSteps.
  Qed.

  Lemma xdlchain𑁒app {src} nodes nodes1 nodes2 dst :
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
      + rewrite /= -!xdlchain𑁒cons𑁒unfold last𑁒cons'.
        iIntros "($ & $ & H)".
        iApply ("IH" with "H").
      + rewrite /= -!xdlchain𑁒cons𑁒unfold last𑁒cons'.
        iIntros "(($ & $ & H1) & H2)".
        iApply ("IH" with "[$H1 $H2]").
  Qed.
  Lemma xdlchain𑁒app₁ {src} nodes nodes1 nodes2 dst :
    nodes = nodes1 ++ nodes2 →
    xdlchain src nodes dst ⊢
      xdlchain src nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xdlchain (from_option #@{location} src (last nodes1)) nodes2 dst.
  Proof.
    intros. rewrite xdlchain𑁒app //.
  Qed.
  Lemma xdlchain𑁒app₂ src nodes1 nodes2 dst :
    xdlchain src nodes1 (from_option #@{location} dst (head nodes2)) -∗
    xdlchain (from_option #@{location} src (last nodes1)) nodes2 dst -∗
    xdlchain src (nodes1 ++ nodes2) dst.
  Proof.
    rewrite (xdlchain𑁒app (nodes1 ++ nodes2)) //. iSteps.
  Qed.

  Lemma xdlchain𑁒snoc {src} nodes nodes' node dst :
    nodes = nodes' ++ [node] →
    xdlchain src nodes dst ⊣⊢
      xdlchain src nodes' #node ∗
      node.[xdlchain_prev] ↦ from_option #@{location} src (last nodes') ∗
      node.[xdlchain_next] ↦ dst.
  Proof.
    intros. rewrite xdlchain𑁒app //.
  Qed.
  Lemma xdlchain𑁒snoc₁ {src} nodes nodes' node dst :
    nodes = nodes' ++ [node] →
    xdlchain src nodes dst ⊢
      xdlchain src nodes' #node ∗
      node.[xdlchain_prev] ↦ from_option #@{location} src (last nodes') ∗
      node.[xdlchain_next] ↦ dst.
  Proof.
    intros. rewrite xdlchain𑁒snoc //.
  Qed.
  Lemma xdlchain𑁒snoc₂ src nodes node dst :
    xdlchain src nodes #node -∗
    node.[xdlchain_prev] ↦ from_option #@{location} src (last nodes) -∗
    node.[xdlchain_next] ↦ dst -∗
    xdlchain src (nodes ++ [node]) dst.
  Proof.
    rewrite (xdlchain𑁒snoc (nodes ++ [node])) //. iSteps.
  Qed.

  Lemma xdlchain𑁒last {src nodes} node dst :
    last nodes = Some node →
    xdlchain src nodes dst ⊢
      ∃ nodes',
      ⌜nodes = nodes' ++ [node]⌝ ∗
      xdlchain src nodes' #node ∗
      node.[xdlchain_prev] ↦ from_option #@{location} src (last nodes') ∗
      node.[xdlchain_next] ↦ dst.
  Proof.
    iIntros ((nodes' & ->)%last_Some) "H".
    iExists nodes'. iStep.
    iApply (xdlchain𑁒snoc₁ with "H"); first done.
  Qed.

  Lemma xdlchain𑁒lookup {src nodes} i node dst :
    nodes !! i = Some node →
    xdlchain src nodes dst ⊣⊢
      xdlchain src (take i nodes) #node ∗
      node.[xdlchain_prev] ↦ from_option #@{location} src (last $ take i nodes) ∗
      node.[xdlchain_next] ↦ from_option #@{location} dst (head $ drop ˖i nodes) ∗
      xdlchain #node (drop ˖i nodes) dst.
  Proof.
    intros Hlookup.
    pose proof Hlookup as Hnodes%take_drop_middle.
    rewrite -{1}Hnodes xdlchain𑁒app // (xdlchain𑁒cons (node :: _)) //.
  Qed.
  Lemma xdlchain𑁒lookup₁ {src nodes} i node dst :
    nodes !! i = Some node →
    xdlchain src nodes dst ⊢
      xdlchain src (take i nodes) #node ∗
      node.[xdlchain_prev] ↦ from_option #@{location} src (last $ take i nodes) ∗
      node.[xdlchain_next] ↦ from_option #@{location} dst (head $ drop ˖i nodes) ∗
      xdlchain #node (drop ˖i nodes) dst.
  Proof.
    intros. rewrite xdlchain𑁒lookup //.
  Qed.
  Lemma xdlchain𑁒lookup₂ {src nodes} i node prev next dst :
    nodes !! i = Some node →
    prev = from_option #@{location} src (last $ take i nodes) →
    next = from_option #@{location} dst (head $ drop ˖i nodes) →
    xdlchain src (take i nodes) #node -∗
    node.[xdlchain_prev] ↦ prev -∗
    node.[xdlchain_next] ↦ next -∗
    xdlchain #node (drop ˖i nodes) dst -∗
    xdlchain src nodes dst.
  Proof.
    intros. rewrite (@xdlchain𑁒lookup _ nodes) //. iSteps.
  Qed.

  Lemma xdlchain𑁒lookup𑁒acc {src nodes} i node dst :
    nodes !! i = Some node →
    xdlchain src nodes dst ⊢
      node.[xdlchain_prev] ↦ from_option #@{location} src (last $ take i nodes) ∗
      node.[xdlchain_next] ↦ from_option #@{location} dst (head $ drop ˖i nodes) ∗
      ( node.[xdlchain_prev] ↦ from_option #@{location} src (last $ take i nodes) -∗
        node.[xdlchain_next] ↦ from_option #@{location} dst (head $ drop ˖i nodes) -∗
        xdlchain src nodes dst
      ).
  Proof.
    intros. rewrite xdlchain𑁒lookup //. iSteps.
  Qed.

  Lemma xdlchain𑁒exclusive src1 src2 nodes dst1 dst2 :
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
    all: iApply (pointsto𑁒exclusive with "H1 H2").
  Qed.

  Lemma xdlchain𑁒NoDup src nodes dst :
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
    iDestruct (xdlchain𑁒lookup (i1 `min` i2) with "H") as "(_ & _ & Hnext_1 & H)"; first done.
    iDestruct (xdlchain𑁒lookup (i1 `max` i2 - i1 `min` i2 - 1) node with "H") as "(_ & _ & Hnext_2 & _)".
    { rewrite lookup_drop -Hlookup_max. f_equal. lia. }
    iApply (pointsto𑁒exclusive with "Hnext_1 Hnext_2").
  Qed.

  Lemma xdlchain٠prev𑁒spec {src nodes node} nodes' dst E :
    nodes = node :: nodes' →
    {{{
      xdlchain src nodes dst
    }}}
      (#node).{xdlchain_prev} @ E
    {{{
      RET src;
      xdlchain src nodes dst
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma xdlchain٠prev𑁒spec𑁒lookup {src nodes} i node dst E :
    nodes !! i = Some node →
    {{{
      xdlchain src nodes dst
    }}}
      (#node).{xdlchain_prev} @ E
    {{{
      RET from_option #@{location} src (last $ take i nodes);
      xdlchain src nodes dst
    }}}.
  Proof.
    intros Hlookup.
    setoid_rewrite xdlchain𑁒lookup𑁒acc at 1; last done.
    iSteps.
  Qed.
  Lemma xdlchain٠prev𑁒spec𑁒head {src nodes} node dst E :
    head nodes = Some node →
    {{{
      xdlchain src nodes dst
    }}}
      (#node).{xdlchain_prev} @ E
    {{{
      RET src;
      xdlchain src nodes dst
    }}}.
  Proof.
    intros (nodes' & ->)%head_Some.
    eapply xdlchain٠prev𑁒spec. done.
  Qed.

  Lemma xdlchain٠next𑁒spec {src nodes node} nodes' dst E :
    nodes = node :: nodes' →
    {{{
      xdlchain src nodes dst
    }}}
      (#node).{xdlchain_next} @ E
    {{{
      RET from_option #@{location} dst (head nodes');
      xdlchain src nodes dst
    }}}.
  Proof.
    iIntros (->) "%Φ H HΦ".
    destruct nodes'; iSteps.
  Qed.
  Lemma xdlchain٠next𑁒spec𑁒lookup {src nodes} i node dst E :
    nodes !! i = Some node →
    {{{
      xdlchain src nodes dst
    }}}
      (#node).{xdlchain_next} @ E
    {{{
      RET from_option #@{location} dst (head $ drop ˖i nodes);
      xdlchain src nodes dst
    }}}.
  Proof.
    intros Hlookup.
    setoid_rewrite xdlchain𑁒lookup𑁒acc at 1; last done.
    iSteps.
  Qed.
  Lemma xdlchain٠next𑁒spec𑁒last {src nodes} node dst E :
    last nodes = Some node →
    {{{
      xdlchain src nodes dst
    }}}
      (#node).{xdlchain_next} @ E
    {{{
      RET dst;
      xdlchain src nodes dst
    }}}.
  Proof.
    iIntros (Hnode) "%Φ H HΦ".
    wp۰apply (xdlchain٠next𑁒spec𑁒lookup (pred (length nodes)) with "H").
    { rewrite -last_lookup //. }
    rewrite skipn_all2; first lia.
    iSteps.
  Qed.

  Lemma xdlchain٠set_prev𑁒spec {src nodes node} nodes' dst v E :
    nodes = node :: nodes' →
    {{{
      xdlchain src nodes dst
    }}}
      #node <-{xdlchain_prev} v @ E
    {{{
      RET ();
      xdlchain v nodes dst
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma xdlchain٠set_prev𑁒spec𑁒lookup {src nodes} i node dst v E :
    nodes !! i = Some node →
    {{{
      xdlchain src nodes dst
    }}}
      #node <-{xdlchain_prev} v @ E
    {{{
      RET ();
      xdlchain src (take i nodes) #node ∗
      xdlchain v (drop i nodes) dst
    }}}.
  Proof.
    intros Hlookup.
    setoid_rewrite xdlchain𑁒lookup at 1; last done.
    iIntros "%Φ (H1 & Hprev & Hnext & H2) HΦ".
    wp۰store.
    iDestruct (xdlchain𑁒cons₂ with "Hprev Hnext H2") as "H2".
    rewrite -drop_S //. iSteps.
  Qed.
  Lemma xdlchain٠set_prev𑁒spec𑁒head {src nodes} node dst v E :
    head nodes = Some node →
    {{{
      xdlchain src nodes dst
    }}}
      #node <-{xdlchain_prev} v @ E
    {{{
      RET ();
      xdlchain v nodes dst
    }}}.
  Proof.
    intros (nodes' & ->)%head_Some.
    eapply xdlchain٠set_prev𑁒spec. done.
  Qed.

  Lemma xdlchain٠set_next𑁒spec {src nodes node} nodes' dst v E :
    nodes = node :: nodes' →
    {{{
      xdlchain src nodes dst
    }}}
      #node <-{xdlchain_next} v @ E
    {{{
      RET ();
      xdlchain src [node] v ∗
      xdlchain #node nodes' dst
    }}}.
  Proof.
    iIntros (->) "%Φ H HΦ".
    destruct nodes'; iSteps.
  Qed.
  Lemma xdlchain٠set_next𑁒spec𑁒lookup {src nodes} i node dst v E :
    nodes !! i = Some node →
    {{{
      xdlchain src nodes dst
    }}}
      #node <-{xdlchain_next} v @ E
    {{{
      RET ();
      xdlchain src (take ˖i nodes) v ∗
      xdlchain #node (drop ˖i nodes) dst
    }}}.
  Proof.
    intros Hlookup.
    setoid_rewrite xdlchain𑁒lookup at 1; last done.
    iIntros "%Φ (H1 & Hprev & Hnext & H2) HΦ".
    wp۰store.
    iDestruct (xdlchain𑁒snoc₂ with "H1 Hprev Hnext") as "H1".
    rewrite -take_S_r //. iSteps.
  Qed.
  Lemma xdlchain٠set_next𑁒spec𑁒last {src nodes} node dst v E :
    last nodes = Some node →
    {{{
      xdlchain src nodes dst
    }}}
      #node <-{xdlchain_next} v @ E
    {{{
      RET ();
      xdlchain src nodes v
    }}}.
  Proof.
    iIntros (Hnode) "%Φ H HΦ".
    wp۰apply (xdlchain٠set_next𑁒spec𑁒lookup (pred (length nodes)) with "H").
    { rewrite -last_lookup //. }
    rewrite firstn_all2; first lia.
    iSteps.
  Qed.
End zoo۰G.

Require zoo_std.xdlchain__opaque.

#[global] Opaque xdlchain.
