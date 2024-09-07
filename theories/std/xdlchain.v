From zoo Require Import
  prelude.
From zoo.common Require Import
  list.
From zoo.language Require Import
  notations
  diaframe.
From zoo.std Require Export
  base
  xdlchain__types.
From zoo Require Import
  options.

Implicit Types node : location.
Implicit Types nodes : list location.
Implicit Types v next prev src dst : val.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Fixpoint xdlchain_model src nodes dst : iProp Σ :=
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
            xdlchain_model #node nodes dst
        end
    end.
  #[global] Arguments xdlchain_model _ !_ _ / : assert.

  #[global] Instance xdlchain_model_timeless src nodes dst :
    Timeless (xdlchain_model src nodes dst).
  Proof.
    move: src. induction nodes as [| ? []]; apply _.
  Qed.

  Lemma xdlchain_model_nil src dst :
    ⊢ xdlchain_model src [] dst.
  Proof.
    iSteps.
  Qed.

  Lemma xdlchain_model_singleton src node dst :
    xdlchain_model src [node] dst ⊣⊢
      node.[xdlchain_prev] ↦ src ∗
      node.[xdlchain_next] ↦ dst.
  Proof.
    iSteps.
  Qed.
  Lemma xdlchain_model_singleton_1 src node dst :
    xdlchain_model src [node] dst ⊢
      node.[xdlchain_prev] ↦ src ∗
      node.[xdlchain_next] ↦ dst.
  Proof.
    iSteps.
  Qed.
  Lemma xdlchain_model_singleton_2 src node dst :
    node.[xdlchain_prev] ↦ src -∗
    node.[xdlchain_next] ↦ dst -∗
    xdlchain_model src [node] dst.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma xdlchain_model_cons_unfold src node nodes dst :
    xdlchain_model src (node :: nodes) dst ⊣⊢
      node.[xdlchain_prev] ↦ src ∗
      match nodes with
      | [] =>
          node.[xdlchain_next] ↦ dst
      | node' :: _ =>
          node.[xdlchain_next] ↦ #node' ∗
          xdlchain_model #node nodes dst
      end.
  Proof.
    done.
  Qed.

  Lemma xdlchain_model_cons src nodes node nodes' dst :
    nodes = node :: nodes' →
    xdlchain_model src nodes dst ⊣⊢
      node.[xdlchain_prev] ↦ src ∗
      node.[xdlchain_next] ↦ from_option #@{location} dst (head nodes') ∗
      xdlchain_model #node nodes' dst.
  Proof.
    destruct nodes'; iSteps.
  Qed.
  Lemma xdlchain_model_cons_1 src nodes node nodes' dst :
    nodes = node :: nodes' →
    xdlchain_model src nodes dst ⊢
      node.[xdlchain_prev] ↦ src ∗
      node.[xdlchain_next] ↦ from_option #@{location} dst (head nodes') ∗
      xdlchain_model #node nodes' dst.
  Proof.
    intros. rewrite xdlchain_model_cons //.
  Qed.
  Lemma xdlchain_model_cons_2 src node nodes dst :
    node.[xdlchain_prev] ↦ src -∗
    node.[xdlchain_next] ↦ from_option #@{location} dst (head nodes) -∗
    xdlchain_model #node nodes dst -∗
    xdlchain_model src (node :: nodes) dst.
  Proof.
    rewrite (xdlchain_model_cons _ (node :: nodes)) //. iSteps.
  Qed.

  Lemma xdlchain_model_app src nodes nodes1 nodes2 dst :
    nodes = nodes1 ++ nodes2 →
    xdlchain_model src nodes dst ⊣⊢
      xdlchain_model src nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xdlchain_model (from_option #@{location} src (last nodes1)) nodes2 dst.
  Proof.
    intros ->.
    iInduction nodes1 as [| node1 [| node1' nodes1]] "IH" forall (src).
    - iSteps.
    - destruct nodes2; iSteps.
    - iSplit.
      + rewrite /= -!xdlchain_model_cons_unfold last_cons'.
        iIntros "($ & $ & H)".
        iApply ("IH" with "H").
      + rewrite /= -!xdlchain_model_cons_unfold last_cons'.
        iIntros "(($ & $ & H1) & H2)".
        iApply ("IH" with "[$H1 $H2]").
  Qed.
  Lemma xdlchain_model_app_1 src nodes nodes1 nodes2 dst :
    nodes = nodes1 ++ nodes2 →
    xdlchain_model src nodes dst ⊢
      xdlchain_model src nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xdlchain_model (from_option #@{location} src (last nodes1)) nodes2 dst.
  Proof.
    intros. rewrite xdlchain_model_app //.
  Qed.
  Lemma xdlchain_model_app_2 src nodes1 nodes2 dst :
    xdlchain_model src nodes1 (from_option #@{location} dst (head nodes2)) -∗
    xdlchain_model (from_option #@{location} src (last nodes1)) nodes2 dst -∗
    xdlchain_model src (nodes1 ++ nodes2) dst.
  Proof.
    rewrite (xdlchain_model_app _ (nodes1 ++ nodes2)) //. iSteps.
  Qed.

  Lemma xdlchain_model_snoc src nodes nodes' node dst :
    nodes = nodes' ++ [node] →
    xdlchain_model src nodes dst ⊣⊢
      xdlchain_model src nodes' #node ∗
      node.[xdlchain_prev] ↦ from_option #@{location} src (last nodes') ∗
      node.[xdlchain_next] ↦ dst.
  Proof.
    intros. rewrite xdlchain_model_app //.
  Qed.
  Lemma xdlchain_model_snoc_1 src nodes nodes' node dst :
    nodes = nodes' ++ [node] →
    xdlchain_model src nodes dst ⊢
      xdlchain_model src nodes' #node ∗
      node.[xdlchain_prev] ↦ from_option #@{location} src (last nodes') ∗
      node.[xdlchain_next] ↦ dst.
  Proof.
    intros. rewrite xdlchain_model_snoc //.
  Qed.
  Lemma xdlchain_model_snoc_2 src nodes node dst :
    xdlchain_model src nodes #node -∗
    node.[xdlchain_prev] ↦ from_option #@{location} src (last nodes) -∗
    node.[xdlchain_next] ↦ dst -∗
    xdlchain_model src (nodes ++ [node]) dst.
  Proof.
    rewrite (xdlchain_model_snoc _ (nodes ++ [node])) //. iSteps.
  Qed.

  Lemma xdlchain_model_lookup {src nodes} i node dst :
    nodes !! i = Some node →
    xdlchain_model src nodes dst ⊣⊢
      xdlchain_model src (take i nodes) #node ∗
      node.[xdlchain_prev] ↦ from_option #@{location} src (last $ take i nodes) ∗
      node.[xdlchain_next] ↦ from_option #@{location} dst (head $ drop (S i) nodes) ∗
      xdlchain_model #node (drop (S i) nodes) dst.
  Proof.
    intros Hlookup.
    pose proof Hlookup as Hnodes%take_drop_middle.
    rewrite -{1}Hnodes xdlchain_model_app // (xdlchain_model_cons _ (node :: _)) //.
  Qed.
  Lemma xdlchain_model_lookup_1 {src nodes} i node dst :
    nodes !! i = Some node →
    xdlchain_model src nodes dst ⊢
      xdlchain_model src (take i nodes) #node ∗
      node.[xdlchain_prev] ↦ from_option #@{location} src (last $ take i nodes) ∗
      node.[xdlchain_next] ↦ from_option #@{location} dst (head $ drop (S i) nodes) ∗
      xdlchain_model #node (drop (S i) nodes) dst.
  Proof.
    intros. rewrite xdlchain_model_lookup //.
  Qed.
  Lemma xdlchain_model_lookup_2 {src nodes} i node prev next dst :
    nodes !! i = Some node →
    prev = from_option #@{location} src (last $ take i nodes) →
    next = from_option #@{location} dst (head $ drop (S i) nodes) →
    xdlchain_model src (take i nodes) #node -∗
    node.[xdlchain_prev] ↦ prev -∗
    node.[xdlchain_next] ↦ next -∗
    xdlchain_model #node (drop (S i) nodes) dst -∗
    xdlchain_model src nodes dst.
  Proof.
    intros. rewrite (@xdlchain_model_lookup _ nodes) //. iSteps.
  Qed.

  Lemma xdlchain_model_lookup_acc {src nodes} i node dst :
    nodes !! i = Some node →
    xdlchain_model src nodes dst ⊢
      node.[xdlchain_prev] ↦ from_option #@{location} src (last $ take i nodes) ∗
      node.[xdlchain_next] ↦ from_option #@{location} dst (head $ drop (S i) nodes) ∗
      ( node.[xdlchain_prev] ↦ from_option #@{location} src (last $ take i nodes) -∗
        node.[xdlchain_next] ↦ from_option #@{location} dst (head $ drop (S i) nodes) -∗
        xdlchain_model src nodes dst
      ).
  Proof.
    intros. rewrite xdlchain_model_lookup //. iSteps.
  Qed.

  Lemma xdlchain_model_exclusive src1 src2 nodes dst1 dst2 :
    0 < length nodes →
    xdlchain_model src1 nodes dst1 -∗
    xdlchain_model src2 nodes dst2 -∗
    False.
  Proof.
    iIntros "% H1 H2".
    destruct nodes as [| ? []]; first naive_solver lia.
    1: iDestruct "H1" as "(H1 & _)".
    1: iDestruct "H2" as "(H2 & _)".
    2: iDestruct "H1" as "(_ & H1 & _)".
    2: iDestruct "H2" as "(_ & H2 & _)".
    all: iApply (pointsto_exclusive with "H1 H2").
  Qed.

  Lemma xdlchain_model_NoDup src nodes dst :
    xdlchain_model src nodes dst ⊢
    ⌜NoDup nodes⌝.
  Proof.
    rewrite NoDup_alt.
    iIntros "H %i1 %i2 %node %Hlookup_1 %Hlookup_2".
    destruct (decide (i1 = i2)) as [| Hne]; [done | iExFalso].
    assert (nodes !! (i1 `min` i2) = Some node) as Hlookup_min.
    { destruct (Nat.min_spec i1 i2) as [(_ & ->) | (_ & ->)]; done. }
    assert (nodes !! (i1 `max` i2) = Some node) as Hlookup_max.
    { destruct (Nat.max_spec i1 i2) as [(_ & ->) | (_ & ->)]; done. }
    iDestruct (xdlchain_model_lookup (i1 `min` i2) with "H") as "(_ & _ & Hnext_1 & H)"; first done.
    iDestruct (xdlchain_model_lookup (i1 `max` i2 - i1 `min` i2 - 1) node with "H") as "(_ & _ & Hnext_2 & _)".
    { rewrite lookup_drop -Hlookup_max. f_equal. lia. }
    iApply (pointsto_exclusive with "Hnext_1 Hnext_2").
  Qed.

  Lemma xdlchain_prev_spec {src nodes node} nodes' dst E :
    nodes = node :: nodes' →
    {{{
      xdlchain_model src nodes dst
    }}}
      (#node).{xdlchain_prev} @ E
    {{{
      RET src;
      xdlchain_model src nodes dst
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma xdlchain_prev_spec_lookup {src nodes} i node dst E :
    nodes !! i = Some node →
    {{{
      xdlchain_model src nodes dst
    }}}
      (#node).{xdlchain_prev} @ E
    {{{
      RET from_option #@{location} src (last $ take i nodes);
      xdlchain_model src nodes dst
    }}}.
  Proof.
    intros Hlookup.
    setoid_rewrite xdlchain_model_lookup_acc at 1; last done.
    iSteps.
  Qed.

  Lemma xdlchain_next_spec {src nodes node} nodes' dst E :
    nodes = node :: nodes' →
    {{{
      xdlchain_model src nodes dst
    }}}
      (#node).{xdlchain_next} @ E
    {{{
      RET from_option #@{location} dst (head nodes');
      xdlchain_model src nodes dst
    }}}.
  Proof.
    iIntros (->) "%Φ H HΦ".
    destruct nodes'; iSteps.
  Qed.
  Lemma xdlchain_next_spec_lookup {src nodes} i node dst E :
    nodes !! i = Some node →
    {{{
      xdlchain_model src nodes dst
    }}}
      (#node).{xdlchain_next} @ E
    {{{
      RET from_option #@{location} dst (head $ drop (S i) nodes);
      xdlchain_model src nodes dst
    }}}.
  Proof.
    intros Hlookup.
    setoid_rewrite xdlchain_model_lookup_acc at 1; last done.
    iSteps.
  Qed.

  Lemma xdlchain_set_prev_spec {src nodes node} nodes' dst v E :
    nodes = node :: nodes' →
    {{{
      xdlchain_model src nodes dst
    }}}
      (#node) <-{xdlchain_prev} v @ E
    {{{
      RET ();
      xdlchain_model v nodes dst
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma xdlchain_set_prev_spec_lookup {src nodes} i node dst v E :
    nodes !! i = Some node →
    {{{
      xdlchain_model src nodes dst
    }}}
      #node <-{xdlchain_prev} v @ E
    {{{
      RET ();
      xdlchain_model src (take i nodes) #node ∗
      xdlchain_model v (drop i nodes) dst
    }}}.
  Proof.
    intros Hlookup.
    setoid_rewrite xdlchain_model_lookup at 1; last done.
    iIntros "%Φ (H1 & Hprev & Hnext & H2) HΦ".
    wp_store.
    iDestruct (xdlchain_model_cons_2 with "Hprev Hnext H2") as "H2".
    rewrite -drop_S //. iSteps.
  Qed.

  Lemma xdlchain_set_next_spec {src nodes node} nodes' dst v E :
    nodes = node :: nodes' →
    {{{
      xdlchain_model src nodes dst
    }}}
      (#node) <-{xdlchain_next} v @ E
    {{{
      RET ();
      xdlchain_model src [node] v ∗
      xdlchain_model #node nodes' dst
    }}}.
  Proof.
    iIntros (->) "%Φ H HΦ".
    destruct nodes'; iSteps.
  Qed.
  Lemma xdlchain_set_next_spec_lookup {src nodes} i node dst v E :
    nodes !! i = Some node →
    {{{
      xdlchain_model src nodes dst
    }}}
      #node <-{xdlchain_next} v @ E
    {{{
      RET ();
      xdlchain_model src (take (S i) nodes) v ∗
      xdlchain_model #node (drop (S i) nodes) dst
    }}}.
  Proof.
    intros Hlookup.
    setoid_rewrite xdlchain_model_lookup at 1; last done.
    iIntros "%Φ (H1 & Hprev & Hnext & H2) HΦ".
    wp_store.
    iDestruct (xdlchain_model_snoc_2 with "H1 Hprev Hnext") as "H1".
    rewrite -take_S_r //. iSteps.
  Qed.
End zoo_G.

#[global] Opaque xdlchain_model.
