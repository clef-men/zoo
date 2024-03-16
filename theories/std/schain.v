From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Export
  base.
From zebre Require Import
  options.

Implicit Types l node dst : location.
Implicit Types nodes : list location.
Implicit Types v : val.

Notation "'schain_data'" := (
  in_type "schain" 0
)(in custom zebre_field
).
Notation "'schain_next'" := (
  in_type "schain" 1
)(in custom zebre_field
).

Definition schain_cons : val :=
  λ: "v" "t",
    { "v"; "t" }.

Section zebre_G.
  Context `{zebre_G : !ZebreG Σ}.

  Fixpoint schain_model node dq nodes dst : iProp Σ :=
    match nodes with
    | [] =>
        ⌜node = dst⌝
    | node' :: nodes =>
        node.[schain_next] ↦{dq} #node' ∗
        schain_model node' dq nodes dst
    end.
  #[global] Arguments schain_model _ _ !_ _ / : assert.

  #[global] Instance schain_model_timeless node dq nodes dst :
    Timeless (schain_model node dq nodes dst).
  Proof.
    move: node. induction nodes; apply _.
  Qed.
  #[global] Instance schain_model_persistent node nodes dst :
    Persistent (schain_model node DfracDiscarded nodes dst).
  Proof.
    move: node. induction nodes; apply _.
  Qed.

  #[global] Instance schain_model_fractional node nodes dst :
    Fractional (λ q, schain_model node (DfracOwn q) nodes dst).
  Proof.
    intros q1 q2.
    move: node. induction nodes as [| node' nodes IH] => node /=; first iSteps.
    setoid_rewrite IH. setoid_rewrite pointsto_fractional.
    iSplit.
    - iIntros "((Hnode1 & Hnode2) & (Hnode'1 & Hnode'2))". iSteps.
    - iIntros "((Hnode1 & Hnode'1) & (Hnode2 & Hnode'2))". iSteps.
  Qed.
  #[global] Instance schain_model_as_fractional node q nodes dst :
    AsFractional (schain_model node (DfracOwn q) nodes dst) (λ q, schain_model node (DfracOwn q) nodes dst) q.
  Proof.
    split; [done | apply _].
  Qed.

  Lemma schain_model_nil node dq dst :
    ⌜node = dst⌝ ⊣⊢
    schain_model node dq [] dst.
  Proof.
    iSteps.
  Qed.
  Lemma schain_model_nil_1 node dq :
    ⊢ schain_model node dq [] node.
  Proof.
    iSteps.
  Qed.
  Lemma schain_model_nil_2 node dq dst :
    schain_model node dq [] dst ⊢
    ⌜node = dst⌝.
  Proof.
    iSteps.
  Qed.

  Lemma schain_model_cons node dq nodes node' nodes' dst :
    nodes = node' :: nodes' →
    schain_model node dq nodes dst ⊣⊢
      node.[schain_next] ↦{dq} #node' ∗
      schain_model node' dq nodes' dst.
  Proof.
    iSteps.
  Qed.
  Lemma schain_model_cons_1 node dq nodes node' nodes' dst :
    nodes = node' :: nodes' →
    schain_model node dq nodes dst ⊢
      node.[schain_next] ↦{dq} #node' ∗
      schain_model node' dq nodes' dst.
  Proof.
    iSteps.
  Qed.
  Lemma schain_model_cons_2 node dq node' nodes dst :
    node.[schain_next] ↦{dq} #node' -∗
    schain_model node' dq nodes dst -∗
    schain_model node dq (node' :: nodes) dst.
  Proof.
    iSteps.
  Qed.

  Lemma schain_model_app_1 dq node1 nodes1 node2 nodes2 dst :
    schain_model node1 dq nodes1 node2 -∗
    schain_model node2 dq nodes2 dst -∗
    schain_model node1 dq (nodes1 ++ nodes2) dst.
  Proof.
    iInduction nodes1 as [| node1' nodes1] "IH" forall (node1); iSteps.
  Qed.
  Lemma schain_model_app_2 nodes1 nodes2 node dq nodes dst :
    nodes = nodes1 ++ nodes2 →
    schain_model node dq nodes dst ⊢
      ∃ node',
      schain_model node dq nodes1 node' ∗
      schain_model node' dq nodes2 dst.
  Proof.
    iInduction nodes1 as [| node1 nodes1] "IH" forall (node nodes); first iSteps.
    iIntros (->). rewrite -app_comm_cons. iIntros "(Hnode & Hnode1)".
    iDestruct ("IH" with "[//] Hnode1") as "(%node' & Hnode1 & Hnode')".
    iSteps.
  Qed.
  Lemma schain_model_app node dq nodes1 nodes2 dst :
    ( ∃ node',
      schain_model node dq nodes1 node' ∗
      schain_model node' dq nodes2 dst
    ) ⊣⊢
    schain_model node dq (nodes1 ++ nodes2) dst.
  Proof.
    iSplit.
    - iIntros "(%node' & Hnode & Hnode')".
      iApply (schain_model_app_1 with "Hnode Hnode'").
    - iApply schain_model_app_2; first done.
  Qed.

  Lemma schain_model_valid node dq nodes dst :
    0 < length nodes →
    schain_model node dq nodes dst ⊢
    ⌜✓ dq⌝.
  Proof.
    intros Hlen. destruct nodes as [| node' nodes]; first naive_solver lia.
    iIntros "(Hnode & _)".
    iApply (pointsto_valid with "Hnode").
  Qed.
  Lemma schain_model_combine node dq1 nodes1 dst1 dq2 nodes2 dst2 :
    length nodes1 ≤ length nodes2 →
    schain_model node dq1 nodes1 dst1 -∗
    schain_model node dq2 nodes2 dst2 -∗
      schain_model node (dq1 ⋅ dq2) nodes1 dst1 ∗
      schain_model dst1 dq2 (drop (length nodes1) nodes2) dst2 ∗
      ⌜nodes1 = take (length nodes1) nodes2⌝.
  Proof.
    iInduction nodes1 as [| node1' nodes1] "IH" forall (node nodes2); first iSteps.
    destruct nodes2 as [| node2' nodes2].
    - iSteps. lia.
    - iIntros "%Hlen (Hnode_1 & Hnode1') (Hnode_2 & Hnode2')".
      simpl in Hlen. apply le_S_n in Hlen.
      iDestruct (pointsto_combine with "Hnode_1 Hnode_2") as "(Hnode & %Heq)". injection Heq as <-.
      iDestruct ("IH" with "[] Hnode1' Hnode2'") as "(Hnode1' & Hdst1 & ->)"; first done.
      rewrite /= take_length min_l //. iSteps.
  Qed.
  Lemma schain_model_combine' node dq1 nodes1 dst1 dq2 nodes2 dst2 :
    length nodes1 = length nodes2 →
    schain_model node dq1 nodes1 dst1 -∗
    schain_model node dq2 nodes2 dst2 -∗
      schain_model node (dq1 ⋅ dq2) nodes1 dst1 ∗
      ⌜nodes1 = nodes2 ∧ dst1 = dst2⌝.
  Proof.
    iIntros "%Hlen Hnode_1 Hnode_2".
    iDestruct (schain_model_combine with "Hnode_1 Hnode_2") as "($ & Hdst1 & ->)"; first lia.
    rewrite Hlen take_length min_l; first lia.
    rewrite drop_all. iDestruct "Hdst1" as %->.
    rewrite take_ge //.
  Qed.
  Lemma schain_model_valid_2 node dq1 nodes1 dst1 dq2 nodes2 dst2 :
    0 < length nodes1 ≤ length nodes2 →
    schain_model node dq1 nodes1 dst1 -∗
    schain_model node dq2 nodes2 dst2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ nodes1 = take (length nodes1) nodes2⌝.
  Proof.
    iIntros "% Hnode_1 Hnode_2".
    iDestruct (schain_model_combine with "Hnode_1 Hnode_2") as "(Hnode & _ & %)"; first lia.
    iDestruct (schain_model_valid with "Hnode") as %?; first lia.
    iSteps.
  Qed.
  Lemma schain_model_valid_2' node dq1 nodes1 dst1 dq2 nodes2 dst2 :
    0 < length nodes1 →
    length nodes1 = length nodes2 →
    schain_model node dq1 nodes1 dst1 -∗
    schain_model node dq2 nodes2 dst2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ nodes1 = nodes2 ∧ dst1 = dst2⌝.
  Proof.
    iIntros "% % Hnode_1 Hnode_2".
    iDestruct (schain_model_combine' with "Hnode_1 Hnode_2") as "(Hnode & <- & <-)"; first done.
    iDestruct (schain_model_valid with "Hnode") as %?; first done.
    iSteps.
  Qed.
  Lemma schain_model_agree node dq1 nodes1 dst1 dq2 nodes2 dst2 :
    length nodes1 = length nodes2 →
    schain_model node dq1 nodes1 dst1 -∗
    schain_model node dq2 nodes2 dst2 -∗
    ⌜nodes1 = nodes2 ∧ dst1 = dst2⌝.
  Proof.
    iIntros "% Hnode_1 Hnode_2".
    iDestruct (schain_model_combine' with "Hnode_1 Hnode_2") as "(_ & <- & <-)"; first done.
    iSteps.
  Qed.
  Lemma schain_model_dfrac_ne node1 dq1 nodes1 dst1 node2 dq2 nodes2 dst2 :
    0 < length nodes1 →
    0 < length nodes2 →
    ¬ ✓ (dq1 ⋅ dq2) →
    schain_model node1 dq1 nodes1 dst1 -∗
    schain_model node2 dq2 nodes2 dst2 -∗
    ⌜node1 ≠ node2⌝.
  Proof.
    intros. destruct nodes1, nodes2; [naive_solver lia.. |].
    iIntros "(Hnode1 & _) (Hnode2 & _) <-".
    iCombine "Hnode1 Hnode2" gives %(? & _). done.
  Qed.
  Lemma schain_model_ne node1 nodes1 dst1 node2 dq2 nodes2 dst2 :
    0 < length nodes1 →
    0 < length nodes2 →
    schain_model node1 (DfracOwn 1) nodes1 dst1 -∗
    schain_model node2 dq2 nodes2 dst2 -∗
    ⌜node1 ≠ node2⌝.
  Proof.
    intros.
    iApply schain_model_dfrac_ne; [done.. | intros []%exclusive_l; apply _].
  Qed.
  Lemma schain_model_exclusive node nodes1 dst1 nodes2 dst2 :
    0 < length nodes1 →
    0 < length nodes2 →
    schain_model node (DfracOwn 1) nodes1 dst1 -∗
    schain_model node (DfracOwn 1) nodes2 dst2 -∗
    False.
  Proof.
    iIntros "% % Hnode_1 Hnode_2".
    iDestruct (schain_model_ne with "Hnode_1 Hnode_2") as %?; done.
  Qed.
  Lemma schain_model_persist node dq nodes dst :
    schain_model node dq nodes dst ⊢ |==>
    schain_model node DfracDiscarded nodes dst.
  Proof.
    iInduction nodes as [] "IH" forall (node); iSteps.
  Qed.

  Lemma schain_cons_spec node dq nodes dst v :
    {{{
      schain_model node dq nodes dst
    }}}
      schain_cons v #node
    {{{ node',
      RET #node';
      node'.[schain_data] ↦ v ∗
      schain_model node' (DfracOwn 1) [node] node ∗
      schain_model node dq nodes dst
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma schain_cons_spec_raw v1 v2 :
    {{{ True }}}
      schain_cons v1 v2
    {{{ node,
      RET #node;
      node.[schain_data] ↦ v1 ∗
      node.[schain_next] ↦ v2
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma schain_next_spec {node dq nodes} node' nodes' dst :
    nodes = node' :: nodes' →
    {{{
      schain_model node dq nodes dst
    }}}
      (#node).{schain_next}
    {{{
      RET #node';
      schain_model node dq [node'] node' ∗
      schain_model node' dq nodes' dst
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma schain_set_next_spec {node nodes} node' nodes' dst l :
    nodes = node' :: nodes' →
    {{{
      schain_model node (DfracOwn 1) nodes dst
    }}}
      #node <-{schain_next} #l
    {{{
      RET ();
      schain_model node (DfracOwn 1) [l] l ∗
      schain_model node' (DfracOwn 1) nodes' dst
    }}}.
  Proof.
    iSteps.
  Qed.
End zebre_G.

#[global] Opaque schain_cons.

#[global] Opaque schain_model.
