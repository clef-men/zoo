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

  Fixpoint schain_model node nodes dst : iProp Σ :=
    match nodes with
    | [] =>
        ⌜node = dst⌝
    | node' :: nodes =>
        node.[schain_next] ↦ #node' ∗
        schain_model node' nodes dst
    end.
  #[global] Arguments schain_model _ !_ _ / : assert.

  #[global] Instance schain_model_timeless node nodes dst :
    Timeless (schain_model node nodes dst).
  Proof.
    move: node. induction nodes; apply _.
  Qed.

  Lemma schain_model_nil node dst :
    ⌜node = dst⌝ ⊣⊢
    schain_model node [] dst.
  Proof.
    iSteps.
  Qed.
  Lemma schain_model_nil_1 node :
    ⊢ schain_model node [] node.
  Proof.
    iSteps.
  Qed.
  Lemma schain_model_nil_2 node dst :
    schain_model node [] dst ⊢
    ⌜node = dst⌝.
  Proof.
    iSteps.
  Qed.

  Lemma schain_model_cons node nodes node' nodes' dst :
    nodes = node' :: nodes' →
    schain_model node nodes dst ⊣⊢
      node.[schain_next] ↦ #node' ∗
      schain_model node' nodes' dst.
  Proof.
    iSteps.
  Qed.
  Lemma schain_model_cons_1 node nodes node' nodes' dst :
    nodes = node' :: nodes' →
    schain_model node nodes dst ⊢
      node.[schain_next] ↦ #node' ∗
      schain_model node' nodes' dst.
  Proof.
    iSteps.
  Qed.
  Lemma schain_model_cons_2 node node' nodes dst :
    node.[schain_next] ↦ #node' -∗
    schain_model node' nodes dst -∗
    schain_model node (node' :: nodes) dst.
  Proof.
    iSteps.
  Qed.

  Lemma schain_model_app_1 node1 nodes1 node2 nodes2 dst :
    schain_model node1 nodes1 node2 -∗
    schain_model node2 nodes2 dst -∗
    schain_model node1 (nodes1 ++ nodes2) dst.
  Proof.
    iInduction nodes1 as [| node1' nodes1] "IH" forall (node1); iSteps.
  Qed.
  Lemma schain_model_app_2 nodes1 nodes2 node nodes dst :
    nodes = nodes1 ++ nodes2 →
    schain_model node nodes dst ⊢
      ∃ node',
      schain_model node nodes1 node' ∗
      schain_model node' nodes2 dst.
  Proof.
    iInduction nodes1 as [| node1 nodes1] "IH" forall (node nodes); first iSteps.
    iIntros (->). rewrite -app_comm_cons. iIntros "(Hnode & Hnode1)".
    iDestruct ("IH" with "[//] Hnode1") as "(%node' & Hnode1 & Hnode')".
    iSteps.
  Qed.
  Lemma schain_model_app node nodes1 nodes2 dst :
    ( ∃ node',
      schain_model node nodes1 node' ∗
      schain_model node' nodes2 dst
    ) ⊣⊢
    schain_model node (nodes1 ++ nodes2) dst.
  Proof.
    iSplit.
    - iIntros "(%node' & Hnode & Hnode')".
      iApply (schain_model_app_1 with "Hnode Hnode'").
    - iApply schain_model_app_2; first done.
  Qed.

  Lemma schain_model_exclusive node nodes1 dst1 nodes2 dst2 :
    0 < length nodes1 →
    0 < length nodes2 →
    schain_model node nodes1 dst1 -∗
    schain_model node nodes2 dst2 -∗
    False.
  Proof.
    intros.
    destruct nodes1, nodes2; [naive_solver lia.. |].
    iIntros "(Hnode1 & _) (Hnode2 & _)".
    iCombine "Hnode1 Hnode2" gives %(? & _). done.
  Qed.

  Lemma schain_cons_spec node nodes dst v :
    {{{
      schain_model node nodes dst
    }}}
      schain_cons v #node
    {{{ node',
      RET #node';
      node'.[schain_data] ↦ v ∗
      schain_model node' (node :: nodes) dst
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma schain_next_spec {node nodes} node' nodes' dst :
    nodes = node' :: nodes' →
    {{{
      schain_model node nodes dst
    }}}
      (#node).{schain_next}
    {{{
      RET #node';
      schain_model node [node'] node' ∗
      schain_model node' nodes' dst
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma schain_set_next_spec {node nodes} node' nodes' dst l :
    nodes = node' :: nodes' →
    {{{
      schain_model node nodes dst
    }}}
      #node <-{schain_next} #l
    {{{
      RET ();
      schain_model node [l] l ∗
      schain_model node' nodes' dst
    }}}.
  Proof.
    iSteps.
  Qed.
End zebre_G.

#[global] Opaque schain_cons.

#[global] Opaque schain_model.
