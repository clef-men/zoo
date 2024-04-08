From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Export
  node2.
From zebre Require Import
  options.

Implicit Types node : location.
Implicit Types nodes : list location.
Implicit Types v dst : val.

Section zebre_G.
  Context `{zebre_G : !ZebreG Σ}.

  Fixpoint node2_schain nodes dst : iProp Σ :=
    match nodes with
    | [] =>
        True
    | node :: nodes =>
        match nodes with
        | [] =>
            node.[node2_next] ↦ dst
        | node' :: _ =>
            node.[node2_next] ↦ #node' ∗
            node2_schain nodes dst
        end
    end.
  #[global] Arguments node2_schain !_ _ / : assert.

  #[global] Instance node2_schain_timeless nodes dst :
    Timeless (node2_schain nodes dst).
  Proof.
    induction nodes as [| ? []]; apply _.
  Qed.

  Lemma node2_schain_nil dst :
    ⊢ node2_schain [] dst.
  Proof.
    iSteps.
  Qed.

  Lemma node2_schain_cons nodes node nodes' dst :
    nodes = node :: nodes' →
    node2_schain nodes dst ⊣⊢
      node.[node2_next] ↦ from_option #@{location} dst (head nodes') ∗
      node2_schain nodes' dst.
  Proof.
    destruct nodes'; iSteps.
  Qed.
  Lemma node2_schain_cons_1 nodes node nodes' dst :
    nodes = node :: nodes' →
    node2_schain nodes dst ⊢
      node.[node2_next] ↦ from_option #@{location} dst (head nodes') ∗
      node2_schain nodes' dst.
  Proof.
    intros. rewrite node2_schain_cons //.
  Qed.
  Lemma node2_schain_cons_2 node nodes dst :
    node.[node2_next] ↦ from_option #@{location} dst (head nodes) -∗
    node2_schain nodes dst -∗
    node2_schain (node :: nodes) dst.
  Proof.
    rewrite (node2_schain_cons (node :: nodes)) //. iSteps.
  Qed.

  Lemma node2_schain_app nodes nodes1 nodes2 dst :
    nodes = nodes1 ++ nodes2 →
    node2_schain nodes dst ⊣⊢
      node2_schain nodes1 (from_option #@{location} dst (head nodes2)) ∗
      node2_schain nodes2 dst.
  Proof.
    intros ->.
    iSplit; iInduction nodes1 as [| ? []] "IH"; destruct nodes2; iSteps.
  Qed.
  Lemma node2_schain_app_1 nodes nodes1 nodes2 dst :
    nodes = nodes1 ++ nodes2 →
    node2_schain nodes dst ⊢
      node2_schain nodes1 (from_option #@{location} dst (head nodes2)) ∗
      node2_schain nodes2 dst.
  Proof.
    intros. rewrite node2_schain_app //.
  Qed.
  Lemma node2_schain_app_2 nodes1 nodes2 dst :
    node2_schain nodes1 (from_option #@{location} dst (head nodes2)) -∗
    node2_schain nodes2 dst -∗
    node2_schain (nodes1 ++ nodes2) dst.
  Proof.
    rewrite (node2_schain_app (nodes1 ++ nodes2)) //. iSteps.
  Qed.

  Lemma node2_schain_snoc nodes nodes' node dst :
    nodes = nodes' ++ [node] →
    node2_schain nodes dst ⊣⊢
      node2_schain nodes' #node ∗
      node.[node2_next] ↦ dst.
  Proof.
    intros. rewrite node2_schain_app //.
  Qed.
  Lemma node2_schain_snoc_1 nodes nodes' node dst :
    nodes = nodes' ++ [node] →
    node2_schain nodes dst ⊢
      node2_schain nodes' #node ∗
      node.[node2_next] ↦ dst.
  Proof.
    intros. rewrite node2_schain_snoc //.
  Qed.
  Lemma node2_schain_snoc_2 nodes node dst :
    node2_schain nodes #node -∗
    node.[node2_next] ↦ dst -∗
    node2_schain (nodes ++ [node]) dst.
  Proof.
    rewrite (node2_schain_snoc (nodes ++ [node])) //. iSteps.
  Qed.

  Lemma node2_schain_lookup {nodes} i node dst :
    nodes !! i = Some node →
    node2_schain nodes dst ⊣⊢
      node2_schain (take i nodes) #node ∗
      node.[node2_next] ↦ from_option #@{location} dst (nodes !! S i) ∗
      node2_schain (drop (S i) nodes) dst.
  Proof.
    intros Hlookup.
    pose proof Hlookup as Hnodes%take_drop_middle.
    rewrite -{1}Hnodes node2_schain_app // (node2_schain_cons (node :: _)) //.
    assert (head (drop (S i) nodes) = nodes !! S i) as ->; last done.
    rewrite head_lookup -{2}Hnodes lookup_app_r take_length; first lia.
    rewrite Nat.min_l. { apply lookup_lt_Some in Hlookup. lia. }
    rewrite (Nat.add_sub 1) //.
  Qed.
  Lemma node2_schain_lookup_1 {nodes} i node dst :
    nodes !! i = Some node →
    node2_schain nodes dst ⊢
      node2_schain (take i nodes) #node ∗
      node.[node2_next] ↦ from_option #@{location} dst (nodes !! S i) ∗
      node2_schain (drop (S i) nodes) dst.
  Proof.
    intros. rewrite node2_schain_lookup //.
  Qed.
  Lemma node2_schain_lookup_2 {nodes} i node dst :
    nodes !! i = Some node →
    node2_schain (take i nodes) #node -∗
    node.[node2_next] ↦ from_option #@{location} dst (nodes !! S i) -∗
    node2_schain (drop (S i) nodes) dst -∗
    node2_schain nodes dst.
  Proof.
    intros. rewrite (@node2_schain_lookup nodes) //. iSteps.
  Qed.

  Lemma node2_schain_exclusive nodes dst1 dst2 :
    0 < length nodes →
    node2_schain nodes dst1 -∗
    node2_schain nodes dst2 -∗
    False.
  Proof.
    iIntros "% H1 H2".
    destruct nodes as [| ? []]; first naive_solver lia.
    2: iDestruct "H1" as "(H1 & _)".
    2: iDestruct "H2" as "(H2 & _)".
    all: iDestruct (pointsto_ne with "H1 H2") as %?; done.
  Qed.

  Lemma node2_create_spec_schain {nodes node} nodes' dst v :
    nodes = node :: nodes' →
    {{{
      node2_schain nodes dst
    }}}
      node2_create v #node
    {{{ node',
      RET #node';
      node'.[node2_data] ↦ v ∗
      node2_schain (node' :: nodes) dst
    }}}.
  Proof.
    iIntros (->) "%Φ H HΦ".
    wp_apply (node2_create_spec with "[//]").
    iSteps.
  Qed.

  Lemma node2_next_spec_schain {nodes node} nodes' dst E :
    nodes = node :: nodes' →
    {{{
      node2_schain nodes dst
    }}}
      !#node.[node2_next] @ E
    {{{
      RET from_option #@{location} dst (head nodes');
      node2_schain nodes dst
    }}}.
  Proof.
    iIntros (->) "%Φ H HΦ".
    destruct nodes'; iSteps.
  Qed.
  Lemma node2_next_spec_schain_lookup {nodes} i node dst E :
    nodes !! i = Some node →
    {{{
      node2_schain nodes dst
    }}}
      !#node.[node2_next] @ E
    {{{
      RET from_option #@{location} dst (nodes !! S i);
      node2_schain nodes dst
    }}}.
  Proof.
    intros Hlookup.
    setoid_rewrite node2_schain_lookup; [| done..].
    iSteps.
  Qed.

  Lemma node2_set_next_spec_schain {nodes node} nodes' dst v E :
    nodes = node :: nodes' →
    {{{
      node2_schain nodes dst
    }}}
      #node.[node2_next] <- v @ E
    {{{
      RET ();
      node2_schain [node] v ∗
      node2_schain nodes' dst
    }}}.
  Proof.
    iIntros (->) "%Φ H HΦ".
    destruct nodes'; iSteps.
  Qed.
  Lemma node2_set_next_spec_schain_lookup {nodes} i node dst v E :
    nodes !! i = Some node →
    {{{
      node2_schain nodes dst
    }}}
      #node.[node2_next] <- v @ E
    {{{
      RET ();
      node2_schain (take (S i) nodes) v ∗
      node2_schain (drop (S i) nodes) dst
    }}}.
  Proof.
    intros Hlookup.
    setoid_rewrite node2_schain_lookup at 1; [| done..].
    iIntros "%Φ (H1 & Hnode & H2) HΦ".
    wp_store.
    iDestruct (node2_schain_snoc_2 with "H1 Hnode") as "H1".
    rewrite -take_S_r //. iSteps.
  Qed.
End zebre_G.

#[global] Opaque node2_schain.
