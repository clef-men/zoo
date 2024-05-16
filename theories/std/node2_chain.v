From zoo Require Import
  prelude.
From zoo.language Require Import
  notations
  diaframe.
From zoo.std Require Export
  node2.
From zoo.std Require Import
  node2_schain.
From zoo Require Import
  options.

Implicit Types node : location.
Implicit Types nodes : list location.
Implicit Types v dst : val.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition node2_chain nodes vs dst : iProp Σ :=
    node2_schain nodes dst ∗
    [∗ list] node; v ∈ nodes; vs,
      node.[node2_data] ↦ v.

  #[global] Instance node2_chain_timeless nodes vs dst :
    Timeless (node2_chain nodes vs dst).
  Proof.
    apply _.
  Qed.

  Lemma node2_chain_valid nodes vs dst :
    node2_chain nodes vs dst ⊢
    ⌜length nodes = length vs⌝.
  Proof.
    iIntros "(_ & Hvs)".
    iApply (big_sepL2_length with "Hvs").
  Qed.

  Lemma node2_chain_nil dst :
    ⊢ node2_chain [] [] dst.
  Proof.
    iSteps.
  Qed.

  Lemma node2_chain_cons nodes vs node v nodes' vs' dst :
    nodes = node :: nodes' →
    vs = v :: vs' →
    node2_chain nodes vs dst ⊣⊢
      node.[node2_data] ↦ v ∗
      node.[node2_next] ↦ from_option #@{location} dst (head nodes') ∗
      node2_chain nodes' vs' dst.
  Proof.
    intros -> ->.
    rewrite /node2_chain node2_schain_cons //. iSteps.
  Qed.
  Lemma node2_chain_cons_1 nodes vs node v nodes' vs' dst :
    nodes = node :: nodes' →
    vs = v :: vs' →
    node2_chain nodes vs dst ⊢
      node.[node2_data] ↦ v ∗
      node.[node2_next] ↦ from_option #@{location} dst (head nodes') ∗
      node2_chain nodes' vs' dst.
  Proof.
    intros. rewrite node2_chain_cons //.
  Qed.
  Lemma node2_chain_cons_2 node v nodes vs dst :
    node.[node2_data] ↦ v ∗
    node.[node2_next] ↦ from_option #@{location} dst (head nodes) -∗
    node2_chain nodes vs dst -∗
    node2_chain (node :: nodes) (v :: vs) dst.
  Proof.
    rewrite (node2_chain_cons (node :: nodes)) //. iSteps.
  Qed.

  Lemma node2_chain_app nodes vs nodes1 vs1 nodes2 vs2 dst :
    nodes = nodes1 ++ nodes2 →
    vs = vs1 ++ vs2 →
    length nodes1 = length vs1 ∨ length nodes2 = length vs2 →
    node2_chain nodes vs dst ⊣⊢
      node2_chain nodes1 vs1 (from_option #@{location} dst (head nodes2)) ∗
      node2_chain nodes2 vs2 dst.
  Proof.
    intros -> -> Hlength.
    rewrite /node2_chain (node2_schain_app (nodes1 ++ nodes2)) // big_sepL2_app_same_length //. iSteps.
  Qed.
  Lemma node2_chain_app_1 nodes vs nodes1 vs1 nodes2 vs2 dst :
    nodes = nodes1 ++ nodes2 →
    vs = vs1 ++ vs2 →
    length nodes1 = length vs1 ∨ length nodes2 = length vs2 →
    node2_chain nodes vs dst ⊢
      node2_chain nodes1 vs1 (from_option #@{location} dst (head nodes2)) ∗
      node2_chain nodes2 vs2 dst.
  Proof.
    intros. rewrite node2_chain_app //.
  Qed.
  Lemma node2_chain_app_2 nodes1 vs1 nodes2 vs2 dst :
    length nodes1 = length vs1 ∨ length nodes2 = length vs2 →
    node2_chain nodes1 vs1 (from_option #@{location} dst (head nodes2)) -∗
    node2_chain nodes2 vs2 dst -∗
    node2_chain (nodes1 ++ nodes2) (vs1 ++ vs2) dst.
  Proof.
    intros. rewrite (node2_chain_app (nodes1 ++ nodes2)) //. iSteps.
  Qed.

  Lemma node2_chain_snoc nodes vs nodes' vs' node v dst :
    nodes = nodes' ++ [node] →
    vs = vs' ++ [v] →
    node2_chain nodes vs dst ⊣⊢
      node2_chain nodes' vs' #node ∗
      node.[node2_data] ↦ v ∗
      node.[node2_next] ↦ dst.
  Proof.
    intros. rewrite node2_chain_app //; first naive_solver. iSteps.
  Qed.
  Lemma node2_chain_snoc_1 nodes vs nodes' vs' node v dst :
    nodes = nodes' ++ [node] →
    vs = vs' ++ [v] →
    node2_chain nodes vs dst ⊢
      node2_chain nodes' vs' #node ∗
      node.[node2_data] ↦ v ∗
      node.[node2_next] ↦ dst.
  Proof.
    intros. rewrite node2_chain_snoc //.
  Qed.
  Lemma node2_chain_snoc_2 nodes vs node v dst :
    node2_chain nodes vs #node -∗
    node.[node2_data] ↦ v ∗
    node.[node2_next] ↦ dst -∗
    node2_chain (nodes ++ [node]) (vs ++ [v]) dst.
  Proof.
    rewrite (node2_chain_snoc (nodes ++ [node])) //. iSteps.
  Qed.

  Lemma node2_chain_exclusive nodes vs1 dst1 vs2 dst2 :
    0 < length nodes →
    node2_chain nodes vs1 dst1 -∗
    node2_chain nodes vs2 dst2 -∗
    False.
  Proof.
    iIntros "% (H1 & _) (H2 & _)".
    iApply (node2_schain_exclusive with "H1 H2"); first done.
  Qed.

  Lemma node_create_spec_chain {nodes node vs} nodes' dst v :
    nodes = node :: nodes' →
    {{{
      node2_chain nodes vs dst
    }}}
      node2_create v #node
    {{{ node',
      RET #node';
      node2_chain (node' :: nodes) (v :: vs) dst
    }}}.
  Proof.
    iIntros (->) "%Φ (Hnodes & Hvs) HΦ".
    wp_apply (node2_create_spec_schain with "Hnodes"); first done.
    iSteps.
  Qed.

  Lemma node2_data_spec_chain {nodes node vs} v dst E :
    head nodes = Some node →
    head vs = Some v →
    {{{
      node2_chain nodes vs dst
    }}}
      !#node.[node2_data] @ E
    {{{
      RET v;
      node2_chain nodes vs dst
    }}}.
  Proof.
    intros (nodes' & ->)%head_Some (vs' & ->)%head_Some.
    iSteps.
  Qed.

  Lemma node2_next_spec_chain {nodes node vs} nodes' dst E :
    nodes = node :: nodes' →
    {{{
      node2_chain nodes vs dst
    }}}
      !#node.[node2_next] @ E
    {{{
      RET from_option #@{location} dst (head nodes');
      node2_chain nodes vs dst
    }}}.
  Proof.
    iIntros (->) "%Φ (Hnodes & Hvs) HΦ".
    wp_apply (node2_next_spec_schain with "Hnodes"); first done.
    iSteps.
  Qed.

  Lemma node_set_data_spec_chain {nodes node vs} nodes' v vs' dst w E :
    nodes = node :: nodes' →
    vs = v :: vs' →
    {{{
      node2_chain nodes vs dst
    }}}
      #node.[node2_data] <- w @ E
    {{{
      RET ();
      node2_chain [node] [w] (from_option #@{location} dst (head nodes')) ∗
      node2_chain nodes' vs' dst
    }}}.
  Proof.
    iIntros (-> ->) "%Φ H HΦ".
    rewrite node2_chain_cons //. iSteps.
  Qed.

  Lemma node_set_next_spec_chain {nodes node vs} nodes' v vs' dst w E :
    nodes = node :: nodes' →
    vs = v :: vs' →
    {{{
      node2_chain nodes vs dst
    }}}
      #node.[node2_next] <- w @ E
    {{{
      RET ();
      node2_chain [node] [v] w ∗
      node2_chain nodes' vs' dst
    }}}.
  Proof.
    iIntros (-> ->) "%Φ (Hnodes & Hvs) HΦ".
    wp_apply (node2_set_next_spec_schain with "Hnodes"); first done.
    iSteps.
  Qed.
End zoo_G.

#[global] Opaque node2_chain.
