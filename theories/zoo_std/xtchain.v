From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  xtchain__types.
From zoo_std Require Import
  xchain.
From zoo Require Import
  options.

Implicit Types node : location.
Implicit Types nodes : list location.
Implicit Types v next dst : val.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition xtchain hdr nodes dst : iProp Σ :=
    xchain nodes dst ∗
    [∗ list] node ∈ nodes, node ↦ₕ hdr.

  #[global] Instance xtchain_timeless hdr nodes dst :
    Timeless (xtchain hdr nodes dst).
  Proof.
    apply _.
  Qed.

  Lemma xtchain_nil hdr dst :
    ⊢ xtchain hdr [] dst.
  Proof.
    iSteps.
  Qed.

  Lemma xtchain_singleton hdr node dst :
    xtchain hdr [node] dst ⊣⊢
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦ dst.
  Proof.
    rewrite /xtchain xchain_singleton. iSteps.
  Qed.
  Lemma xtchain_singleton_1 hdr node dst :
    xtchain hdr [node] dst ⊢
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦ dst.
  Proof.
    rewrite xtchain_singleton //.
  Qed.
  Lemma xtchain_singleton_2 hdr node dst :
    node ↦ₕ hdr ∗
    node.[xtchain_next] ↦ dst -∗
    xtchain hdr [node] dst.
  Proof.
    rewrite -xtchain_singleton. auto.
  Qed.

  Lemma xtchain_cons {hdr} nodes node nodes' dst :
    nodes = node :: nodes' →
    xtchain hdr nodes dst ⊣⊢
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦ from_option #@{location} dst (head nodes') ∗
      xtchain hdr nodes' dst.
  Proof.
    intros ->.
    rewrite /xtchain xchain_cons // big_sepL_cons. iSteps.
  Qed.
  Lemma xtchain_cons_1 {hdr} nodes node nodes' dst :
    nodes = node :: nodes' →
    xtchain hdr nodes dst ⊢
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦ from_option #@{location} dst (head nodes') ∗
      xtchain hdr nodes' dst.
  Proof.
    intros. rewrite xtchain_cons //.
  Qed.
  Lemma xtchain_cons_2 hdr node nodes dst :
    node ↦ₕ hdr ∗
    node.[xtchain_next] ↦ from_option #@{location} dst (head nodes) -∗
    xtchain hdr nodes dst -∗
    xtchain hdr (node :: nodes) dst.
  Proof.
    rewrite (xtchain_cons (node :: nodes)) //. iSteps.
  Qed.

  Lemma xtchain_app {hdr} nodes nodes1 nodes2 dst :
    nodes = nodes1 ++ nodes2 →
    xtchain hdr nodes dst ⊣⊢
      xtchain hdr nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xtchain hdr nodes2 dst.
  Proof.
    intros ->.
    rewrite /xtchain xchain_app // big_sepL_app. iSteps.
  Qed.
  Lemma xtchain_app_1 {hdr} nodes nodes1 nodes2 dst :
    nodes = nodes1 ++ nodes2 →
    xtchain hdr nodes dst ⊢
      xtchain hdr nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xtchain hdr nodes2 dst.
  Proof.
    intros. rewrite xtchain_app //.
  Qed.
  Lemma xtchain_app_2 hdr nodes1 nodes2 dst :
    xtchain hdr nodes1 (from_option #@{location} dst (head nodes2)) -∗
    xtchain hdr nodes2 dst -∗
    xtchain hdr (nodes1 ++ nodes2) dst.
  Proof.
    rewrite (xtchain_app (nodes1 ++ nodes2)) //. iSteps.
  Qed.

  Lemma xtchain_snoc {hdr} nodes nodes' node dst :
    nodes = nodes' ++ [node] →
    xtchain hdr nodes dst ⊣⊢
      xtchain hdr nodes' #node ∗
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦ dst.
  Proof.
    intros ->.
    rewrite /xtchain xchain_snoc // big_sepL_snoc. iSteps.
  Qed.
  Lemma xtchain_snoc_1 {hdr} nodes nodes' node dst :
    nodes = nodes' ++ [node] →
    xtchain hdr nodes dst ⊢
      xtchain hdr nodes' #node ∗
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦ dst.
  Proof.
    intros. rewrite xtchain_snoc //.
  Qed.
  Lemma xtchain_snoc_2 hdr nodes node dst :
    xtchain hdr nodes #node -∗
    node ↦ₕ hdr -∗
    node.[xtchain_next] ↦ dst -∗
    xtchain hdr (nodes ++ [node]) dst.
  Proof.
    rewrite (xtchain_snoc (nodes ++ [node])) //. iSteps.
  Qed.

  Lemma xtchain_lookup {hdr nodes} i node dst :
    nodes !! i = Some node →
    xtchain hdr nodes dst ⊣⊢
      xtchain hdr (take i nodes) #node ∗
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦ from_option #@{location} dst (nodes !! S i) ∗
      xtchain hdr (drop (S i) nodes) dst.
  Proof.
    intros.
    rewrite /xtchain xchain_lookup //.
    rewrite -{4}(take_drop_middle nodes i node) // big_sepL_app.
    iSteps.
  Qed.
  Lemma xtchain_lookup_1 {hdr nodes} i node dst :
    nodes !! i = Some node →
    xtchain hdr nodes dst ⊢
      xtchain hdr (take i nodes) #node ∗
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦ from_option #@{location} dst (nodes !! S i) ∗
      xtchain hdr (drop (S i) nodes) dst.
  Proof.
    intros. rewrite xtchain_lookup //.
  Qed.
  Lemma xtchain_lookup_2 {hdr nodes} i node next dst :
    nodes !! i = Some node →
    next = from_option #@{location} dst (nodes !! S i) →
    xtchain hdr (take i nodes) #node -∗
    node ↦ₕ hdr -∗
    node.[xtchain_next] ↦ next -∗
    xtchain hdr (drop (S i) nodes) dst -∗
    xtchain hdr nodes dst.
  Proof.
    intros. rewrite (@xtchain_lookup _ nodes) //. iSteps.
  Qed.

  Lemma xtchain_lookup_acc {hdr nodes} i node dst :
    nodes !! i = Some node →
    xtchain hdr nodes dst ⊢
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦ from_option #@{location} dst (nodes !! S i) ∗
      ( node.[xtchain_next] ↦ from_option #@{location} dst (nodes !! S i) -∗
        xtchain hdr nodes dst
      ).
  Proof.
    intros. rewrite xtchain_lookup //. iSteps.
  Qed.

  Lemma xtchain_lookup_header {hdr nodes} i node dst :
    nodes !! i = Some node →
    xtchain hdr nodes dst ⊢
    node ↦ₕ hdr.
  Proof.
    intros. rewrite xtchain_lookup //. iSteps.
  Qed.

  Lemma xtchain_exclusive hdr nodes dst1 dst2 :
    0 < length nodes →
    xtchain hdr nodes dst1 -∗
    xtchain hdr nodes dst2 -∗
    False.
  Proof.
    iIntros "% (H1 & _) (H2 & _)".
    iApply (xchain_exclusive with "H1 H2"); first done.
  Qed.

  Lemma xtchain_NoDup hdr nodes dst :
    xtchain hdr nodes dst ⊢
    ⌜NoDup nodes⌝.
  Proof.
    iIntros "(H & _)".
    iApply (xchain_NoDup with "H").
  Qed.

  Lemma xtchain_next_spec {hdr nodes node} nodes' dst E :
    nodes = node :: nodes' →
    {{{
      xtchain hdr nodes dst
    }}}
      (#node).{xtchain_next} @ E
    {{{
      RET from_option #@{location} dst (head nodes');
      xtchain hdr nodes dst
    }}}.
  Proof.
    iIntros (->) "%Φ (H & Hheaders) HΦ".
    wp_apply (xchain_next_spec with "H"); first done.
    iSteps.
  Qed.
  Lemma xtchain_next_spec_lookup {hdr nodes} i node dst E :
    nodes !! i = Some node →
    {{{
      xtchain hdr nodes dst
    }}}
      (#node).{xtchain_next} @ E
    {{{
      RET from_option #@{location} dst (nodes !! S i);
      xtchain hdr nodes dst
    }}}.
  Proof.
    iIntros "%Hlookup %Φ (H & Hheaders) HΦ".
    wp_apply (xchain_next_spec_lookup with "H"); first done.
    iSteps.
  Qed.

  Lemma xtchain_set_next_spec {hdr nodes node} nodes' dst v E :
    nodes = node :: nodes' →
    {{{
      xtchain hdr nodes dst
    }}}
      (#node) <-{xtchain_next} v @ E
    {{{
      RET ();
      xtchain hdr [node] v ∗
      xtchain hdr nodes' dst
    }}}.
  Proof.
    iIntros (->) "%Φ (H & Hheaders) HΦ".
    wp_apply (xchain_set_next_spec with "H"); first done.
    iSteps.
  Qed.
  Lemma xtchain_set_next_spec_lookup {hdr nodes} i node dst v E :
    nodes !! i = Some node →
    {{{
      xtchain hdr nodes dst
    }}}
      #node <-{xtchain_next} v @ E
    {{{
      RET ();
      xtchain hdr (take (S i) nodes) v ∗
      xtchain hdr (drop (S i) nodes) dst
    }}}.
  Proof.
    intros Hlookup.
    setoid_rewrite xtchain_lookup at 1; last done.
    iIntros "%Φ (H1 & Hheader & Hnode & H2) HΦ".
    wp_store.
    iDestruct (xtchain_snoc_2 with "H1 Hheader Hnode") as "H1".
    rewrite -take_S_r //. iSteps.
  Qed.
End zoo_G.

#[global] Opaque xtchain.
