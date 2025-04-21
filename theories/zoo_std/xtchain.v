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

  Definition xtchain hdr dq nodes dst : iProp Σ :=
    xchain dq nodes dst ∗
    [∗ list] node ∈ nodes, node ↦ₕ hdr.

  #[global] Instance xtchain_timeless hdr dq nodes dst :
    Timeless (xtchain hdr dq nodes dst).
  Proof.
    apply _.
  Qed.
  #[global] Instance xtchain_persistent hdr nodes dst :
    Persistent (xtchain hdr DfracDiscarded nodes dst).
  Proof.
    apply _.
  Qed.

  Lemma xtchain_nil hdr dq dst :
    ⊢ xtchain hdr dq [] dst.
  Proof.
    iSteps.
  Qed.

  Lemma xtchain_singleton hdr dq node dst :
    xtchain hdr dq [node] dst ⊣⊢
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦{dq} dst.
  Proof.
    rewrite /xtchain xchain_singleton. iSteps.
  Qed.
  Lemma xtchain_singleton_1 hdr dq node dst :
    xtchain hdr dq [node] dst ⊢
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦{dq} dst.
  Proof.
    rewrite xtchain_singleton //.
  Qed.
  Lemma xtchain_singleton_2 hdr dq node dst :
    node ↦ₕ hdr ∗
    node.[xtchain_next] ↦{dq} dst -∗
    xtchain hdr dq [node] dst.
  Proof.
    rewrite -xtchain_singleton. auto.
  Qed.

  Lemma xtchain_cons {hdr dq} nodes node nodes' dst :
    nodes = node :: nodes' →
    xtchain hdr dq nodes dst ⊣⊢
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦{dq} from_option #@{location} dst (head nodes') ∗
      xtchain hdr dq nodes' dst.
  Proof.
    intros ->.
    rewrite /xtchain xchain_cons // big_sepL_cons. iSteps.
  Qed.
  Lemma xtchain_cons' {hdr dq} node nodes dst :
    xtchain hdr dq (node :: nodes) dst ⊣⊢
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦{dq} from_option #@{location} dst (head nodes) ∗
      xtchain hdr dq nodes dst.
  Proof.
    rewrite xtchain_cons //.
  Qed.
  Lemma xtchain_cons_1 {hdr dq} nodes node nodes' dst :
    nodes = node :: nodes' →
    xtchain hdr dq nodes dst ⊢
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦{dq} from_option #@{location} dst (head nodes') ∗
      xtchain hdr dq nodes' dst.
  Proof.
    intros.
    rewrite xtchain_cons //.
  Qed.
  Lemma xtchain_cons_1' {hdr dq} node nodes dst :
    xtchain hdr dq (node :: nodes) dst ⊢
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦{dq} from_option #@{location} dst (head nodes) ∗
      xtchain hdr dq nodes dst.
  Proof.
    rewrite xtchain_cons //.
  Qed.
  Lemma xtchain_cons_2 hdr dq node nodes dst :
    node ↦ₕ hdr -∗
    node.[xtchain_next] ↦{dq} from_option #@{location} dst (head nodes) -∗
    xtchain hdr dq nodes dst -∗
    xtchain hdr dq (node :: nodes) dst.
  Proof.
    rewrite (xtchain_cons (node :: nodes)) //. iSteps.
  Qed.

  Lemma xtchain_app {hdr dq} nodes nodes1 nodes2 dst :
    nodes = nodes1 ++ nodes2 →
    xtchain hdr dq nodes dst ⊣⊢
      xtchain hdr dq nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xtchain hdr dq nodes2 dst.
  Proof.
    intros ->.
    rewrite /xtchain xchain_app // big_sepL_app. iSteps.
  Qed.
  Lemma xtchain_app' {hdr dq} nodes1 nodes2 dst :
    xtchain hdr dq (nodes1 ++ nodes2) dst ⊣⊢
      xtchain hdr dq nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xtchain hdr dq nodes2 dst.
  Proof.
    rewrite xtchain_app //.
  Qed.
  Lemma xtchain_app_1 {hdr dq} nodes nodes1 nodes2 dst :
    nodes = nodes1 ++ nodes2 →
    xtchain hdr dq nodes dst ⊢
      xtchain hdr dq nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xtchain hdr dq nodes2 dst.
  Proof.
    intros.
    rewrite xtchain_app //.
  Qed.
  Lemma xtchain_app_1' {hdr dq} nodes1 nodes2 dst :
    xtchain hdr dq (nodes1 ++ nodes2) dst ⊢
      xtchain hdr dq nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xtchain hdr dq nodes2 dst.
  Proof.
    rewrite xtchain_app //.
  Qed.
  Lemma xtchain_app_2 hdr dq nodes1 nodes2 dst :
    xtchain hdr dq nodes1 (from_option #@{location} dst (head nodes2)) -∗
    xtchain hdr dq nodes2 dst -∗
    xtchain hdr dq (nodes1 ++ nodes2) dst.
  Proof.
    rewrite (xtchain_app (nodes1 ++ nodes2)) //. iSteps.
  Qed.

  Lemma xtchain_snoc {hdr dq} nodes nodes' node dst :
    nodes = nodes' ++ [node] →
    xtchain hdr dq nodes dst ⊣⊢
      xtchain hdr dq nodes' #node ∗
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦{dq} dst.
  Proof.
    intros ->.
    rewrite /xtchain xchain_snoc // big_sepL_snoc. iSteps.
  Qed.
  Lemma xtchain_snoc' {hdr dq} nodes node dst :
    xtchain hdr dq (nodes ++ [node]) dst ⊣⊢
      xtchain hdr dq nodes #node ∗
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦{dq} dst.
  Proof.
    rewrite xtchain_snoc //.
  Qed.
  Lemma xtchain_snoc_1 {hdr dq} nodes nodes' node dst :
    nodes = nodes' ++ [node] →
    xtchain hdr dq nodes dst ⊢
      xtchain hdr dq nodes' #node ∗
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦{dq} dst.
  Proof.
    intros.
    rewrite xtchain_snoc //.
  Qed.
  Lemma xtchain_snoc_1' {hdr dq} nodes node dst :
    xtchain hdr dq (nodes ++ [node]) dst ⊢
      xtchain hdr dq nodes #node ∗
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦{dq} dst.
  Proof.
    rewrite xtchain_snoc //.
  Qed.
  Lemma xtchain_snoc_2 hdr dq nodes node dst :
    xtchain hdr dq nodes #node -∗
    node ↦ₕ hdr -∗
    node.[xtchain_next] ↦{dq} dst -∗
    xtchain hdr dq (nodes ++ [node]) dst.
  Proof.
    rewrite (xtchain_snoc (nodes ++ [node])) //. iSteps.
  Qed.

  Lemma xtchain_lookup {hdr dq nodes} i node dst :
    nodes !! i = Some node →
    xtchain hdr dq nodes dst ⊣⊢
      xtchain hdr dq (take i nodes) #node ∗
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦{dq} from_option #@{location} dst (nodes !! S i) ∗
      xtchain hdr dq (drop (S i) nodes) dst.
  Proof.
    intros.
    rewrite /xtchain xchain_lookup //.
    rewrite -{4}(take_drop_middle nodes i node) // big_sepL_app.
    iSteps.
  Qed.
  Lemma xtchain_lookup_1 {hdr dq nodes} i node dst :
    nodes !! i = Some node →
    xtchain hdr dq nodes dst ⊢
      xtchain hdr dq (take i nodes) #node ∗
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦{dq} from_option #@{location} dst (nodes !! S i) ∗
      xtchain hdr dq (drop (S i) nodes) dst.
  Proof.
    intros.
    rewrite xtchain_lookup //.
  Qed.
  Lemma xtchain_lookup_2 {hdr dq nodes} i node next dst :
    nodes !! i = Some node →
    next = from_option #@{location} dst (nodes !! S i) →
    xtchain hdr dq (take i nodes) #node -∗
    node ↦ₕ hdr -∗
    node.[xtchain_next] ↦{dq} next -∗
    xtchain hdr dq (drop (S i) nodes) dst -∗
    xtchain hdr dq nodes dst.
  Proof.
    intros. subst.
    rewrite (@xtchain_lookup _ _ nodes) //. iSteps.
  Qed.

  Lemma xtchain_lookup_acc {hdr dq nodes} i node dst :
    nodes !! i = Some node →
    xtchain hdr dq nodes dst ⊢
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦{dq} from_option #@{location} dst (nodes !! S i) ∗
      ( node.[xtchain_next] ↦{dq} from_option #@{location} dst (nodes !! S i) -∗
        xtchain hdr dq nodes dst
      ).
  Proof.
    intros. rewrite xtchain_lookup //. iSteps.
  Qed.

  Lemma xtchain_lookup_header {hdr dq nodes} i node dst :
    nodes !! i = Some node →
    xtchain hdr dq nodes dst ⊢
    node ↦ₕ hdr.
  Proof.
    intros. rewrite xtchain_lookup //. iSteps.
  Qed.

  Lemma xtchain_valid hdr dq nodes dst :
    0 < length nodes →
    xtchain hdr dq nodes dst ⊢
    ⌜✓ dq⌝.
  Proof.
    iIntros "% (H & _)".
    iApply (xchain_valid with "H"); first done.
  Qed.
  Lemma xtchain_combine hdr nodes dq1 dst1 dq2 dst2 :
    0 < length nodes →
    xtchain hdr dq1 nodes dst1 -∗
    xtchain hdr dq2 nodes dst2 -∗
      ⌜dst1 = dst2⌝ ∗
      xtchain hdr (dq1 ⋅ dq2) nodes dst1.
  Proof.
    iIntros "% (H1 & $) (H2 & _)".
    iApply (xchain_combine with "H1 H2"); first done.
  Qed.
  Lemma xtchain_valid_2 hdr nodes dq1 dst1 dq2 dst2 :
    0 < length nodes →
    xtchain hdr dq1 nodes dst1 -∗
    xtchain hdr dq2 nodes dst2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜dst1 = dst2⌝.
  Proof.
    iIntros "% H1 H2".
    iDestruct (xtchain_combine with "H1 H2") as "(-> & H)"; first done.
    iDestruct (xtchain_valid with "H") as "$"; first done.
    iSteps.
  Qed.
  Lemma xtchain_agree hdr nodes dq1 dst1 dq2 dst2 :
    0 < length nodes →
    xtchain hdr dq1 nodes dst1 -∗
    xtchain hdr dq2 nodes dst2 -∗
    ⌜dst1 = dst2⌝.
  Proof.
    iIntros "% H1 H2".
    iDestruct (xtchain_combine with "H1 H2") as "($ & _)"; first done.
  Qed.
  Lemma xtchain_dfrac_ne hdr dq1 nodes1 dst1 dq2 nodes2 dst2 :
    0 < length nodes1 →
    ¬ ✓ (dq1 ⋅ dq2) →
    xtchain hdr dq1 nodes1 dst1 -∗
    xtchain hdr dq2 nodes2 dst2 -∗
    ⌜nodes1 ≠ nodes2⌝.
  Proof.
    iIntros "% % H1 H2" (->).
    iDestruct (xtchain_valid_2 with "H1 H2") as %?; naive_solver.
  Qed.
  Lemma xtchain_ne hdr nodes1 dst1 dq2 nodes2 dst2 :
    0 < length nodes1 →
    xtchain hdr (DfracOwn 1) nodes1 dst1 -∗
    xtchain hdr dq2 nodes2 dst2 -∗
    ⌜nodes1 ≠ nodes2⌝.
  Proof.
    intros.
    iApply xtchain_dfrac_ne; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma xtchain_exclusive hdr nodes dst1 dq2 dst2 :
    0 < length nodes →
    xtchain hdr (DfracOwn 1) nodes dst1 -∗
    xtchain hdr dq2 nodes dst2 -∗
    False.
  Proof.
    iIntros "% H1 H2".
    iDestruct (xtchain_ne with "H1 H2") as %?; done.
  Qed.
  Lemma xtchain_persist hdr dq nodes dst :
    xtchain hdr dq nodes dst ⊢ |==>
    xtchain hdr DfracDiscarded nodes dst.
  Proof.
    iIntros "(H & $)".
    iApply (xchain_persist with "H").
  Qed.

  Lemma xtchain_NoDup hdr nodes dst :
    xtchain hdr (DfracOwn 1) nodes dst ⊢
    ⌜NoDup nodes⌝.
  Proof.
    iIntros "(H & _)".
    iApply (xchain_NoDup with "H").
  Qed.

  Lemma xtchain_next_spec {hdr dq nodes node} nodes' dst E :
    nodes = node :: nodes' →
    {{{
      xtchain dq hdr nodes dst
    }}}
      (#node).{xtchain_next} @ E
    {{{
      RET from_option #@{location} dst (head nodes');
      xtchain dq hdr nodes dst
    }}}.
  Proof.
    iIntros (->) "%Φ (H & Hheaders) HΦ".
    wp_apply (xchain_next_spec with "H"); first done.
    iSteps.
  Qed.
  Lemma xtchain_next_spec_lookup {hdr dq nodes} i node dst E :
    nodes !! i = Some node →
    {{{
      xtchain hdr dq nodes dst
    }}}
      (#node).{xtchain_next} @ E
    {{{
      RET from_option #@{location} dst (nodes !! S i);
      xtchain hdr dq nodes dst
    }}}.
  Proof.
    iIntros "%Hlookup %Φ (H & Hheaders) HΦ".
    wp_apply (xchain_next_spec_lookup with "H"); first done.
    iSteps.
  Qed.

  Lemma xtchain_set_next_spec {hdr nodes node} nodes' dst v E :
    nodes = node :: nodes' →
    {{{
      xtchain hdr (DfracOwn 1) nodes dst
    }}}
      (#node) <-{xtchain_next} v @ E
    {{{
      RET ();
      xtchain hdr (DfracOwn 1) [node] v ∗
      xtchain hdr (DfracOwn 1) nodes' dst
    }}}.
  Proof.
    iIntros (->) "%Φ (H & Hheaders) HΦ".
    wp_apply (xchain_set_next_spec with "H"); first done.
    iSteps.
  Qed.
  Lemma xtchain_set_next_spec_lookup {hdr nodes} i node dst v E :
    nodes !! i = Some node →
    {{{
      xtchain hdr (DfracOwn 1) nodes dst
    }}}
      #node <-{xtchain_next} v @ E
    {{{
      RET ();
      xtchain hdr (DfracOwn 1) (take (S i) nodes) v ∗
      xtchain hdr (DfracOwn 1) (drop (S i) nodes) dst
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
