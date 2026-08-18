Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo_std.xchain.
Require Export zoo_std.xtchain__code.
Require Import zoo_std.xtchain__types.
Require Import zoo.options.

Implicit Type node : location.
Implicit Type nodes : list location.
Implicit Type v next dst : val.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Definition xtchain hdr dq nodes dst : iProp Σ :=
    xchain dq nodes dst ∗
    [∗ list] node ∈ nodes, node ↦ₕ hdr.

  #[global] Instance xtchainｰtimeless hdr dq nodes dst :
    Timeless (xtchain hdr dq nodes dst).
  Proof.
    apply _.
  Qed.

  #[global] Instance xtchainｰpersistent hdr nodes dst :
    Persistent (xtchain hdr DfracDiscarded nodes dst).
  Proof.
    apply _.
  Qed.

  Lemma xtchainｰnil hdr dq dst :
    ⊢ xtchain hdr dq [] dst.
  Proof.
    iSteps.
  Qed.

  Lemma xtchainｰsingleton hdr dq node dst :
    xtchain hdr dq [node] dst ⊣⊢
      node ↦ₕ hdr ∗
      node.[next] ↦{dq} dst.
  Proof.
    rewrite /xtchain xchainｰsingleton. iSteps.
  Qed.
  Lemma xtchainｰsingleton₁ hdr dq node dst :
    xtchain hdr dq [node] dst ⊢
      node ↦ₕ hdr ∗
      node.[next] ↦{dq} dst.
  Proof.
    rewrite xtchainｰsingleton //.
  Qed.
  Lemma xtchainｰsingleton₂ hdr dq node dst :
    node ↦ₕ hdr ∗
    node.[next] ↦{dq} dst -∗
    xtchain hdr dq [node] dst.
  Proof.
    rewrite -xtchainｰsingleton. auto.
  Qed.

  Lemma xtchainｰcons {hdr dq} nodes node nodes' dst :
    nodes = node :: nodes' →
    xtchain hdr dq nodes dst ⊣⊢
      node ↦ₕ hdr ∗
      node.[next] ↦{dq} from_option #@{location} dst (head nodes') ∗
      xtchain hdr dq nodes' dst.
  Proof.
    intros ->.
    rewrite /xtchain xchainｰcons // big_sepL_cons. iSteps.
  Qed.
  Lemma xtchainｰcons' {hdr dq} node nodes dst :
    xtchain hdr dq (node :: nodes) dst ⊣⊢
      node ↦ₕ hdr ∗
      node.[next] ↦{dq} from_option #@{location} dst (head nodes) ∗
      xtchain hdr dq nodes dst.
  Proof.
    rewrite xtchainｰcons //.
  Qed.
  Lemma xtchainｰcons₁ {hdr dq} nodes node nodes' dst :
    nodes = node :: nodes' →
    xtchain hdr dq nodes dst ⊢
      node ↦ₕ hdr ∗
      node.[next] ↦{dq} from_option #@{location} dst (head nodes') ∗
      xtchain hdr dq nodes' dst.
  Proof.
    intros.
    rewrite xtchainｰcons //.
  Qed.
  Lemma xtchainｰcons₁' {hdr dq} node nodes dst :
    xtchain hdr dq (node :: nodes) dst ⊢
      node ↦ₕ hdr ∗
      node.[next] ↦{dq} from_option #@{location} dst (head nodes) ∗
      xtchain hdr dq nodes dst.
  Proof.
    rewrite xtchainｰcons //.
  Qed.
  Lemma xtchainｰcons₂ hdr dq node nodes dst :
    node ↦ₕ hdr -∗
    node.[next] ↦{dq} from_option #@{location} dst (head nodes) -∗
    xtchain hdr dq nodes dst -∗
    xtchain hdr dq (node :: nodes) dst.
  Proof.
    rewrite (xtchainｰcons (node :: nodes)) //. iSteps.
  Qed.

  Lemma xtchainｰapp {hdr dq} nodes nodes1 nodes2 dst :
    nodes = nodes1 ++ nodes2 →
    xtchain hdr dq nodes dst ⊣⊢
      xtchain hdr dq nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xtchain hdr dq nodes2 dst.
  Proof.
    intros ->.
    rewrite /xtchain xchainｰapp // big_sepL_app. iSteps.
  Qed.
  Lemma xtchainｰapp' {hdr dq} nodes1 nodes2 dst :
    xtchain hdr dq (nodes1 ++ nodes2) dst ⊣⊢
      xtchain hdr dq nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xtchain hdr dq nodes2 dst.
  Proof.
    rewrite xtchainｰapp //.
  Qed.
  Lemma xtchainｰapp₁ {hdr dq} nodes nodes1 nodes2 dst :
    nodes = nodes1 ++ nodes2 →
    xtchain hdr dq nodes dst ⊢
      xtchain hdr dq nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xtchain hdr dq nodes2 dst.
  Proof.
    intros.
    rewrite xtchainｰapp //.
  Qed.
  Lemma xtchainｰapp₁' {hdr dq} nodes1 nodes2 dst :
    xtchain hdr dq (nodes1 ++ nodes2) dst ⊢
      xtchain hdr dq nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xtchain hdr dq nodes2 dst.
  Proof.
    rewrite xtchainｰapp //.
  Qed.
  Lemma xtchainｰapp₂ hdr dq nodes1 nodes2 dst :
    xtchain hdr dq nodes1 (from_option #@{location} dst (head nodes2)) -∗
    xtchain hdr dq nodes2 dst -∗
    xtchain hdr dq (nodes1 ++ nodes2) dst.
  Proof.
    rewrite (xtchainｰapp (nodes1 ++ nodes2)) //. iSteps.
  Qed.

  Lemma xtchainｰsnoc {hdr dq} nodes nodes' node dst :
    nodes = nodes' ++ [node] →
    xtchain hdr dq nodes dst ⊣⊢
      xtchain hdr dq nodes' #node ∗
      node ↦ₕ hdr ∗
      node.[next] ↦{dq} dst.
  Proof.
    intros ->.
    rewrite /xtchain xchainｰsnoc // big_sepL_snoc. iSteps.
  Qed.
  Lemma xtchainｰsnoc' {hdr dq} nodes node dst :
    xtchain hdr dq (nodes ++ [node]) dst ⊣⊢
      xtchain hdr dq nodes #node ∗
      node ↦ₕ hdr ∗
      node.[next] ↦{dq} dst.
  Proof.
    rewrite xtchainｰsnoc //.
  Qed.
  Lemma xtchainｰsnoc₁ {hdr dq} nodes nodes' node dst :
    nodes = nodes' ++ [node] →
    xtchain hdr dq nodes dst ⊢
      xtchain hdr dq nodes' #node ∗
      node ↦ₕ hdr ∗
      node.[next] ↦{dq} dst.
  Proof.
    intros.
    rewrite xtchainｰsnoc //.
  Qed.
  Lemma xtchainｰsnoc₁' {hdr dq} nodes node dst :
    xtchain hdr dq (nodes ++ [node]) dst ⊢
      xtchain hdr dq nodes #node ∗
      node ↦ₕ hdr ∗
      node.[next] ↦{dq} dst.
  Proof.
    rewrite xtchainｰsnoc //.
  Qed.
  Lemma xtchainｰsnoc₂ hdr dq nodes node dst :
    xtchain hdr dq nodes #node -∗
    node ↦ₕ hdr -∗
    node.[next] ↦{dq} dst -∗
    xtchain hdr dq (nodes ++ [node]) dst.
  Proof.
    rewrite (xtchainｰsnoc (nodes ++ [node])) //. iSteps.
  Qed.

  Lemma xtchainｰlookup {hdr dq nodes} i node dst :
    nodes !! i = Some node →
    xtchain hdr dq nodes dst ⊣⊢
      xtchain hdr dq (take i nodes) #node ∗
      node ↦ₕ hdr ∗
      node.[next] ↦{dq} from_option #@{location} dst (nodes !! ˖i) ∗
      xtchain hdr dq (drop ˖i nodes) dst.
  Proof.
    intros.
    rewrite /xtchain xchainｰlookup //.
    rewrite -{4}(take_drop_middle nodes i node) // big_sepL_app.
    iSteps.
  Qed.
  Lemma xtchainｰlookup₁ {hdr dq nodes} i node dst :
    nodes !! i = Some node →
    xtchain hdr dq nodes dst ⊢
      xtchain hdr dq (take i nodes) #node ∗
      node ↦ₕ hdr ∗
      node.[next] ↦{dq} from_option #@{location} dst (nodes !! ˖i) ∗
      xtchain hdr dq (drop ˖i nodes) dst.
  Proof.
    intros.
    rewrite xtchainｰlookup //.
  Qed.
  Lemma xtchainｰlookup₂ {hdr dq nodes} i node next dst :
    nodes !! i = Some node →
    next = from_option #@{location} dst (nodes !! ˖i) →
    xtchain hdr dq (take i nodes) #node -∗
    node ↦ₕ hdr -∗
    node.[next] ↦{dq} next -∗
    xtchain hdr dq (drop ˖i nodes) dst -∗
    xtchain hdr dq nodes dst.
  Proof.
    intros. subst.
    rewrite (@xtchainｰlookup _ _ nodes) //. iSteps.
  Qed.
  Lemma xtchainｰlookupｰacc {hdr dq nodes} i node dst :
    nodes !! i = Some node →
    xtchain hdr dq nodes dst ⊢
      node ↦ₕ hdr ∗
      node.[next] ↦{dq} from_option #@{location} dst (nodes !! ˖i) ∗
      ( node.[next] ↦{dq} from_option #@{location} dst (nodes !! ˖i) -∗
        xtchain hdr dq nodes dst
      ).
  Proof.
    intros. rewrite xtchainｰlookup //. iSteps.
  Qed.

  Lemma xtchainｰlookupｰheader {hdr dq nodes} i node dst :
    nodes !! i = Some node →
    xtchain hdr dq nodes dst ⊢
    node ↦ₕ hdr.
  Proof.
    intros. rewrite xtchainｰlookup //. iSteps.
  Qed.

  Lemma xtchainｰlast {hdr dq nodes dst} node :
    last nodes = Some node →
    xtchain hdr dq nodes dst ⊣⊢
      xtchain hdr dq (removelast nodes) #node ∗
      node.[next] ↦{dq} dst ∗
      node ↦ₕ hdr.
  Proof.
    intros.
    rewrite /xtchain xchainｰlast //.
    rewrite {2}(lastｰremovelast nodes node) // big_sepL_snoc.
    iSteps.
  Qed.
  Lemma xtchainｰlastｰacc {hdr dq nodes dst} node :
    last nodes = Some node →
    xtchain hdr dq nodes dst ⊢
      node.[next] ↦{dq} dst ∗
      node ↦ₕ hdr ∗
      ( ∀ dst,
        node.[next] ↦{dq} dst -∗
        xtchain hdr dq nodes dst
      ).
  Proof.
    intros.
    setoid_rewrite (@xtchainｰlast _ _ nodes); [| done..].
    iSteps.
  Qed.

  Lemma xtchainｰvalid hdr dq nodes dst :
    0 < length nodes →
    xtchain hdr dq nodes dst ⊢
    ⌜✓ dq⌝.
  Proof.
    iIntros "% (H & _)".
    iApply (xchainｰvalid with "H"); first done.
  Qed.
  Lemma xtchainｰcombine hdr nodes dq1 dst1 dq2 dst2 :
    0 < length nodes →
    xtchain hdr dq1 nodes dst1 -∗
    xtchain hdr dq2 nodes dst2 -∗
      ⌜dst1 = dst2⌝ ∗
      xtchain hdr (dq1 ⋅ dq2) nodes dst1.
  Proof.
    iIntros "% (H1 & $) (H2 & _)".
    iApply (xchainｰcombine with "H1 H2"); first done.
  Qed.
  Lemma xtchainｰvalidｰ2 hdr nodes dq1 dst1 dq2 dst2 :
    0 < length nodes →
    xtchain hdr dq1 nodes dst1 -∗
    xtchain hdr dq2 nodes dst2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜dst1 = dst2⌝.
  Proof.
    iIntros "% H1 H2".
    iDestruct (xtchainｰcombine with "H1 H2") as "(-> & H)"; first done.
    iDestruct (xtchainｰvalid with "H") as "$"; first done.
    iSteps.
  Qed.
  Lemma xtchainｰagree hdr nodes dq1 dst1 dq2 dst2 :
    0 < length nodes →
    xtchain hdr dq1 nodes dst1 -∗
    xtchain hdr dq2 nodes dst2 -∗
    ⌜dst1 = dst2⌝.
  Proof.
    iIntros "% H1 H2".
    iDestruct (xtchainｰcombine with "H1 H2") as "($ & _)"; first done.
  Qed.
  Lemma xtchainｰdfracｰne hdr dq1 nodes1 dst1 dq2 nodes2 dst2 :
    0 < length nodes1 →
    ¬ ✓ (dq1 ⋅ dq2) →
    xtchain hdr dq1 nodes1 dst1 -∗
    xtchain hdr dq2 nodes2 dst2 -∗
    ⌜nodes1 ≠ nodes2⌝.
  Proof.
    iIntros "% % H1 H2" (->).
    iDestruct (xtchainｰvalidｰ2 with "H1 H2") as %?; naive_solver.
  Qed.
  Lemma xtchainｰne hdr nodes1 dst1 dq2 nodes2 dst2 :
    0 < length nodes1 →
    xtchain hdr (DfracOwn 1) nodes1 dst1 -∗
    xtchain hdr dq2 nodes2 dst2 -∗
    ⌜nodes1 ≠ nodes2⌝.
  Proof.
    intros.
    iApply xtchainｰdfracｰne; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma xtchainｰexclusive hdr nodes dst1 dq2 dst2 :
    0 < length nodes →
    xtchain hdr (DfracOwn 1) nodes dst1 -∗
    xtchain hdr dq2 nodes dst2 -∗
    False.
  Proof.
    iIntros "% H1 H2".
    iDestruct (xtchainｰne with "H1 H2") as %?; done.
  Qed.
  Lemma xtchainｰpersist hdr dq nodes dst :
    xtchain hdr dq nodes dst ⊢ |==>
    xtchain hdr DfracDiscarded nodes dst.
  Proof.
    iIntros "(H & $)".
    iApply (xchainｰpersist with "H").
  Qed.

  Lemma xtchainｰNoDup hdr nodes dst :
    xtchain hdr (DfracOwn 1) nodes dst ⊢
    ⌜NoDup nodes⌝.
  Proof.
    iIntros "(H & _)".
    iApply (xchainｰNoDup with "H").
  Qed.

  Lemma xtchain٠nextｰspec {hdr dq nodes dst node} nodes' E :
    nodes = node :: nodes' →
    {{{
      xtchain dq hdr nodes dst
    }}}
      (#node).{next}
      @ E
    {{{
      RET from_option #@{location} dst (head nodes');
      xtchain dq hdr nodes dst
    }}}.
  Proof.
    iIntros (->) "%Φ (H & Hheaders) HΦ".
    wp۰apply (xchain٠nextｰspec with "H"); first done.
    iSteps.
  Qed.
  Lemma xtchain٠nextｰspecｰlookup {hdr dq nodes dst} i node E :
    nodes !! i = Some node →
    {{{
      xtchain hdr dq nodes dst
    }}}
      (#node).{next}
      @ E
    {{{
      RET from_option #@{location} dst (nodes !! ˖i);
      xtchain hdr dq nodes dst
    }}}.
  Proof.
    iIntros "%Hlookup %Φ (H & Hheaders) HΦ".
    wp۰apply (xchain٠nextｰspecｰlookup with "H"); first done.
    iSteps.
  Qed.
  Lemma xtchain٠nextｰspecｰlast hdr dq nodes dst node E :
    last nodes = Some node →
    {{{
      xtchain hdr dq nodes dst
    }}}
      (#node).{next}
      @ E
    {{{
      RET dst;
      xtchain hdr dq nodes dst
    }}}.
  Proof.
    intros.
    setoid_rewrite xtchainｰlastｰacc at 1; last done.
    iSteps.
  Qed.

  Lemma xtchain٠set_nextｰspec {hdr nodes dst node} nodes' v E :
    nodes = node :: nodes' →
    {{{
      xtchain hdr (DfracOwn 1) nodes dst
    }}}
      (#node) <-{next} v
      @ E
    {{{
      RET ();
      xtchain hdr (DfracOwn 1) [node] v ∗
      xtchain hdr (DfracOwn 1) nodes' dst
    }}}.
  Proof.
    iIntros (->) "%Φ (H & Hheaders) HΦ".
    wp۰apply (xchain٠set_nextｰspec with "H"); first done.
    iSteps.
  Qed.
  Lemma xtchain٠set_nextｰspecｰlookup {hdr nodes dst} i node v E :
    nodes !! i = Some node →
    {{{
      xtchain hdr (DfracOwn 1) nodes dst
    }}}
      #node <-{next} v
      @ E
    {{{
      RET ();
      xtchain hdr (DfracOwn 1) (take ˖i nodes) v ∗
      xtchain hdr (DfracOwn 1) (drop ˖i nodes) dst
    }}}.
  Proof.
    intros Hlookup.
    setoid_rewrite xtchainｰlookup at 1; last done.
    iIntros "%Φ (H1 & Hheader & Hnode & H2) HΦ".
    wp۰store.
    iDestruct (xtchainｰsnoc₂ with "H1 Hheader Hnode") as "H1".
    rewrite -take_S_r //. iSteps.
  Qed.
  Lemma xtchain٠set_nextｰspecｰlast hdr nodes dst node v E :
    last nodes = Some node →
    {{{
      xtchain hdr (DfracOwn 1) nodes dst
    }}}
      #node <-{next} v
      @ E
    {{{
      RET ();
      xtchain hdr (DfracOwn 1) nodes v
    }}}.
  Proof.
    intros.
    setoid_rewrite xtchainｰlastｰacc at 1; last done.
    iSteps.
  Qed.
  Lemma xtchain٠set_nextｰspecｰlast' {hdr nodes dst node} node' dst' E :
    last nodes = Some node →
    {{{
      xtchain hdr (DfracOwn 1) nodes dst ∗
      node'.[next] ↦ dst' ∗
      node' ↦ₕ hdr
    }}}
      #node <-{next} #node'
      @ E
    {{{
      RET ();
      xtchain hdr (DfracOwn 1) (nodes ++ [node']) dst'
    }}}.
  Proof.
    intros.
    setoid_rewrite xtchainｰlastｰacc at 1; last done.
    rewrite xtchainｰsnoc'.
    iSteps.
  Qed.
End zoo۰G.

Require zoo_std.xtchain__opaque.

#[global] Opaque xtchain.
