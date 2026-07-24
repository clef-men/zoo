Require Import zoo.prelude.
Require Import zoo.base.
Require Export zoo_std.xtchain__types.
Require Import zoo_std.xchain.
Require Import zoo.options.

Implicit Type node : location.
Implicit Type nodes : list location.
Implicit Type v next dst : val.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Definition xtchain hdr dq nodes dst : iProp Σ :=
    xchain dq nodes dst ∗
    [∗ list] node ∈ nodes, node ↦ₕ hdr.

  #[global] Instance xtchain𑁒timeless hdr dq nodes dst :
    Timeless (xtchain hdr dq nodes dst).
  Proof.
    apply _.
  Qed.

  #[global] Instance xtchain𑁒persistent hdr nodes dst :
    Persistent (xtchain hdr DfracDiscarded nodes dst).
  Proof.
    apply _.
  Qed.

  Lemma xtchain𑁒nil hdr dq dst :
    ⊢ xtchain hdr dq [] dst.
  Proof.
    iSteps.
  Qed.

  Lemma xtchain𑁒singleton hdr dq node dst :
    xtchain hdr dq [node] dst ⊣⊢
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦{dq} dst.
  Proof.
    rewrite /xtchain xchain𑁒singleton. iSteps.
  Qed.
  Lemma xtchain𑁒singleton₁ hdr dq node dst :
    xtchain hdr dq [node] dst ⊢
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦{dq} dst.
  Proof.
    rewrite xtchain𑁒singleton //.
  Qed.
  Lemma xtchain𑁒singleton₂ hdr dq node dst :
    node ↦ₕ hdr ∗
    node.[xtchain_next] ↦{dq} dst -∗
    xtchain hdr dq [node] dst.
  Proof.
    rewrite -xtchain𑁒singleton. auto.
  Qed.

  Lemma xtchain𑁒cons {hdr dq} nodes node nodes' dst :
    nodes = node :: nodes' →
    xtchain hdr dq nodes dst ⊣⊢
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦{dq} from_option #@{location} dst (head nodes') ∗
      xtchain hdr dq nodes' dst.
  Proof.
    intros ->.
    rewrite /xtchain xchain𑁒cons // big_sepL_cons. iSteps.
  Qed.
  Lemma xtchain𑁒cons' {hdr dq} node nodes dst :
    xtchain hdr dq (node :: nodes) dst ⊣⊢
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦{dq} from_option #@{location} dst (head nodes) ∗
      xtchain hdr dq nodes dst.
  Proof.
    rewrite xtchain𑁒cons //.
  Qed.
  Lemma xtchain𑁒cons₁ {hdr dq} nodes node nodes' dst :
    nodes = node :: nodes' →
    xtchain hdr dq nodes dst ⊢
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦{dq} from_option #@{location} dst (head nodes') ∗
      xtchain hdr dq nodes' dst.
  Proof.
    intros.
    rewrite xtchain𑁒cons //.
  Qed.
  Lemma xtchain𑁒cons₁' {hdr dq} node nodes dst :
    xtchain hdr dq (node :: nodes) dst ⊢
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦{dq} from_option #@{location} dst (head nodes) ∗
      xtchain hdr dq nodes dst.
  Proof.
    rewrite xtchain𑁒cons //.
  Qed.
  Lemma xtchain𑁒cons₂ hdr dq node nodes dst :
    node ↦ₕ hdr -∗
    node.[xtchain_next] ↦{dq} from_option #@{location} dst (head nodes) -∗
    xtchain hdr dq nodes dst -∗
    xtchain hdr dq (node :: nodes) dst.
  Proof.
    rewrite (xtchain𑁒cons (node :: nodes)) //. iSteps.
  Qed.

  Lemma xtchain𑁒app {hdr dq} nodes nodes1 nodes2 dst :
    nodes = nodes1 ++ nodes2 →
    xtchain hdr dq nodes dst ⊣⊢
      xtchain hdr dq nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xtchain hdr dq nodes2 dst.
  Proof.
    intros ->.
    rewrite /xtchain xchain𑁒app // big_sepL_app. iSteps.
  Qed.
  Lemma xtchain𑁒app' {hdr dq} nodes1 nodes2 dst :
    xtchain hdr dq (nodes1 ++ nodes2) dst ⊣⊢
      xtchain hdr dq nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xtchain hdr dq nodes2 dst.
  Proof.
    rewrite xtchain𑁒app //.
  Qed.
  Lemma xtchain𑁒app₁ {hdr dq} nodes nodes1 nodes2 dst :
    nodes = nodes1 ++ nodes2 →
    xtchain hdr dq nodes dst ⊢
      xtchain hdr dq nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xtchain hdr dq nodes2 dst.
  Proof.
    intros.
    rewrite xtchain𑁒app //.
  Qed.
  Lemma xtchain𑁒app₁' {hdr dq} nodes1 nodes2 dst :
    xtchain hdr dq (nodes1 ++ nodes2) dst ⊢
      xtchain hdr dq nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xtchain hdr dq nodes2 dst.
  Proof.
    rewrite xtchain𑁒app //.
  Qed.
  Lemma xtchain𑁒app₂ hdr dq nodes1 nodes2 dst :
    xtchain hdr dq nodes1 (from_option #@{location} dst (head nodes2)) -∗
    xtchain hdr dq nodes2 dst -∗
    xtchain hdr dq (nodes1 ++ nodes2) dst.
  Proof.
    rewrite (xtchain𑁒app (nodes1 ++ nodes2)) //. iSteps.
  Qed.

  Lemma xtchain𑁒snoc {hdr dq} nodes nodes' node dst :
    nodes = nodes' ++ [node] →
    xtchain hdr dq nodes dst ⊣⊢
      xtchain hdr dq nodes' #node ∗
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦{dq} dst.
  Proof.
    intros ->.
    rewrite /xtchain xchain𑁒snoc // big_sepL_snoc. iSteps.
  Qed.
  Lemma xtchain𑁒snoc' {hdr dq} nodes node dst :
    xtchain hdr dq (nodes ++ [node]) dst ⊣⊢
      xtchain hdr dq nodes #node ∗
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦{dq} dst.
  Proof.
    rewrite xtchain𑁒snoc //.
  Qed.
  Lemma xtchain𑁒snoc₁ {hdr dq} nodes nodes' node dst :
    nodes = nodes' ++ [node] →
    xtchain hdr dq nodes dst ⊢
      xtchain hdr dq nodes' #node ∗
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦{dq} dst.
  Proof.
    intros.
    rewrite xtchain𑁒snoc //.
  Qed.
  Lemma xtchain𑁒snoc₁' {hdr dq} nodes node dst :
    xtchain hdr dq (nodes ++ [node]) dst ⊢
      xtchain hdr dq nodes #node ∗
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦{dq} dst.
  Proof.
    rewrite xtchain𑁒snoc //.
  Qed.
  Lemma xtchain𑁒snoc₂ hdr dq nodes node dst :
    xtchain hdr dq nodes #node -∗
    node ↦ₕ hdr -∗
    node.[xtchain_next] ↦{dq} dst -∗
    xtchain hdr dq (nodes ++ [node]) dst.
  Proof.
    rewrite (xtchain𑁒snoc (nodes ++ [node])) //. iSteps.
  Qed.

  Lemma xtchain𑁒lookup {hdr dq nodes} i node dst :
    nodes !! i = Some node →
    xtchain hdr dq nodes dst ⊣⊢
      xtchain hdr dq (take i nodes) #node ∗
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦{dq} from_option #@{location} dst (nodes !! ˖i) ∗
      xtchain hdr dq (drop ˖i nodes) dst.
  Proof.
    intros.
    rewrite /xtchain xchain𑁒lookup //.
    rewrite -{4}(take_drop_middle nodes i node) // big_sepL_app.
    iSteps.
  Qed.
  Lemma xtchain𑁒lookup₁ {hdr dq nodes} i node dst :
    nodes !! i = Some node →
    xtchain hdr dq nodes dst ⊢
      xtchain hdr dq (take i nodes) #node ∗
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦{dq} from_option #@{location} dst (nodes !! ˖i) ∗
      xtchain hdr dq (drop ˖i nodes) dst.
  Proof.
    intros.
    rewrite xtchain𑁒lookup //.
  Qed.
  Lemma xtchain𑁒lookup₂ {hdr dq nodes} i node next dst :
    nodes !! i = Some node →
    next = from_option #@{location} dst (nodes !! ˖i) →
    xtchain hdr dq (take i nodes) #node -∗
    node ↦ₕ hdr -∗
    node.[xtchain_next] ↦{dq} next -∗
    xtchain hdr dq (drop ˖i nodes) dst -∗
    xtchain hdr dq nodes dst.
  Proof.
    intros. subst.
    rewrite (@xtchain𑁒lookup _ _ nodes) //. iSteps.
  Qed.
  Lemma xtchain𑁒lookup𑁒acc {hdr dq nodes} i node dst :
    nodes !! i = Some node →
    xtchain hdr dq nodes dst ⊢
      node ↦ₕ hdr ∗
      node.[xtchain_next] ↦{dq} from_option #@{location} dst (nodes !! ˖i) ∗
      ( node.[xtchain_next] ↦{dq} from_option #@{location} dst (nodes !! ˖i) -∗
        xtchain hdr dq nodes dst
      ).
  Proof.
    intros. rewrite xtchain𑁒lookup //. iSteps.
  Qed.

  Lemma xtchain𑁒lookup𑁒header {hdr dq nodes} i node dst :
    nodes !! i = Some node →
    xtchain hdr dq nodes dst ⊢
    node ↦ₕ hdr.
  Proof.
    intros. rewrite xtchain𑁒lookup //. iSteps.
  Qed.

  Lemma xtchain𑁒last {hdr dq nodes dst} node :
    last nodes = Some node →
    xtchain hdr dq nodes dst ⊣⊢
      xtchain hdr dq (removelast nodes) #node ∗
      node.[xtchain_next] ↦{dq} dst ∗
      node ↦ₕ hdr.
  Proof.
    intros.
    rewrite /xtchain xchain𑁒last //.
    rewrite {2}(last𑁒removelast nodes node) // big_sepL_snoc.
    iSteps.
  Qed.
  Lemma xtchain𑁒last𑁒acc {hdr dq nodes dst} node :
    last nodes = Some node →
    xtchain hdr dq nodes dst ⊢
      node.[xtchain_next] ↦{dq} dst ∗
      node ↦ₕ hdr ∗
      ( ∀ dst,
        node.[xtchain_next] ↦{dq} dst -∗
        xtchain hdr dq nodes dst
      ).
  Proof.
    intros.
    setoid_rewrite (@xtchain𑁒last _ _ nodes); [| done..].
    iSteps.
  Qed.

  Lemma xtchain𑁒valid hdr dq nodes dst :
    0 < length nodes →
    xtchain hdr dq nodes dst ⊢
    ⌜✓ dq⌝.
  Proof.
    iIntros "% (H & _)".
    iApply (xchain𑁒valid with "H"); first done.
  Qed.
  Lemma xtchain𑁒combine hdr nodes dq1 dst1 dq2 dst2 :
    0 < length nodes →
    xtchain hdr dq1 nodes dst1 -∗
    xtchain hdr dq2 nodes dst2 -∗
      ⌜dst1 = dst2⌝ ∗
      xtchain hdr (dq1 ⋅ dq2) nodes dst1.
  Proof.
    iIntros "% (H1 & $) (H2 & _)".
    iApply (xchain𑁒combine with "H1 H2"); first done.
  Qed.
  Lemma xtchain𑁒valid𑁒2 hdr nodes dq1 dst1 dq2 dst2 :
    0 < length nodes →
    xtchain hdr dq1 nodes dst1 -∗
    xtchain hdr dq2 nodes dst2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜dst1 = dst2⌝.
  Proof.
    iIntros "% H1 H2".
    iDestruct (xtchain𑁒combine with "H1 H2") as "(-> & H)"; first done.
    iDestruct (xtchain𑁒valid with "H") as "$"; first done.
    iSteps.
  Qed.
  Lemma xtchain𑁒agree hdr nodes dq1 dst1 dq2 dst2 :
    0 < length nodes →
    xtchain hdr dq1 nodes dst1 -∗
    xtchain hdr dq2 nodes dst2 -∗
    ⌜dst1 = dst2⌝.
  Proof.
    iIntros "% H1 H2".
    iDestruct (xtchain𑁒combine with "H1 H2") as "($ & _)"; first done.
  Qed.
  Lemma xtchain𑁒dfrac𑁒ne hdr dq1 nodes1 dst1 dq2 nodes2 dst2 :
    0 < length nodes1 →
    ¬ ✓ (dq1 ⋅ dq2) →
    xtchain hdr dq1 nodes1 dst1 -∗
    xtchain hdr dq2 nodes2 dst2 -∗
    ⌜nodes1 ≠ nodes2⌝.
  Proof.
    iIntros "% % H1 H2" (->).
    iDestruct (xtchain𑁒valid𑁒2 with "H1 H2") as %?; naive_solver.
  Qed.
  Lemma xtchain𑁒ne hdr nodes1 dst1 dq2 nodes2 dst2 :
    0 < length nodes1 →
    xtchain hdr (DfracOwn 1) nodes1 dst1 -∗
    xtchain hdr dq2 nodes2 dst2 -∗
    ⌜nodes1 ≠ nodes2⌝.
  Proof.
    intros.
    iApply xtchain𑁒dfrac𑁒ne; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma xtchain𑁒exclusive hdr nodes dst1 dq2 dst2 :
    0 < length nodes →
    xtchain hdr (DfracOwn 1) nodes dst1 -∗
    xtchain hdr dq2 nodes dst2 -∗
    False.
  Proof.
    iIntros "% H1 H2".
    iDestruct (xtchain𑁒ne with "H1 H2") as %?; done.
  Qed.
  Lemma xtchain𑁒persist hdr dq nodes dst :
    xtchain hdr dq nodes dst ⊢ |==>
    xtchain hdr DfracDiscarded nodes dst.
  Proof.
    iIntros "(H & $)".
    iApply (xchain𑁒persist with "H").
  Qed.

  Lemma xtchain𑁒NoDup hdr nodes dst :
    xtchain hdr (DfracOwn 1) nodes dst ⊢
    ⌜NoDup nodes⌝.
  Proof.
    iIntros "(H & _)".
    iApply (xchain𑁒NoDup with "H").
  Qed.

  Lemma xtchain٠next𑁒spec {hdr dq nodes dst node} nodes' E :
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
    wp۰apply (xchain٠next𑁒spec with "H"); first done.
    iSteps.
  Qed.
  Lemma xtchain٠next𑁒spec𑁒lookup {hdr dq nodes dst} i node E :
    nodes !! i = Some node →
    {{{
      xtchain hdr dq nodes dst
    }}}
      (#node).{xtchain_next} @ E
    {{{
      RET from_option #@{location} dst (nodes !! ˖i);
      xtchain hdr dq nodes dst
    }}}.
  Proof.
    iIntros "%Hlookup %Φ (H & Hheaders) HΦ".
    wp۰apply (xchain٠next𑁒spec𑁒lookup with "H"); first done.
    iSteps.
  Qed.
  Lemma xtchain٠next𑁒spec𑁒last hdr dq nodes dst node E :
    last nodes = Some node →
    {{{
      xtchain hdr dq nodes dst
    }}}
      (#node).{xtchain_next} @ E
    {{{
      RET dst;
      xtchain hdr dq nodes dst
    }}}.
  Proof.
    intros.
    setoid_rewrite xtchain𑁒last𑁒acc at 1; last done.
    iSteps.
  Qed.

  Lemma xtchain٠set_next𑁒spec {hdr nodes dst node} nodes' v E :
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
    wp۰apply (xchain٠set_next𑁒spec with "H"); first done.
    iSteps.
  Qed.
  Lemma xtchain٠set_next𑁒spec𑁒lookup {hdr nodes dst} i node v E :
    nodes !! i = Some node →
    {{{
      xtchain hdr (DfracOwn 1) nodes dst
    }}}
      #node <-{xtchain_next} v @ E
    {{{
      RET ();
      xtchain hdr (DfracOwn 1) (take ˖i nodes) v ∗
      xtchain hdr (DfracOwn 1) (drop ˖i nodes) dst
    }}}.
  Proof.
    intros Hlookup.
    setoid_rewrite xtchain𑁒lookup at 1; last done.
    iIntros "%Φ (H1 & Hheader & Hnode & H2) HΦ".
    wp۰store.
    iDestruct (xtchain𑁒snoc₂ with "H1 Hheader Hnode") as "H1".
    rewrite -take_S_r //. iSteps.
  Qed.
  Lemma xtchain٠set_next𑁒spec𑁒last hdr nodes dst node v E :
    last nodes = Some node →
    {{{
      xtchain hdr (DfracOwn 1) nodes dst
    }}}
      #node <-{xtchain_next} v @ E
    {{{
      RET ();
      xtchain hdr (DfracOwn 1) nodes v
    }}}.
  Proof.
    intros.
    setoid_rewrite xtchain𑁒last𑁒acc at 1; last done.
    iSteps.
  Qed.
  Lemma xtchain٠set_next𑁒spec𑁒last' {hdr nodes dst node} node' dst' E :
    last nodes = Some node →
    {{{
      xtchain hdr (DfracOwn 1) nodes dst ∗
      node'.[xtchain_next] ↦ dst' ∗
      node' ↦ₕ hdr
    }}}
      #node <-{xtchain_next} #node' @ E
    {{{
      RET ();
      xtchain hdr (DfracOwn 1) (nodes ++ [node']) dst'
    }}}.
  Proof.
    intros.
    setoid_rewrite xtchain𑁒last𑁒acc at 1; last done.
    rewrite xtchain𑁒snoc'.
    iSteps.
  Qed.
End zoo۰G.

Require zoo_std.xtchain__opaque.

#[global] Opaque xtchain.
