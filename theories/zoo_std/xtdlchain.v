Require Import zoo.prelude.
Require Import zoo.base.
Require Export zoo_std.xtdlchain__types.
Require Import zoo_std.xdlchain.
Require Import zoo.options.

Implicit Type node : location.
Implicit Type nodes : list location.
Implicit Type v next prev src dst : val.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Definition xtdlchain hdr src nodes dst : iProp Σ :=
    xdlchain src nodes dst ∗
    [∗ list] node ∈ nodes, headers۰at node hdr.

  #[global] Instance xtdlchainｰtimeless hdr src nodes dst :
    Timeless (xtdlchain hdr src nodes dst).
  Proof.
    apply _.
  Qed.

  Lemma xtdlchainｰnil hdr src dst :
    ⊢ xtdlchain hdr src [] dst.
  Proof.
    iSteps.
  Qed.

  Lemma xtdlchainｰsingleton hdr src node dst :
    xtdlchain hdr src [node] dst ⊣⊢
      node ↦ₕ hdr ∗
      node.[xtdlchain_prev] ↦ src ∗
      node.[xtdlchain_next] ↦ dst.
  Proof.
    rewrite /xtdlchain xdlchainｰsingleton. iSteps.
  Qed.
  Lemma xtdlchainｰsingleton₁ hdr src node dst :
    xtdlchain hdr src [node] dst ⊢
      node ↦ₕ hdr ∗
      node.[xtdlchain_prev] ↦ src ∗
      node.[xtdlchain_next] ↦ dst.
  Proof.
    rewrite xtdlchainｰsingleton //.
  Qed.
  Lemma xtdlchainｰsingleton₂ hdr src node dst :
    node ↦ₕ hdr ∗
    node.[xtdlchain_prev] ↦ src -∗
    node.[xtdlchain_next] ↦ dst -∗
    xtdlchain hdr src [node] dst.
  Proof.
    rewrite xtdlchainｰsingleton. iSteps.
  Qed.

  Lemma xtdlchainｰcons {hdr src} nodes node nodes' dst :
    nodes = node :: nodes' →
    xtdlchain hdr src nodes dst ⊣⊢
      node ↦ₕ hdr ∗
      node.[xtdlchain_prev] ↦ src ∗
      node.[xtdlchain_next] ↦ from_option #@{location} dst (head nodes') ∗
      xtdlchain hdr #node nodes' dst.
  Proof.
    intros ->.
    rewrite /xtdlchain xdlchainｰcons // big_sepL_cons. iSteps.
  Qed.
  Lemma xtdlchainｰcons₁ {hdr src} nodes node nodes' dst :
    nodes = node :: nodes' →
    xtdlchain hdr src nodes dst ⊢
      node ↦ₕ hdr ∗
      node.[xtdlchain_prev] ↦ src ∗
      node.[xtdlchain_next] ↦ from_option #@{location} dst (head nodes') ∗
      xtdlchain hdr #node nodes' dst.
  Proof.
    intros. rewrite xtdlchainｰcons //.
  Qed.
  Lemma xtdlchainｰcons₂ hdr src node nodes dst :
    node ↦ₕ hdr ∗
    node.[xtdlchain_prev] ↦ src -∗
    node.[xtdlchain_next] ↦ from_option #@{location} dst (head nodes) -∗
    xtdlchain hdr #node nodes dst -∗
    xtdlchain hdr src (node :: nodes) dst.
  Proof.
    rewrite (xtdlchainｰcons (node :: nodes)) //. iSteps.
  Qed.

  Lemma xtdlchainｰapp {hdr src} nodes nodes1 nodes2 dst :
    nodes = nodes1 ++ nodes2 →
    xtdlchain hdr src nodes dst ⊣⊢
      xtdlchain hdr src nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xtdlchain hdr (from_option #@{location} src (last nodes1)) nodes2 dst.
  Proof.
    intros ->.
    rewrite /xtdlchain xdlchainｰapp // big_sepL_app. iSteps.
  Qed.
  Lemma xtdlchainｰapp₁ {hdr src} nodes nodes1 nodes2 dst :
    nodes = nodes1 ++ nodes2 →
    xtdlchain hdr src nodes dst ⊢
      xtdlchain hdr src nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xtdlchain hdr (from_option #@{location} src (last nodes1)) nodes2 dst.
  Proof.
    intros. rewrite xtdlchainｰapp //.
  Qed.
  Lemma xtdlchainｰapp₂ hdr src nodes1 nodes2 dst :
    xtdlchain hdr src nodes1 (from_option #@{location} dst (head nodes2)) -∗
    xtdlchain hdr (from_option #@{location} src (last nodes1)) nodes2 dst -∗
    xtdlchain hdr src (nodes1 ++ nodes2) dst.
  Proof.
    rewrite (xtdlchainｰapp (nodes1 ++ nodes2)) //. iSteps.
  Qed.

  Lemma xtdlchainｰsnoc {hdr src} nodes nodes' node dst :
    nodes = nodes' ++ [node] →
    xtdlchain hdr src nodes dst ⊣⊢
      xtdlchain hdr src nodes' #node ∗
      node ↦ₕ hdr ∗
      node.[xtdlchain_prev] ↦ from_option #@{location} src (last nodes') ∗
      node.[xtdlchain_next] ↦ dst.
  Proof.
    intros ->.
    rewrite /xtdlchain xdlchainｰsnoc // big_sepL_snoc. iSteps.
  Qed.
  Lemma xtdlchainｰsnoc₁ {hdr src} nodes nodes' node dst :
    nodes = nodes' ++ [node] →
    xtdlchain hdr src nodes dst ⊢
      xtdlchain hdr src nodes' #node ∗
      node ↦ₕ hdr ∗
      node.[xtdlchain_prev] ↦ from_option #@{location} src (last nodes') ∗
      node.[xtdlchain_next] ↦ dst.
  Proof.
    intros. rewrite xtdlchainｰsnoc //.
  Qed.
  Lemma xtdlchainｰsnoc₂ hdr src nodes node dst :
    xtdlchain hdr src nodes #node -∗
    node ↦ₕ hdr -∗
    node.[xtdlchain_prev] ↦ from_option #@{location} src (last nodes) -∗
    node.[xtdlchain_next] ↦ dst -∗
    xtdlchain hdr src (nodes ++ [node]) dst.
  Proof.
    rewrite (xtdlchainｰsnoc (nodes ++ [node])) //. iSteps.
  Qed.

  Lemma xtdlchainｰlast {hdr src nodes} node dst :
    last nodes = Some node →
    xtdlchain hdr src nodes dst ⊢
      ∃ nodes',
      ⌜nodes = nodes' ++ [node]⌝ ∗
      xtdlchain hdr src nodes' #node ∗
      node ↦ₕ hdr ∗
      node.[xtdlchain_prev] ↦ from_option #@{location} src (last nodes') ∗
      node.[xtdlchain_next] ↦ dst.
  Proof.
    intros Hnode.
    rewrite /xtdlchain xdlchainｰlast // .
    iIntros "((% & -> & H) & Hheaders)".
    rewrite big_sepL_snoc. iSteps.
  Qed.

  Lemma xtdlchainｰlookup {hdr src nodes} i node dst :
    nodes !! i = Some node →
    xtdlchain hdr src nodes dst ⊣⊢
      xtdlchain hdr src (take i nodes) #node ∗
      node ↦ₕ hdr ∗
      node.[xtdlchain_prev] ↦ from_option #@{location} src (last $ take i nodes) ∗
      node.[xtdlchain_next] ↦ from_option #@{location} dst (head $ drop ˖i nodes) ∗
      xtdlchain hdr #node (drop ˖i nodes) dst.
  Proof.
    intros.
    rewrite /xtdlchain xdlchainｰlookup //.
    rewrite -{5}(take_drop_middle nodes i node) // big_sepL_app.
    iSteps.
  Qed.
  Lemma xtdlchainｰlookup₁ {hdr src nodes} i node dst :
    nodes !! i = Some node →
    xtdlchain hdr src nodes dst ⊢
      xtdlchain hdr src (take i nodes) #node ∗
      node ↦ₕ hdr ∗
      node.[xtdlchain_prev] ↦ from_option #@{location} src (last $ take i nodes) ∗
      node.[xtdlchain_next] ↦ from_option #@{location} dst (head $ drop ˖i nodes) ∗
      xtdlchain hdr #node (drop ˖i nodes) dst.
  Proof.
    intros. rewrite xtdlchainｰlookup //.
  Qed.
  Lemma xtdlchainｰlookup₂ {hdr src nodes} i node prev next dst :
    nodes !! i = Some node →
    prev = from_option #@{location} src (last $ take i nodes) →
    next = from_option #@{location} dst (head $ drop ˖i nodes) →
    xtdlchain hdr src (take i nodes) #node -∗
    node ↦ₕ hdr -∗
    node.[xtdlchain_prev] ↦ prev -∗
    node.[xtdlchain_next] ↦ next -∗
    xtdlchain hdr #node (drop ˖i nodes) dst -∗
    xtdlchain hdr src nodes dst.
  Proof.
    intros. rewrite (@xtdlchainｰlookup _ _ nodes) //. iSteps.
  Qed.

  Lemma xtdlchainｰlookupｰacc {hdr src nodes} i node dst :
    nodes !! i = Some node →
    xtdlchain hdr src nodes dst ⊢
      node ↦ₕ hdr ∗
      node.[xtdlchain_prev] ↦ from_option #@{location} src (last $ take i nodes) ∗
      node.[xtdlchain_next] ↦ from_option #@{location} dst (head $ drop ˖i nodes) ∗
      ( node.[xtdlchain_prev] ↦ from_option #@{location} src (last $ take i nodes) -∗
        node.[xtdlchain_next] ↦ from_option #@{location} dst (head $ drop ˖i nodes) -∗
        xtdlchain hdr src nodes dst
      ).
  Proof.
    intros. rewrite xtdlchainｰlookup //. iSteps.
  Qed.

  Lemma xtdlchainｰlookupｰheader {hdr src nodes} i node dst :
    nodes !! i = Some node →
    xtdlchain hdr src nodes dst ⊢
    node ↦ₕ hdr.
  Proof.
    intros. rewrite xtdlchainｰlookup //. iSteps.
  Qed.

  Lemma xtdlchainｰexclusive hdr src1 src2 nodes dst1 dst2 :
    0 < length nodes →
    xtdlchain hdr src1 nodes dst1 -∗
    xtdlchain hdr src2 nodes dst2 -∗
    False.
  Proof.
    iIntros "% (H1 & _) (H2 & _)".
    iApply (xdlchainｰexclusive with "H1 H2"); first done.
  Qed.

  Lemma xtdlchainｰNoDup hdr src nodes dst :
    xtdlchain hdr src nodes dst ⊢
    ⌜NoDup nodes⌝.
  Proof.
    iIntros "(H & _)".
    iApply (xdlchainｰNoDup with "H").
  Qed.

  Lemma xtdlchain٠prevｰspec {hdr src nodes node} nodes' dst E :
    nodes = node :: nodes' →
    {{{
      xtdlchain hdr src nodes dst
    }}}
      (#node).{xtdlchain_prev} @ E
    {{{
      RET src;
      xtdlchain hdr src nodes dst
    }}}.
  Proof.
    iIntros (->) "%Φ (H & Hheaders) HΦ".
    wp۰apply (xdlchain٠prevｰspec with "H"); first done.
    iSteps.
  Qed.
  Lemma xtdlchain٠prevｰspecｰlookup {hdr src nodes} i node dst E :
    nodes !! i = Some node →
    {{{
      xtdlchain hdr src nodes dst
    }}}
      (#node).{xtdlchain_prev} @ E
    {{{
      RET from_option #@{location} src (last $ take i nodes);
      xtdlchain hdr src nodes dst
    }}}.
  Proof.
    iIntros "%Hlookup %Φ (H & Hheaders) HΦ".
    wp۰apply (xdlchain٠prevｰspecｰlookup with "H"); first done.
    iSteps.
  Qed.
  Lemma xtdlchain٠prevｰspecｰhead {hdr src nodes} node dst E :
    head nodes = Some node →
    {{{
      xtdlchain hdr src nodes dst
    }}}
      (#node).{xtdlchain_prev} @ E
    {{{
      RET src;
      xtdlchain hdr src nodes dst
    }}}.
  Proof.
    iIntros "%Hnode %Φ (H & Hheaders) HΦ".
    wp۰apply (xdlchain٠prevｰspecｰhead with "H"); first done.
    iSteps.
  Qed.

  Lemma xtdlchain٠nextｰspec {hdr src nodes node} nodes' dst E :
    nodes = node :: nodes' →
    {{{
      xtdlchain hdr src nodes dst
    }}}
      (#node).{xtdlchain_next} @ E
    {{{
      RET from_option #@{location} dst (head nodes');
      xtdlchain hdr src nodes dst
    }}}.
  Proof.
    iIntros (->) "%Φ (H & Hheaders) HΦ".
    wp۰apply (xdlchain٠nextｰspec with "H"); first done.
    iSteps.
  Qed.
  Lemma xtdlchain٠nextｰspecｰlookup {hdr src nodes} i node dst E :
    nodes !! i = Some node →
    {{{
      xtdlchain hdr src nodes dst
    }}}
      (#node).{xtdlchain_next} @ E
    {{{
      RET from_option #@{location} dst (head $ drop ˖i nodes);
      xtdlchain hdr src nodes dst
    }}}.
  Proof.
    iIntros "%Hlookup %Φ (H & Hheaders) HΦ".
    wp۰apply (xdlchain٠nextｰspecｰlookup with "H"); first done.
    iSteps.
  Qed.
  Lemma xtdlchain٠nextｰspecｰlast {hdr src nodes} node dst E :
    last nodes = Some node →
    {{{
      xtdlchain hdr src nodes dst
    }}}
      (#node).{xtdlchain_next} @ E
    {{{
      RET dst;
      xtdlchain hdr src nodes dst
    }}}.
  Proof.
    iIntros "%Hnode %Φ (H & Hheaders) HΦ".
    wp۰apply (xdlchain٠nextｰspecｰlast with "H"); first done.
    iSteps.
  Qed.

  Lemma xtdlchain٠set_prevｰspec {hdr src nodes node} nodes' dst v E :
    nodes = node :: nodes' →
    {{{
      xtdlchain hdr src nodes dst
    }}}
      #node <-{xtdlchain_prev} v @ E
    {{{
      RET ();
      xtdlchain hdr v nodes dst
    }}}.
  Proof.
    iIntros (->) "%Φ (H & Hheaders) HΦ".
    wp۰apply (xdlchain٠set_prevｰspec with "H"); first done.
    iSteps.
  Qed.
  Lemma xtdlchain٠set_prevｰspecｰlookup {hdr src nodes} i node dst v E :
    nodes !! i = Some node →
    {{{
      xtdlchain hdr src nodes dst
    }}}
      #node <-{xtdlchain_prev} v @ E
    {{{
      RET ();
      xtdlchain hdr src (take i nodes) #node ∗
      xtdlchain hdr v (drop i nodes) dst
    }}}.
  Proof.
    intros Hlookup.
    setoid_rewrite xtdlchainｰlookup at 1; last done.
    iIntros "%Φ (H1 & Hheader & Hprev & Hnext & H2) HΦ".
    wp۰store.
    rewrite (drop_S nodes node i) //.
    rewrite (xtdlchainｰcons (node :: drop _ nodes)) //.
    iSteps.
  Qed.
  Lemma xtdlchain٠set_prevｰspecｰhead {hdr src nodes} node dst v E :
    head nodes = Some node →
    {{{
      xtdlchain hdr src nodes dst
    }}}
      #node <-{xtdlchain_prev} v @ E
    {{{
      RET ();
      xtdlchain hdr v nodes dst
    }}}.
  Proof.
    iIntros "%Hlookup %Φ (H & Hheaders) HΦ".
    wp۰apply (xdlchain٠set_prevｰspecｰhead with "H"); first done.
    iSteps.
  Qed.

  Lemma xtdlchain٠set_nextｰspec {hdr src nodes node} nodes' dst v E :
    nodes = node :: nodes' →
    {{{
      xtdlchain hdr src nodes dst
    }}}
      #node <-{xtdlchain_next} v @ E
    {{{
      RET ();
      xtdlchain hdr src [node] v ∗
      xtdlchain hdr #node nodes' dst
    }}}.
  Proof.
    iIntros (->) "%Φ (H & Hheaders) HΦ".
    wp۰apply (xdlchain٠set_nextｰspec with "H"); first done.
    iSteps.
  Qed.
  Lemma xtdlchain٠set_nextｰspecｰlookup {hdr src nodes} i node dst v E :
    nodes !! i = Some node →
    {{{
      xtdlchain hdr src nodes dst
    }}}
      #node <-{xtdlchain_next} v @ E
    {{{
      RET ();
      xtdlchain hdr src (take ˖i nodes) v ∗
      xtdlchain hdr #node (drop ˖i nodes) dst
    }}}.
  Proof.
    intros Hlookup.
    setoid_rewrite xtdlchainｰlookup at 1; last done.
    iIntros "%Φ (H1 & Hheader & Hprev & Hnext & H2) HΦ".
    wp۰store.
    erewrite take_S_r; last done.
    rewrite (xtdlchainｰsnoc (take _ nodes ++ [node])) //.
    iSteps.
  Qed.
  Lemma xtdlchain٠set_nextｰspecｰlast {hdr src nodes} node dst v E :
    last nodes = Some node →
    {{{
      xtdlchain hdr src nodes dst
    }}}
      #node <-{xtdlchain_next} v @ E
    {{{
      RET ();
      xtdlchain hdr src nodes v
    }}}.
  Proof.
    iIntros "%Hlookup %Φ (H & Hheaders) HΦ".
    wp۰apply (xdlchain٠set_nextｰspecｰlast with "H"); first done.
    iSteps.
  Qed.
End zoo۰G.

Require zoo_std.xtdlchain__opaque.

#[global] Opaque xtdlchain.
