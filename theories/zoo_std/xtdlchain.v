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

  #[global] Instance xtdlchain𑁒timeless hdr src nodes dst :
    Timeless (xtdlchain hdr src nodes dst).
  Proof.
    apply _.
  Qed.

  Lemma xtdlchain𑁒nil hdr src dst :
    ⊢ xtdlchain hdr src [] dst.
  Proof.
    iSteps.
  Qed.

  Lemma xtdlchain𑁒singleton hdr src node dst :
    xtdlchain hdr src [node] dst ⊣⊢
      node ↦ₕ hdr ∗
      node.[xtdlchain_prev] ↦ src ∗
      node.[xtdlchain_next] ↦ dst.
  Proof.
    rewrite /xtdlchain xdlchain𑁒singleton. iSteps.
  Qed.
  Lemma xtdlchain𑁒singleton₁ hdr src node dst :
    xtdlchain hdr src [node] dst ⊢
      node ↦ₕ hdr ∗
      node.[xtdlchain_prev] ↦ src ∗
      node.[xtdlchain_next] ↦ dst.
  Proof.
    rewrite xtdlchain𑁒singleton //.
  Qed.
  Lemma xtdlchain𑁒singleton₂ hdr src node dst :
    node ↦ₕ hdr ∗
    node.[xtdlchain_prev] ↦ src -∗
    node.[xtdlchain_next] ↦ dst -∗
    xtdlchain hdr src [node] dst.
  Proof.
    rewrite xtdlchain𑁒singleton. iSteps.
  Qed.

  Lemma xtdlchain𑁒cons {hdr src} nodes node nodes' dst :
    nodes = node :: nodes' →
    xtdlchain hdr src nodes dst ⊣⊢
      node ↦ₕ hdr ∗
      node.[xtdlchain_prev] ↦ src ∗
      node.[xtdlchain_next] ↦ from_option #@{location} dst (head nodes') ∗
      xtdlchain hdr #node nodes' dst.
  Proof.
    intros ->.
    rewrite /xtdlchain xdlchain𑁒cons // big_sepL_cons. iSteps.
  Qed.
  Lemma xtdlchain𑁒cons₁ {hdr src} nodes node nodes' dst :
    nodes = node :: nodes' →
    xtdlchain hdr src nodes dst ⊢
      node ↦ₕ hdr ∗
      node.[xtdlchain_prev] ↦ src ∗
      node.[xtdlchain_next] ↦ from_option #@{location} dst (head nodes') ∗
      xtdlchain hdr #node nodes' dst.
  Proof.
    intros. rewrite xtdlchain𑁒cons //.
  Qed.
  Lemma xtdlchain𑁒cons₂ hdr src node nodes dst :
    node ↦ₕ hdr ∗
    node.[xtdlchain_prev] ↦ src -∗
    node.[xtdlchain_next] ↦ from_option #@{location} dst (head nodes) -∗
    xtdlchain hdr #node nodes dst -∗
    xtdlchain hdr src (node :: nodes) dst.
  Proof.
    rewrite (xtdlchain𑁒cons (node :: nodes)) //. iSteps.
  Qed.

  Lemma xtdlchain𑁒app {hdr src} nodes nodes1 nodes2 dst :
    nodes = nodes1 ++ nodes2 →
    xtdlchain hdr src nodes dst ⊣⊢
      xtdlchain hdr src nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xtdlchain hdr (from_option #@{location} src (last nodes1)) nodes2 dst.
  Proof.
    intros ->.
    rewrite /xtdlchain xdlchain𑁒app // big_sepL_app. iSteps.
  Qed.
  Lemma xtdlchain𑁒app₁ {hdr src} nodes nodes1 nodes2 dst :
    nodes = nodes1 ++ nodes2 →
    xtdlchain hdr src nodes dst ⊢
      xtdlchain hdr src nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xtdlchain hdr (from_option #@{location} src (last nodes1)) nodes2 dst.
  Proof.
    intros. rewrite xtdlchain𑁒app //.
  Qed.
  Lemma xtdlchain𑁒app₂ hdr src nodes1 nodes2 dst :
    xtdlchain hdr src nodes1 (from_option #@{location} dst (head nodes2)) -∗
    xtdlchain hdr (from_option #@{location} src (last nodes1)) nodes2 dst -∗
    xtdlchain hdr src (nodes1 ++ nodes2) dst.
  Proof.
    rewrite (xtdlchain𑁒app (nodes1 ++ nodes2)) //. iSteps.
  Qed.

  Lemma xtdlchain𑁒snoc {hdr src} nodes nodes' node dst :
    nodes = nodes' ++ [node] →
    xtdlchain hdr src nodes dst ⊣⊢
      xtdlchain hdr src nodes' #node ∗
      node ↦ₕ hdr ∗
      node.[xtdlchain_prev] ↦ from_option #@{location} src (last nodes') ∗
      node.[xtdlchain_next] ↦ dst.
  Proof.
    intros ->.
    rewrite /xtdlchain xdlchain𑁒snoc // big_sepL_snoc. iSteps.
  Qed.
  Lemma xtdlchain𑁒snoc₁ {hdr src} nodes nodes' node dst :
    nodes = nodes' ++ [node] →
    xtdlchain hdr src nodes dst ⊢
      xtdlchain hdr src nodes' #node ∗
      node ↦ₕ hdr ∗
      node.[xtdlchain_prev] ↦ from_option #@{location} src (last nodes') ∗
      node.[xtdlchain_next] ↦ dst.
  Proof.
    intros. rewrite xtdlchain𑁒snoc //.
  Qed.
  Lemma xtdlchain𑁒snoc₂ hdr src nodes node dst :
    xtdlchain hdr src nodes #node -∗
    node ↦ₕ hdr -∗
    node.[xtdlchain_prev] ↦ from_option #@{location} src (last nodes) -∗
    node.[xtdlchain_next] ↦ dst -∗
    xtdlchain hdr src (nodes ++ [node]) dst.
  Proof.
    rewrite (xtdlchain𑁒snoc (nodes ++ [node])) //. iSteps.
  Qed.

  Lemma xtdlchain𑁒last {hdr src nodes} node dst :
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
    rewrite /xtdlchain xdlchain𑁒last // .
    iIntros "((% & -> & H) & Hheaders)".
    rewrite big_sepL_snoc. iSteps.
  Qed.

  Lemma xtdlchain𑁒lookup {hdr src nodes} i node dst :
    nodes !! i = Some node →
    xtdlchain hdr src nodes dst ⊣⊢
      xtdlchain hdr src (take i nodes) #node ∗
      node ↦ₕ hdr ∗
      node.[xtdlchain_prev] ↦ from_option #@{location} src (last $ take i nodes) ∗
      node.[xtdlchain_next] ↦ from_option #@{location} dst (head $ drop ˖i nodes) ∗
      xtdlchain hdr #node (drop ˖i nodes) dst.
  Proof.
    intros.
    rewrite /xtdlchain xdlchain𑁒lookup //.
    rewrite -{5}(take_drop_middle nodes i node) // big_sepL_app.
    iSteps.
  Qed.
  Lemma xtdlchain𑁒lookup₁ {hdr src nodes} i node dst :
    nodes !! i = Some node →
    xtdlchain hdr src nodes dst ⊢
      xtdlchain hdr src (take i nodes) #node ∗
      node ↦ₕ hdr ∗
      node.[xtdlchain_prev] ↦ from_option #@{location} src (last $ take i nodes) ∗
      node.[xtdlchain_next] ↦ from_option #@{location} dst (head $ drop ˖i nodes) ∗
      xtdlchain hdr #node (drop ˖i nodes) dst.
  Proof.
    intros. rewrite xtdlchain𑁒lookup //.
  Qed.
  Lemma xtdlchain𑁒lookup₂ {hdr src nodes} i node prev next dst :
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
    intros. rewrite (@xtdlchain𑁒lookup _ _ nodes) //. iSteps.
  Qed.

  Lemma xtdlchain𑁒lookup𑁒acc {hdr src nodes} i node dst :
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
    intros. rewrite xtdlchain𑁒lookup //. iSteps.
  Qed.

  Lemma xtdlchain𑁒lookup𑁒header {hdr src nodes} i node dst :
    nodes !! i = Some node →
    xtdlchain hdr src nodes dst ⊢
    node ↦ₕ hdr.
  Proof.
    intros. rewrite xtdlchain𑁒lookup //. iSteps.
  Qed.

  Lemma xtdlchain𑁒exclusive hdr src1 src2 nodes dst1 dst2 :
    0 < length nodes →
    xtdlchain hdr src1 nodes dst1 -∗
    xtdlchain hdr src2 nodes dst2 -∗
    False.
  Proof.
    iIntros "% (H1 & _) (H2 & _)".
    iApply (xdlchain𑁒exclusive with "H1 H2"); first done.
  Qed.

  Lemma xtdlchain𑁒NoDup hdr src nodes dst :
    xtdlchain hdr src nodes dst ⊢
    ⌜NoDup nodes⌝.
  Proof.
    iIntros "(H & _)".
    iApply (xdlchain𑁒NoDup with "H").
  Qed.

  Lemma xtdlchain٠prev𑁒spec {hdr src nodes node} nodes' dst E :
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
    wp۰apply (xdlchain٠prev𑁒spec with "H"); first done.
    iSteps.
  Qed.
  Lemma xtdlchain٠prev𑁒spec𑁒lookup {hdr src nodes} i node dst E :
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
    wp۰apply (xdlchain٠prev𑁒spec𑁒lookup with "H"); first done.
    iSteps.
  Qed.
  Lemma xtdlchain٠prev𑁒spec𑁒head {hdr src nodes} node dst E :
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
    wp۰apply (xdlchain٠prev𑁒spec𑁒head with "H"); first done.
    iSteps.
  Qed.

  Lemma xtdlchain٠next𑁒spec {hdr src nodes node} nodes' dst E :
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
    wp۰apply (xdlchain٠next𑁒spec with "H"); first done.
    iSteps.
  Qed.
  Lemma xtdlchain٠next𑁒spec𑁒lookup {hdr src nodes} i node dst E :
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
    wp۰apply (xdlchain٠next𑁒spec𑁒lookup with "H"); first done.
    iSteps.
  Qed.
  Lemma xtdlchain٠next𑁒spec𑁒last {hdr src nodes} node dst E :
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
    wp۰apply (xdlchain٠next𑁒spec𑁒last with "H"); first done.
    iSteps.
  Qed.

  Lemma xtdlchain٠set_prev𑁒spec {hdr src nodes node} nodes' dst v E :
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
    wp۰apply (xdlchain٠set_prev𑁒spec with "H"); first done.
    iSteps.
  Qed.
  Lemma xtdlchain٠set_prev𑁒spec𑁒lookup {hdr src nodes} i node dst v E :
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
    setoid_rewrite xtdlchain𑁒lookup at 1; last done.
    iIntros "%Φ (H1 & Hheader & Hprev & Hnext & H2) HΦ".
    wp۰store.
    rewrite (drop_S nodes node i) //.
    rewrite (xtdlchain𑁒cons (node :: drop _ nodes)) //.
    iSteps.
  Qed.
  Lemma xtdlchain٠set_prev𑁒spec𑁒head {hdr src nodes} node dst v E :
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
    wp۰apply (xdlchain٠set_prev𑁒spec𑁒head with "H"); first done.
    iSteps.
  Qed.

  Lemma xtdlchain٠set_next𑁒spec {hdr src nodes node} nodes' dst v E :
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
    wp۰apply (xdlchain٠set_next𑁒spec with "H"); first done.
    iSteps.
  Qed.
  Lemma xtdlchain٠set_next𑁒spec𑁒lookup {hdr src nodes} i node dst v E :
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
    setoid_rewrite xtdlchain𑁒lookup at 1; last done.
    iIntros "%Φ (H1 & Hheader & Hprev & Hnext & H2) HΦ".
    wp۰store.
    erewrite take_S_r; last done.
    rewrite (xtdlchain𑁒snoc (take _ nodes ++ [node])) //.
    iSteps.
  Qed.
  Lemma xtdlchain٠set_next𑁒spec𑁒last {hdr src nodes} node dst v E :
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
    wp۰apply (xdlchain٠set_next𑁒spec𑁒last with "H"); first done.
    iSteps.
  Qed.
End zoo۰G.

Require zoo_std.xtdlchain__opaque.

#[global] Opaque xtdlchain.
