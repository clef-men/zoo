From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  xtdlchain__types.
From zoo_std Require Import
  xdlchain.
From zoo Require Import
  options.

Implicit Types node : location.
Implicit Types nodes : list location.
Implicit Types v next prev src dst : val.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition xtdlchain hdr src nodes dst : iProp Σ :=
    xdlchain src nodes dst ∗
    [∗ list] node ∈ nodes, has_header node hdr.

  #[global] Instance xtdlchain_timeless hdr src nodes dst :
    Timeless (xtdlchain hdr src nodes dst).
  Proof.
    apply _.
  Qed.

  Lemma xtdlchain_nil hdr src dst :
    ⊢ xtdlchain hdr src [] dst.
  Proof.
    iSteps.
  Qed.

  Lemma xtdlchain_singleton hdr src node dst :
    xtdlchain hdr src [node] dst ⊣⊢
      node ↦ₕ hdr ∗
      node.[xtdlchain_prev] ↦ src ∗
      node.[xtdlchain_next] ↦ dst.
  Proof.
    rewrite /xtdlchain xdlchain_singleton. iSteps.
  Qed.
  Lemma xtdlchain_singleton_1 hdr src node dst :
    xtdlchain hdr src [node] dst ⊢
      node ↦ₕ hdr ∗
      node.[xtdlchain_prev] ↦ src ∗
      node.[xtdlchain_next] ↦ dst.
  Proof.
    rewrite xtdlchain_singleton //.
  Qed.
  Lemma xtdlchain_singleton_2 hdr src node dst :
    node ↦ₕ hdr ∗
    node.[xtdlchain_prev] ↦ src -∗
    node.[xtdlchain_next] ↦ dst -∗
    xtdlchain hdr src [node] dst.
  Proof.
    rewrite xtdlchain_singleton. iSteps.
  Qed.

  Lemma xtdlchain_cons {hdr src} nodes node nodes' dst :
    nodes = node :: nodes' →
    xtdlchain hdr src nodes dst ⊣⊢
      node ↦ₕ hdr ∗
      node.[xtdlchain_prev] ↦ src ∗
      node.[xtdlchain_next] ↦ from_option #@{location} dst (head nodes') ∗
      xtdlchain hdr #node nodes' dst.
  Proof.
    intros ->.
    rewrite /xtdlchain xdlchain_cons // big_sepL_cons. iSteps.
  Qed.
  Lemma xtdlchain_cons_1 {hdr src} nodes node nodes' dst :
    nodes = node :: nodes' →
    xtdlchain hdr src nodes dst ⊢
      node ↦ₕ hdr ∗
      node.[xtdlchain_prev] ↦ src ∗
      node.[xtdlchain_next] ↦ from_option #@{location} dst (head nodes') ∗
      xtdlchain hdr #node nodes' dst.
  Proof.
    intros. rewrite xtdlchain_cons //.
  Qed.
  Lemma xtdlchain_cons_2 hdr src node nodes dst :
    node ↦ₕ hdr ∗
    node.[xtdlchain_prev] ↦ src -∗
    node.[xtdlchain_next] ↦ from_option #@{location} dst (head nodes) -∗
    xtdlchain hdr #node nodes dst -∗
    xtdlchain hdr src (node :: nodes) dst.
  Proof.
    rewrite (xtdlchain_cons (node :: nodes)) //. iSteps.
  Qed.

  Lemma xtdlchain_app {hdr src} nodes nodes1 nodes2 dst :
    nodes = nodes1 ++ nodes2 →
    xtdlchain hdr src nodes dst ⊣⊢
      xtdlchain hdr src nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xtdlchain hdr (from_option #@{location} src (last nodes1)) nodes2 dst.
  Proof.
    intros ->.
    rewrite /xtdlchain xdlchain_app // big_sepL_app. iSteps.
  Qed.
  Lemma xtdlchain_app_1 {hdr src} nodes nodes1 nodes2 dst :
    nodes = nodes1 ++ nodes2 →
    xtdlchain hdr src nodes dst ⊢
      xtdlchain hdr src nodes1 (from_option #@{location} dst (head nodes2)) ∗
      xtdlchain hdr (from_option #@{location} src (last nodes1)) nodes2 dst.
  Proof.
    intros. rewrite xtdlchain_app //.
  Qed.
  Lemma xtdlchain_app_2 hdr src nodes1 nodes2 dst :
    xtdlchain hdr src nodes1 (from_option #@{location} dst (head nodes2)) -∗
    xtdlchain hdr (from_option #@{location} src (last nodes1)) nodes2 dst -∗
    xtdlchain hdr src (nodes1 ++ nodes2) dst.
  Proof.
    rewrite (xtdlchain_app (nodes1 ++ nodes2)) //. iSteps.
  Qed.

  Lemma xtdlchain_snoc {hdr src} nodes nodes' node dst :
    nodes = nodes' ++ [node] →
    xtdlchain hdr src nodes dst ⊣⊢
      xtdlchain hdr src nodes' #node ∗
      node ↦ₕ hdr ∗
      node.[xtdlchain_prev] ↦ from_option #@{location} src (last nodes') ∗
      node.[xtdlchain_next] ↦ dst.
  Proof.
    intros ->.
    rewrite /xtdlchain xdlchain_snoc // big_sepL_snoc. iSteps.
  Qed.
  Lemma xtdlchain_snoc_1 {hdr src} nodes nodes' node dst :
    nodes = nodes' ++ [node] →
    xtdlchain hdr src nodes dst ⊢
      xtdlchain hdr src nodes' #node ∗
      node ↦ₕ hdr ∗
      node.[xtdlchain_prev] ↦ from_option #@{location} src (last nodes') ∗
      node.[xtdlchain_next] ↦ dst.
  Proof.
    intros. rewrite xtdlchain_snoc //.
  Qed.
  Lemma xtdlchain_snoc_2 hdr src nodes node dst :
    xtdlchain hdr src nodes #node -∗
    node ↦ₕ hdr -∗
    node.[xtdlchain_prev] ↦ from_option #@{location} src (last nodes) -∗
    node.[xtdlchain_next] ↦ dst -∗
    xtdlchain hdr src (nodes ++ [node]) dst.
  Proof.
    rewrite (xtdlchain_snoc (nodes ++ [node])) //. iSteps.
  Qed.

  Lemma xtdlchain_last {hdr src nodes} node dst :
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
    rewrite /xtdlchain xdlchain_last // .
    iIntros "((% & -> & H) & Hheaders)".
    rewrite big_sepL_snoc. iSteps.
  Qed.

  Lemma xtdlchain_lookup {hdr src nodes} i node dst :
    nodes !! i = Some node →
    xtdlchain hdr src nodes dst ⊣⊢
      xtdlchain hdr src (take i nodes) #node ∗
      node ↦ₕ hdr ∗
      node.[xtdlchain_prev] ↦ from_option #@{location} src (last $ take i nodes) ∗
      node.[xtdlchain_next] ↦ from_option #@{location} dst (head $ drop (S i) nodes) ∗
      xtdlchain hdr #node (drop (S i) nodes) dst.
  Proof.
    intros.
    rewrite /xtdlchain xdlchain_lookup //.
    rewrite -{5}(take_drop_middle nodes i node) // big_sepL_app.
    iSteps.
  Qed.
  Lemma xtdlchain_lookup_1 {hdr src nodes} i node dst :
    nodes !! i = Some node →
    xtdlchain hdr src nodes dst ⊢
      xtdlchain hdr src (take i nodes) #node ∗
      node ↦ₕ hdr ∗
      node.[xtdlchain_prev] ↦ from_option #@{location} src (last $ take i nodes) ∗
      node.[xtdlchain_next] ↦ from_option #@{location} dst (head $ drop (S i) nodes) ∗
      xtdlchain hdr #node (drop (S i) nodes) dst.
  Proof.
    intros. rewrite xtdlchain_lookup //.
  Qed.
  Lemma xtdlchain_lookup_2 {hdr src nodes} i node prev next dst :
    nodes !! i = Some node →
    prev = from_option #@{location} src (last $ take i nodes) →
    next = from_option #@{location} dst (head $ drop (S i) nodes) →
    xtdlchain hdr src (take i nodes) #node -∗
    node ↦ₕ hdr -∗
    node.[xtdlchain_prev] ↦ prev -∗
    node.[xtdlchain_next] ↦ next -∗
    xtdlchain hdr #node (drop (S i) nodes) dst -∗
    xtdlchain hdr src nodes dst.
  Proof.
    intros. rewrite (@xtdlchain_lookup _ _ nodes) //. iSteps.
  Qed.

  Lemma xtdlchain_lookup_acc {hdr src nodes} i node dst :
    nodes !! i = Some node →
    xtdlchain hdr src nodes dst ⊢
      node ↦ₕ hdr ∗
      node.[xtdlchain_prev] ↦ from_option #@{location} src (last $ take i nodes) ∗
      node.[xtdlchain_next] ↦ from_option #@{location} dst (head $ drop (S i) nodes) ∗
      ( node.[xtdlchain_prev] ↦ from_option #@{location} src (last $ take i nodes) -∗
        node.[xtdlchain_next] ↦ from_option #@{location} dst (head $ drop (S i) nodes) -∗
        xtdlchain hdr src nodes dst
      ).
  Proof.
    intros. rewrite xtdlchain_lookup //. iSteps.
  Qed.

  Lemma xtdlchain_lookup_header {hdr src nodes} i node dst :
    nodes !! i = Some node →
    xtdlchain hdr src nodes dst ⊢
    node ↦ₕ hdr.
  Proof.
    intros. rewrite xtdlchain_lookup //. iSteps.
  Qed.

  Lemma xtdlchain_exclusive hdr src1 src2 nodes dst1 dst2 :
    0 < length nodes →
    xtdlchain hdr src1 nodes dst1 -∗
    xtdlchain hdr src2 nodes dst2 -∗
    False.
  Proof.
    iIntros "% (H1 & _) (H2 & _)".
    iApply (xdlchain_exclusive with "H1 H2"); first done.
  Qed.

  Lemma xtdlchain_NoDup hdr src nodes dst :
    xtdlchain hdr src nodes dst ⊢
    ⌜NoDup nodes⌝.
  Proof.
    iIntros "(H & _)".
    iApply (xdlchain_NoDup with "H").
  Qed.

  Lemma xtdlchain_prev_spec {hdr src nodes node} nodes' dst E :
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
    wp_apply (xdlchain_prev_spec with "H"); first done.
    iSteps.
  Qed.
  Lemma xtdlchain_prev_spec_lookup {hdr src nodes} i node dst E :
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
    wp_apply (xdlchain_prev_spec_lookup with "H"); first done.
    iSteps.
  Qed.
  Lemma xtdlchain_prev_spec_head {hdr src nodes} node dst E :
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
    wp_apply (xdlchain_prev_spec_head with "H"); first done.
    iSteps.
  Qed.

  Lemma xtdlchain_next_spec {hdr src nodes node} nodes' dst E :
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
    wp_apply (xdlchain_next_spec with "H"); first done.
    iSteps.
  Qed.
  Lemma xtdlchain_next_spec_lookup {hdr src nodes} i node dst E :
    nodes !! i = Some node →
    {{{
      xtdlchain hdr src nodes dst
    }}}
      (#node).{xtdlchain_next} @ E
    {{{
      RET from_option #@{location} dst (head $ drop (S i) nodes);
      xtdlchain hdr src nodes dst
    }}}.
  Proof.
    iIntros "%Hlookup %Φ (H & Hheaders) HΦ".
    wp_apply (xdlchain_next_spec_lookup with "H"); first done.
    iSteps.
  Qed.
  Lemma xtdlchain_next_spec_last {hdr src nodes} node dst E :
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
    wp_apply (xdlchain_next_spec_last with "H"); first done.
    iSteps.
  Qed.

  Lemma xtdlchain_set_prev_spec {hdr src nodes node} nodes' dst v E :
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
    wp_apply (xdlchain_set_prev_spec with "H"); first done.
    iSteps.
  Qed.
  Lemma xtdlchain_set_prev_spec_lookup {hdr src nodes} i node dst v E :
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
    setoid_rewrite xtdlchain_lookup at 1; last done.
    iIntros "%Φ (H1 & Hheader & Hprev & Hnext & H2) HΦ".
    wp_store.
    rewrite (drop_S nodes node i) //.
    rewrite (xtdlchain_cons (node :: drop _ nodes)) //.
    iSteps.
  Qed.
  Lemma xtdlchain_set_prev_spec_head {hdr src nodes} node dst v E :
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
    wp_apply (xdlchain_set_prev_spec_head with "H"); first done.
    iSteps.
  Qed.

  Lemma xtdlchain_set_next_spec {hdr src nodes node} nodes' dst v E :
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
    wp_apply (xdlchain_set_next_spec with "H"); first done.
    iSteps.
  Qed.
  Lemma xtdlchain_set_next_spec_lookup {hdr src nodes} i node dst v E :
    nodes !! i = Some node →
    {{{
      xtdlchain hdr src nodes dst
    }}}
      #node <-{xtdlchain_next} v @ E
    {{{
      RET ();
      xtdlchain hdr src (take (S i) nodes) v ∗
      xtdlchain hdr #node (drop (S i) nodes) dst
    }}}.
  Proof.
    intros Hlookup.
    setoid_rewrite xtdlchain_lookup at 1; last done.
    iIntros "%Φ (H1 & Hheader & Hprev & Hnext & H2) HΦ".
    wp_store.
    erewrite take_S_r; last done.
    rewrite (xtdlchain_snoc (take _ nodes ++ [node])) //.
    iSteps.
  Qed.
  Lemma xtdlchain_set_next_spec_last {hdr src nodes} node dst v E :
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
    wp_apply (xdlchain_set_next_spec_last with "H"); first done.
    iSteps.
  Qed.
End zoo_G.

#[global] Opaque xtdlchain.
