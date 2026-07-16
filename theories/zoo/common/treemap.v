Require Import stdpp.gmap.

Require Import zoo.prelude.
Require Import zoo.options.

Section treemap۰rooted.
  Context {N} `{Countable N} {E : Type}.

  Implicit Types node root src dst : N.
  Implicit Types edge : E.
  Implicit Types path : list E.
  Implicit Types ϵ : N * E.
  Implicit Types tree : gmap N (N * E).

  Inductive treemap۰path tree dst : N → list E → Prop :=
    | treemap۰path𑁒nil :
        treemap۰path tree dst dst []
    | treemap۰path𑁒cons {node1} ϵ node2 edge path :
        tree !! node1 = Some ϵ →
        ϵ.1 = node2 →
        ϵ.2 = edge →
        treemap۰path tree dst node2 path →
        treemap۰path tree dst node1 (edge :: path).
  #[local] Hint Constructors treemap۰path : core.

  Definition treemap۰rooted tree root :=
    tree !! root = None ∧
      ∀ node,
      is_Some (tree !! node) →
        ∃ path,
        treemap۰path tree root node path.

  Definition treemap۰reroot tree root root' edge :=
    <[root := (root', edge)]> (delete root' tree).

  Lemma treemap۰path𑁒app tree dst1 node path1 dst2 path2 :
    treemap۰path tree dst1 node path1 →
    treemap۰path tree dst2 dst1 path2 →
    treemap۰path tree dst2 node (path1 ++ path2).
  Proof.
    induction 1; naive_solver.
  Qed.
  Lemma treemap۰path𑁒snoc {tree dst1 node path} ϵ dst2 edge :
    treemap۰path tree dst1 node path →
    tree !! dst1 = Some ϵ →
    ϵ.1 = dst2 →
    ϵ.2 = edge →
    treemap۰path tree dst2 node (path ++ [edge]).
  Proof.
    intros Hpath Hlookup_dst1 ? ?.
    eapply treemap۰path𑁒app; [done | eauto].
  Qed.

  Lemma treemap۰path𑁒nil𑁒inv tree dst node :
    treemap۰path tree dst node [] →
    node = dst.
  Proof.
    inversion 1 => //.
  Qed.
  Lemma treemap۰path𑁒cons𑁒inv tree dst node edge path :
    treemap۰path tree dst node (edge :: path) →
      ∃ node',
      tree !! node = Some (node', edge) ∧
      treemap۰path tree dst node' path.
  Proof.
    inversion 1 as [| ? []]. naive_solver.
  Qed.
  Lemma treemap۰path𑁒app𑁒inv tree dst node path1 path2 :
    treemap۰path tree dst node (path1 ++ path2) →
      ∃ node',
      treemap۰path tree node' node path1 ∧
      treemap۰path tree dst node' path2.
  Proof.
    move: node. induction path1 => node Hpath; invert Hpath; naive_solver.
  Qed.

  Lemma treemap۰path𑁒mono {tree dst node path} tree' :
    tree ##ₘ tree' →
    treemap۰path tree dst node path →
    treemap۰path (tree ∪ tree') dst node path.
  Proof.
    intros Htree'. induction 1; first done.
    econstructor; [| done..].
    rewrite lookup_union_l //.
    apply eq_None_ne_Some_2 => ? ?.
    rewrite map_disjoint_spec in Htree'. naive_solver.
  Qed.

  Lemma treemap۰rooted𑁒empty root :
    treemap۰rooted ∅ root.
  Proof.
    split; first done.
    intros node []%(lookup_empty_is_Some (A := N * E)).
  Qed.

  Lemma treemap۰rooted𑁒root tree root :
    treemap۰rooted tree root →
    tree !! root = None.
  Proof.
    rewrite /treemap۰rooted. naive_solver.
  Qed.

  Lemma treemap۰path𑁒is_nil tree root path :
    treemap۰rooted tree root →
    treemap۰path tree root root path →
    path = [].
  Proof.
    intros (Hlookup_root & _) Hpath.
    invert Hpath. done.
  Qed.
  Lemma treemap۰path𑁒is_cons tree root node path :
    treemap۰rooted tree root →
    treemap۰path tree root node path →
    node ≠ root →
      ∃ node' edge path',
      path = edge :: path' ∧
      tree !! node = Some (node', edge) ∧
      treemap۰path tree root node' path'.
  Proof.
    intros Hrooted Hpath Hnode.
    invert Hpath as [| ? []]. naive_solver.
  Qed.

  #[local] Lemma treemap۰path𑁒acyclic {tree root path} node ϵ node' :
    treemap۰rooted tree root →
    treemap۰path tree root node path →
    tree !! node = Some ϵ →
    ϵ.1 = node' →
    node ≠ node'.
  Proof.
    rewrite /treemap۰rooted. induction 2; naive_solver.
  Qed.
  Lemma treemap۰rooted𑁒acyclic {tree root} node ϵ node' :
    treemap۰rooted tree root →
    tree !! node = Some ϵ →
    ϵ.1 = node' →
    node ≠ node'.
  Proof.
    intros (Hlookup_root & Hrooted) Hlookup.
    odestruct Hrooted as (path & Hpath); first done.
    eapply treemap۰path𑁒acyclic; done.
  Qed.

  Lemma treemap۰rooted𑁒path {tree root} node :
    treemap۰rooted tree root →
    is_Some (tree !! node) →
      ∃ path,
      treemap۰path tree root node path.
  Proof.
    rewrite /treemap۰rooted. naive_solver.
  Qed.

  Lemma treemap۰rooted𑁒lift {tree root} root' edge :
    treemap۰rooted tree root →
    tree !! root' = None →
    root ≠ root' →
    treemap۰rooted (<[root := (root', edge)]> tree) root'.
  Proof.
    set tree' := <[root := (root', edge)]> tree.
    intros (Htree_lookup_root & Hrooted) Htree_lookup_root' Hroot'. split.
    - rewrite lookup_insert_ne //.
    - intros node (ϵ & Htree'_lookup_node).
      assert (tree' !! root = Some (root', edge)) as Htree'_lookup_root.
      { rewrite lookup_insert_eq //. }
      assert (treemap۰path tree' root' root [edge]) as Hpath_root.
      { econstructor; done. }
      destruct_decide (node = root) as -> | Hnode; first eauto.
      pose proof Htree'_lookup_node as Htree_lookup_node.
      rewrite lookup_insert_ne // in Htree_lookup_node.
      odestruct Hrooted as (path & Hpath); first done.
      exists (path ++ [edge]). eapply treemap۰path𑁒app; last done.
      rewrite /tree' insert_union_singleton_r //.
      apply treemap۰path𑁒mono; last done.
      solve_map_disjoint.
  Qed.

  Lemma treemap𑁒reroot𑁒path {tree root} root' ϵ edge dst node path :
    treemap۰rooted tree root →
    tree !! root' = Some ϵ →
    ϵ.1 = root →
    dst ≠ root →
    treemap۰path tree dst node path →
    treemap۰path (treemap۰reroot tree root root' edge) dst node path.
  Proof.
    set tree' := treemap۰reroot tree root root' edge.
    destruct ϵ as (_root, edge').
    intros (Htree_lookup_root & Hrooted) Htree_lookup_root' [= ->] Hdst.
    assert (root ≠ root') as Hroot' by congruence.
    induction 1 as [| node ϵ node' edge'' path Htree_lookup_node ? ? Hpath Hpath']; first done.
    destruct_decide (node = root) as -> | Hnode; first congruence.
    destruct_decide (node = root') as -> | Hnode_; first invert Hpath.
    econstructor; try done.
    rewrite lookup_insert_ne // lookup_delete_ne //.
  Qed.
  Lemma treemap𑁒reroot𑁒path' {tree root} root' ϵ edge node path :
    treemap۰rooted tree root →
    tree !! root' = Some ϵ →
    ϵ.1 = root →
    treemap۰path tree root' node path →
    treemap۰path (treemap۰reroot tree root root' edge) root' node path.
  Proof.
    intros (Htree_lookup_root & Hrooted) Htree_lookup_root' ? Hpath.
    assert (root ≠ root') as Hroot' by congruence.
    eapply treemap𑁒reroot𑁒path; done.
  Qed.
  Lemma treemap𑁒reroot𑁒rooted {tree root} root' ϵ edge :
    treemap۰rooted tree root →
    tree !! root' = Some ϵ →
    ϵ.1 = root →
    treemap۰rooted (treemap۰reroot tree root root' edge) root'.
  Proof.
    set tree' := treemap۰reroot tree root root' edge.
    destruct ϵ as (_root, edge').
    intros (Htree_lookup_root & Hrooted) Htree_lookup_root' [= ->].
    assert (root ≠ root') as Hroot' by congruence.
    split.
    - rewrite lookup_insert_ne // lookup_delete_eq //.
    - intros node (ϵ & Htree'_lookup_node).
      assert (tree' !! root = Some (root', edge)) as Htree'_lookup_root.
      { rewrite lookup_insert_eq //. }
      assert (treemap۰path tree' root' root [edge]) as Hpath_root.
      { econstructor; done. }
      destruct_decide (node = root) as -> | Hnode; first eauto.
      rewrite lookup_insert_ne // in Htree'_lookup_node.
      apply lookup_delete_Some in Htree'_lookup_node as (Hnode_ & Htree_lookup_node).
      odestruct Hrooted as (path & Hpath); first done.
      clear- Htree_lookup_root Hpath_root Hpath.
      induction Hpath as [| node ϵ node' edge' path Htree_lookup_node ? ? Hpath (path' & Hpath')]; first eauto.
      destruct_decide (node = root') as -> | Hnode; first eauto.
      exists (edge' :: path'). econstructor; try done.
      rewrite lookup_insert_ne; first congruence.
      rewrite lookup_delete_ne //.
  Qed.
End treemap۰rooted.

#[global] Opaque treemap۰rooted.
