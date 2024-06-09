From stdpp Require Import
  gmap.

From zoo Require Import
  prelude.
From zoo Require Import
  options.

Section treemap_rooted.
  Context {N} `{Countable N} {E : Type}.

  Implicit Types node root src dst : N.
  Implicit Types edge : E.
  Implicit Types path : list E.
  Implicit Types ϵ : N * E.
  Implicit Types tree : gmap N (N * E).

  Inductive treemap_path tree dst : N → list E → Prop :=
    | treemap_path_nil :
        treemap_path tree dst dst []
    | treemap_path_cons {node1} ϵ node2 edge path :
        tree !! node1 = Some ϵ →
        ϵ.1 = node2 →
        ϵ.2 = edge →
        treemap_path tree dst node2 path →
        treemap_path tree dst node1 (edge :: path).
  #[local] Hint Constructors treemap_path : core.

  Definition treemap_rooted tree root :=
    tree !! root = None ∧
      ∀ node,
      is_Some (tree !! node) →
        ∃ path,
        treemap_path tree root node path.

  Definition treemap_reroot tree root root' edge:=
    <[root := (root', edge)]> (delete root' tree).

  Lemma treemap_path_app tree dst1 node path1 dst2 path2 :
    treemap_path tree dst1 node path1 →
    treemap_path tree dst2 dst1 path2 →
    treemap_path tree dst2 node (path1 ++ path2).
  Proof.
    induction 1; naive_solver.
  Qed.

  Lemma treemap_path_mono {tree dst node path} tree' :
    tree ##ₘ tree' →
    treemap_path tree dst node path →
    treemap_path (tree ∪ tree') dst node path.
  Proof.
    intros Htree'. induction 1; first done.
    econstructor; [| done..].
    rewrite lookup_union_l //.
    apply eq_None_ne_Some_2 => ? ?.
    rewrite map_disjoint_spec in Htree'. naive_solver.
  Qed.

  Lemma treemap_rooted_empty root :
    treemap_rooted ∅ root.
  Proof.
    split; first done.
    intros node []%(lookup_empty_is_Some (A := N * E)).
  Qed.

  Lemma treemap_path_is_nil tree root path :
    treemap_rooted tree root →
    treemap_path tree root root path →
    path = [].
  Proof.
    intros (Hlookup_root & _) Hpath.
    invert Hpath. done.
  Qed.
  Lemma treemap_path_is_cons tree root node path :
    treemap_rooted tree root →
    treemap_path tree root node path →
    node ≠ root →
      ∃ node' edge path',
      path = edge :: path' ∧
      tree !! node = Some (node', edge) ∧
      treemap_path tree root node' path'.
  Proof.
    intros Hrooted Hpath Hnode.
    invert Hpath as [| ? []]. naive_solver.
  Qed.

  #[local] Lemma treemap_path_acyclic {tree root path} node ϵ :
    treemap_rooted tree root →
    treemap_path tree root node path →
    tree !! node = Some ϵ →
    ϵ.1 ≠ node.
  Proof.
    rewrite /treemap_rooted. induction 2; naive_solver.
  Qed.
  Lemma treemap_rooted_acyclic {tree root} node ϵ :
    treemap_rooted tree root →
    tree !! node = Some ϵ →
    ϵ.1 ≠ node.
  Proof.
    intros (Hlookup_root & Hrooted) Hlookup.
    odestruct Hrooted as (path & Hpath); first done.
    eapply treemap_path_acyclic; done.
  Qed.

  Lemma treemap_rooted_path {tree root} node :
    treemap_rooted tree root →
    is_Some (tree !! node) →
      ∃ path,
      treemap_path tree root node path.
  Proof.
    rewrite /treemap_rooted. naive_solver.
  Qed.

  Lemma treemap_rooted_lift {tree root} root' edge :
    treemap_rooted tree root →
    tree !! root' = None →
    root ≠ root' →
    treemap_rooted (<[root := (root', edge)]> tree) root'.
  Proof.
    set tree' := <[root := (root', edge)]> tree.
    intros (Htree_lookup_root & Hrooted) Htree_lookup_root' Hroot'. split.
    - rewrite lookup_insert_ne //.
    - intros node (ϵ & Htree'_lookup_node).
      assert (tree' !! root = Some (root', edge)) as Htree'_lookup_root.
      { rewrite lookup_insert //. }
      assert (treemap_path tree' root' root [edge]) as Hpath_root.
      { econstructor; done. }
      destruct (decide (node = root)) as [-> | Hnode]; first eauto.
      pose proof Htree'_lookup_node as Htree_lookup_node.
      rewrite lookup_insert_ne // in Htree_lookup_node.
      odestruct Hrooted as (path & Hpath); first done.
      exists (path ++ [edge]). eapply treemap_path_app; last done.
      rewrite /tree' insert_union_singleton_r //.
      apply treemap_path_mono; last done.
      solve_map_disjoint.
  Qed.

  Lemma treemap_reroot_path {tree root} root' ϵ edge node path :
    treemap_rooted tree root →
    tree !! root' = Some ϵ →
    ϵ.1 = root →
    treemap_path tree root' node path →
    treemap_path (treemap_reroot tree root root' edge) root' node path.
  Proof.
    set tree' := treemap_reroot tree root root' edge.
    destruct ϵ as (_root, edge').
    intros (Htree_lookup_root & Hrooted) Htree_lookup_root' [= ->].
    assert (root ≠ root') as Hroot' by congruence.
    induction 1 as [| node ϵ node' edge'' path Htree_lookup_node ? ? Hpath Hpath']; first done.
    destruct (decide (node = root)) as [-> | Hnode]; first congruence.
    destruct (decide (node = root')) as [-> | Hnode_]; first invert Hpath.
    econstructor; try done.
    rewrite lookup_insert_ne // lookup_delete_ne //.
  Qed.
  Lemma treemap_reroot_rooted {tree root} root' ϵ edge :
    treemap_rooted tree root →
    tree !! root' = Some ϵ →
    ϵ.1 = root →
    treemap_rooted (treemap_reroot tree root root' edge) root'.
  Proof.
    set tree' := treemap_reroot tree root root' edge.
    destruct ϵ as (_root, edge').
    intros (Htree_lookup_root & Hrooted) Htree_lookup_root' [= ->].
    assert (root ≠ root') as Hroot' by congruence.
    split.
    - rewrite lookup_insert_ne // lookup_delete //.
    - intros node (ϵ & Htree'_lookup_node).
      assert (tree' !! root = Some (root', edge)) as Htree'_lookup_root.
      { rewrite lookup_insert //. }
      assert (treemap_path tree' root' root [edge]) as Hpath_root.
      { econstructor; done. }
      destruct (decide (node = root)) as [-> | Hnode]; first eauto.
      rewrite lookup_insert_ne // in Htree'_lookup_node.
      apply lookup_delete_Some in Htree'_lookup_node as (Hnode_ & Htree_lookup_node).
      odestruct Hrooted as (path & Hpath); first done.
      clear- Htree_lookup_root Hpath_root Hpath.
      induction Hpath as [| node ϵ node' edge' path Htree_lookup_node ? ? Hpath (path' & Hpath')]; first eauto.
      destruct (decide (node = root')) as [-> | Hnode]; first eauto.
      exists (edge' :: path'). econstructor; try done.
      rewrite lookup_insert_ne; first congruence.
      rewrite lookup_delete_ne //.
  Qed.
End treemap_rooted.

#[global] Opaque treemap_rooted.
