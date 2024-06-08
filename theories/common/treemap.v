From stdpp Require Import
  gmap.

From zoo Require Import
  prelude.
From zoo Require Import
  options.

Definition treemap N `{Countable N} E :=
  gmap N (N * E).

Section treemap_rooted.
  Context {N} `{Countable N} {E : Type}.

  Implicit Types node root src dst : N.
  Implicit Types edge : E.
  Implicit Types edges : list E.
  Implicit Types ϵ : N * E.
  Implicit Types tree : treemap N E.

  Inductive treemap_path tree root : N → list E → Prop :=
    | treemap_path_nil :
        treemap_path tree root root []
    | treemap_path_cons {node1} ϵ node2 edge edges :
        tree !! node1 = Some ϵ →
        ϵ.1 = node2 →
        ϵ.2 = edge →
        treemap_path tree root node2 edges →
        treemap_path tree root node1 (edge :: edges).
  #[local] Hint Constructors treemap_path : core.

  Definition treemap_rooted tree root :=
    tree !! root = None ∧
      ∀ node,
      is_Some (tree !! node) →
        ∃ edges,
        treemap_path tree root node edges.

  Lemma treemap_rooted_empty root :
    treemap_rooted ∅ root.
  Proof.
    split; first done.
    intros node []%(lookup_empty_is_Some (A := N * E)).
  Qed.

  Axiom treemap_rooted_lift : ∀ {tree root} root_edge root',
    treemap_rooted tree root →
    tree !! root' = None →
    treemap_rooted (<[root := (root', root_edge)]> tree) root'.

  Lemma treemap_rooted_path {tree root} node :
    treemap_rooted tree root →
    is_Some (tree !! node) →
      ∃ edges,
      treemap_path tree root node edges.
  Proof.
    rewrite /treemap_rooted. naive_solver.
  Qed.

  Lemma treemap_path_is_nil tree root edges :
    treemap_rooted tree root →
    treemap_path tree root root edges →
    edges = [].
  Proof.
    intros (Hlookup_root & _) Hpath.
    invert Hpath. done.
  Qed.
  Lemma treemap_path_is_cons tree root node edges :
    treemap_rooted tree root →
    treemap_path tree root node edges →
    node ≠ root →
      ∃ node' edge edges',
      edges = edge :: edges' ∧
      tree !! node = Some (node', edge) ∧
      treemap_path tree root node' edges'.
  Proof.
    intros Hrooted Hpath Hnode.
    invert Hpath as [| ? []]. naive_solver.
  Qed.
End treemap_rooted.

#[global] Opaque treemap_rooted.
