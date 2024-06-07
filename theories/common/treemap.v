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

  Inductive treemap_path tree dst : N → list E → Prop :=
    | treemap_path_nil :
        treemap_path tree dst dst []
    | treemap_path_cons {node1} ϵ node2 edge edges :
        tree !! node1 = Some ϵ →
        ϵ.1 = node2 →
        ϵ.2 = edge →
        treemap_path tree dst node2 edges →
        treemap_path tree dst node1 (edge :: edges).
  #[local] Hint Constructors treemap_path : core.

  Definition treemap_rooted tree root :=
    ∀ node,
    is_Some (tree !! node) →
      ∃ edges,
      treemap_path tree root node edges.

  Lemma treemap_rooted_empty root :
    treemap_rooted ∅ root.
  Proof.
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
    auto.
  Qed.
End treemap_rooted.
