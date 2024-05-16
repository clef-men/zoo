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
  Implicit Types δ : E * N.
  Implicit Types tree : treemap N E.

  Parameter treemap_rooted : treemap N E → N → Prop.

  Axiom treemap_rooted_empty : ∀ root,
    treemap_rooted ∅ root.

  Axiom treemap_rooted_lift : ∀ {tree root} root_edge root',
    treemap_rooted tree root →
    tree !! root' = None →
    treemap_rooted (<[root := (root', root_edge)]> tree) root'.
End treemap_rooted.
