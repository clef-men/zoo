From stdpp Require Export
  fin_map_dom.

From zoo Require Import
  prelude.
From zoo Require Import
  options.

Section fin_map_dom.
  Context `{FinMapDom K M D}.
  Context {A : Type}.

  Implicit Types m : M A.

  Lemma elem_of_dom_1 m k :
    k ∈ dom m →
    is_Some (m !! k).
  Proof.
    rewrite elem_of_dom //.
  Qed.
End fin_map_dom.
