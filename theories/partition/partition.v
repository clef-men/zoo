From zoo Require Import
  prelude.
From zoo.language Require Import
  notations
  diaframe.
From partition Require Import
  partition__types.
From partition Require Export
  partition__code.
From zoo Require Import
  options.

Implicit Types v t elt : val.
Implicit Types part : gset (gset val).

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition partition_elt_model t elt v : iProp Σ.
  Admitted.

  Definition partition_model t part : iProp Σ.
  Admitted.

  Lemma partition_create_spec v :
    {{{
      True
    }}}
      partition_create v
    {{{ t elt,
      RET t;
      partition_model t {[{[elt]}]} ∗
      partition_elt_model t elt v
    }}}.
  Proof.
  Admitted.

  Lemma partition_add_same_class_spec t part v :
    {{{
      partition_model t part
    }}}
      partition_add_new_class t v
    {{{ elt,
      RET elt;
      partition_model t (part ∪ {[{[v]}]}) ∗
      partition_elt_model t elt v
    }}}.
  Proof.
  Admitted.
End zoo_G.
