From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Export
  base.
From zebre Require Import
  options.

Implicit Types l : location.

Notation "'node2_data'" := (
  in_type "node2" 0
)(in custom zebre_field
).
Notation "'node2_next'" := (
  in_type "node2" 1
)(in custom zebre_field
).

Definition node2_create : val :=
  λ: "v1" "v2",
    { "v1"; "v2" }.

Section zebre_G.
  Context `{zebre_G : !ZebreG Σ}.

  Definition node2_model l v1 v2 : iProp Σ :=
    l.[node2_data] ↦ v1 ∗
    l.[node2_next] ↦ v2.

  Lemma node2_create_spec v1 v2 :
    {{{ True }}}
      node2_create v1 v2
    {{{ l,
      RET #l;
      node2_model l v1 v2
    }}}.
  Proof.
    iSteps.
  Qed.
End zebre_G.

#[global] Opaque node2_create.
