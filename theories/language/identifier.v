From zoo Require Import
  prelude.
From zoo.language Require Export
  wp.
From zoo.language Require Import
  notations
  diaframe.
From zoo Require Import
  options.

Definition identifier :=
  prophet_id.
Canonical identifier_O :=
  leibnizO identifier.

Implicit Types id : identifier.

Definition LitIdentifier id :=
  LitProph id.
Coercion LitIdentifier : identifier >-> literal.

Notation Id :=
  Proph
( only parsing
).
Notation ValId id := (
  ValProph id
)(only parsing
).

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition identifier_model id : iProp Σ :=
    ∃ prophs,
    prophet_model id prophs.

  Lemma identifier_model_exclusive id :
    identifier_model id -∗
    identifier_model id -∗
    False.
  Proof.
    iSteps.
  Qed.

  Lemma wp_id E :
    {{{
      True
    }}}
      Id @ E
    {{{ id,
      RET #id;
      identifier_model id
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_apply (wp_proph with "[//]").
    rewrite /identifier_model. iSteps.
  Qed.
End zoo_G.

#[global] Opaque identifier_model.
