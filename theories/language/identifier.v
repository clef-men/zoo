From zebra Require Import
  prelude.
From zebra.language Require Export
  rules.
From zebra.language Require Import
  notations
  diaframe.
From zebra Require Import
  options.

Definition identifier :=
  prophecy_id.
Canonical identifier_O :=
  leibnizO identifier.

Implicit Types id : identifier.

Definition LiteralIdentifier id :=
  LiteralProphecy id.
Coercion LiteralIdentifier : identifier >-> literal.

Notation Id :=
  Proph
( only parsing
).

Section zebra_G.
  Context `{zebra_G : !ZebraG Σ}.

  Definition identifier_model id : iProp Σ :=
    ∃ prophs, proph id prophs.

  Lemma identifier_model_exclusive id :
    identifier_model id -∗
    identifier_model id -∗
    False.
  Proof.
    iSteps.
  Qed.

  Lemma wp_new_id E :
    {{{ True }}}
      Id @ E
    {{{ id,
      RET #id;
      identifier_model id
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_apply (wp_proph with "[//]").
    iSteps.
  Qed.
End zebra_G.

#[global] Opaque LiteralIdentifier.

#[global] Opaque identifier_model.
