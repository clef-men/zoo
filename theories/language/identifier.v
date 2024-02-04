From zebre Require Import
  prelude.
From zebre.language Require Export
  rules.
From zebre.language Require Import
  notations
  diaframe.
From zebre Require Import
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

Section zebre_G.
  Context `{zebre_G : !ZebreG Σ}.

  Definition identifier_model id : iProp Σ :=
    ∃ prophs, proph id prophs.

  Lemma identifier_model_exclusive id :
    identifier_model id -∗
    identifier_model id -∗
    False.
  Proof.
    iSteps.
  Qed.

  Lemma wp_id E :
    {{{ True }}}
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
End zebre_G.

#[global] Opaque LiteralIdentifier.

#[global] Opaque identifier_model.
