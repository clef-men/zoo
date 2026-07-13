Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo.options.

Definition identifier :=
  prophet_id.
Canonical identifier_O {SI : sidx} :=
  leibnizO identifier.

Implicit Types id : identifier.

Definition LitIdentifier id :=
  LitProph id.
Coercion LitIdentifier : identifier >-> literal.

Definition Id :=
  Proph.
Notation ValId id := (
  ValProph id
)(only parsing
).

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition identifier_model id : iProp Σ :=
    ∃ prophs,
    prophet_model id prophs.

  #[global] Instance identifier_model_timeless id :
    Timeless (identifier_model id).
  Proof.
    apply _.
  Qed.

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
    {{{
      id
    , RET #id;
      identifier_model id
    }}}.
  Proof.
    iSteps.
  Qed.
End zoo_G.

#[global] Opaque identifier_model.
