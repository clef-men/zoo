Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo.options.

Definition identifier :=
  prophet_id.
Canonical identifier۰O {SI : sidx} :=
  leibnizO identifier.

Implicit Type id : identifier.

Definition LitIdentifier id :=
  LitProph id.
Coercion LitIdentifier : identifier >-> literal.

Definition Id :=
  Proph.
Notation ValId id := (
  ValProph id
)(only parsing
).

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Definition identifier۰model id : iProp Σ :=
    ∃ prophs,
    prophet۰model id prophs.

  #[global] Instance identifier۰model𑁒timeless id :
    Timeless (identifier۰model id).
  Proof.
    apply _.
  Qed.

  Lemma identifier۰model𑁒exclusive id :
    identifier۰model id -∗
    identifier۰model id -∗
    False.
  Proof.
    iSteps.
  Qed.

  Lemma wp𑁒id E :
    {{{
      True
    }}}
      Id @ E
    {{{
      id
    , RET #id;
      identifier۰model id
    }}}.
  Proof.
    iSteps.
  Qed.
End zoo۰G.

#[global] Opaque identifier۰model.
