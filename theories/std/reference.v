From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Export
  base.
From zebre Require Import
  options.

Section zebre_G.
  Context `{zebre_G : !ZebreG Σ}.
  Context τ `{!iType (iPropI Σ) τ}.

  Definition reference_type t : iProp Σ :=
    ∃ (l : loc),
    ⌜t = #l⌝ ∗
    inv nroot (
      ∃ w,
      l ↦ w ∗ τ w
    ).
  #[global] Instance reference_type_itype :
    iType _ reference_type.
  Proof.
    split. apply _.
  Qed.

  Lemma reference_make_type v :
    {{{
      τ v
    }}}
      ref v
    {{{ t,
      RET t; reference_type t
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma reference_get_type t :
    {{{
      reference_type t
    }}}
      !t
    {{{ v,
      RET v; τ v
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma reference_set_type t v :
    {{{
      reference_type t ∗
      τ v
    }}}
      t <- v
    {{{
      RET #(); True
    }}}.
  Proof.
    iSteps.
  Qed.
End zebre_G.
