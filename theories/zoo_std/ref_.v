From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base.
From zoo Require Import
  options.

Implicit Types l : location.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.
  Context τ `{!iType (iPropI Σ) τ}.

  Definition itype_ref t : iProp Σ :=
    ∃ l,
    ⌜t = #l⌝ ∗
    inv nroot (
      ∃ w,
      l ↦ᵣ w ∗
      τ w
    ).
  #[global] Instance itype_ref_itype :
    iType _ itype_ref.
  Proof.
    split. apply _.
  Qed.

  Lemma ref_make_type v :
    {{{
      τ v
    }}}
      ref v
    {{{ t,
      RET t;
      itype_ref t
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma ref_get_type t :
    {{{
      itype_ref t
    }}}
      !t
    {{{ v,
      RET v;
      τ v
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma ref_set_type t v :
    {{{
      itype_ref t ∗
      τ v
    }}}
      t <- v
    {{{
      RET ();
      True
    }}}.
  Proof.
    iSteps.
  Qed.
End zoo_G.
