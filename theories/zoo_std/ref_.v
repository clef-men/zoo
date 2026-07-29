Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo.options.

Implicit Type l : location.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.
  Context τ `{!iType (iPropI Σ) τ}.

  Definition itype۰ref t : iProp Σ :=
    ∃ l,
    ⌜t = #l⌝ ∗
    inv nroot (
      ∃ w,
      l ↦ᵣ w ∗
      τ w
    ).
  #[global] Instance itype۰refｰitype :
    iType _ itype۰ref.
  Proof.
    split. apply _.
  Qed.

  Lemma ref٠makeｰtype v :
    {{{
      τ v
    }}}
      𝗿𝗲𝗳 v
    {{{
      t
    , RET t;
      itype۰ref t
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma ref٠getｰtype t :
    {{{
      itype۰ref t
    }}}
      !t
    {{{
      v
    , RET v;
      τ v
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma ref٠setｰtype t v :
    {{{
      itype۰ref t ∗
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
End zoo۰G.
