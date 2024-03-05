From zebre Require Import
  prelude.
From zebre.language Require Import
  notations.
From zebre.std Require Export
  base.
From zebre Require Import
  options.

Implicit Types l slot : location.
Implicit Types slots : list location.
Implicit Types t fn : val.

Parameter xdeque_create : val.

Parameter xdeque_push_back : val.

Parameter xdeque_remove : val.

Parameter xdeque_iter : val.

Parameter xdeque_model : ∀ `{zebre_G : !ZebreG Σ}, val → list location → iProp Σ.

Axiom xdeque_model_no_dup : ∀ `{zebre_G : !ZebreG Σ} t slots,
  xdeque_model t slots ⊢
  ⌜NoDup slots⌝.

Axiom xdeque_create_spec : ∀ `{zebre_G : !ZebreG Σ},
  {{{ True }}}
    xdeque_create ()
  {{{ t,
    RET t;
    (∃ l, ⌜t = #l⌝ ∗ meta_token l ⊤) ∗
    xdeque_model t []
  }}}.

Axiom xdeque_push_back_spec : ∀ `{zebre_G : !ZebreG Σ} t slots v,
  {{{
    xdeque_model t slots
  }}}
    xdeque_push_back t v
  {{{ slot,
    RET #slot;
    xdeque_model t (slots ++ [slot]) ∗
    slot ↦ v
  }}}.

Axiom xdeque_remove_spec : ∀ `{zebre_G : !ZebreG Σ} {t slots slot} i,
  slots !! i = Some slot →
  {{{
    xdeque_model t slots
  }}}
    xdeque_remove t #slot
  {{{
    RET ();
    xdeque_model t (delete i slots)
  }}}.

Axiom xdeque_iter_spec : ∀ `{zebre_G : !ZebreG Σ} Ψ t slots fn,
  {{{
    ▷ Ψ [] ∗
    xdeque_model t slots ∗
    □ (
      ∀ slots_done slot slots_todo,
      ⌜slots = slots_done ++ slot :: slots_todo⌝ -∗
      Ψ slots_done -∗
      WP fn #slot {{ res,
        ⌜res = ()%V⌝ ∗
        ▷ Ψ (slots_done ++ [#slot])
      }}
    )
  }}}
    xdeque_iter t fn
  {{{
    RET ();
    xdeque_model t slots ∗
    Ψ slots
  }}}.
