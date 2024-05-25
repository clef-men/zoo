From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.std Require Export
  base.
From zoo Require Import
  options.

Implicit Types l slot : location.
Implicit Types slots : list location.
Implicit Types t fn : val.

Parameter xdeque_create : val.

Parameter xdeque_push_back : val.

Parameter xdeque_remove : val.

Parameter xdeque_iter : val.

Parameter xdeque_model : ∀ `{zoo_G : !ZooG Σ}, val → list location → iProp Σ.

Axiom xdeque_model_NoDup : ∀ `{zoo_G : !ZooG Σ} t slots,
  xdeque_model t slots ⊢
  ⌜NoDup slots⌝.

Axiom xdeque_create_spec : ∀ `{zoo_G : !ZooG Σ},
  {{{ True }}}
    xdeque_create ()
  {{{ t,
    RET t;
    (∃ l, ⌜t = #l⌝ ∗ meta_token l ⊤) ∗
    xdeque_model t []
  }}}.

Axiom xdeque_push_back_spec : ∀ `{zoo_G : !ZooG Σ} t slots v,
  {{{
    xdeque_model t slots
  }}}
    xdeque_push_back t v
  {{{ slot,
    RET #slot;
    xdeque_model t (slots ++ [slot]) ∗
    slot ↦ v
  }}}.

Axiom xdeque_remove_spec : ∀ `{zoo_G : !ZooG Σ} {t slots slot} i,
  slots !! i = Some slot →
  {{{
    xdeque_model t slots
  }}}
    xdeque_remove t #slot
  {{{
    RET ();
    xdeque_model t (delete i slots)
  }}}.

Axiom xdeque_iter_spec : ∀ `{zoo_G : !ZooG Σ} Ψ t slots fn,
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
