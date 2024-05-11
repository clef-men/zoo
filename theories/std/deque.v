From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Export
  base.
From zebre.std Require Import
  opt.
From zebre Require Import
  options.

Parameter deque_create : val.
Parameter deque_is_empty : val.
Parameter deque_push_front : val.
Parameter deque_pop_front : val.
Parameter deque_push_back : val.
Parameter deque_pop_back : val.

Parameter deque_model : ∀ `{zebre_G : !ZebreG Σ}, val → list val → iProp Σ.

Axiom deque_model_timeless : ∀ `{zebre_G : !ZebreG Σ} t vs,
  Timeless (deque_model t vs).
#[global] Existing Instance deque_model_timeless.

Axiom deque_create_spec : ∀ `{zebre_G : !ZebreG Σ},
  {{{ True }}}
    deque_create ()
  {{{ t,
    RET t;
    deque_model t []
  }}}.

Axiom deque_is_empty_spec : ∀ `{zebre_G : !ZebreG Σ} t vs,
  {{{
    deque_model t vs
  }}}
    deque_is_empty t
  {{{
    RET #(bool_decide (vs = []));
    deque_model t vs
  }}}.

Axiom deque_push_front_spec : ∀ `{zebre_G : !ZebreG Σ} t vs v,
  {{{
    deque_model t vs
  }}}
    deque_push_front t v
  {{{
    RET ();
    deque_model t (v :: vs)
  }}}.

Axiom deque_pop_front_spec : ∀ `{zebre_G : !ZebreG Σ} t vs,
  {{{
    deque_model t vs
  }}}
    deque_pop_front t
  {{{
    RET head vs : val;
    deque_model t (tail vs)
  }}}.

Axiom deque_push_back_spec : ∀ `{zebre_G : !ZebreG Σ} t vs v,
  {{{
    deque_model t vs
  }}}
    deque_push_back t v
  {{{
    RET ();
    deque_model t (vs ++ [v])
  }}}.

Axiom deque_pop_back_spec : ∀ `{zebre_G : !ZebreG Σ} t vs,
  {{{
    deque_model t vs
  }}}
    deque_pop_back t
  {{{ o,
    RET o : val;
    match o with
    | None =>
        ⌜vs = []⌝ ∗
        deque_model t []
    | Some v =>
        ∃ vs',
        ⌜vs = vs' ++ [v]⌝ ∗
        deque_model t vs'
    end
  }}}.
