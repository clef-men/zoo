From zoo Require Import
  prelude.
From zoo.language Require Import
  notations
  diaframe.
From zoo.std Require Export
  base.
From zoo.std Require Import
  opt.
From zoo Require Import
  options.

Parameter deque_create : val.
Parameter deque_is_empty : val.
Parameter deque_push_front : val.
Parameter deque_pop_front : val.
Parameter deque_push_back : val.
Parameter deque_pop_back : val.

Parameter deque_model : ∀ `{zoo_G : !ZooG Σ}, val → list val → iProp Σ.

Axiom deque_model_timeless : ∀ `{zoo_G : !ZooG Σ} t vs,
  Timeless (deque_model t vs).
#[global] Existing Instance deque_model_timeless.

Axiom deque_create_spec : ∀ `{zoo_G : !ZooG Σ},
  {{{ True }}}
    deque_create ()
  {{{ t,
    RET t;
    deque_model t []
  }}}.

Axiom deque_is_empty_spec : ∀ `{zoo_G : !ZooG Σ} t vs,
  {{{
    deque_model t vs
  }}}
    deque_is_empty t
  {{{
    RET #(bool_decide (vs = []));
    deque_model t vs
  }}}.

Axiom deque_push_front_spec : ∀ `{zoo_G : !ZooG Σ} t vs v,
  {{{
    deque_model t vs
  }}}
    deque_push_front t v
  {{{
    RET ();
    deque_model t (v :: vs)
  }}}.

Axiom deque_pop_front_spec : ∀ `{zoo_G : !ZooG Σ} t vs,
  {{{
    deque_model t vs
  }}}
    deque_pop_front t
  {{{
    RET head vs : val;
    deque_model t (tail vs)
  }}}.

Axiom deque_push_back_spec : ∀ `{zoo_G : !ZooG Σ} t vs v,
  {{{
    deque_model t vs
  }}}
    deque_push_back t v
  {{{
    RET ();
    deque_model t (vs ++ [v])
  }}}.

Axiom deque_pop_back_spec : ∀ `{zoo_G : !ZooG Σ} t vs,
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
