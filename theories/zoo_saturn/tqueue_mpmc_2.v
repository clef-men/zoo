Require Import zoo.prelude.
Require Import zoo.base.
Require Export zoo_saturn.tqueue_mpmc_2__code.
Require Import zoo_saturn.tqueue_mpmc_2__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type v : val.
Implicit Type vs : list val.

Zoo name :=
  { self : location
  }.

Zoo global :=
  {
  }.

Section tqueue_mpmc_2۰G.
  Context `{tqueue_mpmc_2۰G : TqueueMpmc2G Σ}.

  Definition tqueue_mpmc_2۰inv γ (ι : namespace) : iProp Σ.
  Admitted.

  Definition tqueue_mpmc_2۰model γ vs : iProp Σ.
  Admitted.

  Definition tqueue_mpmc_2۰full γ : iProp Σ.
  Admitted.

  Definition tqueue_mpmc_2۰nonfull γ : iProp Σ.
  Admitted.

  Definition tqueue_mpmc_2۰finished γ : iProp Σ.
  Admitted.

  #[global] Instance tqueue_mpmc_2۰modelｰtimeless γ vs :
    Timeless (tqueue_mpmc_2۰model γ vs).
  Proof.
  Admitted.

  #[global] Instance tqueue_mpmc_2۰invｰpersistent γ ι :
    Persistent (tqueue_mpmc_2۰inv γ ι).
  Proof.
  Admitted.
  #[global] Instance tqueue_mpmc_2۰fullｰpersistent γ :
    Persistent (tqueue_mpmc_2۰full γ).
  Proof.
  Admitted.
  #[global] Instance tqueue_mpmc_2۰finishedｰpersistent γ :
    Persistent (tqueue_mpmc_2۰finished γ).
  Proof.
  Admitted.

  Lemma tqueue_mpmc_2۰modelｰexclusive γ vs1 vs2 :
    tqueue_mpmc_2۰model γ vs1 -∗
    tqueue_mpmc_2۰model γ vs2 -∗
    False.
  Proof.
  Admitted.

  Lemma tqueue_mpmc_2ｰfullｰnonfull γ :
    tqueue_mpmc_2۰full γ -∗
    tqueue_mpmc_2۰nonfull γ -∗
    False.
  Proof.
  Admitted.

  Lemma tqueue_mpmc_2ｰmodelｰfinished γ ι vs E :
    ↑ι ⊆ E →
    tqueue_mpmc_2۰inv γ ι -∗
    tqueue_mpmc_2۰model γ vs -∗
    tqueue_mpmc_2۰finished γ ={E}=∗
      ⌜vs = []⌝ ∗
      tqueue_mpmc_2۰model γ vs.
  Proof.
  Admitted.

  Lemma tqueue_mpmc_2٠createｰspec ι cap :
    (0 ≤ cap)%Z →
    {{{
      True
    }}}
      tqueue_mpmc_2٠create #cap
    {{{
      γ
    , RET γ;
      tqueue_mpmc_2۰inv γ ι ∗
      tqueue_mpmc_2۰model γ []
    }}}.
  Proof.
  Admitted.

  Lemma tqueue_mpmc_2٠makeｰspec ι cap v :
    (0 ≤ cap)%Z →
    {{{
      True
    }}}
      tqueue_mpmc_2٠make #cap v
    {{{
      γ
    , RET γ;
      tqueue_mpmc_2۰inv γ ι ∗
      tqueue_mpmc_2۰model γ [v]
    }}}.
  Proof.
  Admitted.

  Lemma tqueue_mpmc_2٠is_emptyｰspec γ ι :
    <<<
      tqueue_mpmc_2۰inv γ ι
    | ∀∀ vs,
      tqueue_mpmc_2۰model γ vs
    >>>
      tqueue_mpmc_2٠is_empty γ
      @ ↑ι
    <<<
      tqueue_mpmc_2۰model γ vs
    | b,
      RET #b;
      ⌜if b then vs = [] else True⌝
    >>>.
  Proof.
  Admitted.

  Lemma tqueue_mpmc_2٠pushｰspec γ ι v E Φ :
    tqueue_mpmc_2۰inv γ ι -∗
    ▷ (
      |={⊤ ∖ ↑ι, E}=>
      ∃ vs,
      tqueue_mpmc_2۰model γ vs ∗
        ∀ b,
        ( if b then
            tqueue_mpmc_2۰model γ (vs ++ [v]) ∗
            tqueue_mpmc_2۰nonfull γ
          else
            tqueue_mpmc_2۰model γ vs ∗
            tqueue_mpmc_2۰full γ
        ) ={E}=∗
          ( if b then
              tqueue_mpmc_2۰nonfull γ
            else
              True
          ) ∗
            |={E, ⊤ ∖ ↑ι}=>
            Φ #b
    ) -∗
    WP tqueue_mpmc_2٠push γ v {{ Φ }}.
  Proof.
  Admitted.

  Lemma tqueue_mpmc_2٠popｰspec γ ι :
    <<<
      tqueue_mpmc_2۰inv γ ι
    | ∀∀ vs,
      tqueue_mpmc_2۰model γ vs
    >>>
      tqueue_mpmc_2٠pop γ
      @ ↑ι
    <<<
      ∃∃ o vs',
      tqueue_mpmc_2۰model γ vs' ∗
      ⌜ match o with
        | Something v =>
            vs = v :: vs'
        | Nothing =>
            vs' = vs
        | Anything =>
            vs = [] ∧
            vs' = vs
        end
      ⌝
    | RET o;
      if o is Anything then
        tqueue_mpmc_2۰finished γ
      else
        True
    >>>.
  Proof.
  Admitted.
End tqueue_mpmc_2۰G.

Require zoo_saturn.tqueue_mpmc_2__opaque.

#[global] Opaque tqueue_mpmc_2۰inv.
#[global] Opaque tqueue_mpmc_2۰model.
#[global] Opaque tqueue_mpmc_2۰full.
#[global] Opaque tqueue_mpmc_2۰nonfull.
#[global] Opaque tqueue_mpmc_2۰finished.
