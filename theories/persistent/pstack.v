From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Import
  opt
  lst.
From zebre.persistent Require Export
  base.
From zebre Require Import
  options.

Implicit Types v t lst : val.

Definition pstack_empty :=
  §Nil.

Definition pstack_is_empty :=
  lst_is_empty.

Definition pstack_push : val :=
  λ: "t" "v",
    ‘Cons {"v", "t"}.

Definition pstack_pop : val :=
  λ: "t",
    match: "t" with
    | Nil =>
        §None
    | Cons "v" "t'" =>
        ‘Some {("v", "t'")}
    end.

Section zebre_G.
  Context `{zebre_G : !ZebreG Σ}.

  Definition pstack_model t vs : iProp Σ :=
    lst_model t vs.

  #[global] Instance pstack_model_persistent t vs :
    Persistent (pstack_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance pstack_model_timeless t vs :
    Timeless (pstack_model t vs).
  Proof.
    apply _.
  Qed.

  Lemma pstack_model_nil :
    ⊢ pstack_model pstack_empty [].
  Proof.
    iSteps.
  Qed.

  Lemma pstack_is_empty_spec t vs :
    {{{
      pstack_model t vs
    }}}
      pstack_is_empty t
    {{{
      RET #(bool_decide (vs = [])); True
    }}}.
  Proof.
    apply lst_is_empty_spec.
  Qed.

  Lemma pstack_push_spec t vs v :
    {{{
      pstack_model t vs
    }}}
      pstack_push t v
    {{{ t',
      RET t';
      pstack_model t' (v :: vs)
    }}}.
  Proof.
    iIntros "%Φ -> HΦ".
    iSteps.
  Qed.

  Lemma pstack_pop_spec t vs :
    {{{
      pstack_model t vs
    }}}
      pstack_pop t
    {{{ o,
      RET o : val;
      match o with
      | None =>
          ⌜vs = []⌝
      | Some p =>
          ∃ v vs' t',
          ⌜vs = v :: vs' ∧ p = (v, t')%V⌝ ∗
          pstack_model t' vs'
      end
    }}}.
  Proof.
    iIntros "%Φ -> HΦ".
    wp_rec.
    destruct vs as [| v vs]; wp_pures.
    - iSpecialize ("HΦ" $! None). iSteps.
    - iSpecialize ("HΦ" $! (Some _)). iSteps.
  Qed.
End zebre_G.

#[global] Opaque pstack_empty.
#[global] Opaque pstack_is_empty.
#[global] Opaque pstack_push.
#[global] Opaque pstack_pop.

#[global] Opaque pstack_model.
