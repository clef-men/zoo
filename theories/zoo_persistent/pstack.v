Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo_std.option.
Require Import zoo_std.list.
Require Export zoo_persistent.pstack__code.
Require Import zoo.options.

Implicit Type v t : val.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Definition pstack۰model t vs : iProp Σ :=
    list۰model t vs.

  #[global] Instance pstack۰modelｰtimeless t vs :
    Timeless (pstack۰model t vs).
  Proof.
    apply _.
  Qed.

  #[global] Instance pstack۰modelｰpersistent t vs :
    Persistent (pstack۰model t vs).
  Proof.
    apply _.
  Qed.

  Lemma pstack۰modelｰnil :
    ⊢ pstack۰model pstack٠empty [].
  Proof.
    iSteps.
  Qed.

  Lemma pstack٠is_emptyｰspec t vs :
    {{{
      pstack۰model t vs
    }}}
      pstack٠is_empty t
    {{{
      RET #(bool_decide (vs = []%list));
      True
    }}}.
  Proof.
    iIntros "%Φ -> HΦ".
    wp۰apply (list٠is_emptyｰspec with "[//] HΦ"); first done.
  Qed.

  Lemma pstack٠pushｰspec t vs v :
    {{{
      pstack۰model t vs
    }}}
      pstack٠push t v
    {{{
      t'
    , RET t';
      pstack۰model t' (v :: vs)
    }}}.
  Proof.
    iIntros "%Φ -> HΦ".
    iSteps.
  Qed.

  Lemma pstack٠popｰspec t vs :
    {{{
      pstack۰model t vs
    }}}
      pstack٠pop t
    {{{
      o
    , RET o;
      match o with
      | None =>
          ⌜vs = []⌝
      | Some p =>
          ∃ v vs' t',
          ⌜vs = v :: vs'⌝ ∗
          ⌜p = (v, t')%V⌝ ∗
          pstack۰model t' vs'
      end
    }}}.
  Proof.
    iIntros "%Φ -> HΦ".
    wp۰rec.
    destruct vs as [| v vs]; wp۰pures.
    - iSpecialize ("HΦ" $! None). iSteps.
    - iSpecialize ("HΦ" $! (Some _)). iSteps.
  Qed.
End zoo۰G.

Require zoo_persistent.pstack__opaque.

#[global] Opaque pstack۰model.
