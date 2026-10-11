Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_data.pstack__code.
Require Import zoo_data.pstack__types.
Require Import zoo.options.

Implicit Type v t : val.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Please Definition pstack۰model t vs : iProp Σ :=
    list۰model t vs.

  Zoo derive Timeless for pstack۰model.

  Zoo derive Persistent for pstack۰model.

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

Require zoo_data.pstack__opaque.

Please opacify.
