Require Import zoo.prelude.
Require Import zoo.language.notations.
Require Import zoo.diaframe.
Require Import zoo_std.option.
Require Import zoo_std.list.
Require Export zoo_persistent.base.
Require Export zoo_persistent.pstack__code.
Require Import zoo.options.

Implicit Types v t : val.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition pstack_model t vs : iProp Σ :=
    list_model t vs.

  #[global] Instance pstack_model_timeless t vs :
    Timeless (pstack_model t vs).
  Proof.
    apply _.
  Qed.

  #[global] Instance pstack_model_persistent t vs :
    Persistent (pstack_model t vs).
  Proof.
    apply _.
  Qed.

  Lemma pstack_model_nil :
    ⊢ pstack_model pstack٠empty [].
  Proof.
    iSteps.
  Qed.

  Lemma pstack٠is_empty𑁒spec t vs :
    {{{
      pstack_model t vs
    }}}
      pstack٠is_empty t
    {{{
      RET #(bool_decide (vs = []%list));
      True
    }}}.
  Proof.
    iIntros "%Φ -> HΦ".
    wp_apply (list٠is_empty𑁒spec with "[//] HΦ"); first done.
  Qed.

  Lemma pstack٠push𑁒spec t vs v :
    {{{
      pstack_model t vs
    }}}
      pstack٠push t v
    {{{
      t'
    , RET t';
      pstack_model t' (v :: vs)
    }}}.
  Proof.
    iIntros "%Φ -> HΦ".
    iSteps.
  Qed.

  Lemma pstack٠pop𑁒spec t vs :
    {{{
      pstack_model t vs
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
End zoo_G.

Require zoo_persistent.pstack__opaque.

#[global] Opaque pstack_model.
