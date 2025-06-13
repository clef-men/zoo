From zoo Require Import
  prelude.
From zoo.common Require Import
  list.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  option
  lst.
From zoo_persistent Require Export
  base
  pqueue__code.
From zoo_persistent Require Import
  pqueue__types.
From zoo Require Import
  options.

Implicit Types v t : val.
Implicit Types back front : list val.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition pqueue_model t vs : iProp Σ :=
    ∃ front back,
    ⌜t = (lst_to_val front, lst_to_val back)%V ∧ vs = front ++ reverse back⌝.

  #[global] Instance pqueue_model_persistent t vs :
    Persistent (pqueue_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance pqueue_model_timeless t vs :
    Timeless (pqueue_model t vs).
  Proof.
    apply _.
  Qed.

  Lemma pqueue_model_nil :
    ⊢ pqueue_model pqueue_empty [].
  Proof.
    iExists [], []. iSteps.
  Qed.

  Lemma pqueue_is_empty_spec t vs :
    {{{
      pqueue_model t vs
    }}}
      pqueue_is_empty t
    {{{
      RET #(bool_decide (vs = []%list));
      True
    }}}.
  Proof.
    iIntros "%Φ (%front & %back & (-> & ->)) HΦ".
    wp_rec.
    wp_smart_apply (lst_is_empty_spec with "[//]") as "_"; first done.
    destruct front as [| v front]; wp_pures.
    - wp_apply (lst_is_empty_spec with "[//]") as "_"; first done.
      erewrite bool_decide_ext by apply reverse_nil_iff. iSteps.
    - rewrite bool_decide_eq_false_2 //. iSteps.
  Qed.

  Lemma pqueue_push_spec t vs v :
    {{{
      pqueue_model t vs
    }}}
      pqueue_push t v
    {{{ t',
      RET t';
      pqueue_model t' (vs ++ [v])
    }}}.
  Proof.
    iIntros "%Φ (%front & %back & (-> & ->)) HΦ".
    wp_rec. wp_pures.
    iApply "HΦ".
    iExists front, (v :: back). iSteps. rewrite reverse_cons assoc //.
  Qed.

  Lemma pqueue_pop_spec t vs :
    {{{
      pqueue_model t vs
    }}}
      pqueue_pop t
    {{{ o,
      RET o : val;
      match o with
      | None =>
          ⌜vs = []⌝
      | Some p =>
          ∃ v vs' t',
          ⌜vs = v :: vs'⌝ ∗
          ⌜p = (v, t')%V⌝ ∗
          pqueue_model t' vs'
      end
    }}}.
  Proof.
    iIntros "%Φ (%front & %back & (-> & ->)) HΦ".
    wp_rec.
    destruct front as [| v front]; wp_pures.
    - wp_apply (lst_rev_spec with "[//]") as "%front ->"; first done.
      destruct back as [| v back _] using rev_ind.
      + wp_pures.
        iApply ("HΦ" $! None with "[//]").
      + rewrite reverse_snoc. wp_pures.
        iApply ("HΦ" $! (Some _)).
        iSteps.
        iExists _, []. rewrite right_id. iSteps.
    - iApply ("HΦ" $! (Some (_, _)%V)).
      iSteps.
  Qed.
End zoo_G.

From zoo_persistent Require
  pqueue__opaque.

#[global] Opaque pqueue_model.
