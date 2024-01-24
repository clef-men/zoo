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

Implicit Types v t back front : val.

#[local] Notation "t '.<back>'" :=
  t.𝟙%E
( at level 5
) : expr_scope.
#[local] Notation "t '.<front>'" :=
  t.𝟚%E
( at level 5
) : expr_scope.

Definition pqueue_empty : val :=
  (&&Nil, &&Nil).

Definition pqueue_is_empty : val :=
  λ: "t",
    lst_is_empty "t".<front> && lst_is_empty "t".<back>.

Definition pqueue_push : val :=
  λ: "t" "v",
    (&Cons "v" "t".<back>, "t".<front>).

Definition pqueue_pop : val :=
  λ: "t",
    if: lst_is_empty "t".<front> then (
      let: "front" := lst_rev "t".<back> in
      if: lst_is_empty "front" then (
        &&None
      ) else (
        &Some (lst_head "front", (&&Nil, lst_tail "front"))
      )
    ) else (
      &Some (lst_head "t".<front>, ("t".<back>, lst_tail "t".<front>))
    ).

Section zebre_G.
  Context `{zebre_G : !ZebreG Σ}.

  Definition pqueue_model t vs : iProp Σ :=
    ∃ back vs_back front vs_front,
    ⌜t = (back, front)%V ∧ vs = vs_back ++ reverse vs_front⌝ ∗
    lst_model back vs_back ∗
    lst_model front vs_front.

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
    iExists &&Nil, [], &&Nil, []. iStep. iSplit; iApply lst_model_Nil.
  Qed.

  Lemma pqueue_is_empty_spec t vs :
    {{{
      pqueue_model t vs
    }}}
      pqueue_is_empty t
    {{{
      RET #(bool_decide (vs = [])); True
    }}}.
  Proof.
    iIntros "%Φ (%back & %vs_back & %front & %vs_front & (-> & ->) & #Hback & #Hfront) HΦ".
    wp_rec.
    wp_smart_apply (lst_is_empty_spec with "Hfront") as "_".
    destruct vs_front as [| v_front vs_front]; wp_pures.
    - wp_apply (lst_is_empty_spec with "Hback") as "_".
      destruct vs_back; iSteps.
    - rewrite bool_decide_eq_false_2.
      { rewrite reverse_cons. intros (_ & (_ & [=])%app_eq_nil)%app_eq_nil. }
      iSteps.
  Qed.

  Lemma pqueue_push_spec t vs v :
    {{{
      pqueue_model t vs
    }}}
      pqueue_push t v
    {{{ t',
      RET t';
      pqueue_model t' (v :: vs)
    }}}.
  Proof.
    iIntros "%Φ (%back & %vs_back & %front & %vs_front & (-> & ->) & #Hback & #Hfront) HΦ".
    wp_rec. wp_pures.
    iApply "HΦ". iExists _, (v :: vs_back), front, vs_front. iFrame "#∗". iStep.
    iApply (lst_model_Cons with "Hback").
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
          ∃ vs' v t',
          ⌜vs = vs' ++ [v] ∧ p = (v, t')%V⌝ ∗
          pqueue_model t' vs'
      end
    }}}.
  Proof.
    iIntros "%Φ (%back & %vs_back & %front & %vs_front & (-> & ->) & #Hback & #Hfront) HΦ".
    wp_rec.
    wp_smart_apply (lst_is_empty_spec with "Hfront") as "_".
    destruct vs_front as [| v_front vs_front]; wp_pures.
    - iClear "Hfront". clear.
      wp_apply (lst_rev_spec with "Hback") as "%front #Hfront".
      wp_smart_apply (lst_is_empty_spec with "Hfront") as "_".
      destruct (reverse vs_back) as [| v vs_front] eqn:Heq;
        apply (f_equal reverse) in Heq; rewrite reverse_involutive in Heq; subst;
        wp_pures.
      + iApply ("HΦ" $! None with "[//]").
      + wp_apply (lst_tail_spec with "Hfront") as "%front' #Hfront'"; first done.
        wp_smart_apply (lst_head_spec with "Hfront") as "_"; first done.
        wp_pures.
        iApply ("HΦ" $! (Some (_, _)%V)). iExists (reverse vs_front), v, _. iSplitR.
        { iPureIntro. split; last done.
          rewrite reverse_nil reverse_cons. list_simplifier. done.
        }
        iExists &&Nil, [], front', vs_front. iFrame "#∗". iStep. iApply lst_model_Nil.
    - wp_apply (lst_tail_spec with "Hfront") as "%front' Hfront'"; first done.
      wp_smart_apply (lst_head_spec with "Hfront") as "_"; first done.
      wp_pures.
      iApply ("HΦ" $! (Some (_, _)%V)). iExists (vs_back ++ reverse vs_front), v_front, _. iSplitR.
      { iSteps. list_simplifier. rewrite reverse_cons //. }
      iSteps; iFrame "#∗".
  Qed.
End zebre_G.

#[global] Opaque pqueue_empty.
#[global] Opaque pqueue_is_empty.
#[global] Opaque pqueue_push.
#[global] Opaque pqueue_pop.

#[global] Opaque pqueue_model.
