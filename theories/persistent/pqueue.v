From zebre Require Import
  prelude.
From zebre.common Require Import
  list.
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

Implicit Types v t : val.
Implicit Types back front : list val.

#[local] Notation "'back'" :=
  0
( in custom zebre_proj
).
#[local] Notation "'front'" :=
  1
( in custom zebre_proj
).

Definition pqueue_empty : val :=
  (§Nil, §Nil).

Definition pqueue_is_empty : val :=
  λ: "t",
    lst_is_empty "t".<front> && lst_is_empty "t".<back>.

Definition pqueue_push : val :=
  λ: "t" "v",
    (‘Cons{"v", "t".<back>}, "t".<front>).

Definition pqueue_pop : val :=
  λ: "t",
    match: "t".<front> with
    | Nil =>
        match: lst_rev "t".<back> with
        | Nil =>
            §None
        | Cons "v" "vs" =>
            ‘Some{("v", (§Nil, "vs"))}
        end
    | Cons "v" "vs" =>
        ‘Some{("v", ("t".<back>, "vs"))}
    end.

Section zebre_G.
  Context `{zebre_G : !ZebreG Σ}.

  Definition pqueue_model t vs : iProp Σ :=
    ∃ back front,
    ⌜t = (lst_to_val back, lst_to_val front)%V ∧ vs = back ++ reverse front⌝.

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
      RET #(bool_decide (vs = [])); True
    }}}.
  Proof.
    iIntros "%Φ (%back & %front & (-> & ->)) HΦ".
    wp_rec.
    wp_smart_apply (lst_is_empty_spec with "[//]") as "_".
    destruct front as [| v front]; wp_pures.
    - wp_apply (lst_is_empty_spec with "[//]") as "_".
      destruct back; iSteps.
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
    iIntros "%Φ (%back & %front & (-> & ->)) HΦ".
    wp_rec. wp_pures.
    iApply "HΦ". iExists (v :: back), front. iSteps.
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
    iIntros "%Φ (%back & %front & (-> & ->)) HΦ".
    wp_rec.
    destruct front as [| v front]; wp_pures.
    - wp_apply (lst_rev_spec with "[//]") as "%front ->".
      destruct (rev_elim back) as [-> | (back' & v & ->)].
      + wp_pures.
        iApply ("HΦ" $! None with "[//]").
      + rewrite reverse_snoc. wp_pures.
        iApply ("HΦ" $! (Some _)). iExists back', v, _. iSplitR.
        { iPureIntro. rewrite reverse_nil right_id //. }
        iExists [], _. iSteps. rewrite reverse_involutive //.
    - iApply ("HΦ" $! (Some (_, _)%V)). iExists (back ++ reverse front), v, _. iSplitR.
      { iSteps. list_simplifier. rewrite reverse_cons //. }
      iSteps.
  Qed.
End zebre_G.

#[global] Opaque pqueue_empty.
#[global] Opaque pqueue_is_empty.
#[global] Opaque pqueue_push.
#[global] Opaque pqueue_pop.

#[global] Opaque pqueue_model.
