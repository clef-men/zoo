From zoo Require Import
  prelude.
From zoo.common Require Import
  list.
From zoo.language Require Import
  notations
  diaframe.
From zoo.std Require Import
  option
  lst.
From zoo.persistent Require Export
  base.
From zoo Require Import
  options.

Implicit Types v t : val.
Implicit Types back front : list val.

#[local] Notation "'front'" := (
  in_type "t" 0
)(in custom zoo_proj
).
#[local] Notation "'back'" := (
  in_type "t" 1
)(in custom zoo_proj
).

Definition pqueue_empty : val :=
  (§Nil, §Nil).

Definition pqueue_is_empty : val :=
  fun: "t" =>
    lst_is_empty "t".<front> and lst_is_empty "t".<back>.

Definition pqueue_push : val :=
  fun: "t" "v" =>
    ("t".<front>, ‘Cons{ "v", "t".<back> }).

Definition pqueue_pop : val :=
  fun: "t" =>
    match: "t".<front> with
    | Nil =>
        match: lst_rev "t".<back> with
        | Nil =>
            §None
        | Cons "v" "vs" =>
            ‘Some{ ("v", ("vs", §Nil)) }
        end
    | Cons "v" "vs" =>
        ‘Some{ ("v", ("vs", "t".<back>)) }
    end.

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
      RET #(bool_decide (vs = [])); True
    }}}.
  Proof.
    iIntros "%Φ (%front & %back & (-> & ->)) HΦ".
    wp_rec.
    wp_smart_apply (lst_is_empty_spec with "[//]") as "_".
    destruct front as [| v front]; wp_pures.
    - wp_apply (lst_is_empty_spec with "[//]") as "_".
      erewrite bool_decide_ext; last apply reverse_nil_iff. iSteps.
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
          ⌜vs = v :: vs' ∧ p = (v, t')%V⌝ ∗
          pqueue_model t' vs'
      end
    }}}.
  Proof.
    iIntros "%Φ (%front & %back & (-> & ->)) HΦ".
    wp_rec.
    destruct front as [| v front]; wp_pures.
    - wp_apply (lst_rev_spec with "[//]") as "%front ->".
      destruct (rev_elim back) as [-> | (back' & v & ->)].
      + wp_pures.
        iApply ("HΦ" $! None with "[//]").
      + rewrite reverse_snoc. wp_pures.
        iApply ("HΦ" $! (Some _)).
        iExists v, (reverse back'), _. iSplitR; first iSteps.
        iExists _, []. iSteps. rewrite right_id //.
    - iApply ("HΦ" $! (Some (_, _)%V)).
      iSteps.
  Qed.
End zoo_G.

#[global] Opaque pqueue_empty.
#[global] Opaque pqueue_is_empty.
#[global] Opaque pqueue_push.
#[global] Opaque pqueue_pop.

#[global] Opaque pqueue_model.
