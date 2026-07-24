Require Import zoo.prelude.
Require Import zoo.common.list.
Require Import zoo.base.
Require Import zoo_std.option.
Require Import zoo_std.list.
Require Export zoo_persistent.pqueue__code.
Require Import zoo_persistent.pqueue__types.
Require Import zoo.options.

Implicit Type v t : val.
Implicit Type back front : list val.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Definition pqueue۰model t vs : iProp Σ :=
    ∃ front back,
    ⌜t = (list۰to_val front, list۰to_val back)%V ∧ vs = front ++ reverse back⌝.

  #[global] Instance pqueue۰model𑁒timeless t vs :
    Timeless (pqueue۰model t vs).
  Proof.
    apply _.
  Qed.

  #[global] Instance pqueue۰model𑁒persistent t vs :
    Persistent (pqueue۰model t vs).
  Proof.
    apply _.
  Qed.

  Lemma pqueue۰model𑁒nil :
    ⊢ pqueue۰model pqueue٠empty [].
  Proof.
    iExists [], []. iSteps.
  Qed.

  Lemma pqueue٠is_empty𑁒spec t vs :
    {{{
      pqueue۰model t vs
    }}}
      pqueue٠is_empty t
    {{{
      RET #(bool_decide (vs = []%list));
      True
    }}}.
  Proof.
    iIntros "%Φ (%front & %back & (-> & ->)) HΦ".
    wp۰rec.
    wp۰apply+ (list٠is_empty𑁒spec with "[//]") as "_"; first done.
    destruct front as [| v front]; wp۰pures.
    - wp۰apply (list٠is_empty𑁒spec with "[//]") as "_"; first done.
      erewrite bool_decide_ext by apply reverse𑁒nil𑁒iff. iSteps.
    - rewrite bool_decide_eq_false_2 //. iSteps.
  Qed.

  Lemma pqueue٠push𑁒spec t vs v :
    {{{
      pqueue۰model t vs
    }}}
      pqueue٠push t v
    {{{
      t'
    , RET t';
      pqueue۰model t' (vs ++ [v])
    }}}.
  Proof.
    iIntros "%Φ (%front & %back & (-> & ->)) HΦ".
    wp۰rec. wp۰pures.
    iApply "HΦ".
    iExists front, (v :: back). iSteps. rewrite reverse_cons assoc //.
  Qed.

  Lemma pqueue٠pop𑁒spec t vs :
    {{{
      pqueue۰model t vs
    }}}
      pqueue٠pop t
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
          pqueue۰model t' vs'
      end
    }}}.
  Proof.
    iIntros "%Φ (%front & %back & (-> & ->)) HΦ".
    wp۰rec.
    destruct front as [| v front]; wp۰pures.
    - wp۰apply (list٠rev𑁒spec with "[//]") as "%front ->"; first done.
      destruct back as [| v back _] using rev_ind.
      + wp۰pures.
        iApply ("HΦ" $! None with "[//]").
      + rewrite reverse_snoc. wp۰pures.
        iApply ("HΦ" $! (Some _)).
        iSteps.
        iExists _, []. rewrite right_id. iSteps.
    - iApply ("HΦ" $! (Some (_, _)%V)).
      iSteps.
  Qed.
End zoo۰G.

Require zoo_persistent.pqueue__opaque.

#[global] Opaque pqueue۰model.
