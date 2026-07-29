Require Import zoo.prelude.
Require Import zoo.base.
Require Export zoo_std.glist__types.
Require Export zoo_std.glist__code.
Require Import zoo.options.

Implicit Type v : val.
Implicit Type vs : list val.

Fixpoint glist۰to_val vs :=
  match vs with
  | [] =>
      §Gnil%V
  | v :: vs =>
      ‘Gcons[ v, glist۰to_val vs ]%V
  end.
#[global] Arguments glist۰to_val !_ / : assert.

#[global] Instance glist۰to_valｰinjｰsimilar :
  Inj (=) (≈@{val}) glist۰to_val.
Proof.
  intros vs1. induction vs1 as [| v1 vs1 IH]; intros [| v2 vs2]; [done.. |].
  intros (_ & _ & [= <- <-%valｰsimilarｰrefl%IH]). done.
Qed.
#[global] Instance glist۰to_valｰinj :
  Inj (=) (=) glist۰to_val.
Proof.
  intros ?* ->%valｰsimilarｰrefl%(inj _). done.
Qed.

Lemma glist۰to_valｰnil :
  glist۰to_val [] = §Gnil%V.
Proof.
  done.
Qed.
Lemma glist۰to_valｰcons v vs :
  glist۰to_val (v :: vs) = ‘Gcons[ v, glist۰to_val vs ]%V.
Proof.
  done.
Qed.
Lemma glist۰to_valｰsingleton v :
  glist۰to_val [v] = ‘Gcons[ v, §Gnil ]%V.
Proof.
  done.
Qed.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Definition glist۰model' t vs :=
    t = glist۰to_val vs.
  Definition glist۰model t vs : iProp Σ :=
    ⌜glist۰model' t vs⌝.

  Lemma glist٠rev_appｰspec {t1} vs1 {t2} vs2 :
    glist۰model' t1 vs1 →
    glist۰model' t2 vs2 →
    {{{
      True
    }}}
      glist٠rev_app t1 t2
    {{{
      RET glist۰to_val (reverse vs1 ++ vs2);
      True
    }}}.
  Proof.
    iInduction vs1 as [| v1 vs1] "IH" forall (t1 t2 vs2).
    all: iIntros (-> ->) "%Φ _ HΦ".
    all: wp۰rec.
    - iSteps.
    - wp۰pures.
      wp۰apply+ ("IH" $! _ _ (v1 :: vs2) with "[//]"); iSteps.
      rewrite reverse_cons -assoc. iSteps.
  Qed.

  Lemma glist٠revｰspec {t} vs :
    glist۰model' t vs →
    {{{
      True
    }}}
      glist٠rev t
    {{{
      RET glist۰to_val (reverse vs);
      True
    }}}.
  Proof.
    iIntros "%Ht %Φ _ HΦ".
    wp۰rec.
    wp۰apply (glist٠rev_appｰspec _ [] with "[//]"); [done.. |].
    rewrite right_id //.
  Qed.
End zoo۰G.

Require zoo_std.glist__opaque.
