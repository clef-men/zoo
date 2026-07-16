Require Import zoo.prelude.
Require Import zoo.base.
Require Export zoo_std.glist__types.
Require Export zoo_std.glist__code.
Require Import zoo.options.

Implicit Types v : val.
Implicit Types vs : list val.

Fixpoint glist۰to_val vs :=
  match vs with
  | [] =>
      §Gnil%V
  | v :: vs =>
      ‘Gcons[ v, glist۰to_val vs ]%V
  end.
#[global] Arguments glist۰to_val !_ / : assert.

#[global] Instance glist۰to_val𑁒inj𑁒similar :
  Inj (=) (≈@{val}) glist۰to_val.
Proof.
  intros vs1. induction vs1 as [| v1 vs1 IH]; intros [| v2 vs2]; [done.. |].
  intros (_ & _ & [= <- <-%val𑁒similar𑁒refl%IH]). done.
Qed.
#[global] Instance glist۰to_val𑁒inj :
  Inj (=) (=) glist۰to_val.
Proof.
  intros ?* ->%val𑁒similar𑁒refl%(inj _). done.
Qed.

Lemma glist۰to_val𑁒nil :
  glist۰to_val [] = §Gnil%V.
Proof.
  done.
Qed.
Lemma glist۰to_val𑁒cons v vs :
  glist۰to_val (v :: vs) = ‘Gcons[ v, glist۰to_val vs ]%V.
Proof.
  done.
Qed.
Lemma glist۰to_val𑁒singleton v :
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

  Lemma glist٠rev_app𑁒spec {t1} vs1 {t2} vs2 :
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

  Lemma glist٠rev𑁒spec {t} vs :
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
    wp۰apply (glist٠rev_app𑁒spec _ [] with "[//]"); [done.. |].
    rewrite right_id //.
  Qed.
End zoo۰G.

Require zoo_std.glist__opaque.
