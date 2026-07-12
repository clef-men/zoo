Require Import zoo.prelude.
Require Import zoo.language.notations.
Require Import zoo.diaframe.
Require Export zoo_std.base.
Require Export zoo_std.glist__types.
Require Export zoo_std.glist__code.
Require Import zoo.options.

Implicit Types v : val.
Implicit Types vs : list val.

Fixpoint glist_to_val vs :=
  match vs with
  | [] =>
      §Gnil%V
  | v :: vs =>
      ‘Gcons[ v, glist_to_val vs ]%V
  end.
#[global] Arguments glist_to_val !_ / : assert.

#[global] Instance glist_to_val_inj_similar :
  Inj (=) (≈@{val}) glist_to_val.
Proof.
  intros vs1. induction vs1 as [| v1 vs1 IH]; intros [| v2 vs2]; [done.. |].
  intros (_ & _ & [= <- <-%val_similar_refl%IH]). done.
Qed.
#[global] Instance glist_to_val_inj :
  Inj (=) (=) glist_to_val.
Proof.
  intros ?* ->%val_similar_refl%(inj _). done.
Qed.

Lemma glist_to_val_nil :
  glist_to_val [] = §Gnil%V.
Proof.
  done.
Qed.
Lemma glist_to_val_cons v vs :
  glist_to_val (v :: vs) = ‘Gcons[ v, glist_to_val vs ]%V.
Proof.
  done.
Qed.
Lemma glist_to_val_singleton v :
  glist_to_val [v] = ‘Gcons[ v, §Gnil ]%V.
Proof.
  done.
Qed.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition glist_model' t vs :=
    t = glist_to_val vs.
  Definition glist_model t vs : iProp Σ :=
    ⌜glist_model' t vs⌝.

  Lemma glist٠rev_app𑁒spec {t1} vs1 {t2} vs2 :
    glist_model' t1 vs1 →
    glist_model' t2 vs2 →
    {{{
      True
    }}}
      glist٠rev_app t1 t2
    {{{
      RET glist_to_val (reverse vs1 ++ vs2);
      True
    }}}.
  Proof.
    iInduction vs1 as [| v1 vs1] "IH" forall (t1 t2 vs2).
    all: iIntros (-> ->) "%Φ _ HΦ".
    all: wp_rec.
    - iSteps.
    - wp_pures.
      wp_apply+ ("IH" $! _ _ (v1 :: vs2) with "[//]"); iSteps.
      rewrite reverse_cons -assoc. iSteps.
  Qed.

  Lemma glist٠rev𑁒spec {t} vs :
    glist_model' t vs →
    {{{
      True
    }}}
      glist٠rev t
    {{{
      RET glist_to_val (reverse vs);
      True
    }}}.
  Proof.
    iIntros "%Ht %Φ _ HΦ".
    wp_rec.
    wp_apply (glist٠rev_app𑁒spec _ [] with "[//]"); [done.. |].
    rewrite right_id //.
  Qed.
End zoo_G.

Require zoo_std.glist__opaque.
