From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  glst__types
  glst__code.
From zoo Require Import
  options.

Implicit Types v : val.
Implicit Types vs : list val.

Fixpoint glst_to_val vs :=
  match vs with
  | [] =>
      §Gnil%V
  | v :: vs =>
      ‘Gcons[ v, glst_to_val vs ]%V
  end.
#[global] Arguments glst_to_val !_ / : assert.

#[global] Instance glst_to_val_inj_similar :
  Inj (=) (≈@{val}) glst_to_val.
Proof.
  intros vs1. induction vs1 as [| v1 vs1 IH]; intros [| v2 vs2]; [done.. |].
  intros (_ & [= <- <-%val_similar_refl%IH]). done.
Qed.
#[global] Instance glst_to_val_inj :
  Inj (=) (=) glst_to_val.
Proof.
  intros ?* ->%val_similar_refl%(inj _). done.
Qed.

Lemma glst_to_val_nil :
  glst_to_val [] = §Gnil%V.
Proof.
  done.
Qed.
Lemma glst_to_val_cons v vs :
  glst_to_val (v :: vs) = ‘Gcons[ v, glst_to_val vs ]%V.
Proof.
  done.
Qed.
Lemma glst_to_val_singleton v :
  glst_to_val [v] = ‘Gcons[ v, §Gnil ]%V.
Proof.
  done.
Qed.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition glst_model' t vs :=
    t = glst_to_val vs.
  Definition glst_model t vs : iProp Σ :=
    ⌜glst_model' t vs⌝.

  Lemma glst_rev_app_spec {t1} vs1 {t2} vs2 :
    glst_model' t1 vs1 →
    glst_model' t2 vs2 →
    {{{
      True
    }}}
      glst_rev_app t1 t2
    {{{
      RET glst_to_val (reverse vs1 ++ vs2);
      True
    }}}.
  Proof.
    iInduction vs1 as [| v1 vs1] "IH" forall (t1 t2 vs2).
    all: iIntros (-> ->) "%Φ _ HΦ".
    all: wp_rec.
    - iSteps.
    - wp_pures.
      wp_smart_apply ("IH" $! _ _ (v1 :: vs2) with "[//]"); iSteps.
      rewrite reverse_cons -assoc. iSteps.
  Qed.

  Lemma glst_rev_spec {t} vs :
    glst_model' t vs →
    {{{
      True
    }}}
      glst_rev t
    {{{
      RET glst_to_val (reverse vs);
      True
    }}}.
  Proof.
    iIntros "%Ht %Φ _ HΦ".
    wp_rec.
    wp_apply (glst_rev_app_spec _ [] with "[//]"); [done.. |].
    rewrite right_id //.
  Qed.
End zoo_G.

#[global] Opaque glst_rev_app.
#[global] Opaque glst_rev.
