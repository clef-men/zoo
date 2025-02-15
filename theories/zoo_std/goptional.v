From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  goptional__types.
From zoo Require Import
  options.

Implicit Types v : val.

Inductive goptional {A} :=
  | Gnothing
  | Ganything
  | Gsomething (a : A).
#[global] Arguments goptional : clear implicits.

#[global] Instance goptional_inhabited A : Inhabited (goptional A) :=
  populate Gnothing.
#[global] Instance Gsomething_inj A :
  Inj (=) (=) (@Gsomething A).
Proof.
  rewrite /Inj. naive_solver.
Qed.

Definition option_to_goptional {A} (o : option A) :=
  match o with
  | None =>
      Gnothing
  | Some a =>
      Gsomething a
  end.
#[global] Arguments option_to_goptional _ !_ / : assert.

Coercion goptional_to_val o :=
  match o with
  | Gnothing =>
      §Gnothing
  | Ganything =>
      §Ganything
  | Gsomething v =>
      ‘Gsomething[ v ]
  end%V.
#[global] Arguments goptional_to_val !_ / : assert.

#[global] Instance goptional_to_val_inj_similar :
  Inj (=) (≈@{val}) goptional_to_val.
Proof.
  intros [] []; naive_solver.
Qed.
#[global] Instance goptional_to_val_inj :
  Inj (=) (=) goptional_to_val.
Proof.
  intros ?* ->%val_similar_refl%(inj _). done.
Qed.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.
  Context τ `{!iType (iPropI Σ) τ}.

  Definition itype_goptional t : iProp Σ :=
      ⌜t = §Gnothing%V⌝
    ∨ ⌜t = §Ganything%V⌝
    ∨ ∃ v,
      ⌜t = ‘Gsomething( v )%V⌝ ∗
      τ v.
  #[global] Instance itype_goptional_itype :
    iType _ itype_goptional.
  Proof.
    split. apply _.
  Qed.

  Lemma wp_match_goptional t e1 e2 x e3 Φ :
    itype_goptional t -∗
    ( WP e1 {{ Φ }} ∧
      WP e2 {{ Φ }} ∧
      ∀ v, τ v -∗ WP subst' x v e3 {{ Φ }}
    ) -∗
    WP match: t with Gnothing => e1 | Ganything => e2 | Gsomething x => e3 end {{ Φ }}.
  Proof.
    iIntros "[-> | [-> | (%v & -> & #Hv)]] H".
    1: rewrite bi.and_elim_l.
    2,3: rewrite bi.and_elim_r.
    2: rewrite bi.and_elim_l.
    3: rewrite bi.and_elim_r.
    all: iSteps.
  Qed.
End zoo_G.
