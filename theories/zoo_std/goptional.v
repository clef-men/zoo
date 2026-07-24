Require Import zoo.prelude.
Require Import zoo.base.
Require Export zoo_std.goptional__types.
Require Import zoo.options.

Implicit Type v : val.

Variant goptional {A} :=
  | Gnothing
  | Ganything
  | Gsomething (a : A).
#[global] Arguments goptional : clear implicits.

#[global] Instance goptional𑁒inhabited A : Inhabited (goptional A) :=
  populate Gnothing.
#[global] Instance Gsomething𑁒inj A :
  Inj (=) (=) (@Gsomething A).
Proof.
  rewrite /Inj. naive_solver.
Qed.

Definition option۰to_goptional {A} (o : option A) :=
  match o with
  | None =>
      Gnothing
  | Some a =>
      Gsomething a
  end.
#[global] Arguments option۰to_goptional _ !_ / : assert.

Coercion goptional۰to_val o :=
  match o with
  | Gnothing =>
      §Gnothing
  | Ganything =>
      §Ganything
  | Gsomething v =>
      ‘Gsomething[ v ]
  end%V.
#[global] Arguments goptional۰to_val !_ / : assert.

#[global] Instance goptional۰to_val𑁒inj𑁒similar :
  Inj (=) (≈@{val}) goptional۰to_val.
Proof.
  intros [] [] ?; try done.
  zoo_simplify. done.
Qed.
#[global] Instance goptional۰to_val𑁒inj :
  Inj (=) (=) goptional۰to_val.
Proof.
  intros ?* ->%val𑁒similar𑁒refl%(inj _). done.
Qed.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.
  Context τ `{!iType (iPropI Σ) τ}.

  Definition itype۰goptional t : iProp Σ :=
      ⌜t = §Gnothing%V⌝
    ∨ ⌜t = §Ganything%V⌝
    ∨ ∃ v,
      ⌜t = ‘Gsomething( v )%V⌝ ∗
      τ v.
  #[global] Instance itype۰goptional𑁒itype :
    iType _ itype۰goptional.
  Proof.
    split. apply _.
  Qed.

  Lemma wp𑁒match𑁒goptional t e1 e2 x e3 Φ :
    itype۰goptional t -∗
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
End zoo۰G.
