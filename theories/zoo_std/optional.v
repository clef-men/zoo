Require Import zoo.prelude.
Require Import zoo.base.
Require Export zoo_std.optional__types.
Require Import zoo.options.

Implicit Types v : val.

Variant optional {A} :=
  | Nothing
  | Anything
  | Something (a : A).
#[global] Arguments optional : clear implicits.
Implicit Types o : optional val.

#[global] Instance optional𑁒inhabited A : Inhabited (optional A) :=
  populate Nothing.
#[global] Instance Something𑁒inj A :
  Inj (=) (=) (@Something A).
Proof.
  rewrite /Inj. naive_solver.
Qed.

Definition option۰to_optional {A} (o : option A) :=
  match o with
  | None =>
      Nothing
  | Some a =>
      Something a
  end.
#[global] Arguments option۰to_optional _ !_ / : assert.

Coercion optional۰to_val o :=
  match o with
  | Nothing =>
      §Nothing
  | Anything =>
      §Anything
  | Something v =>
      ‘Something( v )
  end%V.
#[global] Arguments optional۰to_val !_ / : assert.

#[global] Instance optional۰to_val𑁒inj :
  Inj (=) (=) optional۰to_val.
Proof.
  intros [] []; naive_solver.
Qed.

Lemma optional۰to_val𑁒similar𑁒Nothing_l o :
  §Nothing%V ≈ o →
  o = Nothing.
Proof.
  destruct o; done.
Qed.
Lemma optional۰to_val𑁒similar𑁒Nothing𑁒r o :
  (o : val) ≈ §Nothing%V →
  o = Nothing.
Proof.
  intros ?%symmetry%optional۰to_val𑁒similar𑁒Nothing_l. done.
Qed.

Lemma optional۰to_val𑁒similar𑁒Anything𑁒l o :
  §Anything%V ≈ o →
  o = Anything.
Proof.
  destruct o; done.
Qed.
Lemma optional۰to_val𑁒similar𑁒Anything𑁒r o :
  (o : val) ≈ §Anything%V →
  o = Anything.
Proof.
  intros ?%symmetry%optional۰to_val𑁒similar𑁒Anything𑁒l. done.
Qed.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.
  Context τ `{!iType (iPropI Σ) τ}.

  Definition itype۰optional t : iProp Σ :=
      ⌜t = §Nothing%V⌝
    ∨ ⌜t = §Anything%V⌝
    ∨ ∃ v,
      ⌜t = ‘Something( v )%V⌝ ∗
      τ v.
  #[global] Instance itype۰optional𑁒itype :
    iType _ itype۰optional.
  Proof.
    split. apply _.
  Qed.

  Lemma wp𑁒match𑁒optional t e1 e2 x e3 Φ :
    itype۰optional t -∗
    ( WP e1 {{ Φ }} ∧
      WP e2 {{ Φ }} ∧
      ∀ v, τ v -∗ WP subst' x v e3 {{ Φ }}
    ) -∗
    WP match: t with Nothing => e1 | Anything => e2 | Something x => e3 end {{ Φ }}.
  Proof.
    iIntros "[-> | [-> | (%v & -> & #Hv)]] H".
    1: rewrite bi.and_elim_l.
    2,3: rewrite bi.and_elim_r.
    2: rewrite bi.and_elim_l.
    3: rewrite bi.and_elim_r.
    all: iSteps.
  Qed.
End zoo۰G.
