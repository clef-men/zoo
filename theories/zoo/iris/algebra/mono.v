Require Export iris.algebra.cmra.
Require Import iris.algebra.local_updates.

Require Import zoo.prelude.
Require Import zoo.options.

Definition mono `(R : relation A) : Type :=
  list A.

Section relation.
  Context {SI : sidx}.
  Context `{R : relation A}.

  Implicit Type a b c : A.
  Implicit Type x y z : mono R.

  #[local] Definition below a x :=
    ∃ b,
    b ∈ x ∧
    R a b.

  #[local] Lemma below𑁒app a x y :
    below a (x ++ y) ↔
    below a x ∨ below a y.
  Proof.
    split.
    - intros (b & []%elem_of_app & ?);
        [left | right];
        exists b; done.
    - intros [(b & ? & ?) | (b & ? & ?)];
        exists b; rewrite elem_of_app; auto.
  Qed.

  #[local] Instance mono۰equiv : Equiv (mono R) :=
    λ x y,
      ∀ a,
      below a x ↔
      below a y.

  #[local] Instance mono۰equiv𑁒equiv :
    Equivalence mono۰equiv.
  Proof.
    split.
    - done.
    - firstorder.
    - intros ?* Heq1 Heq2 ?. split; intros.
      + apply Heq2, Heq1. done.
      + apply Heq1, Heq2. done.
  Qed.

  Canonical mono۰O :=
    discreteO (mono R).

  #[local] Instance mono۰valid : Valid (mono R) :=
    λ x,
      True.
  #[local] Instance mono۰validN : ValidN (mono R) :=
    λ n x,
      True.
  #[local] Program Instance mono۰op : Op (mono R) :=
    λ x1 x2,
      x1 ++ x2.
  #[local] Instance mono۰pcore : PCore (mono R) :=
    Some.

  #[local] Lemma mono𑁒cmra_mixin :
    CmraMixin (mono R).
  Proof.
    apply: discrete_cmra_mixin.
    apply ra_total_mixin; try done.
    - intros ? ?* Heq a.
      specialize (Heq a).
      rewrite !below𑁒app. naive_solver.
    - intros ?*. done.
    - intros ?* ?*. rewrite !below𑁒app. naive_solver.
    - intros ?* ?*. rewrite !below𑁒app. naive_solver.
    - intros ? ?*. rewrite below𑁒app. naive_solver.
  Qed.
  Canonical mono۰R :=
    Cmra (mono R) mono𑁒cmra_mixin.

  #[global] Instance mono𑁒cmra_total :
    CmraTotal mono۰R.
  Proof.
    rewrite /CmraTotal. auto.
  Qed.
  #[global] Instance mono𑁒core_id x :
    CoreId x.
  Proof.
    constructor. done.
  Qed.

  #[global] Instance mono𑁒cmra_discrete :
    CmraDiscrete mono۰R.
  Proof.
    split; last done. intros ?* ?*. done.
  Qed.

  #[local] Instance mono۰unit : Unit (mono R) :=
    nil.
  #[local] Lemma mono𑁒ucmra_mixin :
    UcmraMixin (mono R).
  Proof.
    split; done.
  Qed.
  Canonical mono۰UR :=
    Ucmra (mono R) mono𑁒ucmra_mixin.

  Lemma mono𑁒idemp x :
    x ⋅ x ≡ x.
  Proof.
    intros ?*. rewrite below𑁒app. naive_solver.
  Qed.

  Lemma mono𑁒included x y :
    x ≼ y ↔
    y ≡ x ⋅ y.
  Proof using SI.
    split.
    - intros (z & ->). rewrite assoc mono𑁒idemp //.
    - eexists. done.
  Qed.

  Definition mono۰principal a : mono۰UR :=
    [a].

  #[local] Lemma below𑁒principal a b :
    below a (mono۰principal b) ↔
    R a b.
  Proof.
    split.
    - intros (c & ->%list_elem_of_singleton & ?). done.
    - intros Hab. exists b.
      split; first apply list_elem_of_singleton; done.
  Qed.

  Lemma mono۰principal𑁒R𑁒opN𑁒base `{!Transitive R} n x y :
    ( ∀ b,
      b ∈ y →
        ∃ c,
        c ∈ x ∧
        R b c
    ) →
    y ⋅ x ≡{n}≡ x.
  Proof.
    intros HR. split.
    all: rewrite below𑁒app.
    - intros [(c & (d & Hd1 & Hd2)%HR & Hc2) |]; last done.
      exists d. eauto.
    - naive_solver.
  Qed.
  Lemma mono۰principal𑁒R𑁒opN `{!Transitive R} n a b :
    R a b →
    mono۰principal a ⋅ mono۰principal b ≡{n}≡ mono۰principal b.
  Proof.
    intros.
    apply mono۰principal𑁒R𑁒opN𑁒base => c.
    setoid_rewrite list_elem_of_singleton.
    naive_solver.
  Qed.
  Lemma mono۰principal𑁒R𑁒op `{!Transitive R} a b :
    R a b →
    mono۰principal a ⋅ mono۰principal b ≡ mono۰principal b.
  Proof.
    intros ? ?*.
    apply (mono۰principal𑁒R𑁒opN 0ᵢ). done.
  Qed.

  Lemma mono۰principal𑁒opN𑁒R n a b x :
    R a a →
    mono۰principal a ⋅ x ≡{n}≡ mono۰principal b →
    R a b.
  Proof.
    intros Ha HR.
    destruct (HR a) as [[z [HR1%list_elem_of_singleton HR2]] _].
    - rewrite below𑁒app below𑁒principal. auto.
    - naive_solver.
  Qed.
  Lemma mono۰principal𑁒op𑁒R' a b x :
    R a a →
    mono۰principal a ⋅ x ≡ mono۰principal b →
    R a b.
  Proof.
    intros.
    eapply (mono۰principal𑁒opN𑁒R 0ᵢ); done.
  Qed.
  Lemma mono۰principal𑁒op𑁒R `{!Reflexive R} a b x :
    mono۰principal a ⋅ x ≡ mono۰principal b →
    R a b.
  Proof.
    intros.
    eapply mono۰principal𑁒op𑁒R'; done.
  Qed.

  Lemma mono۰principal𑁒includedN `{!Reflexive R} `{!Transitive R} n a b :
    mono۰principal a ≼{n} mono۰principal b ↔
    R a b.
  Proof.
    split.
    - intros (z & Hz).
      eapply mono۰principal𑁒opN𑁒R; first done.
      rewrite Hz //.
    - intros.
      exists (mono۰principal b). rewrite mono۰principal𑁒R𑁒opN //.
  Qed.
  Lemma mono۰principal𑁒included `{!Reflexive R} `{!Transitive R} a b :
    mono۰principal a ≼ mono۰principal b ↔
    R a b.
  Proof.
    apply (mono۰principal𑁒includedN 0ᵢ).
  Qed.

  Lemma mono𑁒local_update𑁒grow `{!Transitive R} a x b:
    R a b →
    (mono۰principal a, x) ~l~> (mono۰principal b, mono۰principal b).
  Proof.
    intros Hana Hanb.
    apply local_update_unital_discrete => z _ Habz.
    split; first done. intros w. split.
    - intros (y & ->%list_elem_of_singleton & Hy2).
      exists b. split; [constructor | done].
    - intros (y & [-> | Hy1]%elem_of_cons & Hy2).
      + exists b. split; [constructor | done].
      + exists b. split; first constructor.
        specialize (Habz w) as [_ [c [->%list_elem_of_singleton Hc2]]].
        { exists y. split; last done.
          apply elem_of_app. naive_solver.
        }
        etrans; eauto.
  Qed.

  Lemma mono𑁒local_update𑁒get_frag `{!Reflexive R} `{!Transitive R} a b:
    R b a →
    (mono۰principal a, ε) ~l~> (mono۰principal a, mono۰principal b).
  Proof.
    intros Hana.
    apply local_update_unital_discrete => z _.
    rewrite left_id => <-.
    split; first done.
    apply mono𑁒included, mono۰principal𑁒included. done.
  Qed.
End relation.

#[global] Arguments mono۰R {_ _} _ : assert.
#[global] Arguments mono۰UR {_ _} _ : assert.
#[global] Arguments mono۰principal {_ _} _ _ : assert.

Section ofe_relation.
  Context {SI : sidx}.
  Context {A : ofe} {R : relation A}.

  Implicit Type a b c : A.
  Implicit Type x y z : mono R.

  #[global] Instance mono۰principal𑁒ne :
    (∀ n, Proper ((≡{n}≡) ==> (≡{n}≡) ==> (↔)) R) →
    NonExpansive (mono۰principal R).
  Proof.
    intros HR n a1 a2 Ha.
    split; rewrite !below𑁒principal Ha //.
  Qed.
  #[global] Instance mono۰principal𑁒proper :
    Proper ((≡) ==> (≡) ==> (↔)) R →
    Proper ((≡) ==> (≡)) (mono۰principal R).
  Proof.
    intros HR a1 a2 Ha.
    split; rewrite !below𑁒principal Ha //.
  Qed.

  Lemma mono۰principal𑁒inj𑁒related a b :
    mono۰principal R a ≡ mono۰principal R b →
    R a a →
    R a b.
  Proof.
    intros Hab ?.
    destruct (Hab a) as [[? [?%list_elem_of_singleton ?]] _].
    - exists a. rewrite list_elem_of_singleton //.
    - naive_solver.
  Qed.
  Lemma mono۰principal𑁒inj𑁒general a b :
    mono۰principal R a ≡ mono۰principal R b →
    R a a →
    R b b →
    (R a b → R b a → a ≡ b) →
    a ≡ b.
  Proof.
    intros ? ? ? Has.
    apply Has; apply mono۰principal𑁒inj𑁒related; auto.
  Qed.

  #[global] Instance mono۰principal𑁒inj `{!Reflexive R} `{!AntiSymm (≡) R} :
    Inj (≡) (≡) (mono۰principal R).
  Proof.
    intros ? ? ?.
    apply mono۰principal𑁒inj𑁒general; auto.
  Qed.
  #[global] Instance mono۰principal𑁒inj' `{!Reflexive R} `{!AntiSymm (≡) R} n :
    Inj (≡{n}≡) (≡{n}≡) (mono۰principal R).
  Proof.
    intros x y Hxy%discrete_iff; last apply _.
    apply equiv_dist. move: Hxy. apply inj, _.
  Qed.
End ofe_relation.

#[global] Opaque mono۰principal.
