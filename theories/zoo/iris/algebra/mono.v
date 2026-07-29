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

  #[local] Lemma belowｰapp a x y :
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

  #[local] Instance mono۰equivｰequiv :
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

  #[local] Lemma monoｰcmra_mixin :
    CmraMixin (mono R).
  Proof.
    apply: discrete_cmra_mixin.
    apply ra_total_mixin; try done.
    - intros ? ?* Heq a.
      specialize (Heq a).
      rewrite !belowｰapp. naive_solver.
    - intros ?*. done.
    - intros ?* ?*. rewrite !belowｰapp. naive_solver.
    - intros ?* ?*. rewrite !belowｰapp. naive_solver.
    - intros ? ?*. rewrite belowｰapp. naive_solver.
  Qed.
  Canonical mono۰R :=
    Cmra (mono R) monoｰcmra_mixin.

  #[global] Instance monoｰcmra_total :
    CmraTotal mono۰R.
  Proof.
    rewrite /CmraTotal. auto.
  Qed.
  #[global] Instance monoｰcore_id x :
    CoreId x.
  Proof.
    constructor. done.
  Qed.

  #[global] Instance monoｰcmra_discrete :
    CmraDiscrete mono۰R.
  Proof.
    split; last done. intros ?* ?*. done.
  Qed.

  #[local] Instance mono۰unit : Unit (mono R) :=
    nil.
  #[local] Lemma monoｰucmra_mixin :
    UcmraMixin (mono R).
  Proof.
    split; done.
  Qed.
  Canonical mono۰UR :=
    Ucmra (mono R) monoｰucmra_mixin.

  Lemma monoｰidemp x :
    x ⋅ x ≡ x.
  Proof.
    intros ?*. rewrite belowｰapp. naive_solver.
  Qed.

  Lemma monoｰincluded x y :
    x ≼ y ↔
    y ≡ x ⋅ y.
  Proof using SI.
    split.
    - intros (z & ->). rewrite assoc monoｰidemp //.
    - eexists. done.
  Qed.

  Definition mono۰principal a : mono۰UR :=
    [a].

  #[local] Lemma belowｰprincipal a b :
    below a (mono۰principal b) ↔
    R a b.
  Proof.
    split.
    - intros (c & ->%list_elem_of_singleton & ?). done.
    - intros Hab. exists b.
      split; first apply list_elem_of_singleton; done.
  Qed.

  Lemma mono۰principalｰRｰopNｰbase `{!Transitive R} n x y :
    ( ∀ b,
      b ∈ y →
        ∃ c,
        c ∈ x ∧
        R b c
    ) →
    y ⋅ x ≡{n}≡ x.
  Proof.
    intros HR. split.
    all: rewrite belowｰapp.
    - intros [(c & (d & Hd1 & Hd2)%HR & Hc2) |]; last done.
      exists d. eauto.
    - naive_solver.
  Qed.
  Lemma mono۰principalｰRｰopN `{!Transitive R} n a b :
    R a b →
    mono۰principal a ⋅ mono۰principal b ≡{n}≡ mono۰principal b.
  Proof.
    intros.
    apply mono۰principalｰRｰopNｰbase => c.
    setoid_rewrite list_elem_of_singleton.
    naive_solver.
  Qed.
  Lemma mono۰principalｰRｰop `{!Transitive R} a b :
    R a b →
    mono۰principal a ⋅ mono۰principal b ≡ mono۰principal b.
  Proof.
    intros ? ?*.
    apply (mono۰principalｰRｰopN 0ᵢ). done.
  Qed.

  Lemma mono۰principalｰopNｰR n a b x :
    R a a →
    mono۰principal a ⋅ x ≡{n}≡ mono۰principal b →
    R a b.
  Proof.
    intros Ha HR.
    destruct (HR a) as [[z [HR1%list_elem_of_singleton HR2]] _].
    - rewrite belowｰapp belowｰprincipal. auto.
    - naive_solver.
  Qed.
  Lemma mono۰principalｰopｰR' a b x :
    R a a →
    mono۰principal a ⋅ x ≡ mono۰principal b →
    R a b.
  Proof.
    intros.
    eapply (mono۰principalｰopNｰR 0ᵢ); done.
  Qed.
  Lemma mono۰principalｰopｰR `{!Reflexive R} a b x :
    mono۰principal a ⋅ x ≡ mono۰principal b →
    R a b.
  Proof.
    intros.
    eapply mono۰principalｰopｰR'; done.
  Qed.

  Lemma mono۰principalｰincludedN `{!Reflexive R} `{!Transitive R} n a b :
    mono۰principal a ≼{n} mono۰principal b ↔
    R a b.
  Proof.
    split.
    - intros (z & Hz).
      eapply mono۰principalｰopNｰR; first done.
      rewrite Hz //.
    - intros.
      exists (mono۰principal b). rewrite mono۰principalｰRｰopN //.
  Qed.
  Lemma mono۰principalｰincluded `{!Reflexive R} `{!Transitive R} a b :
    mono۰principal a ≼ mono۰principal b ↔
    R a b.
  Proof.
    apply (mono۰principalｰincludedN 0ᵢ).
  Qed.

  Lemma monoｰlocal_updateｰgrow `{!Transitive R} a x b:
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

  Lemma monoｰlocal_updateｰget_frag `{!Reflexive R} `{!Transitive R} a b:
    R b a →
    (mono۰principal a, ε) ~l~> (mono۰principal a, mono۰principal b).
  Proof.
    intros Hana.
    apply local_update_unital_discrete => z _.
    rewrite left_id => <-.
    split; first done.
    apply monoｰincluded, mono۰principalｰincluded. done.
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

  #[global] Instance mono۰principalｰne :
    (∀ n, Proper ((≡{n}≡) ==> (≡{n}≡) ==> (↔)) R) →
    NonExpansive (mono۰principal R).
  Proof.
    intros HR n a1 a2 Ha.
    split; rewrite !belowｰprincipal Ha //.
  Qed.
  #[global] Instance mono۰principalｰproper :
    Proper ((≡) ==> (≡) ==> (↔)) R →
    Proper ((≡) ==> (≡)) (mono۰principal R).
  Proof.
    intros HR a1 a2 Ha.
    split; rewrite !belowｰprincipal Ha //.
  Qed.

  Lemma mono۰principalｰinjｰrelated a b :
    mono۰principal R a ≡ mono۰principal R b →
    R a a →
    R a b.
  Proof.
    intros Hab ?.
    destruct (Hab a) as [[? [?%list_elem_of_singleton ?]] _].
    - exists a. rewrite list_elem_of_singleton //.
    - naive_solver.
  Qed.
  Lemma mono۰principalｰinjｰgeneral a b :
    mono۰principal R a ≡ mono۰principal R b →
    R a a →
    R b b →
    (R a b → R b a → a ≡ b) →
    a ≡ b.
  Proof.
    intros ? ? ? Has.
    apply Has; apply mono۰principalｰinjｰrelated; auto.
  Qed.

  #[global] Instance mono۰principalｰinj `{!Reflexive R} `{!AntiSymm (≡) R} :
    Inj (≡) (≡) (mono۰principal R).
  Proof.
    intros ? ? ?.
    apply mono۰principalｰinjｰgeneral; auto.
  Qed.
  #[global] Instance mono۰principalｰinj' `{!Reflexive R} `{!AntiSymm (≡) R} n :
    Inj (≡{n}≡) (≡{n}≡) (mono۰principal R).
  Proof.
    intros x y Hxy%discrete_iff; last apply _.
    apply equiv_dist. move: Hxy. apply inj, _.
  Qed.
End ofe_relation.

#[global] Opaque mono۰principal.
