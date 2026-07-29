Require Export iris.algebra.cmra.
Require Import iris.algebra.local_updates.

Require Import zoo.prelude.
Require Import zoo.common.listne.
Require Export zoo.common.relations.
Require Import zoo.options.

Definition monopoi `(R : relation A) : Type :=
  listne A.

Section relation.
  Context {SI : sidx}.
  Context `{R : relation A}.
  Context `{!Reflexive R} `{!Transitive R}.
  Context `{!Initial R}.

  Implicit Type a b c : A.
  Implicit Type x y z : monopoi R.

  #[local] Definition below a x :=
    ∃ b,
    b ∈ x ∧
    R a b.

  #[local] Lemma belowｰelem_of a x :
    a ∈ x →
    below a x.
  Proof.
    intros Ha. exists a. done.
  Qed.
  #[local] Lemma belowｰapp a x y :
    below a (listne۰app x y) ↔
    below a x ∨ below a y.
  Proof.
    split.
    - intros (b & []%elem_of_app & ?);
        [left | right];
        exists b; done.
    - intros [(b & ? & ?) | (b & ? & ?)];
        exists b; rewrite listneｰelem_ofｰapp; auto.
  Qed.

  #[local] Instance monopoi۰equiv : Equiv (monopoi R) :=
    λ x y,
      ∀ a,
      below a x ↔
      below a y.

  #[local] Instance monopoi۰equivｰequiv :
    Equivalence monopoi۰equiv.
  Proof.
    split.
    - done.
    - firstorder.
    - intros ?* Heq1 Heq2 ?. split; intros.
      + apply Heq2, Heq1. done.
      + apply Heq1, Heq2. done.
  Qed.

  Canonical monopoi۰O :=
    discreteO (monopoi R).

  #[local] Instance monopoi۰valid : Valid (monopoi R) :=
    λ x,
      ∃ a,
      listne۰Forall (flip R a) x.
  #[local] Instance monopoi۰validN : ValidN (monopoi R) :=
    λ _,
      valid.
  #[local] Instance monopoi۰op : Op (monopoi R) :=
    λ x1 x2,
      listne۰app x1 x2.
  #[local] Instance monopoi۰pcore : PCore (monopoi R) :=
    Some.

  #[local] Lemma monopoiｰcmra_mixin :
    CmraMixin (monopoi R).
  Proof.
    apply: discrete_cmra_mixin.
    apply ra_total_mixin; try done.
    - intros ? ?* Heq a.
      specialize (Heq a).
      rewrite !belowｰapp. naive_solver.
    - intros ?*. done.
    - intros x1 x2 Heq (a & Ha).
      exists a. apply listne۰Forallｰforall.
      intros b (c & Hc & ?)%belowｰelem_of%Heq.
      eapply listne۰Forallｰelem_of in Hc; last done.
      naive_solver.
    - intros ?* ?*. rewrite !belowｰapp. naive_solver.
    - intros ?* ?*. rewrite !belowｰapp. naive_solver.
    - intros ? ?*. rewrite belowｰapp. naive_solver.
    - intros x1 x2 H.
      destruct H as (a & (? & _)%listne۰Forallｰapp).
      exists a. done.
  Qed.
  Canonical monopoi۰R :=
    Cmra (monopoi R) monopoiｰcmra_mixin.

  #[global] Instance monopoiｰcmra_total :
    CmraTotal monopoi۰R.
  Proof.
    rewrite /CmraTotal. auto.
  Qed.
  #[global] Instance monopoiｰcore_id x :
    CoreId x.
  Proof.
    constructor. done.
  Qed.

  #[global] Instance monopoiｰcmra_discrete :
    CmraDiscrete monopoi۰R.
  Proof.
    split; last done. intros ?* ?*. done.
  Qed.

  #[local] Program Definition principal a : monopoi R :=
    [a].
  Next Obligation.
    done.
  Qed.

  #[local] Instance monopoi۰unit : Unit (monopoi R) :=
    principal initial.
  #[local] Lemma monopoiｰucmra_mixin :
    UcmraMixin (monopoi R).
  Proof.
    split; last done.
    - exists initial.
      rewrite listne۰Forallｰsingleton //.
    - intros x a.
      split.
      + intros (b & [->%listneｰelem_ofｰsingleton | Hb]%listneｰelem_ofｰapp & ?).
        * destruct (listneｰnon_empty x) as (b & Hb).
          exists b. split; first done.
          trans initial; first done.
          apply initialｰlb.
        * exists b. auto.
      + intros (b & Hb & ?).
        exists b. split; last done.
        apply listneｰelem_ofｰapp. auto.
  Qed.
  Canonical monopoi۰UR :=
    Ucmra (monopoi R) monopoiｰucmra_mixin.

  Lemma monopoiｰidemp x :
    x ⋅ x ≡ x.
  Proof.
    intros ?*. rewrite belowｰapp. naive_solver.
  Qed.

  Lemma monopoiｰincluded x y :
    x ≼ y ↔
    y ≡ x ⋅ y.
  Proof using All.
    split.
    - intros (z & ->). rewrite assoc monopoiｰidemp //.
    - eexists. done.
  Qed.

  Definition monopoi۰principal : A → monopoi۰UR :=
    principal.

  #[local] Lemma belowｰprincipal a b :
    below a (monopoi۰principal b) ↔
    R a b.
  Proof.
    split.
    - intros (? & ->%listneｰelem_ofｰsingleton & ?). done.
    - intros Hab. exists b.
      split; first apply listneｰelem_ofｰsingleton; done.
  Qed.

  Lemma monopoi۰principalｰRｰopNｰbase n x y :
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
  Lemma monopoi۰principalｰRｰopN n a b :
    R a b →
    monopoi۰principal a ⋅ monopoi۰principal b ≡{n}≡ monopoi۰principal b.
  Proof.
    intros.
    apply monopoi۰principalｰRｰopNｰbase => c.
    setoid_rewrite listneｰelem_ofｰsingleton.
    naive_solver.
  Qed.
  Lemma monopoi۰principalｰRｰop a b :
    R a b →
    monopoi۰principal a ⋅ monopoi۰principal b ≡ monopoi۰principal b.
  Proof.
    intros ? ?*.
    apply (monopoi۰principalｰRｰopN 0ᵢ). done.
  Qed.

  Lemma monopoi۰principalｰopNｰR n a b x :
    R a a →
    monopoi۰principal a ⋅ x ≡{n}≡ monopoi۰principal b →
    R a b.
  Proof.
    intros Ha HR.
    destruct (HR a) as [[z [HR1%listneｰelem_ofｰsingleton HR2]] _].
    - rewrite belowｰapp belowｰprincipal. auto.
    - naive_solver.
  Qed.
  Lemma monopoi۰principalｰopｰR' a b x :
    R a a →
    monopoi۰principal a ⋅ x ≡ monopoi۰principal b →
    R a b.
  Proof.
    intros.
    eapply (monopoi۰principalｰopNｰR 0ᵢ); done.
  Qed.
  Lemma monopoi۰principalｰopｰR a b x :
    monopoi۰principal a ⋅ x ≡ monopoi۰principal b →
    R a b.
  Proof.
    intros.
    eapply monopoi۰principalｰopｰR'; done.
  Qed.

  Lemma monopoi۰principalｰvalid a :
    ✓ monopoi۰principal a.
  Proof.
    exists a. rewrite listne۰Forallｰsingleton //.
  Qed.
  Lemma monopoi۰principalｰopｰvalid a1 a2 :
    ✓ (monopoi۰principal a1 ⋅ monopoi۰principal a2) →
      ∃ a,
      R a1 a ∧
      R a2 a.
  Proof.
    intros (a & (? & (? & _)%Forall_cons)%Forall_cons).
    naive_solver.
  Qed.

  Lemma monopoi۰principalｰincludedN n a b :
    monopoi۰principal a ≼{n} monopoi۰principal b ↔
    R a b.
  Proof.
    split.
    - intros (z & Hz).
      eapply monopoi۰principalｰopNｰR; first done.
      rewrite Hz //.
    - intros.
      exists (monopoi۰principal b). rewrite monopoi۰principalｰRｰopN //.
  Qed.
  Lemma monopoi۰principalｰincluded a b :
    monopoi۰principal a ≼ monopoi۰principal b ↔
    R a b.
  Proof.
    apply (monopoi۰principalｰincludedN 0ᵢ).
  Qed.

  Lemma monopoiｰlocal_updateｰgrow a x b:
    R a b →
    (monopoi۰principal a, x) ~l~> (monopoi۰principal b, monopoi۰principal b).
  Proof.
    intros Hana Hanb.
    apply local_update_unital_discrete => z _ Habz.
    split.
    - apply monopoi۰principalｰvalid.
    - intros w. split.
      + intros (y & ->%listneｰelem_ofｰsingleton & Hy2).
        exists b. split; [constructor | done].
      + intros (y & [-> | Hy1]%elem_of_cons & Hy2).
        * exists b. split; [constructor | done].
        * exists b. split; first constructor.
          specialize (Habz w) as [_ [c [->%listneｰelem_ofｰsingleton Hc2]]].
          { exists y. split; last done.
            apply elem_of_app. naive_solver.
          }
          etrans; eauto.
  Qed.

  Lemma monopoiｰlocal_updateｰget_frag a b:
    R b a →
    (monopoi۰principal a, ε) ~l~> (monopoi۰principal a, monopoi۰principal b).
  Proof.
    intros Hana.
    apply local_update_unital_discrete => z _.
    rewrite left_id => <-.
    split.
    - apply monopoi۰principalｰvalid.
    - apply monopoiｰincluded, monopoi۰principalｰincluded. done.
  Qed.
End relation.

#[global] Arguments monopoi۰R {_ _} _ {_ _ _} : assert.
#[global] Arguments monopoi۰UR {_ _} _ {_ _ _} : assert.
#[global] Arguments monopoi۰principal {_ _} _ {_ _ _} _ : assert.

Section ofe_relation.
  Context {SI : sidx}.
  Context {A : ofe} {R : relation A}.
  Context `{!Reflexive R} `{!Transitive R}.
  Context `{!Initial R}.

  Implicit Type a b c : A.
  Implicit Type x y z : monopoi R.

  #[global] Instance monopoi۰principalｰne :
    (∀ n, Proper ((≡{n}≡) ==> (≡{n}≡) ==> (↔)) R) →
    NonExpansive (monopoi۰principal R).
  Proof.
    intros HR n a1 a2 Ha.
    split; rewrite !belowｰprincipal Ha //.
  Qed.
  #[global] Instance monopoi۰principalｰproper :
    Proper ((≡) ==> (≡) ==> (↔)) R →
    Proper ((≡) ==> (≡)) (monopoi۰principal R).
  Proof.
    intros HR a1 a2 Ha.
    split; rewrite !belowｰprincipal Ha //.
  Qed.

  Lemma monopoi۰principalｰinjｰrelated a b :
    monopoi۰principal R a ≡ monopoi۰principal R b →
    R a a →
    R a b.
  Proof.
    intros Hab ?.
    destruct (Hab a) as [[? [?%listneｰelem_ofｰsingleton ?]] _].
    - exists a. rewrite listneｰelem_ofｰsingleton //.
    - naive_solver.
  Qed.
  Lemma monopoi۰principalｰinjｰgeneral a b :
    monopoi۰principal R a ≡ monopoi۰principal R b →
    R a a →
    R b b →
    (R a b → R b a → a ≡ b) →
    a ≡ b.
  Proof.
    intros ? ? ? Has.
    apply Has; apply monopoi۰principalｰinjｰrelated; auto.
  Qed.

  #[global] Instance monopoi۰principalｰinj `{!AntiSymm (≡) R} :
    Inj (≡) (≡) (monopoi۰principal R).
  Proof.
    intros ? ? ?.
    apply monopoi۰principalｰinjｰgeneral; auto.
  Qed.
  #[global] Instance monopoi۰principalｰinj' `{!AntiSymm (≡) R} n :
    Inj (≡{n}≡) (≡{n}≡) (monopoi۰principal R).
  Proof.
    intros x y Hxy%discrete_iff; last apply _.
    apply equiv_dist. move: Hxy. apply inj, _.
  Qed.
End ofe_relation.

#[global] Opaque monopoi۰principal.
