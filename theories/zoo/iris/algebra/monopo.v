Require Export iris.algebra.cmra.
Require Import iris.algebra.local_updates.

Require Import zoo.prelude.
Require Import zoo.common.list.
Require Import zoo.options.

Definition monopo `(R : relation A) : Type :=
  list A.

Section relation.
  Context {SI : sidx}.
  Context `{R : relation A}.
  Context `{!Reflexive R} `{!Transitive R}.

  Implicit Type a b c : A.
  Implicit Type x y z : monopo R.

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

  #[local] Instance monopo۰equiv : Equiv (monopo R) :=
    λ x y,
      ∀ a,
      below a x ↔
      below a y.

  #[local] Instance monopo۰equivｰequiv :
    Equivalence monopo۰equiv.
  Proof.
    split.
    - done.
    - firstorder.
    - intros ?* Heq1 Heq2 ?. split; intros.
      + apply Heq2, Heq1. done.
      + apply Heq1, Heq2. done.
  Qed.

  #[local] Lemma monopoｰequivｰnil x :
    x ≡ [] →
    x = [].
  Proof.
    intros Hx.
    apply elem_of_nil_inv. intros a (? & []%elem_of_nil & _)%belowｰelem_of%Hx.
  Qed.

  Canonical monopo۰O :=
    discreteO (monopo R).

  #[local] Instance monopo۰valid : Valid (monopo R) :=
    λ x,
      x ≠ [] →
        ∃ a,
        Forall (flip R a) x.
  #[local] Instance monopo۰validN : ValidN (monopo R) :=
    λ _,
      valid.
  #[local] Program Instance monopo۰op : Op (monopo R) :=
    λ x1 x2,
      x1 ++ x2.
  #[local] Instance monopo۰pcore : PCore (monopo R) :=
    Some.

  #[local] Lemma monopoｰcmra_mixin :
    CmraMixin (monopo R).
  Proof.
    apply: discrete_cmra_mixin.
    apply ra_total_mixin; try done.
    - intros ? ?* Heq a.
      specialize (Heq a).
      rewrite !belowｰapp. naive_solver.
    - intros ?*. done.
    - intros x1 x2 H.
      destruct_decide (x1 = []) as -> | ?.
      + apply symmetry, monopoｰequivｰnil in H.
        intros ?* ?*. done.
      + intros (a & Ha); first done.
        exists a. apply Forall_forall. intros b (c & Hc & ?)%belowｰelem_of%H.
        eapply Forallｰelem_of in Hc; last done.
        naive_solver.
    - intros ?* ?*. rewrite !belowｰapp. naive_solver.
    - intros ?* ?*. rewrite !belowｰapp. naive_solver.
    - intros ? ?*. rewrite belowｰapp. naive_solver.
    - intros x1 x2 H.
      destruct_decide (x1 = []) as -> | ?.
      + intros ?*. done.
      + destruct H as (a & (? & _)%Forall_app).
        { eauto using appｰnotｰnil. }
        exists a. done.
  Qed.
  Canonical monopo۰R :=
    Cmra (monopo R) monopoｰcmra_mixin.

  #[global] Instance monopoｰcmra_total :
    CmraTotal monopo۰R.
  Proof.
    rewrite /CmraTotal. auto.
  Qed.
  #[global] Instance monopoｰcore_id x :
    CoreId x.
  Proof.
    constructor. done.
  Qed.

  #[global] Instance monopoｰcmra_discrete :
    CmraDiscrete monopo۰R.
  Proof.
    split; last done. intros ?* ?*. done.
  Qed.

  #[local] Instance monopo۰unit : Unit (monopo R) :=
    nil.
  #[local] Lemma monopoｰucmra_mixin :
    UcmraMixin (monopo R).
  Proof.
    split; try done. intros ?*. done.
  Qed.
  Canonical monopo۰UR :=
    Ucmra (monopo R) monopoｰucmra_mixin.

  Lemma monopoｰidemp x :
    x ⋅ x ≡ x.
  Proof.
    intros ?*. rewrite belowｰapp. naive_solver.
  Qed.

  Lemma monopoｰincluded x y :
    x ≼ y ↔
    y ≡ x ⋅ y.
  Proof using All.
    split.
    - intros (z & ->). rewrite assoc monopoｰidemp //.
    - eexists. done.
  Qed.

  Definition monopo۰principal a : monopo۰UR :=
    [a].

  #[local] Lemma belowｰprincipal a b :
    below a (monopo۰principal b) ↔
    R a b.
  Proof.
    split.
    - intros (c & ->%list_elem_of_singleton & ?). done.
    - intros Hab. exists b.
      split; first apply list_elem_of_singleton; done.
  Qed.

  Lemma monopo۰principalｰRｰopNｰbase n x y :
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
  Lemma monopo۰principalｰRｰopN n a b :
    R a b →
    monopo۰principal a ⋅ monopo۰principal b ≡{n}≡ monopo۰principal b.
  Proof.
    intros.
    apply monopo۰principalｰRｰopNｰbase => c.
    setoid_rewrite list_elem_of_singleton.
    naive_solver.
  Qed.
  Lemma monopo۰principalｰRｰop a b :
    R a b →
    monopo۰principal a ⋅ monopo۰principal b ≡ monopo۰principal b.
  Proof.
    intros ? ?*.
    apply (monopo۰principalｰRｰopN 0ᵢ). done.
  Qed.

  Lemma monopo۰principalｰopNｰR n a b x :
    R a a →
    monopo۰principal a ⋅ x ≡{n}≡ monopo۰principal b →
    R a b.
  Proof.
    intros Ha HR.
    destruct (HR a) as [[z [HR1%list_elem_of_singleton HR2]] _].
    - rewrite belowｰapp belowｰprincipal. auto.
    - naive_solver.
  Qed.
  Lemma monopo۰principalｰopｰR' a b x :
    R a a →
    monopo۰principal a ⋅ x ≡ monopo۰principal b →
    R a b.
  Proof.
    intros.
    eapply (monopo۰principalｰopNｰR 0ᵢ); done.
  Qed.
  Lemma monopo۰principalｰopｰR a b x :
    monopo۰principal a ⋅ x ≡ monopo۰principal b →
    R a b.
  Proof.
    intros.
    eapply monopo۰principalｰopｰR'; done.
  Qed.

  Lemma monopo۰principalｰvalid a :
    ✓ monopo۰principal a.
  Proof.
    exists a. rewrite Forall_singleton //.
  Qed.
  Lemma monopo۰principalｰopｰvalid a1 a2 :
    ✓ (monopo۰principal a1 ⋅ monopo۰principal a2) →
      ∃ a,
      R a1 a ∧
      R a2 a.
  Proof.
    intros (a & (? & (? & _)%Forall_cons)%Forall_cons); first done.
    naive_solver.
  Qed.

  Lemma monopo۰principalｰincludedN n a b :
    monopo۰principal a ≼{n} monopo۰principal b ↔
    R a b.
  Proof.
    split.
    - intros (z & Hz).
      eapply monopo۰principalｰopNｰR; first done.
      rewrite Hz //.
    - intros.
      exists (monopo۰principal b). rewrite monopo۰principalｰRｰopN //.
  Qed.
  Lemma monopo۰principalｰincluded a b :
    monopo۰principal a ≼ monopo۰principal b ↔
    R a b.
  Proof.
    apply (monopo۰principalｰincludedN 0ᵢ).
  Qed.

  Lemma monopoｰlocal_updateｰgrow a x b:
    R a b →
    (monopo۰principal a, x) ~l~> (monopo۰principal b, monopo۰principal b).
  Proof.
    intros Hana Hanb.
    apply local_update_unital_discrete => z _ Habz.
    split.
    - apply monopo۰principalｰvalid.
    - intros w. split.
      + intros (y & ->%list_elem_of_singleton & Hy2).
        exists b. split; [constructor | done].
      + intros (y & [-> | Hy1]%elem_of_cons & Hy2).
        * exists b. split; [constructor | done].
        * exists b. split; first constructor.
          specialize (Habz w) as [_ [c [->%list_elem_of_singleton Hc2]]].
          { exists y. split; last done.
            apply elem_of_app. naive_solver.
          }
          etrans; eauto.
  Qed.

  Lemma monopoｰlocal_updateｰget_frag a b:
    R b a →
    (monopo۰principal a, ε) ~l~> (monopo۰principal a, monopo۰principal b).
  Proof.
    intros Hana.
    apply local_update_unital_discrete => z _.
    rewrite left_id => <-.
    split.
    - apply monopo۰principalｰvalid.
    - apply monopoｰincluded, monopo۰principalｰincluded. done.
  Qed.
End relation.

#[global] Arguments monopo۰R {_ _} _ {_ _} : assert.
#[global] Arguments monopo۰UR {_ _} _ {_ _} : assert.
#[global] Arguments monopo۰principal {_ _} _ {_ _} _ : assert.

Section ofe_relation.
  Context {SI : sidx}.
  Context {A : ofe} {R : relation A}.
  Context `{!Reflexive R} `{!Transitive R}.

  Implicit Type a b c : A.
  Implicit Type x y z : monopo R.

  #[global] Instance monopo۰principalｰne :
    (∀ n, Proper ((≡{n}≡) ==> (≡{n}≡) ==> (↔)) R) →
    NonExpansive (monopo۰principal R).
  Proof.
    intros HR n a1 a2 Ha.
    split; rewrite !belowｰprincipal Ha //.
  Qed.
  #[global] Instance monopo۰principalｰproper :
    Proper ((≡) ==> (≡) ==> (↔)) R →
    Proper ((≡) ==> (≡)) (monopo۰principal R).
  Proof.
    intros HR a1 a2 Ha.
    split; rewrite !belowｰprincipal Ha //.
  Qed.

  Lemma monopo۰principalｰinjｰrelated a b :
    monopo۰principal R a ≡ monopo۰principal R b →
    R a a →
    R a b.
  Proof.
    intros Hab ?.
    destruct (Hab a) as [[? [?%list_elem_of_singleton ?]] _].
    - exists a. rewrite list_elem_of_singleton //.
    - naive_solver.
  Qed.
  Lemma monopo۰principalｰinjｰgeneral a b :
    monopo۰principal R a ≡ monopo۰principal R b →
    R a a →
    R b b →
    (R a b → R b a → a ≡ b) →
    a ≡ b.
  Proof.
    intros ? ? ? Has.
    apply Has; apply monopo۰principalｰinjｰrelated; auto.
  Qed.

  #[global] Instance monopo۰principalｰinj `{!AntiSymm (≡) R} :
    Inj (≡) (≡) (monopo۰principal R).
  Proof.
    intros ? ? ?.
    apply monopo۰principalｰinjｰgeneral; auto.
  Qed.
  #[global] Instance monopo۰principalｰinj' `{!AntiSymm (≡) R} n :
    Inj (≡{n}≡) (≡{n}≡) (monopo۰principal R).
  Proof.
    intros x y Hxy%discrete_iff; last apply _.
    apply equiv_dist. move: Hxy. apply inj, _.
  Qed.
End ofe_relation.

#[global] Opaque monopo۰principal.
