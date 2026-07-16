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

  Implicit Types a b c : A.
  Implicit Types x y z : monopoi R.

  #[local] Definition below a x :=
    ∃ b,
    b ∈ x ∧
    R a b.

  #[local] Lemma below𑁒elem_of a x :
    a ∈ x →
    below a x.
  Proof.
    intros Ha. exists a. done.
  Qed.
  #[local] Lemma below𑁒app a x y :
    below a (listne۰app x y) ↔
    below a x ∨ below a y.
  Proof.
    split.
    - intros (b & []%elem_of_app & ?);
        [left | right];
        exists b; done.
    - intros [(b & ? & ?) | (b & ? & ?)];
        exists b; rewrite listne𑁒elem_of𑁒app; auto.
  Qed.

  #[local] Instance monopoi۰equiv : Equiv (monopoi R) :=
    λ x y,
      ∀ a,
      below a x ↔
      below a y.

  #[local] Instance monopoi۰equiv𑁒equiv :
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

  #[local] Lemma monopoi𑁒cmra_mixin :
    CmraMixin (monopoi R).
  Proof.
    apply: discrete_cmra_mixin.
    apply ra_total_mixin; try done.
    - intros ? ?* Heq a.
      specialize (Heq a).
      rewrite !below𑁒app. naive_solver.
    - intros ?*. done.
    - intros x1 x2 Heq (a & Ha).
      exists a. apply listne۰Forall𑁒forall.
      intros b (c & Hc & ?)%below𑁒elem_of%Heq.
      eapply listne۰Forall𑁒elem_of in Hc; last done.
      naive_solver.
    - intros ?* ?*. rewrite !below𑁒app. naive_solver.
    - intros ?* ?*. rewrite !below𑁒app. naive_solver.
    - intros ? ?*. rewrite below𑁒app. naive_solver.
    - intros x1 x2 H.
      destruct H as (a & (? & _)%listne۰Forall𑁒app).
      exists a. done.
  Qed.
  Canonical monopoi۰R :=
    Cmra (monopoi R) monopoi𑁒cmra_mixin.

  #[global] Instance monopoi𑁒cmra_total :
    CmraTotal monopoi۰R.
  Proof.
    rewrite /CmraTotal. auto.
  Qed.
  #[global] Instance monopoi𑁒core_id x :
    CoreId x.
  Proof.
    constructor. done.
  Qed.

  #[global] Instance monopoi𑁒cmra_discrete :
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
  #[local] Lemma monopoi𑁒ucmra_mixin :
    UcmraMixin (monopoi R).
  Proof.
    split; last done.
    - exists initial.
      rewrite listne۰Forall𑁒singleton //.
    - intros x a.
      split.
      + intros (b & [->%listne𑁒elem_of𑁒singleton | Hb]%listne𑁒elem_of𑁒app & ?).
        * destruct (listne𑁒non_empty x) as (b & Hb).
          exists b. split; first done.
          trans initial; first done.
          apply initial𑁒lb.
        * exists b. auto.
      + intros (b & Hb & ?).
        exists b. split; last done.
        apply listne𑁒elem_of𑁒app. auto.
  Qed.
  Canonical monopoi۰UR :=
    Ucmra (monopoi R) monopoi𑁒ucmra_mixin.

  Lemma monopoi𑁒idemp x :
    x ⋅ x ≡ x.
  Proof.
    intros ?*. rewrite below𑁒app. naive_solver.
  Qed.

  Lemma monopoi𑁒included x y :
    x ≼ y ↔
    y ≡ x ⋅ y.
  Proof using All.
    split.
    - intros (z & ->). rewrite assoc monopoi𑁒idemp //.
    - eexists. done.
  Qed.

  Definition monopoi۰principal : A → monopoi۰UR :=
    principal.

  #[local] Lemma below𑁒principal a b :
    below a (monopoi۰principal b) ↔
    R a b.
  Proof.
    split.
    - intros (? & ->%listne𑁒elem_of𑁒singleton & ?). done.
    - intros Hab. exists b.
      split; first apply listne𑁒elem_of𑁒singleton; done.
  Qed.

  Lemma monopoi۰principal𑁒R𑁒opN𑁒base n x y :
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
  Lemma monopoi۰principal𑁒R𑁒opN n a b :
    R a b →
    monopoi۰principal a ⋅ monopoi۰principal b ≡{n}≡ monopoi۰principal b.
  Proof.
    intros.
    apply monopoi۰principal𑁒R𑁒opN𑁒base => c.
    setoid_rewrite listne𑁒elem_of𑁒singleton.
    naive_solver.
  Qed.
  Lemma monopoi۰principal𑁒R𑁒op a b :
    R a b →
    monopoi۰principal a ⋅ monopoi۰principal b ≡ monopoi۰principal b.
  Proof.
    intros ? ?*.
    apply (monopoi۰principal𑁒R𑁒opN 0ᵢ). done.
  Qed.

  Lemma monopoi۰principal𑁒opN𑁒R n a b x :
    R a a →
    monopoi۰principal a ⋅ x ≡{n}≡ monopoi۰principal b →
    R a b.
  Proof.
    intros Ha HR.
    destruct (HR a) as [[z [HR1%listne𑁒elem_of𑁒singleton HR2]] _].
    - rewrite below𑁒app below𑁒principal. auto.
    - naive_solver.
  Qed.
  Lemma monopoi۰principal𑁒op𑁒R' a b x :
    R a a →
    monopoi۰principal a ⋅ x ≡ monopoi۰principal b →
    R a b.
  Proof.
    intros.
    eapply (monopoi۰principal𑁒opN𑁒R 0ᵢ); done.
  Qed.
  Lemma monopoi۰principal𑁒op𑁒R a b x :
    monopoi۰principal a ⋅ x ≡ monopoi۰principal b →
    R a b.
  Proof.
    intros.
    eapply monopoi۰principal𑁒op𑁒R'; done.
  Qed.

  Lemma monopoi۰principal𑁒valid a :
    ✓ monopoi۰principal a.
  Proof.
    exists a. rewrite listne۰Forall𑁒singleton //.
  Qed.
  Lemma monopoi۰principal𑁒op𑁒valid a1 a2 :
    ✓ (monopoi۰principal a1 ⋅ monopoi۰principal a2) →
      ∃ a,
      R a1 a ∧
      R a2 a.
  Proof.
    intros (a & (? & (? & _)%Forall_cons)%Forall_cons).
    naive_solver.
  Qed.

  Lemma monopoi۰principal𑁒includedN n a b :
    monopoi۰principal a ≼{n} monopoi۰principal b ↔
    R a b.
  Proof.
    split.
    - intros (z & Hz).
      eapply monopoi۰principal𑁒opN𑁒R; first done.
      rewrite Hz //.
    - intros.
      exists (monopoi۰principal b). rewrite monopoi۰principal𑁒R𑁒opN //.
  Qed.
  Lemma monopoi۰principal𑁒included a b :
    monopoi۰principal a ≼ monopoi۰principal b ↔
    R a b.
  Proof.
    apply (monopoi۰principal𑁒includedN 0ᵢ).
  Qed.

  Lemma monopoi𑁒local_update𑁒grow a x b:
    R a b →
    (monopoi۰principal a, x) ~l~> (monopoi۰principal b, monopoi۰principal b).
  Proof.
    intros Hana Hanb.
    apply local_update_unital_discrete => z _ Habz.
    split.
    - apply monopoi۰principal𑁒valid.
    - intros w. split.
      + intros (y & ->%listne𑁒elem_of𑁒singleton & Hy2).
        exists b. split; [constructor | done].
      + intros (y & [-> | Hy1]%elem_of_cons & Hy2).
        * exists b. split; [constructor | done].
        * exists b. split; first constructor.
          specialize (Habz w) as [_ [c [->%listne𑁒elem_of𑁒singleton Hc2]]].
          { exists y. split; last done.
            apply elem_of_app. naive_solver.
          }
          etrans; eauto.
  Qed.

  Lemma monopoi𑁒local_update𑁒get_frag a b:
    R b a →
    (monopoi۰principal a, ε) ~l~> (monopoi۰principal a, monopoi۰principal b).
  Proof.
    intros Hana.
    apply local_update_unital_discrete => z _.
    rewrite left_id => <-.
    split.
    - apply monopoi۰principal𑁒valid.
    - apply monopoi𑁒included, monopoi۰principal𑁒included. done.
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

  Implicit Types a b c : A.
  Implicit Types x y z : monopoi R.

  #[global] Instance monopoi۰principal𑁒ne :
    (∀ n, Proper ((≡{n}≡) ==> (≡{n}≡) ==> (↔)) R) →
    NonExpansive (monopoi۰principal R).
  Proof.
    intros HR n a1 a2 Ha.
    split; rewrite !below𑁒principal Ha //.
  Qed.
  #[global] Instance monopoi۰principal𑁒proper :
    Proper ((≡) ==> (≡) ==> (↔)) R →
    Proper ((≡) ==> (≡)) (monopoi۰principal R).
  Proof.
    intros HR a1 a2 Ha.
    split; rewrite !below𑁒principal Ha //.
  Qed.

  Lemma monopoi۰principal𑁒inj𑁒related a b :
    monopoi۰principal R a ≡ monopoi۰principal R b →
    R a a →
    R a b.
  Proof.
    intros Hab ?.
    destruct (Hab a) as [[? [?%listne𑁒elem_of𑁒singleton ?]] _].
    - exists a. rewrite listne𑁒elem_of𑁒singleton //.
    - naive_solver.
  Qed.
  Lemma monopoi۰principal𑁒inj𑁒general a b :
    monopoi۰principal R a ≡ monopoi۰principal R b →
    R a a →
    R b b →
    (R a b → R b a → a ≡ b) →
    a ≡ b.
  Proof.
    intros ? ? ? Has.
    apply Has; apply monopoi۰principal𑁒inj𑁒related; auto.
  Qed.

  #[global] Instance monopoi۰principal𑁒inj `{!AntiSymm (≡) R} :
    Inj (≡) (≡) (monopoi۰principal R).
  Proof.
    intros ? ? ?.
    apply monopoi۰principal𑁒inj𑁒general; auto.
  Qed.
  #[global] Instance monopoi۰principal𑁒inj' `{!AntiSymm (≡) R} n :
    Inj (≡{n}≡) (≡{n}≡) (monopoi۰principal R).
  Proof.
    intros x y Hxy%discrete_iff; last apply _.
    apply equiv_dist. move: Hxy. apply inj, _.
  Qed.
End ofe_relation.

#[global] Opaque monopoi۰principal.
