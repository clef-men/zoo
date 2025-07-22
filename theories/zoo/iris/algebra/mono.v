From iris.algebra Require Export
  cmra.
From iris.algebra Require Import
  local_updates.

From zoo Require Import
  prelude.
From zoo Require Import
  options.

Definition mono `(R : relation A) : Type :=
  list A.

Section relation.
  Context {SI : sidx}.
  Context `{R : relation A}.

  Implicit Types a b c : A.
  Implicit Types x y z : mono R.

  #[local] Definition below a x :=
    ∃ b,
    b ∈ x ∧
    R a b.

  #[local] Lemma below_app a x y :
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

  #[local] Instance mono_equiv : Equiv (mono R) :=
    λ x y,
      ∀ a,
      below a x ↔
      below a y.

  #[local] Instance mono_equiv_equiv :
    Equivalence mono_equiv.
  Proof.
    split.
    - done.
    - firstorder.
    - intros ?* Heq1 Heq2 ?. split; intros.
      + apply Heq2, Heq1. done.
      + apply Heq1, Heq2. done.
  Qed.

  Canonical mono_O :=
    discreteO (mono R).

  #[local] Instance mono_valid : Valid (mono R) :=
    λ x,
      True.
  #[local] Instance mono_validN : ValidN (mono R) :=
    λ n x,
      True.
  #[local] Program Instance mono_op : Op (mono R) :=
    λ x1 x2,
      x1 ++ x2.
  #[local] Instance mono_pcore : PCore (mono R) :=
    Some.

  #[local] Lemma mono_cmra_mixin :
    CmraMixin (mono R).
  Proof.
    apply: discrete_cmra_mixin.
    apply ra_total_mixin; try done.
    - intros ? ?* Heq a.
      specialize (Heq a).
      rewrite !below_app. naive_solver.
    - intros ?*. done.
    - intros ?* ?*. rewrite !below_app. naive_solver.
    - intros ?* ?*. rewrite !below_app. naive_solver.
    - intros ? ?*. rewrite below_app. naive_solver.
  Qed.
  Canonical mono_R :=
    Cmra (mono R) mono_cmra_mixin.

  #[global] Instance mono_cmra_total :
    CmraTotal mono_R.
  Proof.
    rewrite /CmraTotal. auto.
  Qed.
  #[global] Instance mono_core_id x :
    CoreId x.
  Proof.
    constructor. done.
  Qed.

  #[global] Instance mono_cmra_discrete :
    CmraDiscrete mono_R.
  Proof.
    split; last done. intros ?* ?*. done.
  Qed.

  #[local] Instance mono_unit : Unit (mono R) :=
    nil.
  #[local] Lemma auth_ucmra_mixin :
    UcmraMixin (mono R).
  Proof.
    split; done.
  Qed.
  Canonical mono_UR :=
    Ucmra (mono R) auth_ucmra_mixin.

  Lemma mono_idemp x :
    x ⋅ x ≡ x.
  Proof.
    intros ?*. rewrite below_app. naive_solver.
  Qed.

  Lemma mono_included x y :
    x ≼ y ↔
    y ≡ x ⋅ y.
  Proof using SI.
    split.
    - intros (z & ->). rewrite assoc mono_idemp //.
    - eexists. done.
  Qed.

  Definition mono_principal a : mono_UR :=
    [a].

  #[local] Lemma below_principal a b :
    below a (mono_principal b) ↔
    R a b.
  Proof.
    split.
    - intros (c & ->%elem_of_list_singleton & ?). done.
    - intros Hab. exists b.
      split; first apply elem_of_list_singleton; done.
  Qed.

  Lemma mono_principal_R_opN_base `{!Transitive R} n x y :
    (∀ b, b ∈ y → ∃ c, c ∈ x ∧ R b c) →
    y ⋅ x ≡{n}≡ x.
  Proof.
    intros HR. split.
    all: rewrite below_app.
    - intros [(c & (d & Hd1 & Hd2)%HR & Hc2) |]; last done.
      exists d. eauto.
    - naive_solver.
  Qed.
  Lemma mono_principal_R_opN `{!Transitive R} n a b :
    R a b →
    mono_principal a ⋅ mono_principal b ≡{n}≡ mono_principal b.
  Proof.
    intros.
    apply mono_principal_R_opN_base => c.
    setoid_rewrite elem_of_list_singleton. naive_solver.
  Qed.
  Lemma mono_principal_R_op `{!Transitive R} a b :
    R a b →
    mono_principal a ⋅ mono_principal b ≡ mono_principal b.
  Proof.
    intros ? ?*.
    apply (mono_principal_R_opN 0ᵢ). done.
  Qed.

  Lemma mono_principal_opN_R n a b x :
    R a a →
    mono_principal a ⋅ x ≡{n}≡ mono_principal b →
    R a b.
  Proof.
    intros Ha HR.
    destruct (HR a) as [[z [HR1%elem_of_list_singleton HR2]] _].
    - rewrite below_app below_principal. auto.
    - naive_solver.
  Qed.
  Lemma mono_principal_op_R' a b x :
    R a a →
    mono_principal a ⋅ x ≡ mono_principal b →
    R a b.
  Proof.
    intros.
    eapply (mono_principal_opN_R 0ᵢ); done.
  Qed.
  Lemma mono_principal_op_R `{!Reflexive R} a b x :
    mono_principal a ⋅ x ≡ mono_principal b →
    R a b.
  Proof.
    intros.
    eapply mono_principal_op_R'; done.
  Qed.

  Lemma mono_principal_includedN `{!Reflexive R} `{!Transitive R} n a b :
    mono_principal a ≼{n} mono_principal b ↔
    R a b.
  Proof.
    split.
    - intros (z & Hz).
      eapply mono_principal_opN_R; first done.
      rewrite Hz //.
    - intros.
      exists (mono_principal b). rewrite mono_principal_R_opN //.
  Qed.
  Lemma mono_principal_included `{!Reflexive R} `{!Transitive R} a b :
    mono_principal a ≼ mono_principal b ↔
    R a b.
  Proof.
    apply (mono_principal_includedN 0ᵢ).
  Qed.

  Lemma mono_local_update_grow `{!Transitive R} a x b:
    R a b →
    (mono_principal a, x) ~l~> (mono_principal b, mono_principal b).
  Proof.
    intros Hana Hanb.
    apply local_update_unital_discrete => z _ Habz.
    split; first done. intros w. split.
    - intros (y & ->%elem_of_list_singleton & Hy2).
      exists b. split; [constructor | done].
    - intros (y & [-> | Hy1]%elem_of_cons & Hy2).
      + exists b. split; [constructor | done].
      + exists b. split; first constructor.
        specialize (Habz w) as [_ [c [->%elem_of_list_singleton Hc2]]].
        { exists y. split; last done.
          apply elem_of_app. naive_solver.
        }
        etrans; eauto.
  Qed.

  Lemma mono_local_update_get_frag `{!Reflexive R} `{!Transitive R} a b:
    R b a →
    (mono_principal a, ε) ~l~> (mono_principal a, mono_principal b).
  Proof.
    intros Hana.
    apply local_update_unital_discrete => z _.
    rewrite left_id => <-.
    split; first done.
    apply mono_included, mono_principal_included. done.
  Qed.
End relation.

#[global] Arguments mono_R {_ _} _ : assert.
#[global] Arguments mono_UR {_ _} _ : assert.
#[global] Arguments mono_principal {_ _} _ _ : assert.

Section ofe_relation.
  Context {SI : sidx}.
  Context {A : ofe} {R : relation A}.

  Implicit Types a b c : A.
  Implicit Types x y z : mono R.

  #[global] Instance mono_principal_ne :
    (∀ n, Proper ((≡{n}≡) ==> (≡{n}≡) ==> (↔)) R) →
    NonExpansive (mono_principal R).
  Proof.
    intros HR n a1 a2 Ha.
    split; rewrite !below_principal Ha //.
  Qed.
  #[global] Instance mono_principal_proper :
    Proper ((≡) ==> (≡) ==> (↔)) R →
    Proper ((≡) ==> (≡)) (mono_principal R).
  Proof.
    intros HR a1 a2 Ha.
    split; rewrite !below_principal Ha //.
  Qed.

  Lemma mono_principal_inj_related a b :
    mono_principal R a ≡ mono_principal R b →
    R a a →
    R a b.
  Proof.
    intros Hab ?.
    destruct (Hab a) as [[? [?%elem_of_list_singleton ?]] _].
    - exists a. rewrite elem_of_list_singleton //.
    - naive_solver.
  Qed.
  Lemma mono_principal_inj_general a b :
    mono_principal R a ≡ mono_principal R b →
    R a a →
    R b b →
    (R a b → R b a → a ≡ b) →
    a ≡ b.
  Proof.
    intros ? ? ? Has.
    apply Has; apply mono_principal_inj_related; auto.
  Qed.

  #[global] Instance mono_principal_inj `{!Reflexive R} `{!AntiSymm (≡) R} :
    Inj (≡) (≡) (mono_principal R).
  Proof.
    intros ? ? ?.
    apply mono_principal_inj_general; auto.
  Qed.
  #[global] Instance mono_principal_inj' `{!Reflexive R} `{!AntiSymm (≡) R} n :
    Inj (≡{n}≡) (≡{n}≡) (mono_principal R).
  Proof.
    intros x y Hxy%discrete_iff; last apply _.
    apply equiv_dist. move: Hxy. apply inj, _.
  Qed.
End ofe_relation.

#[global] Opaque mono_principal.
