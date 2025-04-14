From iris.algebra Require Export
  cmra.
From iris.algebra Require Import
  local_updates.

From zoo Require Import
  prelude.
From zoo.common Require Import
  list.
From zoo Require Import
  options.

Definition monopo `(R : relation A) : Type :=
  list A.

Section relation.
  Context `{R : relation A}.
  Context `{!Reflexive R} `{!Transitive R}.

  Implicit Types a b c : A.
  Implicit Types x y z : monopo R.

  #[local] Definition below a x :=
    ∃ b,
    b ∈ x ∧
    R a b.

  #[local] Lemma below_elem_of a x :
    a ∈ x →
    below a x.
  Proof.
    intros Ha. exists a. done.
  Qed.
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

  #[local] Instance monopo_equiv : Equiv (monopo R) :=
    λ x y,
      ∀ a,
      below a x ↔
      below a y.

  #[local] Instance monopo_equiv_equiv :
    Equivalence monopo_equiv.
  Proof.
    split.
    - done.
    - firstorder.
    - intros ?* Heq1 Heq2 ?. split; intros.
      + apply Heq2, Heq1. done.
      + apply Heq1, Heq2. done.
  Qed.

  #[local] Lemma monopo_equiv_nil x :
    x ≡ [] →
    x = [].
  Proof.
    intros Hx.
    apply elem_of_nil_inv. intros a (? & []%elem_of_nil & _)%below_elem_of%Hx.
  Qed.

  Canonical monopo_O :=
    discreteO (monopo R).

  #[local] Instance monopo_valid : Valid (monopo R) :=
    λ x,
      x ≠ [] →
        ∃ a,
        Forall (flip R a) x.
  #[local] Instance monopo_validN : ValidN (monopo R) :=
    λ _,
      valid.
  #[local] Program Instance monopo_op : Op (monopo R) :=
    λ x1 x2,
      x1 ++ x2.
  #[local] Instance monopo_pcore : PCore (monopo R) :=
    Some.

  #[local] Lemma monopo_cmra_mixin :
    CmraMixin (monopo R).
  Proof.
    apply: discrete_cmra_mixin.
    apply ra_total_mixin; try done.
    - intros ? ?* Heq a.
      specialize (Heq a).
      rewrite !below_app. naive_solver.
    - intros ?*. done.
    - intros x1 x2 H.
      destruct (decide (x1 = [])) as [-> |].
      + apply symmetry, monopo_equiv_nil in H.
        intros ?* ?*. done.
      + intros (a & Ha); first done.
        exists a. apply Forall_forall. intros b (c & Hc & ?)%below_elem_of%H.
        eapply Forall_elem_of in Hc; last done.
        naive_solver.
    - intros ?* ?*. rewrite !below_app. naive_solver.
    - intros ?* ?*. rewrite !below_app. naive_solver.
    - intros ? ?*. rewrite below_app. naive_solver.
    - intros x1 x2 H.
      destruct (decide (x1 = [])) as [-> |].
      + intros ?*. done.
      + destruct H as (a & (? & _)%Forall_app).
        { apply app_not_nil_l. done. }
        exists a. done.
  Qed.
  Canonical monopo_R :=
    Cmra (monopo R) monopo_cmra_mixin.

  #[global] Instance monopo_cmra_total :
    CmraTotal monopo_R.
  Proof.
    rewrite /CmraTotal. auto.
  Qed.
  #[global] Instance monopo_core_id x :
    CoreId x.
  Proof.
    constructor. done.
  Qed.

  #[global] Instance monopo_cmra_discrete :
    CmraDiscrete monopo_R.
  Proof.
    split; last done. intros ?* ?*. done.
  Qed.

  #[local] Instance monopo_unit : Unit (monopo R) :=
    nil.
  #[local] Lemma auth_ucmra_mixin :
    UcmraMixin (monopo R).
  Proof.
    split; try done. intros ?*. done.
  Qed.
  Canonical monopo_UR :=
    Ucmra (monopo R) auth_ucmra_mixin.

  Lemma monopo_idemp x :
    x ⋅ x ≡ x.
  Proof.
    intros ?*. rewrite below_app. naive_solver.
  Qed.

  Lemma monopo_included x y :
    x ≼ y ↔
    y ≡ x ⋅ y.
  Proof.
    split.
    - intros (z & ->). rewrite assoc monopo_idemp //.
    - eexists. done.
  Qed.

  Definition monopo_principal a : monopo_UR :=
    [a].

  #[local] Lemma below_principal a b :
    below a (monopo_principal b) ↔
    R a b.
  Proof.
    split.
    - intros (c & ->%elem_of_list_singleton & ?). done.
    - intros Hab. exists b.
      split; first apply elem_of_list_singleton; done.
  Qed.

  Lemma monopo_principal_R_opN_base n x y :
    (∀ b, b ∈ y → ∃ c, c ∈ x ∧ R b c) →
    y ⋅ x ≡{n}≡ x.
  Proof.
    intros HR. split.
    all: rewrite below_app.
    - intros [(c & (d & Hd1 & Hd2)%HR & Hc2) |]; last done.
      exists d. eauto.
    - naive_solver.
  Qed.
  Lemma monopo_principal_R_opN n a b :
    R a b →
    monopo_principal a ⋅ monopo_principal b ≡{n}≡ monopo_principal b.
  Proof.
    intros.
    apply monopo_principal_R_opN_base => c.
    setoid_rewrite elem_of_list_singleton. naive_solver.
  Qed.
  Lemma monopo_principal_R_op a b :
    R a b →
    monopo_principal a ⋅ monopo_principal b ≡ monopo_principal b.
  Proof.
    intros ? ?*. apply (monopo_principal_R_opN 0). done.
  Qed.

  Lemma monopo_principal_opN_R n a b x :
    R a a →
    monopo_principal a ⋅ x ≡{n}≡ monopo_principal b →
    R a b.
  Proof.
    intros Ha HR.
    destruct (HR a) as [[z [HR1%elem_of_list_singleton HR2]] _].
    - rewrite below_app below_principal. auto.
    - naive_solver.
  Qed.
  Lemma monopo_principal_op_R' a b x :
    R a a →
    monopo_principal a ⋅ x ≡ monopo_principal b →
    R a b.
  Proof.
    intros. eapply (monopo_principal_opN_R 0); done.
  Qed.
  Lemma monopo_principal_op_R a b x :
    monopo_principal a ⋅ x ≡ monopo_principal b →
    R a b.
  Proof.
    intros. eapply monopo_principal_op_R'; done.
  Qed.

  Lemma monopo_principal_valid a :
    ✓ monopo_principal a.
  Proof.
    exists a. rewrite Forall_singleton //.
  Qed.
  Lemma monopo_principal_op_valid a1 a2 :
    ✓ (monopo_principal a1 ⋅ monopo_principal a2) →
      ∃ a,
      R a1 a ∧
      R a2 a.
  Proof.
    intros (a & (? & (? & _)%Forall_cons)%Forall_cons); first done.
    naive_solver.
  Qed.

  Lemma monopo_principal_includedN n a b :
    monopo_principal a ≼{n} monopo_principal b ↔
    R a b.
  Proof.
    split.
    - intros (z & Hz).
      eapply monopo_principal_opN_R; first done.
      rewrite Hz //.
    - intros.
      exists (monopo_principal b). rewrite monopo_principal_R_opN //.
  Qed.
  Lemma monopo_principal_included a b :
    monopo_principal a ≼ monopo_principal b ↔
    R a b.
  Proof.
    apply (monopo_principal_includedN 0).
  Qed.

  Lemma monopo_local_update_grow a x b:
    R a b →
    (monopo_principal a, x) ~l~> (monopo_principal b, monopo_principal b).
  Proof.
    intros Hana Hanb.
    apply local_update_unital_discrete => z _ Habz.
    split.
    - apply monopo_principal_valid.
    - intros w. split.
      + intros (y & ->%elem_of_list_singleton & Hy2).
        exists b. split; [constructor | done].
      + intros (y & [-> | Hy1]%elem_of_cons & Hy2).
        * exists b. split; [constructor | done].
        * exists b. split; first constructor.
          specialize (Habz w) as [_ [c [->%elem_of_list_singleton Hc2]]].
          { exists y. split; last done.
            apply elem_of_app. naive_solver.
          }
          etrans; eauto.
  Qed.

  Lemma monopo_local_update_get_frag a b:
    R b a →
    (monopo_principal a, ε) ~l~> (monopo_principal a, monopo_principal b).
  Proof.
    intros Hana.
    apply local_update_unital_discrete => z _.
    rewrite left_id => <-.
    split.
    - apply monopo_principal_valid.
    - apply monopo_included, monopo_principal_included. done.
  Qed.
End relation.

#[global] Arguments monopo_R {_} _ {_ _} : assert.
#[global] Arguments monopo_UR {_} _ {_ _} : assert.
#[global] Arguments monopo_principal {_} _ {_ _} _ : assert.

Section ofe_relation.
  Context {A : ofe} {R : relation A}.
  Context `{!Reflexive R} `{!Transitive R}.

  Implicit Types a b c : A.
  Implicit Types x y z : monopo R.

  #[global] Instance monopo_principal_ne :
    (∀ n, Proper ((≡{n}≡) ==> (≡{n}≡) ==> (↔)) R) →
    NonExpansive (monopo_principal R).
  Proof.
    intros HR n a1 a2 Ha.
    split; rewrite !below_principal Ha //.
  Qed.
  #[global] Instance monopo_principal_proper :
    Proper ((≡) ==> (≡) ==> (↔)) R →
    Proper ((≡) ==> (≡)) (monopo_principal R).
  Proof.
    intros HR a1 a2 Ha.
    split; rewrite !below_principal Ha //.
  Qed.

  Lemma monopo_principal_inj_related a b :
    monopo_principal R a ≡ monopo_principal R b →
    R a a →
    R a b.
  Proof.
    intros Hab ?.
    destruct (Hab a) as [[? [?%elem_of_list_singleton ?]] _].
    - exists a. rewrite elem_of_list_singleton //.
    - naive_solver.
  Qed.
  Lemma monopo_principal_inj_general a b :
    monopo_principal R a ≡ monopo_principal R b →
    R a a →
    R b b →
    (R a b → R b a → a ≡ b) →
    a ≡ b.
  Proof.
    intros ? ? ? Has.
    apply Has; apply monopo_principal_inj_related; auto.
  Qed.

  #[global] Instance monopo_principal_inj `{!AntiSymm (≡) R} :
    Inj (≡) (≡) (monopo_principal R).
  Proof.
    intros ? ? ?.
    apply monopo_principal_inj_general; auto.
  Qed.
  #[global] Instance monopo_principal_inj' `{!AntiSymm (≡) R} n :
    Inj (≡{n}≡) (≡{n}≡) (monopo_principal R).
  Proof.
    intros x y Hxy%discrete_iff; last apply _.
    apply equiv_dist. move: Hxy. apply inj, _.
  Qed.
End ofe_relation.

#[global] Opaque monopo_principal.
