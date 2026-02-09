From iris.algebra Require Export
  cmra.
From iris.algebra Require Import
  local_updates.

From zoo Require Import
  prelude.
From zoo.common Require Import
  listne.
From zoo.common Require Export
  relations.
From zoo Require Import
  options.

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

  #[local] Lemma below_elem_of a x :
    a ∈ x →
    below a x.
  Proof.
    intros Ha. exists a. done.
  Qed.
  #[local] Lemma below_app a x y :
    below a (listne_app x y) ↔
    below a x ∨ below a y.
  Proof.
    split.
    - intros (b & []%elem_of_app & ?);
        [left | right];
        exists b; done.
    - intros [(b & ? & ?) | (b & ? & ?)];
        exists b; rewrite listne_elem_of_app; auto.
  Qed.

  #[local] Instance monopoi_equiv : Equiv (monopoi R) :=
    λ x y,
      ∀ a,
      below a x ↔
      below a y.

  #[local] Instance monopoi_equiv_equiv :
    Equivalence monopoi_equiv.
  Proof.
    split.
    - done.
    - firstorder.
    - intros ?* Heq1 Heq2 ?. split; intros.
      + apply Heq2, Heq1. done.
      + apply Heq1, Heq2. done.
  Qed.

  Canonical monopoi_O :=
    discreteO (monopoi R).

  #[local] Instance monopoi_valid : Valid (monopoi R) :=
    λ x,
      ∃ a,
      listne_Forall (flip R a) x.
  #[local] Instance monopoi_validN : ValidN (monopoi R) :=
    λ _,
      valid.
  #[local] Instance monopoi_op : Op (monopoi R) :=
    λ x1 x2,
      listne_app x1 x2.
  #[local] Instance monopoi_pcore : PCore (monopoi R) :=
    Some.

  #[local] Lemma monopoi_cmra_mixin :
    CmraMixin (monopoi R).
  Proof.
    apply: discrete_cmra_mixin.
    apply ra_total_mixin; try done.
    - intros ? ?* Heq a.
      specialize (Heq a).
      rewrite !below_app. naive_solver.
    - intros ?*. done.
    - intros x1 x2 Heq (a & Ha).
      exists a. apply listne_Forall_forall.
      intros b (c & Hc & ?)%below_elem_of%Heq.
      eapply listne_Forall_elem_of in Hc; last done.
      naive_solver.
    - intros ?* ?*. rewrite !below_app. naive_solver.
    - intros ?* ?*. rewrite !below_app. naive_solver.
    - intros ? ?*. rewrite below_app. naive_solver.
    - intros x1 x2 H.
      destruct H as (a & (? & _)%listne_Forall_app).
      exists a. done.
  Qed.
  Canonical monopoi_R :=
    Cmra (monopoi R) monopoi_cmra_mixin.

  #[global] Instance monopoi_cmra_total :
    CmraTotal monopoi_R.
  Proof.
    rewrite /CmraTotal. auto.
  Qed.
  #[global] Instance monopoi_core_id x :
    CoreId x.
  Proof.
    constructor. done.
  Qed.

  #[global] Instance monopoi_cmra_discrete :
    CmraDiscrete monopoi_R.
  Proof.
    split; last done. intros ?* ?*. done.
  Qed.

  #[local] Program Definition principal a : monopoi R :=
    [a].
  Next Obligation.
    done.
  Qed.

  #[local] Instance monopoi_unit : Unit (monopoi R) :=
    principal initial.
  #[local] Lemma monopoi_ucmra_mixin :
    UcmraMixin (monopoi R).
  Proof.
    split; last done.
    - exists initial.
      rewrite listne_Forall_singleton //.
    - intros x a.
      split.
      + intros (b & [->%listne_elem_of_singleton | Hb]%listne_elem_of_app & ?).
        * destruct (listne_non_empty x) as (b & Hb).
          exists b. split; first done.
          trans initial; first done.
          apply initial_lb.
        * exists b. auto.
      + intros (b & Hb & ?).
        exists b. split; last done.
        apply listne_elem_of_app. auto.
  Qed.
  Canonical monopoi_UR :=
    Ucmra (monopoi R) monopoi_ucmra_mixin.

  Lemma monopoi_idemp x :
    x ⋅ x ≡ x.
  Proof.
    intros ?*. rewrite below_app. naive_solver.
  Qed.

  Lemma monopoi_included x y :
    x ≼ y ↔
    y ≡ x ⋅ y.
  Proof using All.
    split.
    - intros (z & ->). rewrite assoc monopoi_idemp //.
    - eexists. done.
  Qed.

  Definition monopoi_principal : A → monopoi_UR :=
    principal.

  #[local] Lemma below_principal a b :
    below a (monopoi_principal b) ↔
    R a b.
  Proof.
    split.
    - intros (? & ->%listne_elem_of_singleton & ?). done.
    - intros Hab. exists b.
      split; first apply listne_elem_of_singleton; done.
  Qed.

  Lemma monopoi_principal_R_opN_base n x y :
    ( ∀ b,
      b ∈ y →
        ∃ c,
        c ∈ x ∧
        R b c
    ) →
    y ⋅ x ≡{n}≡ x.
  Proof.
    intros HR. split.
    all: rewrite below_app.
    - intros [(c & (d & Hd1 & Hd2)%HR & Hc2) |]; last done.
      exists d. eauto.
    - naive_solver.
  Qed.
  Lemma monopoi_principal_R_opN n a b :
    R a b →
    monopoi_principal a ⋅ monopoi_principal b ≡{n}≡ monopoi_principal b.
  Proof.
    intros.
    apply monopoi_principal_R_opN_base => c.
    setoid_rewrite listne_elem_of_singleton.
    naive_solver.
  Qed.
  Lemma monopoi_principal_R_op a b :
    R a b →
    monopoi_principal a ⋅ monopoi_principal b ≡ monopoi_principal b.
  Proof.
    intros ? ?*.
    apply (monopoi_principal_R_opN 0ᵢ). done.
  Qed.

  Lemma monopoi_principal_opN_R n a b x :
    R a a →
    monopoi_principal a ⋅ x ≡{n}≡ monopoi_principal b →
    R a b.
  Proof.
    intros Ha HR.
    destruct (HR a) as [[z [HR1%listne_elem_of_singleton HR2]] _].
    - rewrite below_app below_principal. auto.
    - naive_solver.
  Qed.
  Lemma monopoi_principal_op_R' a b x :
    R a a →
    monopoi_principal a ⋅ x ≡ monopoi_principal b →
    R a b.
  Proof.
    intros.
    eapply (monopoi_principal_opN_R 0ᵢ); done.
  Qed.
  Lemma monopoi_principal_op_R a b x :
    monopoi_principal a ⋅ x ≡ monopoi_principal b →
    R a b.
  Proof.
    intros.
    eapply monopoi_principal_op_R'; done.
  Qed.

  Lemma monopoi_principal_valid a :
    ✓ monopoi_principal a.
  Proof.
    exists a. rewrite listne_Forall_singleton //.
  Qed.
  Lemma monopoi_principal_op_valid a1 a2 :
    ✓ (monopoi_principal a1 ⋅ monopoi_principal a2) →
      ∃ a,
      R a1 a ∧
      R a2 a.
  Proof.
    intros (a & (? & (? & _)%Forall_cons)%Forall_cons).
    naive_solver.
  Qed.

  Lemma monopoi_principal_includedN n a b :
    monopoi_principal a ≼{n} monopoi_principal b ↔
    R a b.
  Proof.
    split.
    - intros (z & Hz).
      eapply monopoi_principal_opN_R; first done.
      rewrite Hz //.
    - intros.
      exists (monopoi_principal b). rewrite monopoi_principal_R_opN //.
  Qed.
  Lemma monopoi_principal_included a b :
    monopoi_principal a ≼ monopoi_principal b ↔
    R a b.
  Proof.
    apply (monopoi_principal_includedN 0ᵢ).
  Qed.

  Lemma monopoi_local_update_grow a x b:
    R a b →
    (monopoi_principal a, x) ~l~> (monopoi_principal b, monopoi_principal b).
  Proof.
    intros Hana Hanb.
    apply local_update_unital_discrete => z _ Habz.
    split.
    - apply monopoi_principal_valid.
    - intros w. split.
      + intros (y & ->%listne_elem_of_singleton & Hy2).
        exists b. split; [constructor | done].
      + intros (y & [-> | Hy1]%elem_of_cons & Hy2).
        * exists b. split; [constructor | done].
        * exists b. split; first constructor.
          specialize (Habz w) as [_ [c [->%listne_elem_of_singleton Hc2]]].
          { exists y. split; last done.
            apply elem_of_app. naive_solver.
          }
          etrans; eauto.
  Qed.

  Lemma monopoi_local_update_get_frag a b:
    R b a →
    (monopoi_principal a, ε) ~l~> (monopoi_principal a, monopoi_principal b).
  Proof.
    intros Hana.
    apply local_update_unital_discrete => z _.
    rewrite left_id => <-.
    split.
    - apply monopoi_principal_valid.
    - apply monopoi_included, monopoi_principal_included. done.
  Qed.
End relation.

#[global] Arguments monopoi_R {_ _} _ {_ _ _} : assert.
#[global] Arguments monopoi_UR {_ _} _ {_ _ _} : assert.
#[global] Arguments monopoi_principal {_ _} _ {_ _ _} _ : assert.

Section ofe_relation.
  Context {SI : sidx}.
  Context {A : ofe} {R : relation A}.
  Context `{!Reflexive R} `{!Transitive R}.
  Context `{!Initial R}.

  Implicit Types a b c : A.
  Implicit Types x y z : monopoi R.

  #[global] Instance monopoi_principal_ne :
    (∀ n, Proper ((≡{n}≡) ==> (≡{n}≡) ==> (↔)) R) →
    NonExpansive (monopoi_principal R).
  Proof.
    intros HR n a1 a2 Ha.
    split; rewrite !below_principal Ha //.
  Qed.
  #[global] Instance monopoi_principal_proper :
    Proper ((≡) ==> (≡) ==> (↔)) R →
    Proper ((≡) ==> (≡)) (monopoi_principal R).
  Proof.
    intros HR a1 a2 Ha.
    split; rewrite !below_principal Ha //.
  Qed.

  Lemma monopoi_principal_inj_related a b :
    monopoi_principal R a ≡ monopoi_principal R b →
    R a a →
    R a b.
  Proof.
    intros Hab ?.
    destruct (Hab a) as [[? [?%listne_elem_of_singleton ?]] _].
    - exists a. rewrite listne_elem_of_singleton //.
    - naive_solver.
  Qed.
  Lemma monopoi_principal_inj_general a b :
    monopoi_principal R a ≡ monopoi_principal R b →
    R a a →
    R b b →
    (R a b → R b a → a ≡ b) →
    a ≡ b.
  Proof.
    intros ? ? ? Has.
    apply Has; apply monopoi_principal_inj_related; auto.
  Qed.

  #[global] Instance monopoi_principal_inj `{!AntiSymm (≡) R} :
    Inj (≡) (≡) (monopoi_principal R).
  Proof.
    intros ? ? ?.
    apply monopoi_principal_inj_general; auto.
  Qed.
  #[global] Instance monopoi_principal_inj' `{!AntiSymm (≡) R} n :
    Inj (≡{n}≡) (≡{n}≡) (monopoi_principal R).
  Proof.
    intros x y Hxy%discrete_iff; last apply _.
    apply equiv_dist. move: Hxy. apply inj, _.
  Qed.
End ofe_relation.

#[global] Opaque monopoi_principal.
