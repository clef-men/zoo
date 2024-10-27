From iris.algebra Require Export
  cmra.
From iris.algebra Require Import
  updates
  local_updates.
From iris.prelude Require Import
  options.

#[local] Arguments pcore _ _ !_ /.
#[local] Arguments cmra_pcore _ !_ /.
#[local] Arguments validN _ _ _ !_ /.
#[local] Arguments valid _ _  !_ /.
#[local] Arguments cmra_validN _ _ !_ /.
#[local] Arguments cmra_valid _  !_ /.

(* Given a preorder relation R on a type A we construct a resource algebra mra R
   and an injection principal : A -> mra R such that:
   [R x y] iff [principal x ≼ principal y]
   where ≼ is the extension order of mra R resource algebra. This is exactly
   what the lemma [principal_included] shows.

   This resource algebra is useful for reasoning about monotonicity.
   See the following paper for more details:

   Reasoning About Monotonicity in Separation Logic
   Amin Timany and Lars Birkedal
   in Certified Programs and Proofs (CPP) 2021
*)

Definition mra {A : Type} (R : relation A) : Type :=
  list A.
Definition principal {A : Type} (R : relation A) (a : A) : mra R :=
  [a].

Section ofe.
  Context {A : Type} {R : relation A}.

  Implicit Types a b : A.
  Implicit Types x y : mra R.

  #[local] Definition below (a : A) (x : mra R) :=
    ∃ b, b ∈ x ∧ R a b.

  #[local] Lemma below_app a x y :
    below a (x ++ y) ↔ below a x ∨ below a y.
  Proof.
    split.
    - intros (b & [|]%elem_of_app & ?); [left|right]; exists b; eauto.
    - intros [(b & ? & ?)|(b & ? & ?)]; exists b; rewrite elem_of_app; eauto.
  Qed.

  #[local] Lemma below_principal a b :
    below a (principal R b) ↔ R a b.
  Proof.
    split.
    - intros (c & ->%elem_of_list_singleton & ?); done.
    - intros Hab; exists b; split; first apply elem_of_list_singleton; done.
  Qed.

  #[local] Instance mra_equiv : Equiv (mra R) :=
    λ x y,
      ∀ a, below a x ↔ below a y.

  #[local] Instance mra_equiv_equiv :
    Equivalence mra_equiv.
  Proof.
    split; [by firstorder|by firstorder|].
    intros ??? Heq1 Heq2 ?; split; intros ?;
      [apply Heq2; apply Heq1|apply Heq1; apply Heq2]; done.
  Qed.

  Canonical mraO :=
    discreteO (mra R).
End ofe.

#[global] Arguments mraO [_] _.

Section cmra.
  Context {A : Type} {R : relation A}.

  Implicit Types a b : A.
  Implicit Types x y : mra R.

  #[local] Instance mra_valid : Valid (mra R) :=
    λ x, True.
  #[local] Instance mra_validN : ValidN (mra R) :=
    λ n x, True.
  #[local] Program Instance mra_op : Op (mra R) :=
    λ x y, x ++ y.
  #[local] Instance mra_pcore : PCore (mra R) :=
    Some.

  Lemma mra_cmra_mixin :
    CmraMixin (mra R).
  Proof.
    apply discrete_cmra_mixin; first apply _.
    apply ra_total_mixin.
    - eauto.
    - intros ??? Heq a; specialize (Heq a); rewrite !below_app; firstorder.
    - intros ?; done.
    - done.
    - intros ????; rewrite !below_app; firstorder.
    - intros ???; rewrite !below_app; firstorder.
    - rewrite /core /pcore /=; intros ??; rewrite below_app; firstorder.
    - done.
    - intros ? ? [? ?]; eexists _; done.
    - done.
  Qed.

  Canonical mraR : cmra :=
    Cmra (mra R) mra_cmra_mixin.

  #[global] Instance mra_cmra_total :
    CmraTotal mraR.
  Proof.
    rewrite /CmraTotal; eauto.
  Qed.
  #[global] Instance mra_core_id (x : mra R) :
    CoreId x.
  Proof.
    by constructor.
  Qed.

  #[global] Instance mra_cmra_discrete :
    CmraDiscrete mraR.
  Proof.
    split; last done. intros ? ?; done.
  Qed.

  #[local] Instance mra_unit : Unit (mra R) :=
    @nil A.
  Lemma auth_ucmra_mixin :
    UcmraMixin (mra R).
  Proof.
    split; done.
  Qed.

  Canonical mraUR :=
    Ucmra (mra R) auth_ucmra_mixin.

  Lemma mra_idemp (x : mra R) :
    x ⋅ x ≡ x.
  Proof.
    intros a; rewrite below_app; naive_solver.
  Qed.

  Lemma mra_included (x y : mra R) :
    x ≼ y ↔ y ≡ x ⋅ y.
  Proof.
    split; [|by intros ?; exists y].
    intros [z ->]; rewrite assoc mra_idemp; done.
  Qed.

  Lemma principal_R_opN_base `{!Transitive R} n x y :
    (∀ b, b ∈ y → ∃ c, c ∈ x ∧ R b c) →
    y ⋅ x ≡{n}≡ x.
  Proof.
    intros HR; split; rewrite /op /mra_op below_app; [|by firstorder].
    intros [(c & (d & Hd1 & Hd2)%HR & Hc2)|]; [|done].
    exists d; split; [|transitivity c]; done.
  Qed.

  Lemma principal_R_opN `{!Transitive R} n a b :
    R a b →
    principal R a ⋅ principal R b ≡{n}≡ principal R b.
  Proof.
    intros; apply principal_R_opN_base; intros c; rewrite /principal.
    setoid_rewrite elem_of_list_singleton => ->; eauto.
  Qed.

  Lemma principal_R_op `{!Transitive R} a b :
    R a b →
    principal R a ⋅ principal R b ≡ principal R b.
  Proof.
    by intros ? ?; apply (principal_R_opN 0).
  Qed.

  Lemma principal_op_RN n a b x :
    R a a →
    principal R a ⋅ x ≡{n}≡ principal R b →
    R a b.
  Proof.
    intros Ha HR.
    destruct (HR a) as [[z [HR1%elem_of_list_singleton HR2]] _];
      last by subst; eauto.
    rewrite /op /mra_op /principal below_app below_principal; auto.
  Qed.

  Lemma principal_op_R' a b x :
    R a a →
    principal R a ⋅ x ≡ principal R b →
    R a b.
  Proof.
    intros ? ?; eapply (principal_op_RN 0); eauto.
  Qed.

  Lemma principal_op_R `{!Reflexive R} a b x :
    principal R a ⋅ x ≡ principal R b →
    R a b.
  Proof.
    intros; eapply principal_op_R'; eauto.
  Qed.

  Lemma principal_includedN `{!PreOrder R} n a b :
    principal R a ≼{n} principal R b ↔ R a b.
  Proof.
    split.
    - intros [z Hz]; eapply principal_op_RN; first done. by rewrite Hz.
    - intros ?; exists (principal R b); rewrite principal_R_opN; eauto.
  Qed.

  Lemma principal_included `{!PreOrder R} a b :
    principal R a ≼ principal R b ↔ R a b.
  Proof.
    apply (principal_includedN 0).
  Qed.

  Lemma mra_local_update_grow `{!Transitive R} a x b:
    R a b →
    (principal R a, x) ~l~> (principal R b, principal R b).
  Proof.
    intros Hana Hanb.
    apply local_update_unital_discrete.
    intros z _ Habz.
    split; first done.
    intros w; split.
    - intros (y & ->%elem_of_list_singleton & Hy2).
      exists b; split; first constructor; done.
    - intros (y & [->|Hy1]%elem_of_cons & Hy2).
      + exists b; split; first constructor; done.
      + exists b; split; first constructor.
        specialize (Habz w) as [_ [c [->%elem_of_list_singleton Hc2]]].
        { exists y; split; first (by apply elem_of_app; right); eauto. }
        etrans; eauto.
  Qed.

  Lemma mra_local_update_get_frag `{!PreOrder R} a b:
    R b a →
    (principal R a, ε) ~l~> (principal R a, principal R b).
  Proof.
    intros Hana.
    apply local_update_unital_discrete.
    intros z _; rewrite left_id; intros <-.
    split; first done.
    apply mra_included; by apply principal_included.
  Qed.
End cmra.

#[global] Arguments mraR {_} _.
#[global] Arguments mraUR {_} _.

Section mra_over_ofe.
  Context {A : ofe} {R : relation A}.

  Implicit Types a b : A.
  Implicit Types x y : mra R.

  #[global] Instance principal_ne :
    (∀ n, Proper ((≡{n}≡) ==> (≡{n}≡) ==> (↔)) R) →
    NonExpansive (principal R).
  Proof.
    intros ? n a1 a2 Ha; split; rewrite !below_principal !Ha //.
  Qed.
  #[global] Instance principal_proper :
    (∀ n, Proper ((≡{n}≡) ==> (≡{n}≡) ==> (↔)) R) →
    Proper ((≡) ==> (≡)) (principal R).
  Proof.
    intros ?. apply: ne_proper.
  Qed.

  Lemma principal_inj_related a b :
    principal R a ≡ principal R b →
    R a a →
    R a b.
  Proof.
    intros Hab ?.
    destruct (Hab a) as [[? [?%elem_of_list_singleton ?]] _];
      last by subst; auto.
    exists a; rewrite /principal elem_of_list_singleton; done.
  Qed.

  Lemma principal_inj_general a b :
    principal R a ≡ principal R b →
    R a a →
    R b b →
    (R a b → R b a → a ≡ b) →
    a ≡ b.
  Proof.
    intros ??? Has; apply Has; apply principal_inj_related; auto.
  Qed.

  #[global] Instance principal_inj `{!Reflexive R} `{!AntiSymm (≡) R} :
    Inj (≡) (≡) (principal R).
  Proof.
    intros ???; apply principal_inj_general; auto.
  Qed.
  #[global] Instance principal_inj' `{!Reflexive R} `{!AntiSymm (≡) R} n :
    Inj (≡{n}≡) (≡{n}≡) (principal R).
  Proof.
    intros x y Hxy%discrete_iff; last apply _.
    eapply equiv_dist; revert Hxy; apply inj; apply _.
  Qed.
End mra_over_ofe.

#[global] Opaque principal.
