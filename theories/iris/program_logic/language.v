From iris.algebra Require Import
  ofe.

From zoo Require Import
  prelude.
From zoo Require Import
  options.

Section language_mixin.
  Context {expr val state observation : Type}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).
  Context (prim_step : expr → state → list observation → expr → state → list expr → Prop).

  Record LanguageMixin := {
    mixin_to_of_val v :
      to_val (of_val v) = Some v ;
    mixin_of_to_val e v :
      to_val e = Some v →
      of_val v = e ;
    mixin_val_stuck e σ κ e' σ' es :
      prim_step e σ κ e' σ' es →
      to_val e = None ;
  }.
End language_mixin.

Structure language := {
  expr : Type ;
  val : Type ;
  state : Type ;
  observation : Type ;
  of_val : val → expr ;
  to_val : expr → option val ;
  prim_step : expr → state → list observation → expr → state → list expr → Prop ;
  language_mixin : LanguageMixin of_val to_val prim_step ;
}.
#[global] Arguments Build_language {_ _ _ _ _ _ _} _ : assert.
#[global] Arguments of_val {_} _ : assert.
#[global] Arguments to_val {_} _ : assert.
#[global] Arguments prim_step {_} _ _ _ _ _ _ : assert.

Implicit Types Λ : language.

Declare Scope expr_scope.
Delimit Scope expr_scope with E.

Declare Scope val_scope.
Delimit Scope val_scope with V.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Canonical state_O Λ :=
  leibnizO (state Λ).
Canonical val_O Λ :=
  leibnizO (val Λ).
Canonical expr_O Λ :=
  leibnizO (expr Λ).

Definition config Λ : Type :=
  list (expr Λ) * state Λ.

Class LanguageCtx {Λ} (K : expr Λ → expr Λ) := {
  fill_not_val e :
    to_val e = None →
    to_val (K e) = None ;
  fill_step e1 σ1 κ e2 σ2 es :
    prim_step e1 σ1 κ e2 σ2 es →
    prim_step (K e1) σ1 κ (K e2) σ2 es ;
  fill_step_inv e1' σ1 κ e2 σ2 es :
    to_val e1' = None →
    prim_step (K e1') σ1 κ e2 σ2 es →
      ∃ e2',
      e2 = K e2' ∧
      prim_step e1' σ1 κ e2' σ2 es ;
}.

#[global] Instance language_ctx_id Λ :
  LanguageCtx (@id (expr Λ)).
Proof.
  constructor; naive_solver.
Qed.

Section language.
  Context {Λ}.

  Implicit Types e : expr Λ.
  Implicit Types v : val Λ.
  Implicit Types σ : state Λ.
  Implicit Types ρ : config Λ.
  Implicit Types κ : list (observation Λ).

  Lemma to_of_val v :
    to_val (of_val v) = Some v.
  Proof.
    apply language_mixin.
  Qed.
  Lemma of_to_val e v :
    to_val e = Some v →
    of_val v = e.
  Proof.
    apply language_mixin.
  Qed.
  Lemma val_stuck e σ κ e' σ' es :
    prim_step e σ κ e' σ' es →
    to_val e = None.
  Proof.
    apply language_mixin.
  Qed.

  Definition reducible e σ :=
    ∃ κ e' σ' es,
    prim_step e σ κ e' σ' es.
  Definition reducible_no_obs e σ :=
    ∃ e' σ' es,
    prim_step e σ [] e' σ' es.
  Definition irreducible e σ :=
    ∀ κ e' σ' es,
    ¬ prim_step e σ κ e' σ' es.
  Definition stuck e σ :=
    to_val e = None ∧
    irreducible e σ.
  Definition not_stuck e σ :=
    is_Some (to_val e) ∨
    reducible e σ.

  Class Atomic e :=
    atomic σ e' κ σ' es :
      prim_step e σ κ e' σ' es →
      is_Some (to_val e').

  Inductive step ρ1 κ ρ2 : Prop :=
    | step_atomic e1 σ1 e2 σ2 es t1 t2 :
        ρ1 = (t1 ++ e1 :: t2, σ1) →
        ρ2 = (t1 ++ e2 :: t2 ++ es, σ2) →
        prim_step e1 σ1 κ e2 σ2 es →
        step ρ1 κ ρ2.
  #[local] Hint Constructors step : core.

  Inductive nsteps : nat → config Λ → list (observation Λ) → config Λ → Prop :=
    | nsteps_refl ρ :
       nsteps 0 ρ [] ρ
    | nsteps_l n ρ1 ρ2 ρ3 κ κs :
       step ρ1 κ ρ2 →
       nsteps n ρ2 κs ρ3 →
       nsteps (S n) ρ1 (κ ++ κs) ρ3.
  #[local] Hint Constructors nsteps : core.

  Lemma of_to_val_flip v e :
    of_val v = e →
    to_val e = Some v.
  Proof.
    intros <-. rewrite to_of_val //.
  Qed.

  Lemma not_reducible e σ :
    ¬ reducible e σ ↔
    irreducible e σ.
  Proof.
    unfold reducible, irreducible. naive_solver.
  Qed.
  Lemma reducible_not_val e σ :
    reducible e σ →
    to_val e = None.
  Proof.
    intros (? & ? & ? & ? & ?); eauto using val_stuck.
  Qed.
  Lemma reducible_no_obs_reducible e σ :
    reducible_no_obs e σ →
    reducible e σ.
  Proof.
    intros (? & ? & ? & ?); eexists; eauto.
  Qed.
  Lemma val_irreducible e σ :
    is_Some (to_val e) →
    irreducible e σ.
  Proof.
    intros [? ?] ? ? ? ? ?%val_stuck. destruct (to_val e); done.
  Qed.
  #[global] Instance of_val_inj :
    Inj (=) (=) (@of_val Λ).
  Proof.
    intros v v' Hv; apply (inj Some); rewrite -!to_of_val Hv //.
  Qed.
  Lemma not_not_stuck e σ :
    ¬ not_stuck e σ ↔
    stuck e σ.
  Proof.
    rewrite /stuck /not_stuck -not_eq_None_Some -not_reducible.
    destruct (decide (to_val e = None)); naive_solver.
  Qed.

  Lemma reducible_fill `{!@LanguageCtx Λ K} e σ :
    reducible e σ →
    reducible (K e) σ.
  Proof.
    unfold reducible in *. naive_solver eauto using fill_step.
  Qed.
  Lemma reducible_fill_inv `{!@LanguageCtx Λ K} e σ :
    to_val e = None →
    reducible (K e) σ →
    reducible e σ.
  Proof.
    intros ? (e' & σ' & k & es & Hstep); unfold reducible.
    apply fill_step_inv in Hstep as (e2' & _ & Hstep); naive_solver.
  Qed.
  Lemma reducible_no_obs_fill `{!@LanguageCtx Λ K} e σ :
    reducible_no_obs e σ →
    reducible_no_obs (K e) σ.
  Proof.
    unfold reducible_no_obs in *. naive_solver eauto using fill_step.
  Qed.
  Lemma reducible_no_obs_fill_inv `{!@LanguageCtx Λ K} e σ :
    to_val e = None →
    reducible_no_obs (K e) σ →
    reducible_no_obs e σ.
  Proof.
    intros ? (e' & σ' & es & Hstep); unfold reducible_no_obs.
    apply fill_step_inv in Hstep as (e2' & _ & Hstep); eauto.
  Qed.
  Lemma irreducible_fill `{!@LanguageCtx Λ K} e σ :
    to_val e = None →
    irreducible e σ →
    irreducible (K e) σ.
  Proof.
    rewrite -!not_reducible. naive_solver eauto using reducible_fill_inv.
  Qed.
  Lemma irreducible_fill_inv `{!@LanguageCtx Λ K} e σ :
    irreducible (K e) σ →
    irreducible e σ.
  Proof.
    rewrite -!not_reducible. naive_solver eauto using reducible_fill.
  Qed.

  Lemma not_stuck_fill_inv K `{!@LanguageCtx Λ K} e σ :
    not_stuck (K e) σ →
    not_stuck e σ.
  Proof.
    rewrite /not_stuck -!not_eq_None_Some. intros [? | ?].
    - auto using fill_not_val.
    - destruct (decide (to_val e = None)); eauto using reducible_fill_inv.
  Qed.

  Lemma stuck_fill `{!@LanguageCtx Λ K} e σ :
    stuck e σ →
    stuck (K e) σ.
  Proof.
    rewrite -!not_not_stuck. eauto using not_stuck_fill_inv.
  Qed.

  Lemma step_insert i t2 σ2 e κ e' σ3 es :
    t2 !! i = Some e →
    prim_step e σ2 κ e' σ3 es →
    step (t2, σ2) κ (<[i:=e']> t2 ++ es, σ3).
  Proof.
    intros.
    edestruct (elem_of_list_split_length t2) as (t21 & t22 & ? & ?).
    { eauto using elem_of_list_lookup_2. }
    simplify_eq.
    econstructor; eauto.
    rewrite insert_app_r_alt // Nat.sub_diag /= -assoc_L //.
  Qed.

  Record pure_step e1 e2 := {
    pure_step_safe σ1 :
      reducible_no_obs e1 σ1 ;
    pure_step_det σ1 κ e2' σ2 es :
      prim_step e1 σ1 κ e2' σ2 es →
        κ = [] ∧
        σ2 = σ1 ∧
        e2' = e2 ∧
        es = [] ;
  }.

  Notation pure_steps_tp := (
    Forall2 (rtc pure_step)
  ).

  Class PureExec (ϕ : Prop) n e1 e2 :=
    pure_exec :
      ϕ →
      relations.nsteps pure_step n e1 e2.

  Lemma pure_step_ctx K `{!@LanguageCtx Λ K} e1 e2 :
    pure_step e1 e2 →
    pure_step (K e1) (K e2).
  Proof.
    intros [Hred Hstep]. split.
    - unfold reducible_no_obs in *. naive_solver eauto using fill_step.
    - intros σ1 κ e2' σ2 es Hpstep.
      destruct (fill_step_inv e1 σ1 κ e2' σ2 es) as (e2'' & -> & ?); [|exact Hpstep|].
      + destruct (Hred σ1) as (? & ? & ? & ?); eauto using val_stuck.
      + edestruct (Hstep σ1 κ e2'' σ2 es) as (? & -> & -> & ->); auto.
  Qed.

  Lemma pure_step_nsteps_ctx K `{!@LanguageCtx Λ K} n e1 e2 :
    relations.nsteps pure_step n e1 e2 →
    relations.nsteps pure_step n (K e1) (K e2).
  Proof.
    eauto using nsteps_congruence, pure_step_ctx.
  Qed.

  Lemma rtc_pure_step_ctx K `{!@LanguageCtx Λ K} e1 e2 :
    rtc pure_step e1 e2 →
    rtc pure_step (K e1) (K e2).
  Proof.
    eauto using rtc_congruence, pure_step_ctx.
  Qed.

  Lemma pure_exec_ctx K `{!@LanguageCtx Λ K} ϕ n e1 e2 :
    PureExec ϕ n e1 e2 →
    PureExec ϕ n (K e1) (K e2).
  Proof.
    rewrite /PureExec; eauto using pure_step_nsteps_ctx.
  Qed.

  Class AsVal e v :=
    as_val : of_val v = e.

  Lemma as_val_is_Some e :
    (∃ v, of_val v = e) →
    is_Some (to_val e).
  Proof.
    intros [v <-]. rewrite to_of_val. eauto.
  Qed.

  Lemma prim_step_not_stuck e σ κ e' σ' es :
    prim_step e σ κ e' σ' es →
    not_stuck e σ.
  Proof.
    rewrite /not_stuck /reducible. eauto 10.
  Qed.

  Lemma rtc_pure_step_val `{!Inhabited (state Λ)} v e :
    rtc pure_step (of_val v) e →
    to_val e = Some v.
  Proof.
    intros ?; rewrite <- to_of_val.
    f_equal; symmetry; eapply rtc_nf; first done.
    intros [e' [Hstep _]].
    destruct (Hstep inhabitant) as (? & ? & ? & Hval%val_stuck).
    rewrite to_of_val // in Hval.
  Qed.
End language.

#[global] Hint Mode PureExec + - - ! - : typeclass_instances.

#[global] Arguments step_atomic {Λ ρ1 κ ρ2}.
