From zoo Require Import
  prelude.
From zoo.iris.program_logic Require Import
  language.
From zoo Require Import
  options.

Section ectx_language_mixin.
  Context {expr val ectx state observation : Type}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).
  Context (empty_ectx : ectx).
  Context (comp_ectx : ectx → ectx → ectx).
  Context (fill : ectx → expr → expr).
  Context (base_step : expr → state → list observation → expr → state → list expr → Prop).

  Record EctxLanguageMixin := {
    mixin_to_of_val v :
      to_val (of_val v) = Some v ;
    mixin_of_to_val e v :
      to_val e = Some v →
      of_val v = e ;
    mixin_val_base_stuck e1 σ1 κ e2 σ2 es :
      base_step e1 σ1 κ e2 σ2 es →
      to_val e1 = None ;

    mixin_fill_empty e :
      fill empty_ectx e = e ;
    mixin_fill_comp K1 K2 e :
      fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e ;
    mixin_fill_inj K :
      Inj (=) (=) (fill K) ;
    mixin_fill_val K e :
      is_Some (to_val (fill K e)) →
      is_Some (to_val e) ;

    mixin_step_by_val K' K_redex e1' e1_redex σ1 κ e2 σ2 es :
      fill K' e1' = fill K_redex e1_redex →
      to_val e1' = None →
      base_step e1_redex σ1 κ e2 σ2 es →
        ∃ K'',
        K_redex = comp_ectx K' K'' ;

    mixin_base_ctx_step_val K e σ1 κ e2 σ2 es :
      base_step (fill K e) σ1 κ e2 σ2 es →
        is_Some (to_val e) ∨
        K = empty_ectx ;
  }.
End ectx_language_mixin.

Structure ectx_language := {
  expr : Type ;
  val : Type ;
  ectx : Type ;
  state : Type ;
  observation : Type ;

  of_val : val → expr ;
  to_val : expr → option val ;
  empty_ectx : ectx ;
  comp_ectx : ectx → ectx → ectx ;
  fill : ectx → expr → expr ;
  base_step : expr → state → list observation → expr → state → list expr → Prop ;

  ectx_language_mixin : EctxLanguageMixin of_val to_val empty_ectx comp_ectx fill base_step ;
}.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

#[global] Arguments Build_ectx_language {_ _ _ _ _ _ _ _ _ _ _} _ : assert.
#[global] Arguments of_val {_} _ : assert.
#[global] Arguments to_val {_} _ : assert.
#[global] Arguments empty_ectx {_} : assert.
#[global] Arguments comp_ectx {_} _ _ : assert.
#[global] Arguments fill {_} _ _ : assert.
#[global] Arguments base_step {_} _ _ _ _ _ _ : assert.

Section ectx_language.
  Context {Λ : ectx_language}.

  Implicit Types e : expr Λ.
  Implicit Types v : val Λ.
  Implicit Types σ : state Λ.
  Implicit Types K : ectx Λ.
  Implicit Types κ : list (observation Λ).

  Definition base_reducible e σ :=
    ∃ κ e' σ' es,
    base_step e σ κ e' σ' es.
  Definition base_reducible_no_obs e σ :=
    ∃ e' σ' es,
    base_step e σ [] e' σ' es.
  Definition base_irreducible e σ :=
    ∀ κ e' σ' es,
    ¬ base_step e σ κ e' σ' es.
  Definition base_stuck e σ :=
    to_val e = None ∧
    base_irreducible e σ.

  Definition sub_redexes_are_values e :=
    ∀ K e', e = fill K e' →
    to_val e' = None →
    K = empty_ectx.

  Inductive prim_step e1 σ1 κ e2 σ2 es : Prop :=
    | base_step_fill_prim_step' K e1' e2' :
        e1 = fill K e1' →
        e2 = fill K e2' →
        base_step e1' σ1 κ e2' σ2 es →
        prim_step e1 σ1 κ e2 σ2 es.

  Definition base_atomic e :=
    ∀ σ κ e' σ' es,
    base_step e σ κ e' σ' es →
    is_Some (to_val e').

  Record pure_base_step e1 e2 := {
    pure_base_step_safe σ1 :
      base_reducible_no_obs e1 σ1 ;
    pure_base_step_det σ1 κ e2' σ2 es :
      base_step e1 σ1 κ e2' σ2 es →
        κ = [] ∧
        σ2 = σ1 ∧
        e2' = e2 ∧
        es = [] ;
  }.

  Lemma base_step_not_val e1 σ1 κ e2 σ2 es :
    base_step e1 σ1 κ e2 σ2 es →
    to_val e1 = None.
  Proof.
    apply ectx_language_mixin.
  Qed.
  Lemma base_reducible_not_val e σ :
    base_reducible e σ →
    to_val e = None.
  Proof.
    intros (κ & e' & σ' & es & He%base_step_not_val). done.
  Qed.

  #[global] Instance fill_inj K :
    Inj (=) (=) (fill K).
  Proof.
    apply ectx_language_mixin.
  Qed.
  Lemma fill_empty e :
    fill empty_ectx e = e.
  Proof.
    apply ectx_language_mixin.
  Qed.
  Lemma fill_comp K1 K2 e :
    fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
  Proof.
    apply ectx_language_mixin.
  Qed.
  Lemma fill_val K e :
    is_Some (to_val (fill K e)) →
    is_Some (to_val e).
  Proof.
    apply ectx_language_mixin.
  Qed.

  Lemma step_by_val K' K_redex e1' e1_redex σ1 κ e2 σ2 es :
    fill K' e1' = fill K_redex e1_redex →
    to_val e1' = None →
    base_step e1_redex σ1 κ e2 σ2 es →
      ∃ K'',
      K_redex = comp_ectx K' K''.
  Proof.
    apply ectx_language_mixin.
  Qed.

  Lemma base_ctx_step_val K e σ1 κ e2 σ2 es :
    base_step (fill K e) σ1 κ e2 σ2 es →
      is_Some (to_val e) ∨
      K = empty_ectx.
  Proof.
    apply ectx_language_mixin.
  Qed.

  Lemma base_step_fill_prim_step K e1 σ1 κ e2 σ2 es :
    base_step e1 σ1 κ e2 σ2 es →
    prim_step (fill K e1) σ1 κ (fill K e2) σ2 es.
  Proof.
    eauto using prim_step.
  Qed.

  Definition ectx_lang_mixin :
    LanguageMixin of_val to_val prim_step.
  Proof.
    split.
    - apply ectx_language_mixin.
    - apply ectx_language_mixin.
    - intros ? ? ? ? ? ? [? ? ? -> -> ?%base_step_not_val].
      apply eq_None_not_Some. intros ?%fill_val%eq_None_not_Some; done.
  Qed.
  Canonical ectx_lang :=
    Build_language ectx_lang_mixin.

  Lemma fill_not_val K e :
    to_val e = None →
    to_val (fill K e) = None.
  Proof.
    rewrite !eq_None_not_Some. eauto using fill_val.
  Qed.

  Lemma base_reducible_no_obs_base_reducible e σ :
    base_reducible_no_obs e σ →
    base_reducible e σ.
  Proof.
    intros (? & ? & ? & ?). eexists. eauto.
  Qed.
  Lemma not_base_reducible e σ :
    ¬ base_reducible e σ ↔
    base_irreducible e σ.
  Proof.
    rewrite /base_reducible /base_irreducible. naive_solver.
  Qed.

  Lemma base_redex_unique K K' e e' σ :
    fill K e = fill K' e' →
    base_reducible e σ →
    base_reducible e' σ →
      K = comp_ectx K' empty_ectx ∧
      e = e'.
  Proof.
    intros Heq (κ & e2 & σ2 & es & Hred) (κ' & e2' & σ2' & es' & Hred').
    edestruct (step_by_val K' K e' e) as [K'' HK]; [eauto using base_step_not_val.. |].
    subst K. move: Heq. rewrite -fill_comp. intros <-%(inj (fill _)).
    destruct (base_ctx_step_val _ _ _ _ _ _ _ Hred') as [[]%not_eq_None_Some | HK''].
    { eapply base_step_not_val. done. }
    subst K''. rewrite fill_empty //.
  Qed.

  Lemma base_step_prim_step e1 σ1 κ e2 σ2 es :
    base_step e1 σ1 κ e2 σ2 es →
    prim_step e1 σ1 κ e2 σ2 es.
  Proof.
    apply base_step_fill_prim_step' with empty_ectx.
    all: rewrite ?fill_empty //.
  Qed.

  Lemma base_step_not_stuck e σ κ e' σ' es :
    base_step e σ κ e' σ' es →
    not_stuck e σ.
  Proof.
    rewrite /not_stuck /reducible /=.
    eauto 10 using base_step_prim_step.
  Qed.

  Lemma fill_prim_step K e1 σ1 κ e2 σ2 es :
    prim_step e1 σ1 κ e2 σ2 es →
    prim_step (fill K e1) σ1 κ (fill K e2) σ2 es.
  Proof.
    destruct 1 as [K' e1' e2' -> ->].
    rewrite !fill_comp. econstructor; done.
  Qed.
  Lemma fill_reducible K e σ :
    reducible e σ →
    reducible (fill K e) σ.
  Proof.
    intros (κ & e' & σ' & es & ?). exists κ, (fill K e'), σ', es.
    apply fill_prim_step. done.
  Qed.
  Lemma fill_reducible_no_obs K e σ :
    reducible_no_obs e σ →
    reducible_no_obs (fill K e) σ.
  Proof.
    intros (e' & σ' & es & ?). exists (fill K e'), σ', es.
    apply fill_prim_step. done.
  Qed.
  Lemma base_reducible_reducible e σ :
    base_reducible e σ →
    reducible e σ.
  Proof.
    intros (κ & e' & σ' & es & ?). eexists κ, e', σ', es.
    apply base_step_prim_step. done.
  Qed.
  Lemma base_reducible_prim_fill_reducible e K σ :
    base_reducible e σ →
    reducible (fill K e) σ.
  Proof.
    intro.
    apply fill_reducible, base_reducible_reducible. done.
  Qed.
  Lemma base_reducible_no_obs_reducible e σ :
    base_reducible_no_obs e σ →
    reducible_no_obs e σ.
  Proof.
    intros (e' & σ' & es & ?). eexists e', σ', es.
    apply base_step_prim_step. done.
  Qed.
  Lemma irreducible_base_irreducible e σ :
    irreducible e σ →
    base_irreducible e σ.
  Proof.
    rewrite -not_reducible -not_base_reducible.
    auto using base_reducible_reducible.
  Qed.
  Lemma base_reducible_no_obs_fill_reducible e K σ :
    base_reducible_no_obs e σ →
    reducible_no_obs (fill K e) σ.
  Proof.
    intro.
    apply fill_reducible_no_obs, base_reducible_no_obs_reducible. done.
  Qed.

  Lemma reducible_base_reducible e σ :
    reducible e σ →
    sub_redexes_are_values e →
    base_reducible e σ.
  Proof.
    intros (κ & e' & σ' & es & [K e1' e2' -> -> Hstep]) ?.
    assert (K = empty_ectx) as -> by eauto 10 using base_step_not_val.
    rewrite fill_empty /base_reducible. eauto 10.
  Qed.
  Lemma base_irreducible_irreducible e σ :
    base_irreducible e σ →
    sub_redexes_are_values e →
    irreducible e σ.
  Proof.
    rewrite -not_reducible -not_base_reducible.
    auto using reducible_base_reducible.
  Qed.
  Lemma base_stuck_stuck e σ :
    base_stuck e σ →
    sub_redexes_are_values e →
    stuck e σ.
  Proof.
    intros [] ?.
    split; first done.
    apply base_irreducible_irreducible; done.
  Qed.

  Lemma ectx_language_atomic e :
    base_atomic e →
    sub_redexes_are_values e →
    Atomic e.
  Proof.
    intros Hatomic_step Hatomic_fill σ κ e' σ' es [K e1' e2' -> -> Hstep].
    assert (K = empty_ectx) as -> by eauto 10 using base_step_not_val.
    rewrite fill_empty. eapply Hatomic_step. rewrite fill_empty //.
  Qed.

  Lemma base_reducible_fill_prim_step K e1 σ1 κ e2 σ2 es :
    base_reducible e1 σ1 →
    prim_step (fill K e1) σ1 κ e2 σ2 es →
      ∃ e2',
      e2 = fill K e2' ∧
      base_step e1 σ1 κ e2' σ2 es.
  Proof.
    intros (κ' & e2'' & σ2'' & es'' & HhstepK) [K' e1' e2' HKe1 -> Hstep].
    edestruct (step_by_val K) as [K'' ?]; eauto using base_step_not_val; simplify_eq/=.
    rewrite -fill_comp in HKe1; simplify_eq.
    exists (fill K'' e2'). rewrite fill_comp; split; first done.
    apply base_ctx_step_val in HhstepK as [[v ?] | ?]; simplify_eq.
    { apply base_step_not_val in Hstep. simplify_eq. }
    rewrite !fill_empty //.
  Qed.

  Lemma base_reducible_prim_step e1 σ1 κ e2 σ2 es :
    base_reducible e1 σ1 →
    prim_step e1 σ1 κ e2 σ2 es →
    base_step e1 σ1 κ e2 σ2 es.
  Proof.
    intros.
    edestruct (base_reducible_fill_prim_step empty_ectx) as (? & ? & ?).
    all: rewrite ?fill_empty; eauto.
    simplify. rewrite fill_empty //.
  Qed.

  Lemma pure_base_step_pure_step e1 e2 :
    pure_base_step e1 e2 →
    pure_step e1 e2.
  Proof.
    intros [Hsafe Hdet]. split.
    - intros σ. destruct (Hsafe σ) as (e2' & σ2 & es & ?).
      eexists e2', σ2, es. apply base_step_prim_step. done.
    - intros σ1 κ e2' σ2 es ?%base_reducible_prim_step.
      all: auto using base_reducible_no_obs_base_reducible.
  Qed.

  #[global] Instance ectx_lang_ctx K :
    LanguageCtx (fill K).
  Proof.
    split; simpl.
    - auto using fill_not_val.
    - intros ? ? ? ? ? ? [K' e1' e2' Heq1 Heq2 Hstep].
      exists (comp_ectx K K') e1' e2'; rewrite ?Heq1 ?Heq2 ?fill_comp //.
    - intros e1 σ1 κ e2 σ2 es Hnval [K'' e1'' e2'' Heq1 -> Hstep].
      destruct (step_by_val K K'' e1 e1'' σ1 κ e2'' σ2 es) as [K' ->]; auto.
      rewrite -fill_comp in Heq1; apply (inj (fill _)) in Heq1.
      exists (fill K' e2''); rewrite -fill_comp; split; auto.
      eauto using prim_step.
  Qed.

  Lemma pure_exec_fill K ϕ n e1 e2 :
    PureExec ϕ n e1 e2 →
    PureExec ϕ n (fill K e1) (fill K e2).
  Proof.
    apply: pure_exec_ctx.
  Qed.
  Lemma pure_nsteps_fill {n e1 e2} K :
    relations.nsteps pure_step n e1 e2 →
    relations.nsteps pure_step n (fill K e1) (fill K e2).
  Proof.
    intros Hsteps.
    eapply pure_exec_fill; last done.
    intros _. done.
  Qed.
  Lemma pure_steps_fill {e1 e2} K :
    rtc pure_step e1 e2 →
    rtc pure_step (fill K e1) (fill K e2).
  Proof.
    rewrite !rtc_nsteps.
    intros (n & Hsteps%(pure_nsteps_fill K)).
    naive_solver.
  Qed.
  Lemma pure_step_fill {e1 e2} K :
    pure_step e1 e2 →
    pure_step (fill K e1) (fill K e2).
  Proof.
    intros Hstep%nsteps_once%(pure_nsteps_fill K).
    apply nsteps_once_inv. done.
  Qed.
End ectx_language.

#[global] Arguments base_step_fill_prim_step' {_ _ _ _ _ _ _}.

#[global] Arguments ectx_lang : clear implicits.
Coercion ectx_lang : ectx_language >-> language.

Definition LanguageOfEctx '(Build_ectx_language mixin) : language :=
  Eval compute in
  Build_ectx_language mixin.
#[global] Arguments LanguageOfEctx : simpl never.
