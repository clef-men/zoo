Require Import zoo.prelude.
Require Export zoo.language.semantics.
Require Import zoo.options.

Implicit Type e : expr.
Implicit Type es : list expr.
Implicit Type v : val.
Implicit Type σ : state.
Implicit Type κ κs : list observation.
Implicit Type k : ectxi.
Implicit Type K : ectx.
Implicit Type ρ : config.

Declare Scope expr_scope.
Delimit Scope expr_scope with E.
Bind Scope expr_scope with expr.

Declare Scope val_scope.
Delimit Scope val_scope with V.
Bind Scope val_scope with val.

Class AsVal e v :=
  as_val : of_val v = e.

Variant prim_step tid e1 σ1 κ e2 σ2 es : Prop :=
  | base_stepｰfillｰprim_step' K e1' e2' :
      e1 = fill K e1' →
      e2 = fill K e2' →
      base_step tid e1' σ1 κ e2' σ2 es →
      prim_step tid e1 σ1 κ e2 σ2 es.
#[global] Arguments base_stepｰfillｰprim_step' {_ _ _ _ _ _ _}.

Definition step ρ1 κ ρ2 :=
  ∃ tid e1 e2 σ2 es,
  prim_step tid e1 ρ1.2 κ e2 σ2 es ∧
  ρ1.1 !! tid = Some e1 ∧
  ρ2 = (<[tid := e2]> ρ1.1 ++ es, σ2).

Inductive nsteps : nat → config → list observation → config → Prop :=
  | nstepsｰrefl ρ :
     nsteps 0 ρ [] ρ
  | nstepsｰl n ρ1 ρ2 ρ3 κ κs :
     step ρ1 κ ρ2 →
     nsteps n ρ2 κs ρ3 →
     nsteps ˖n ρ1 (κ ++ κs) ρ3.
#[local] Hint Constructors nsteps : core.

Definition silent_step ρ1 ρ2 :=
  ∃ κ,
  step ρ1 κ ρ2.

Definition base_reducible tid e σ :=
  ∃ κ e' σ' es,
  base_step tid e σ κ e' σ' es.
Definition base_reducible_no_obs tid e σ :=
  ∃ e' σ' es,
  base_step tid e σ [] e' σ' es.
Definition base_irreducible tid e σ :=
  ∀ κ e' σ' es,
  ¬ base_step tid e σ κ e' σ' es.
Definition base_stuck tid e σ :=
  to_val e = None ∧
  base_irreducible tid e σ.
Definition base_atomic e :=
  ∀ tid σ κ e' σ' es,
  base_step tid e σ κ e' σ' es →
  is_Some (to_val e').

Record pure_base_step e1 e2 :=
  { pure_base_stepｰsafe tid σ1 :
      base_reducible_no_obs tid e1 σ1
  ; pure_base_stepｰdet tid σ1 κ e2' σ2 es :
      base_step tid e1 σ1 κ e2' σ2 es →
        κ = [] ∧
        σ2 = σ1 ∧
        e2' = e2 ∧
        es = []
  }.

Definition reducible tid e σ :=
  ∃ κ e' σ' es,
  prim_step tid e σ κ e' σ' es.
Definition reducible_no_obs tid e σ :=
  ∃ e' σ' es,
  prim_step tid e σ [] e' σ' es.
Definition irreducible tid e σ :=
  ∀ κ e' σ' es,
  ¬ prim_step tid e σ κ e' σ' es.
Definition stuck tid e σ :=
  to_val e = None ∧
  irreducible tid e σ.
Definition not_stuck tid e σ :=
  is_Some (to_val e) ∨
  reducible tid e σ.
Class Atomic e :=
  atomic tid σ e' κ σ' es :
    prim_step tid e σ κ e' σ' es →
    is_Some (to_val e').
Definition safe ρ :=
  ∀ ρ',
  rtc silent_step ρ ρ' →
  Foralli (λ tid e, not_stuck tid e ρ'.2) ρ'.1.

Record pure_step e1 e2 :=
  { pure_stepｰsafe tid σ1 :
      reducible_no_obs tid e1 σ1
  ; pure_stepｰdet tid σ1 κ e2' σ2 es :
      prim_step tid e1 σ1 κ e2' σ2 es →
        κ = [] ∧
        σ2 = σ1 ∧
        e2' = e2 ∧
        es = []
  }.

Class Context (K : expr → expr) :=
  { contextｰfillｰnot_val e :
      to_val e = None →
      to_val (K e) = None
  ; contextｰfillｰstep tid e1 σ1 κ e2 σ2 es :
      prim_step tid e1 σ1 κ e2 σ2 es →
      prim_step tid (K e1) σ1 κ (K e2) σ2 es
  ; contextｰfillｰstepｰinv tid e1' σ1 κ e2 σ2 es :
      to_val e1' = None →
      prim_step tid (K e1') σ1 κ e2 σ2 es →
        ∃ e2',
        e2 = K e2' ∧
        prim_step tid e1' σ1 κ e2' σ2 es
  }.

Class PureExec (ϕ : Prop) n e1 e2 :=
  pure_exec :
    ϕ →
    relations.nsteps pure_step n e1 e2.

Definition sub_redexes_are_values e :=
  ∀ K e', e = fill K e' →
  to_val e' = None →
  K = [].

#[global] Instance filliｰinj k :
  Inj (=) (=) (filli k).
Proof.
  induction k; intros ?*; naive_solver.
Qed.
Lemma filliｰval k e :
  is_Some (to_val (filli k e)) →
  is_Some (to_val e).
Proof.
  intros (v & ?). destruct k; done.
Qed.
Lemma filliｰno_valｰinj k1 e1 k2 e2 :
  to_val e1 = None →
  to_val e2 = None →
  filli k1 e1 = filli k2 e2 →
  k1 = k2.
Proof.
  move: k1.
  induction k2; intros k1; destruct k1; try naive_solver.
  intros H1 H2 [= -> -> H%app_inj_2]; first naive_solver.
  simpl. do 3 f_equal.
  apply (f_equal reverse) in H.
  rewrite !reverse_app !reverse_cons -!fmap_reverse /= in H.
  match goal with |- ?vs1 = ?vs2 =>
    apply (inj reverse);
    remember (reverse vs1) as vs1';
    remember (reverse vs2) as vs2';
    clear- H1 H2 H; move: vs2' H; induction vs1'; intros []; naive_solver
  end.
Qed.
Lemma base_stepｰfilliｰval tid k e σ1 κ e2 σ2 es :
  base_step tid (filli k e) σ1 κ e2 σ2 es →
  is_Some (to_val e).
Proof.
  move: κ e2.
  induction k; try (inversion_clear 1; eauto || done).
  all: inversion_clear 1.
  all:
    match goal with H: _ ++ _ :: of_vals ?vs1 = of_vals ?vs2 |- _ =>
      apply (f_equal reverse) in H;
      rewrite reverse_app reverse_cons -!fmap_reverse /= in H;
      remember (reverse vs1) as vs1';
      remember (reverse vs2) as vs2';
      clear- H; move: vs2' H; induction vs1'; intros []; naive_solver
    end.
Qed.

#[global] Instance fillｰinj K :
  Inj (=) (=) (fill K).
Proof.
  induction K as [| k K IH].
  all: rewrite /Inj.
  all: naive_solver.
Qed.
Lemma fillｰnil e :
  fill [] e = e.
Proof.
  done.
Qed.
Lemma fillｰapp K1 K2 e :
  fill (K1 ++ K2) e = fill K2 (fill K1 e).
Proof.
  apply foldl_app.
Qed.
Lemma fillｰval K e :
  is_Some (to_val (fill K e)) →
  is_Some (to_val e).
Proof.
  move: e. induction K as [| k K IH] => e //=.
  intros ?%IH%filliｰval => //.
Qed.
Lemma fillｰnot_val K e :
  to_val e = None →
  to_val (fill K e) = None.
Proof.
  rewrite !eq_None_not_Some.
  eauto using fillｰval.
Qed.

Lemma base_stepｰnot_val tid e1 σ1 κ e2 σ2 es :
  base_step tid e1 σ1 κ e2 σ2 es →
  to_val e1 = None.
Proof.
  destruct 1; naive_solver.
Qed.
Lemma stepｰbyｰval tid K1 K2 e1 e2 σ1 κ e2' σ2 es :
  fill K1 e1 = fill K2 e2 →
  to_val e1 = None →
  base_step tid e2 σ1 κ e2' σ2 es →
    ∃ K,
    K2 = K ++ K1.
Proof.
  intros Hfill Hred Hstep.
  move: K2 Hfill. induction K1 as [| k1 K1 IH] using rev_ind => /= K2 Hfill.
  - eauto using app_nil_r.
  - destruct K2 as [| k2 K2 _] using rev_ind; simplify_eq/=.
    { rewrite fillｰapp in Hstep. apply base_stepｰfilliｰval in Hstep.
      apply fillｰval in Hstep. apply not_eq_None_Some in Hstep. done.
    }
    rewrite !fillｰapp /= in Hfill.
    assert (k1 = k2) as ->.
    { eapply filliｰno_valｰinj, Hfill.
      all: eauto using fillｰnot_val, base_stepｰnot_val.
    }
    simplify_eq. destruct (IH K2) as [K ->]; auto.
    exists K. rewrite assoc //.
Qed.
Lemma base_stepｰfillｰval tid K e σ1 κ e2 σ2 es :
  base_step tid (fill K e) σ1 κ e2 σ2 es →
    is_Some (to_val e) ∨
    K = [].
Proof.
  destruct K as [| k K _] using rev_ind; simpl; first by auto.
  rewrite fillｰapp /=. intros ?%base_stepｰfilliｰval.
  eauto using fillｰval.
Qed.

Lemma base_reducible_no_obsｰbase_reducible tid e σ :
  base_reducible_no_obs tid e σ →
  base_reducible tid e σ.
Proof.
  intros (? & ? & ? & ?). eexists. eauto.
Qed.

Lemma base_stepｰprim_step tid e1 σ1 κ e2 σ2 es :
  base_step tid e1 σ1 κ e2 σ2 es →
  prim_step tid e1 σ1 κ e2 σ2 es.
Proof.
  apply (base_stepｰfillｰprim_step' []).
  all: rewrite ?fillｰnil //.
Qed.
Lemma prim_stepｰnot_val tid e σ κ e' σ' es :
  prim_step tid e σ κ e' σ' es →
  to_val e = None.
Proof.
  intros [? ? ? -> -> ?%base_stepｰnot_val].
  apply eq_None_not_Some. intros ?%fillｰval%eq_None_not_Some; done.
Qed.
Lemma reducibleｰnot_val tid e σ :
  reducible tid e σ →
  to_val e = None.
Proof.
  intros (? & ? & ? & ? & ?).
  eauto using prim_stepｰnot_val.
Qed.
Lemma reducible_no_obsｰreducible tid e σ :
  reducible_no_obs tid e σ →
  reducible tid e σ.
Proof.
  intros (? & ? & ? & ?).
  eexists. eauto.
Qed.
Lemma base_reducibleｰreducible tid e σ :
  base_reducible tid e σ →
  reducible tid e σ.
Proof.
  intros (κ & e' & σ' & es & ?).
  exists κ, e', σ', es.
  apply base_stepｰprim_step. done.
Qed.

Lemma base_atomicｰatomic e :
  base_atomic e →
  sub_redexes_are_values e →
  Atomic e.
Proof.
  intros Hatomic_step Hatomic_fill tid σ κ e' σ' es [K e1' e2' -> -> Hstep].
  assert (K = []) as -> by eauto 10 using base_stepｰnot_val.
  rewrite fillｰnil. eapply Hatomic_step. rewrite fillｰnil //.
Qed.

Lemma base_reducibleｰfillｰprim_step tid K e1 σ1 κ e2 σ2 es :
  base_reducible tid e1 σ1 →
  prim_step tid (fill K e1) σ1 κ e2 σ2 es →
    ∃ e2',
    e2 = fill K e2' ∧
    base_step tid e1 σ1 κ e2' σ2 es.
Proof.
  intros (κ' & e2'' & σ2'' & es'' & HhstepK) [K' e1' e2' HKe1 -> Hstep].
  edestruct (stepｰbyｰval tid K) as [K'' ?]; eauto using base_stepｰnot_val; simplify_eq/=.
  rewrite fillｰapp in HKe1; simplify_eq.
  exists (fill K'' e2'). rewrite fillｰapp; split; first done.
  apply base_stepｰfillｰval in HhstepK as [[v ?] | ?]; simplify_eq.
  { apply base_stepｰnot_val in Hstep. simplify_eq. }
  rewrite !fillｰnil //.
Qed.
Lemma base_reducibleｰprim_step tid e1 σ1 κ e2 σ2 es :
  base_reducible tid e1 σ1 →
  prim_step tid e1 σ1 κ e2 σ2 es →
  base_step tid e1 σ1 κ e2 σ2 es.
Proof.
  intros.
  edestruct (base_reducibleｰfillｰprim_step tid []) as (? & ? & ?).
  all: rewrite ?fillｰnil; eauto.
  simplify. done.
Qed.

Lemma pure_base_stepｰpure_step e1 e2 :
  pure_base_step e1 e2 →
  pure_step e1 e2.
Proof.
  intros [Hsafe Hdet]. split.
  - intros tid σ.
    destruct (Hsafe tid σ) as (e2' & σ2 & es & ?).
    exists e2', σ2, es.
    apply base_stepｰprim_step. done.
  - intros tid σ1 κ e2' σ2 es ?%base_reducibleｰprim_step.
    all: eauto using base_reducible_no_obsｰbase_reducible.
Qed.

#[global] Instance contextｰid :
  Context (@id expr).
Proof.
  constructor; naive_solver.
Qed.
#[global] Instance contextｰfill K :
  Context (fill K).
Proof.
  split => /=.
  - auto using fillｰnot_val.
  - intros ? ? ? ? ? ? ? [K' e1' e2' Heq1 Heq2 Hstep].
    exists (K' ++ K) e1' e2'.
    all: rewrite ?Heq1 ?Heq2 ?fillｰapp //.
  - intros tid e1 σ1 κ e2 σ2 es Hnval [K'' e1'' e2'' Heq1 -> Hstep].
    destruct (stepｰbyｰval tid K K'' e1 e1'' σ1 κ e2'' σ2 es) as [K' ->]; try done.
    rewrite fillｰapp in Heq1. apply (inj (fill _)) in Heq1.
    exists (fill K' e2''). rewrite fillｰapp. split; first done.
    eauto using prim_step.
Qed.
#[global] Instance contextｰfilli k :
  Context (filli k).
Proof.
  change (Context (fill [k])). apply _.
Qed.

Lemma reducibleｰcontext (K : expr → expr) `{!Context K} tid e σ :
  reducible tid e σ →
  reducible tid (K e) σ.
Proof.
  rewrite /reducible.
  naive_solver eauto using contextｰfillｰstep.
Qed.
Lemma reducibleｰcontextｰinv (K : expr → expr) `{!Context K} tid e σ :
  to_val e = None →
  reducible tid (K e) σ →
  reducible tid e σ.
Proof.
  intros He (e' & σ' & k & es & Hstep). rewrite /reducible.
  apply contextｰfillｰstepｰinv in Hstep as (e2' & _ & Hstep); naive_solver.
Qed.

Lemma pure_stepｰcontext (K : expr → expr) `{!Context K} e1 e2 :
  pure_step e1 e2 →
  pure_step (K e1) (K e2).
Proof.
  intros [Hred Hstep]. split.
  - rewrite /reducible_no_obs in Hred |- *. naive_solver eauto using contextｰfillｰstep.
  - intros tid σ1 κ e2' σ2 es Hpstep.
    destruct (contextｰfillｰstepｰinv tid e1 σ1 κ e2' σ2 es) as (e2'' & -> & ?); [|exact Hpstep|].
    + destruct (Hred tid σ1) as (? & ? & ? & ?); eauto using prim_stepｰnot_val.
    + edestruct (Hstep tid σ1 κ e2'' σ2 es) as (? & -> & -> & ->); done.
Qed.
Lemma pure_stepｰnstepsｰcontext (K : expr → expr) `{!Context K} n e1 e2 :
  relations.nsteps pure_step n e1 e2 →
  relations.nsteps pure_step n (K e1) (K e2).
Proof.
  eauto using nsteps_congruence, pure_stepｰcontext.
Qed.

Lemma pure_execｰcontext (K : expr → expr) `{!Context K} ϕ n e1 e2 :
  PureExec ϕ n e1 e2 →
  PureExec ϕ n (K e1) (K e2).
Proof.
  rewrite /PureExec; auto using pure_stepｰnstepsｰcontext.
Qed.
Lemma pure_execｰfill K ϕ n e1 e2 :
  PureExec ϕ n e1 e2 →
  PureExec ϕ n (fill K e1) (fill K e2).
Proof.
  apply: pure_execｰcontext.
Qed.

Lemma sub_redexes_are_valuesｰalt e :
  ( ∀ k e',
    e = filli k e' →
    is_Some (to_val e')
  ) →
  sub_redexes_are_values e.
Proof.
  intros H K e' ->.
  destruct K as [| k K _] using rev_ind => //=.
  intros []%eq_None_not_Some.
  eapply fillｰval, H. rewrite fillｰapp //.
Qed.

Lemma to_valｰfillｰSome K e v :
  to_val (fill K e) = Some v →
  K = [] ∧ e = Val v.
Proof.
  intro H. destruct K as [| k K]; first by apply of_valｰto_val in H. exfalso.
  assert (to_val e ≠ None) as He.
  { intro A. rewrite fillｰnot_val // in H. }
  assert (∃ w, e = Val w) as [w ->].
  { destruct e; try done; eauto. }
  assert (to_val (fill (k :: K) (Val w)) = None).
  { destruct k; simpl; apply fillｰnot_val; done. }
  simplify.
Qed.
Lemma prim_stepｰto_valｰisｰbase_step tid e σ1 κ v σ2 es :
  prim_step tid e σ1 κ (Val v) σ2 es →
  base_step tid e σ1 κ (Val v) σ2 es.
Proof.
  intro H. destruct H as [K e1 e2 H1 H2].
  assert (to_val (fill K e2) = Some v) as H3; first rewrite -H2 //.
  apply to_valｰfillｰSome in H3 as [-> ->]. subst e. done.
Qed.

Lemma silent_stepsｰnsteps ρ1 ρ2 :
  rtc silent_step ρ1 ρ2 ↔
    ∃ n κs,
    nsteps n ρ1 κs ρ2.
Proof.
  rewrite /silent_step. split.
  - induction 1; naive_solver.
  - intros (n & κs & Hsteps).
    induction Hsteps; eauto using rtc.
Qed.

Lemma stepｰlength ρ1 κ ρ2 :
  step ρ1 κ ρ2 →
  length ρ1.1 ≤ length ρ2.1.
Proof.
  intros (tid & e1 & e2 & σ2 & es & Hstep & Hlookup & ->).
  simpl_length/=. lia.
Qed.
Lemma nstepsｰlength n ρ1 κs ρ2 :
  nsteps n ρ1 κs ρ2 →
  length ρ1.1 ≤ length ρ2.1.
Proof.
  induction 1 as [| ? ? ? ? ? ? Hstep%stepｰlength]; lia.
Qed.

Lemma base_reducible_no_obsｰequal tid v1 v2 σ :
  base_reducible_no_obs tid (Equal (Val v1) (Val v2)) σ.
Proof.
  destruct (valｰsimilarｰorｰnonsimilar v1 v2).
  all: repeat econstructor; done.
Qed.
Lemma base_reducibleｰequal tid v1 v2 σ :
  base_reducible tid (Equal (Val v1) (Val v2)) σ.
Proof.
  apply base_reducible_no_obsｰbase_reducible, base_reducible_no_obsｰequal.
Qed.
Lemma reducibleｰequal tid v1 v2 σ :
  reducible tid (Equal (Val v1) (Val v2)) σ.
Proof.
  apply base_reducibleｰreducible, base_reducibleｰequal.
Qed.

Lemma base_reducible_no_obsｰcas tid l fld v1 v2 v σ :
  σ.(state۰heap) !! (l +ₗ fld) = Some v →
  base_reducible_no_obs tid (CAS (Val $ ValTuple [ValLoc l; ValInt fld]) (Val v1) (Val v2)) σ.
Proof.
  destruct (valｰsimilarｰorｰnonsimilar v v1).
  all: repeat econstructor; done.
Qed.
Lemma base_reducibleｰcas tid l fld v1 v2 v σ :
  σ.(state۰heap) !! (l +ₗ fld) = Some v →
  base_reducible tid (CAS (Val $ ValTuple [ValLoc l; ValInt fld]) (Val v1) (Val v2)) σ.
Proof.
  intros.
  eapply base_reducible_no_obsｰbase_reducible, base_reducible_no_obsｰcas. done.
Qed.
Lemma reducibleｰcas tid l fld v1 v2 v σ :
  σ.(state۰heap) !! (l +ₗ fld) = Some v →
  reducible tid (CAS (Val $ ValTuple [ValLoc l; ValInt fld]) (Val v1) (Val v2)) σ.
Proof.
  intros.
  eapply base_reducibleｰreducible, base_reducibleｰcas. done.
Qed.

Lemma reducibleｰresolve tid e σ pid v :
  Atomic e →
  reducible tid e σ →
  reducible tid (Resolve e (Val $ ValProph pid) (Val v)) σ.
Proof.
  intros Hatomic (κ & e' & σ' & es & H).
  exists (κ ++ [(pid, (default v (to_val e'), v))]), e', σ', es.
  eapply (base_stepｰfillｰprim_step' []); try done.
  assert (∃ w, Val w = e') as (w & <-).
  { apply (Hatomic tid σ e' κ σ' es) in H as (w & H).
    exists w. apply (of_valｰto_val _ _ H).
  }
  econstructor.
  apply prim_stepｰto_valｰisｰbase_step. done.
Qed.
Lemma prim_stepｰresolveｰinv tid e v1 v2 σ1 κ e2 σ2 es :
  Atomic e →
  prim_step tid (Resolve e (Val v1) (Val v2)) σ1 κ e2 σ2 es →
  base_step tid (Resolve e (Val v1) (Val v2)) σ1 κ e2 σ2 es.
Proof.
  intros Hatomic [K e1' e2' Hfill -> Hstep]. simpl in *.
  induction K as [| k K _] using rev_ind.
  - invert Hstep.
    constructor. done.
  - rewrite fillｰapp /= in Hfill. destruct k; inversion Hfill; subst; clear Hfill.
    + assert (filli k (fill K e1') = fill (K ++ [k]) e1') as Heq1; first by rewrite fillｰapp.
      assert (filli k (fill K e2') = fill (K ++ [k]) e2') as Heq2; first by rewrite fillｰapp.
      rewrite fillｰapp /=. rewrite Heq1 in Hatomic.
      assert (is_Some (to_val (fill (K ++ [k]) e2'))) as H.
      { eapply (Hatomic tid σ1 _ κ σ2 es), (base_stepｰfillｰprim_step' (K ++ [k])); done. }
      destruct H as [v H]. apply to_valｰfillｰSome in H. destruct H, K; done.
    + rename select (of_val v1 = _) into Hv1.
      assert (to_val (fill K e1') = Some v1) as Hfill_v1 by rewrite -Hv1 //.
      apply to_valｰfillｰSome in Hfill_v1 as (-> & ->).
      invert Hstep.
    + rename select (of_val v2 = _) into Hv2.
      assert (to_val (fill K e1') = Some v2) as Hfill_v2 by rewrite -Hv2 //.
      apply to_valｰfillｰSome in Hfill_v2 as (-> & ->).
      invert Hstep.
Qed.
