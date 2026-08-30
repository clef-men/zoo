Require Import zoo.prelude.
Require Export zoo.language.semantics.
Require Import zoo.options.

Implicit Type e eᵣ : expr.
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
  | base_stepｰfillｰprim_step' K eᵣ1 eᵣ2 :
      e1 = fill K eᵣ1 →
      e2 = fill K eᵣ2 →
      base_step tid eᵣ1 σ1 κ eᵣ2 σ2 es →
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
#[global] Arguments nsteps n ρ1 κ ρ2 : assert.
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
  { contextｰfillｰnotｰval e :
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
  induction k; intros ?*; naive.
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
  induction k2; intros k1; destruct k1; try naive.
  intros H1 H2 [= -> -> H%app_inj_2]; first naive.
  simpl. do 3 f_equal.
  apply (f_equal reverse) in H.
  rewrite !reverse_app !reverse_cons -!fmap_reverse /= in H.
  match goal with |- ?vs1 = ?vs2 =>
    apply (inj reverse);
    remember (reverse vs1) as vs1';
    remember (reverse vs2) as vs2';
    clear- H1 H2 H; move: vs2' H; induction vs1'; intros []; naive
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
      clear- H; move: vs2' H; induction vs1'; intros []; naive
    end.
Qed.

#[global] Instance fillｰinj K :
  Inj (=) (=) (fill K).
Proof.
  induction K as [| k K IH].
  all: rewrite /Inj.
  all: naive.
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
Lemma fillｰnotｰval K e :
  to_val e = None →
  to_val (fill K e) = None.
Proof.
  rewrite !eq_None_not_Some.
  eauto using fillｰval.
Qed.
Lemma fillｰprim_step tid K e1 σ1 κ e2 σ2 es :
  prim_step tid e1 σ1 κ e2 σ2 es →
  prim_step tid (fill K e1) σ1 κ (fill K e2) σ2 es.
Proof.
  destruct 1 as [K' e1ᵣ e2ᵣ -> ->].
  rewrite -!fillｰapp.
  econstructor => //.
Qed.
Lemma fillｰreducible tid K e σ :
  reducible tid e σ →
  reducible tid (fill K e) σ.
Proof.
  intros (κ & e' & σ' & es & ?).
  exists κ, (fill K e'), σ', es.
  apply fillｰprim_step => //.
Qed.

Lemma base_stepｰnotｰval tid e1 σ1 κ e2 σ2 es :
  base_step tid e1 σ1 κ e2 σ2 es →
  to_val e1 = None.
Proof.
  destruct 1; naive.
Qed.
Lemma base_stepｰtoｰval tid e σ κ1 e1 σ1' es1 κ2 e2 σ2' es2 :
  base_step tid e σ κ1 e1 σ1' es1 →
  base_step tid e σ κ2 e2 σ2' es2 →
  is_Some (to_val e1) →
  is_Some (to_val e2).
Proof.
  intros Hstep1 Hstep2 He1.
  inv Hstep1; inv Hstep2 => //.
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
      all: eauto using fillｰnotｰval, base_stepｰnotｰval.
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
Lemma baseｰredexｰunique tid K1 e1 σ1 K2 e2 σ2 :
  fill K1 e1 = fill K2 e2 →
  base_reducible tid e1 σ1 →
  base_reducible tid e2 σ2 →
    K1 = K2 ∧
    e1 = e2.
Proof.
  intros Heq (κ1 & e1' & σ1' & es1 & Hstep1) (κ2 & e2' & σ2' & es2 & Hstep2).
  edestruct (stepｰbyｰval tid K2 K1 e2 e1) as (K & ->).
  { done. }
  { eauto using base_stepｰnotｰval. }
  { eauto using base_stepｰnotｰval. }
  rewrite fillｰapp in Heq.
  apply (inj (fill _)) in Heq as <-.
  odestruct (base_stepｰfillｰval _ K) as [[]%not_eq_None_Some | ->] => //.
  { eapply base_stepｰnotｰval => //. }
Qed.

Lemma base_reducible_no_obsｰbase_reducible tid e σ :
  base_reducible_no_obs tid e σ →
  base_reducible tid e σ.
Proof.
  intros (e' & σ' & es & Hstep).
  eexists. eauto.
Qed.

Lemma base_stepｰprim_step tid e1 σ1 κ e2 σ2 es :
  base_step tid e1 σ1 κ e2 σ2 es →
  prim_step tid e1 σ1 κ e2 σ2 es.
Proof.
  apply (base_stepｰfillｰprim_step' []).
  all: rewrite ?fillｰnil //.
Qed.
Lemma base_stepｰfillｰprim_step tid K e1 σ1 κ e2 σ2 es :
  base_step tid e1 σ1 κ e2 σ2 es →
  prim_step tid (fill K e1) σ1 κ (fill K e2) σ2 es.
Proof.
  econstructor => //.
Qed.

Lemma prim_stepｰnotｰval tid e σ κ e' σ' es :
  prim_step tid e σ κ e' σ' es →
  to_val e = None.
Proof.
  intros [K eᵣ1 eᵣ2 -> -> ?%base_stepｰnotｰval].
  apply eq_None_not_Some. intros ?%fillｰval%eq_None_not_Some; done.
Qed.

Lemma reducibleｰnotｰval tid e σ :
  reducible tid e σ →
  to_val e = None.
Proof.
  intros (κ & e' & σ' & es & Hstep).
  eauto using prim_stepｰnotｰval.
Qed.
Lemma reducible_no_obsｰreducible tid e σ :
  reducible_no_obs tid e σ →
  reducible tid e σ.
Proof.
  intros (e' & σ' & es & Hstep).
  eexists. eauto.
Qed.
Lemma base_reducibleｰreducible tid e σ :
  base_reducible tid e σ →
  reducible tid e σ.
Proof.
  intros (κ & e' & σ' & es & Hstep).
  exists κ, e', σ', es.
  apply base_stepｰprim_step. done.
Qed.
Lemma reducibleｰfillｰbase_reducible tid e σ :
  reducible tid e σ →
    ∃ K eᵣ,
    e = fill K eᵣ ∧
    base_reducible tid eᵣ σ.
Proof.
  intros (κ & e' & σ' & es & [K eᵣ eᵣ' -> -> Hstep]).
  exists K, eᵣ. split => //.
  exists κ, eᵣ', σ', es => //.
Qed.

Lemma base_atomicｰatomic e :
  base_atomic e →
  sub_redexes_are_values e →
  Atomic e.
Proof.
  intros Hatomic_step Hatomic_fill tid σ κ e' σ' es [K eᵣ1 eᵣ2 -> -> Hstep].
  assert (K = []) as -> by eauto 10 using base_stepｰnotｰval.
  rewrite fillｰnil. eapply Hatomic_step. rewrite fillｰnil //.
Qed.

Lemma base_reducibleｰfillｰprim_step tid K eᵣ σ κ e' σ' es :
  base_reducible tid eᵣ σ →
  prim_step tid (fill K eᵣ) σ κ e' σ' es →
    ∃ eᵣ',
    e' = fill K eᵣ' ∧
    base_step tid eᵣ σ κ eᵣ' σ' es.
Proof.
  intros (κᵣ & eᵣ' & σᵣ & esᵣ & Hstep) [𝐾 𝑒ᵣ 𝑒ᵣ' Heq -> H𝑠𝑡𝑒𝑝].
  edestruct (stepｰbyｰval tid K) as [K' ?]; eauto using base_stepｰnotｰval. simplify_eq/=.
  rewrite !fillｰapp in Heq |- *.
  simplify_eq.
  exists (fill K' 𝑒ᵣ'). split => //.
  apply base_stepｰfillｰval in Hstep as [(v & H𝑒ᵣ) | ->].
  { apply base_stepｰnotｰval in H𝑠𝑡𝑒𝑝. simplify_eq. }
  { rewrite !fillｰnil //. }
Qed.
Lemma base_reducibleｰprim_step tid e1 σ1 κ e2 σ2 es :
  base_reducible tid e1 σ1 →
  prim_step tid e1 σ1 κ e2 σ2 es →
  base_step tid e1 σ1 κ e2 σ2 es.
Proof.
  intros.
  edestruct (base_reducibleｰfillｰprim_step tid []) as (? & ? & ?).
  all: rewrite ?fillｰnil; eauto.
  simp. done.
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
  constructor; naive.
Qed.
#[global] Instance contextｰfill K :
  Context (fill K).
Proof.
  split => /=.
  - auto using fillｰnotｰval.
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
  naive eauto using contextｰfillｰstep.
Qed.
Lemma reducibleｰcontextｰinv (K : expr → expr) `{!Context K} tid e σ :
  to_val e = None →
  reducible tid (K e) σ →
  reducible tid e σ.
Proof.
  intros He (e' & σ' & k & es & Hstep). rewrite /reducible.
  apply contextｰfillｰstepｰinv in Hstep as (e2' & _ & Hstep); naive.
Qed.

Lemma pure_stepｰcontext (K : expr → expr) `{!Context K} e1 e2 :
  pure_step e1 e2 →
  pure_step (K e1) (K e2).
Proof.
  intros [Hred Hstep]. split.
  - rewrite /reducible_no_obs in Hred |- *. naive eauto using contextｰfillｰstep.
  - intros tid σ1 κ e2' σ2 es Hpstep.
    destruct (contextｰfillｰstepｰinv tid e1 σ1 κ e2' σ2 es) as (e2'' & -> & ?); [|exact Hpstep|].
    + destruct (Hred tid σ1) as (? & ? & ? & ?); eauto using prim_stepｰnotｰval.
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

Lemma pure_nstepsｰfill {n e1 e2} K :
  relations.nsteps pure_step n e1 e2 →
  relations.nsteps pure_step n (fill K e1) (fill K e2).
Proof.
  intros Hsteps.
  eapply pure_execｰfill. 2: done.
  intros _ => //.
Qed.
Lemma pure_stepsｰfill {e1 e2} K :
  rtc pure_step e1 e2 →
  rtc pure_step (fill K e1) (fill K e2).
Proof.
  rewrite !rtc_nsteps.
  intros (n & Hsteps%(pure_nstepsｰfill K)).
  eauto.
Qed.
Lemma pure_stepｰfill {e1 e2} K :
  pure_step e1 e2 →
  pure_step (fill K e1) (fill K e2).
Proof.
  intros Hstep%nsteps_once%(pure_nstepsｰfill K).
  apply nsteps_once_inv => //.
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
  { intro A. rewrite fillｰnotｰval // in H. }
  assert (∃ w, e = Val w) as [w ->].
  { destruct e; try done; eauto. }
  assert (to_val (fill (k :: K) (Val w)) = None).
  { destruct k; simpl; apply fillｰnotｰval; done. }
  simp.
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
  - induction 1; naive.
  - intros (n & κs & Hsteps).
    induction Hsteps; eauto using rtc.
Qed.

Lemma stepｰlength ρ1 κ ρ2 :
  step ρ1 κ ρ2 →
  length ρ1.1 ≤ length ρ2.1.
Proof.
  intros (tid & e1 & e2 & σ2 & es & Hstep & Hlookup & ->).
  simp_length/=. lia.
Qed.
Lemma nstepsｰlength n ρ1 κs ρ2 :
  nsteps n ρ1 κs ρ2 →
  length ρ1.1 ≤ length ρ2.1.
Proof.
  induction 1 as [| ? ? ? ? ? ? Hstep%stepｰlength]; lia.
Qed.

Lemma valｰnot_stuck tid e σ :
  is_Some (to_val e) →
  not_stuck tid e σ.
Proof.
  intros (v & ?). left => //.
Qed.
Lemma reducibleｰnot_stuck tid e σ :
  reducible tid e σ →
  not_stuck tid e σ.
Proof.
  rewrite /not_stuck. auto.
Qed.
Lemma pure_stepｰnot_stuck tid e1 e2 σ :
  pure_step e1 e2 →
  not_stuck tid e1 σ.
Proof.
  intros Hstep.
  eapply reducibleｰnot_stuck, reducible_no_obsｰreducible, pure_stepｰsafe => //.
Qed.

Lemma safeｰstep ρ1 ρ2 :
  safe ρ1 →
  silent_step ρ1 ρ2 →
  safe ρ2.
Proof.
  intros Hsafe Hstep ρ3 Hsteps.
  apply Hsafe. eauto using rtc.
Qed.
Lemma safeｰnot_stuck ρ tid e :
  safe ρ →
  ρ.1 !! tid = Some e →
  not_stuck tid e ρ.2.
Proof.
  intros Hsafe Hlookup.
  specialize (Hsafe ρ). rewrite Foralliｰlookup in Hsafe.
  eauto using rtc.
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
  - inv/= Hstep.
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
      inv Hstep.
    + rename select (of_val v2 = _) into Hv2.
      assert (to_val (fill K e1') = Some v2) as Hfill_v2 by rewrite -Hv2 //.
      apply to_valｰfillｰSome in Hfill_v2 as (-> & ->).
      inv Hstep.
Qed.
