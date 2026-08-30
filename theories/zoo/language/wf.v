Require Import stdpp.gmap.

Require Import zoo.prelude.
Require Import zoo.common.fin_maps.
Require Export zoo.language.language.
Require Import zoo.options.

Implicit Type i : nat.
Implicit Type n m : Z.
Implicit Type tag : tag.
Implicit Type l : location.
Implicit Type pid : prophet_id.
Implicit Type gen : generativity.
Implicit Type mut : mutability.
Implicit Type lit : literal.
Implicit Type e eᵣ : expr.
Implicit Type es : list expr.
Implicit Type v w : val.
Implicit Type vs : list val.
Implicit Type br : branch.
Implicit Type brs : list branch.
Implicit Type subj : subject.
Implicit Type rec : recursive.
Implicit Type recs : list recursive.
Implicit Type tid : thread_id.
Implicit Type hdr : header.
Implicit Type κ κs s : list observation.
Implicit Type k : ectxi.
Implicit Type K : ectx.
Implicit Type h : gmap location val.
Implicit Type σ : state.
Implicit Type ρ : config.

Fixpoint expr۰wf e :=
  match e with
  | Val v =>
      val۰wf v
  | Var _ =>
      True
  | Rec _ _ e =>
      expr۰wf e
  | App e1 e2 =>
      expr۰wf e1 ∧
      expr۰wf e2
  | Let _ e1 e2 =>
      expr۰wf e1 ∧
      expr۰wf e2
  | Unop _ e =>
      expr۰wf e
  | Binop _ e1 e2 =>
      expr۰wf e1 ∧
      expr۰wf e2
  | Equal e1 e2 =>
      expr۰wf e1 ∧
      expr۰wf e2
  | If e0 e1 e2 =>
      expr۰wf e0 ∧
      expr۰wf e1 ∧
      expr۰wf e2
  | For e1 e2 e3 =>
      expr۰wf e1 ∧
      expr۰wf e2 ∧
      expr۰wf e3
  | Alloc e1 e2 =>
      expr۰wf e1 ∧
      expr۰wf e2
  | Block _ _ es =>
      Forall' expr۰wf es
  | Match e0 _ e1 brs =>
      expr۰wf e0 ∧
      expr۰wf e1 ∧
      Forall' (λ br, expr۰wf br.2) brs
  | GetTag e =>
      expr۰wf e
  | GetSize e =>
      expr۰wf e
  | Load e1 e2 =>
      expr۰wf e1 ∧
      expr۰wf e2
  | Store e1 e2 e3 =>
      expr۰wf e1 ∧
      expr۰wf e2 ∧
      expr۰wf e3
  | Xchg e1 e2 =>
      expr۰wf e1 ∧
      expr۰wf e2
  | CAS e0 e1 e2 =>
      expr۰wf e0 ∧
      expr۰wf e1 ∧
      expr۰wf e2
  | FAA e1 e2 =>
      expr۰wf e1 ∧
      expr۰wf e2
  | Fork e =>
      expr۰wf e
  | LocalGet =>
      True
  | LocalSet e =>
      expr۰wf e
  | Proph =>
      True
  | Resolve e0 e1 e2 =>
      expr۰wf e0 ∧
      expr۰wf e1 ∧
      expr۰wf e2
  | ResolveErasure _ _ _ =>
      False
  end
with val۰wf v :=
  match v with
  | ValLit _ =>
      True
  | ValRecs _ recs =>
      Forall' (λ rec, expr۰wf rec.2) recs
  | ValBlock _ _ vs =>
      Forall' val۰wf vs
  end.
#[global] Arguments expr۰wf !_ / : assert.
#[global] Arguments val۰wf !_ / : assert.

Fixpoint ectxi۰wf k :=
  match k with
  | CtxApp1 v2 =>
      val۰wf v2
  | CtxApp2 e1 =>
      expr۰wf e1
  | CtxLet _ e2 =>
      expr۰wf e2
  | CtxUnop _ =>
      True
  | CtxBinop1 _ v2 =>
      val۰wf v2
  | CtxBinop2 _ e1 =>
      expr۰wf e1
  | CtxEqual1 v2 =>
      val۰wf v2
  | CtxEqual2 e1 =>
      expr۰wf e1
  | CtxIf e1 e2 =>
      expr۰wf e1 ∧
      expr۰wf e2
  | CtxFor1 e2 e3 =>
      expr۰wf e2 ∧
      expr۰wf e3
  | CtxFor2 v1 e3 =>
      val۰wf v1 ∧
      expr۰wf e3
  | CtxAlloc1 v2 =>
      val۰wf v2
  | CtxAlloc2 e1 =>
      expr۰wf e1
  | CtxBlock _ _ es vs =>
      Forall' expr۰wf es ∧
      Forall' val۰wf vs
  | CtxMatch _ e1 brs =>
      expr۰wf e1 ∧
      Forall' (λ br, expr۰wf br.2) brs
  | CtxGetTag =>
      True
  | CtxGetSize =>
      True
  | CtxLoad1 v2 =>
      val۰wf v2
  | CtxLoad2 e1 =>
      expr۰wf e1
  | CtxStore1 v2 v3 =>
      val۰wf v2 ∧
      val۰wf v3
  | CtxStore2 e1 v3 =>
      expr۰wf e1 ∧
      val۰wf v3
  | CtxStore3 e1 e2 =>
      expr۰wf e1 ∧
      expr۰wf e2
  | CtxXchg1 v2 =>
      val۰wf v2
  | CtxXchg2 e1 =>
      expr۰wf e1
  | CtxCAS0 v1 v2 =>
      val۰wf v1 ∧
      val۰wf v2
  | CtxCAS1 e0 v2 =>
      expr۰wf e0 ∧
      val۰wf v2
  | CtxCAS2 e0 e1 =>
      expr۰wf e0 ∧
      expr۰wf e1
  | CtxFAA1 v2 =>
      val۰wf v2
  | CtxFAA2 e1 =>
      expr۰wf e1
  | CtxLocalSet =>
      True
  | CtxResolve0 k v1 v2 =>
      ectxi۰wf k ∧
      val۰wf v1 ∧
      val۰wf v2
  | CtxResolve1 e0 v2 =>
      expr۰wf e0 ∧
      val۰wf v2
  | CtxResolve2 e0 e1 =>
      expr۰wf e0 ∧
      expr۰wf e1
  | CtxResolveErasure0 _ _ =>
      False
  | CtxResolveErasure1 _ _ =>
      False
  | CtxResolveErasure2 _ _ =>
      False
  end.
#[global] Arguments ectxi۰wf !_ / : assert.

Definition branch۰wf br :=
  expr۰wf br.2.

Definition recursive۰wf rec :=
  expr۰wf rec.2.

Definition subject۰wf subj :=
  match subj with
  | SubjectLoc _ =>
      True
  | SubjectBlock _ vs =>
      Forall val۰wf vs
  end.
#[global] Arguments subject۰wf !_ / : assert.

Definition ectx۰wf K :=
  Forall ectxi۰wf K.

Definition heap۰wf h :=
  map_Forall (const val۰wf) h.

Record state۰wf σ :=
  { state۰wfｰheap :
      heap۰wf σ.(state۰heap)
  ; state۰wfｰlocals :
      Forall val۰wf σ.(state۰locals)
  }.

Record config۰wf ρ :=
  { config۰wfｰexprs :
      Forall expr۰wf ρ.1
  ; config۰wfｰstate :
      state۰wf ρ.2
  }.

Lemma valｰimmediateｰwf v :
  val۰immediate v →
  val۰wf v.
Proof.
  destruct v as [| | gen tag []] => //.
Qed.

Lemma filliｰwf₁ k e :
  expr۰wf (filli k e) →
    ectxi۰wf k ∧
    expr۰wf e.
Proof.
  induction k; try naive.
  rewrite /= /of_vals. simp_Forall. naive.
Qed.
Lemma filliｰwf₂ k e :
  ectxi۰wf k →
  expr۰wf e →
  expr۰wf (filli k e).
Proof.
  induction k; try naive.
  rewrite /= /of_vals. simp_Forall. naive.
Qed.
Lemma filliｰwf k e :
  expr۰wf (filli k e) ↔
    ectxi۰wf k ∧
    expr۰wf e.
Proof.
  split.
  - apply filliｰwf₁.
  - intros (Hwf_k & Hwf_e).
    apply filliｰwf₂ => //.
Qed.

Lemma fillｰwf₁ K e :
  expr۰wf (fill K e) →
    ectx۰wf K ∧
    expr۰wf e.
Proof.
  move: e. induction K as [| k K IH] using rev_ind => /= e Hwf.
  all: rewrite /ectx۰wf.
  - done.
  - rewrite fillｰapp /= in Hwf.
    apply filliｰwf in Hwf as (Hwf_k & Hwf).
    simp_Forall. naive.
Qed.
Lemma fillｰwf₂ K e :
  ectx۰wf K →
  expr۰wf e →
  expr۰wf (fill K e).
Proof.
  move: e. induction K as [| k K IH] using rev_ind => //= e Hwf Hwf_e.
  rewrite /ectx۰wf in Hwf. simp_Forall in Hwf.
  rewrite fillｰapp.
  apply filliｰwf; naive.
Qed.
Lemma fillｰwf K e :
  expr۰wf (fill K e) ↔
    ectx۰wf K ∧
    expr۰wf e.
Proof.
  split.
  - apply fillｰwf₁.
  - intros (Hwf_K & Hwf_e).
    apply fillｰwf₂ => //.
Qed.

Lemma substｰwf x v e :
  val۰wf v →
  expr۰wf e →
  expr۰wf (subst x v e).
Proof.
  induction e => /= Hwf_v Hwf_e.
  all: try naive.
  all: simp_Forall+ in *; eauto.
  all: case_match => /=.
  all: try naive.
  all: split_and!; [naive.. |].
  all: intros; case_match; naive.
Qed.
Lemma subst'ｰwf x v e :
  val۰wf v →
  expr۰wf e →
  expr۰wf (subst' x v e).
Proof.
  destruct x => //=.
  apply substｰwf.
Qed.
Lemma subst_listｰwf xs vs e :
  length xs = length vs →
  Forall val۰wf vs →
  expr۰wf e →
  expr۰wf (subst_list xs vs e).
Proof.
  intros Hlength Hwf_vs Hws_e.
  move: vs Hwf_vs xs Hlength. induction 1 as [| v vs Hwf_v Hwf_vs IH] using Forall_ind => xs Hlength.
  all: destruct xs as [| x xs] => //=.
  apply subst'ｰwf; naive.
Qed.

Lemma eval_app۰auxｰwf recs i rec e :
  Forall recursive۰wf recs →
  recursive۰wf rec →
  expr۰wf e →
  expr۰wf (eval_app۰aux recs i rec e).
Proof.
  intros Hwf_recs Hwf_rec Hwf_e.
  apply subst'ｰwf => //. simp_Forall+/=.
Qed.
Lemma eval_appｰwf recs x v e :
  Forall recursive۰wf recs →
  val۰wf v →
  expr۰wf e →
  expr۰wf (eval_app recs x v e).
Proof.
  intros Hwf_recs Hwf_v Hwf_e.
  cut (
    ∀ recs0,
    Forall recursive۰wf recs0 →
      ∀ recs,
      Forall recursive۰wf recs →
        ∀ acc i,
        expr۰wf acc →
        expr۰wf (foldri' (eval_app۰aux recs0) acc recs i)
  ).
  { intros Hcut.
    apply Hcut. 1,2: done.
    apply subst'ｰwf => //.
  }
  clear. intros recs0 Hwf_recs0.
  induction 1 as [| rec recs Hwf_rec Hwf_recs IH] using Forall_ind => //= acc i Hacc.
  apply eval_app۰auxｰwf.
  - done.
  - done.
  - naive.
Qed.

Lemma subject۰to_valｰwf tag subj :
  subject۰wf subj →
  val۰wf (subject۰to_val tag subj).
Proof.
  destruct subj => //.
  simp_Forall+/=.
Qed.

Lemma eval_matchｰwf tag sz subj x_fb e_fb brs e :
  eval_match tag sz subj x_fb e_fb brs = Some e →
  subject۰wf subj →
  (if subj is SubjectBlock _ vs then sz = length vs else True) →
  expr۰wf e_fb →
  Forall branch۰wf brs →
  expr۰wf e.
Proof.
  intros H Hwf_subj Hsubj Hwf_e_fb Hwf_brs.
  move: brs Hwf_brs H. induction 1 as [| br brs Hwf_br Hwf_brs IH] using Forall_ind.
  - injection 1 as <-.
    apply subst'ｰwf => //.
    apply subject۰to_valｰwf => //.
  - destruct subj => /=.
    all: repeat case_match.
    all: try done.
    + injection 1 as <-.
      apply subst'ｰwf => //.
    + injection 1 as <-.
      apply subst_listｰwf => //.
      { apply andb_true_iff in H as (_ & ?).
        rewrite -beqｰspec. eauto.
      }
      apply subst'ｰwf => //.
      simp_Forall+/=.
Qed.

Lemma heapｰunionｰwf h1 h2 :
  heap۰wf h1 →
  heap۰wf h2 →
  heap۰wf (h1 ∪ h2).
Proof.
  apply map_Forall_union_2.
Qed.
Lemma heapｰinsertｰwf h l v :
  heap۰wf h →
  val۰wf v →
  heap۰wf (<[l := v]> h).
Proof.
  intros Hwf_h Hwf_v.
  apply map_Forallｰinsert₂' => //.
  apply map_Forall_delete => //.
Qed.
Lemma chunkｰwf l vs :
  Forall val۰wf vs →
  heap۰wf (chunk l vs).
Proof.
  intros Hwf_vs.
  move: vs Hwf_vs l. induction 1 as [| v vs Hwf_v Hwf_vs IH] using Forall_ind => //= l.
  apply heapｰinsertｰwf => //.
Qed.

Lemma state۰allocｰwf l hdr vs σ :
  state۰wf σ →
  Forall val۰wf vs →
  state۰wf (state۰alloc l hdr vs σ).
Proof.
  intros Hwf_σ Hwf_vs.
  split => /=.
  - apply heapｰunionｰwf.
    + apply chunkｰwf => //.
    + apply Hwf_σ.
  - apply Hwf_σ.
Qed.
Lemma state۰set_locationｰwf l v σ :
  val۰wf v →
  state۰wf σ →
  state۰wf (state۰set_location l v σ).
Proof.
  intros Hwf_v Hwf_σ.
  split => /=.
  - apply heapｰinsertｰwf => //.
    apply Hwf_σ.
  - apply Hwf_σ.
Qed.
Lemma state۰add_localｰwf v σ :
  val۰wf v →
  state۰wf σ →
  state۰wf (state۰add_local v σ).
Proof.
  intros Hwf_v Hwf_σ.
  split => /=.
  - apply Hwf_σ.
  - simp_Forall.
    split_and! => //.
    apply Hwf_σ.
Qed.
Lemma state۰set_localｰwf tid v σ :
  val۰wf v →
  state۰wf σ →
  state۰wf (state۰set_local tid v σ).
Proof.
  intros Hwf_v Hwf_σ.
  split => /=.
  - apply Hwf_σ.
  - apply Forall_insert => //.
    apply Hwf_σ.
Qed.
Lemma state۰add_prophetｰwf pid σ :
  state۰wf σ →
  state۰wf (state۰add_prophet pid σ).
Proof.
  intros Hwf_σ.
  split => /=.
  all: apply Hwf_σ.
Qed.

Lemma base_stepｰwf tid e σ κ e' σ' es :
  base_step tid e σ κ e' σ' es →
  expr۰wf e →
  state۰wf σ →
    expr۰wf e' ∧
    state۰wf σ' ∧
    Forall expr۰wf es.
Proof.
  intros Hstep Hwf_e Hwf_σ.
  induction Hstep.
  all: try done.
  all: simpl in *.
  all: try (split_and! => //; []).
  - apply eval_appｰwf.
    + simp_Forall in *. naive.
    + naive.
    + simp_Forall+ in *. naive.
  - apply subst'ｰwf; naive.
  - case_match; naive.
  - case_match; naive.
  - apply state۰allocｰwf => //.
    apply Forall_replicate => //.
  - apply state۰allocｰwf => //.
    subst. rewrite /of_vals in Hwf_e.
    simp_Forall+ in *.
  - subst. rewrite /of_vals in Hwf_e.
    simp_Forall+ in *.
  - subst. rewrite /of_vals in Hwf_e.
    simp_Forall+ in *.
  - subst. rewrite /of_vals in Hwf_e.
    simp_Forall+ in *.
  - eapply eval_matchｰwf; try naive.
    simp_Forall in *. naive.
  - eapply eval_matchｰwf; try naive.
    all: simp_Forall in *; naive.
  - eapply state۰wfｰheap, map_Forall_lookup_1 in Hwf_σ => //.
  - simp_Forall+ in *. naive.
  - apply state۰set_locationｰwf; naive.
  - split_and! => //.
    + eapply state۰wfｰheap, map_Forall_lookup_1 in Hwf_σ => //.
    + apply state۰set_locationｰwf; naive.
  - apply state۰set_locationｰwf; naive.
  - apply state۰set_locationｰwf; naive.
  - split_and! => //.
    + apply state۰add_localｰwf => //.
      apply valｰimmediateｰwf => //.
    + auto.
  - eapply state۰wfｰlocals, Forall_lookup in Hwf_σ => //.
  - apply state۰set_localｰwf => //.
  - apply state۰add_prophetｰwf => //.
  - naive.
Qed.
Lemma prim_stepｰwf tid e σ κ e' σ' es :
  prim_step tid e σ κ e' σ' es →
  expr۰wf e →
  state۰wf σ →
    expr۰wf e' ∧
    state۰wf σ' ∧
    Forall expr۰wf es.
Proof.
  intros [K eᵣ eᵣ' -> -> Hstep] Hwf_e Hwf_σ.
  apply fillｰwf in Hwf_e as (Hwf_K & Hwf_eᵣ).
  apply base_stepｰwf in Hstep as (Hwf_e' & Hwf_σ' & Hwf_es) => //.
  rewrite fillｰwf //.
Qed.
