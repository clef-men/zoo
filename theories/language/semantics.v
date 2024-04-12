From stdpp Require Import
  gmap.

From iris.algebra Require Import
  ofe.

From zebre Require Import
  prelude.
From zebre.language Require Export
  syntax.
From zebre Require Import
  options.

Implicit Types b : bool.
Implicit Types tag proj : nat.
Implicit Types n m : Z.
Implicit Types l : location.
Implicit Types lit : literal.
Implicit Types x : binder.
Implicit Types e : expr.
Implicit Types es : list expr.
Implicit Types v w : val.
Implicit Types vs : list val.
Implicit Types br : branch.
Implicit Types brs : list branch.

Definition literal_physical lit :=
  match lit with
  | LiteralBool _
  | LiteralInt _
  | LiteralLoc _ =>
      True
  | LiteralProphecy _
  | LiteralPoison =>
      False
  end.
#[global] Arguments literal_physical !_ / : assert.

Definition literal_eq lit1 lit2 :=
  match lit1, lit2 with
  | LiteralBool b1, LiteralBool b2 =>
      b1 = b2
  | LiteralInt i1, LiteralInt i2 =>
      i1 = i2
  | LiteralLoc l1, LiteralLoc l2 =>
      l1 = l2
  | LiteralLoc _, _
  | _, LiteralLoc _ =>
      False
  | _, _ =>
      True
  end.
#[global] Arguments literal_eq !_ !_ / : assert.

#[global] Instance literal_eq_refl :
  Reflexive literal_eq.
Proof.
  intros []; done.
Qed.
#[global] Instance literal_eq_sym :
  Symmetric literal_eq.
Proof.
  do 2 intros []; done.
Qed.

Definition val_physical v :=
  match v with
  | ValLiteral lit =>
      literal_physical lit
  | _ =>
      True
  end.
#[global] Arguments val_physical !_ / : assert.
Class ValPhysical v :=
  val_physical' : val_physical v.

Definition val_neq v1 v2 :=
  match v1, v2 with
  | ValLiteral lit1, ValLiteral lit2 =>
      lit1 ≠ lit2
  | ValConstr (Some cid1) _ _, ValConstr (Some cid2) _ _ =>
      cid1 ≠ cid2
  | ValConstr _ tag1 [], ValConstr _ tag2 [] =>
      tag1 ≠ tag2
  | _, _ =>
      True
  end.
#[global] Arguments val_neq !_ !_ / : assert.

#[global] Instance val_neq_sym :
  Symmetric val_neq.
Proof.
  do 2 intros [| | [] ? []]; done.
Qed.

Definition val_eq v1 v2 :=
  match v1 with
  | ValLiteral lit1 =>
      match v2 with
      | ValLiteral lit2 =>
          literal_eq lit1 lit2
      | ValConstr _ _ [] =>
          match lit1 with
          | LiteralBool _
          | LiteralInt _ =>
              True
          | _ =>
              False
          end
      | _ =>
          False
      end
  | ValRec f1 x1 e1 =>
      match v2 with
      | ValRec f2 x2 e2 =>
          f1 = f2 ∧ x1 = x2 ∧ e1 = e2
      | _ =>
          False
      end
  | ValConstr (Some cid1) tag1 [] =>
      match v2 with
      | ValBool _
      | ValInt _ =>
          True
      | ValConstr (Some cid2) _ _ =>
          cid1 = cid2
      | ValConstr None tag2 es2 =>
          tag1 = tag2 ∧ [] = es2
      | _ =>
          False
      end
  | ValConstr (Some cid1) tag1 es1 =>
      match v2 with
      | ValConstr (Some cid2) _ _ =>
          cid1 = cid2
      | ValConstr None tag2 es2 =>
          tag1 = tag2 ∧ es1 = es2
      | _ =>
          False
      end
  | ValConstr _ tag1 [] =>
      match v2 with
      | ValBool _
      | ValInt _ =>
          True
      | ValConstr _ tag2 [] =>
          tag1 = tag2
      | _ =>
          False
      end
  | ValConstr _ tag1 es1 =>
      match v2 with
      | ValConstr _ tag2 es2 =>
          tag1 = tag2 ∧ es1 = es2
      | _ =>
          False
      end
  end.
#[global] Arguments val_eq !_ !_ / : assert.

Definition val_consistency v1 v2 :=
  match v1, v2 with
  | ValConstr (Some _) tag1 es1, ValConstr (Some _) tag2 es2 =>
      tag1 = tag2 ∧ es1 = es2
  | _, _ =>
      True
  end.
#[global] Arguments val_consistency !_ !_ / : assert.

#[global] Instance val_eq_refl :
  Reflexive val_eq.
Proof.
  intros [[] | | [] ? []]; done.
Qed.
#[global] Instance val_eq_sym :
  Symmetric val_eq.
Proof.
  do 2 intros [| | [] ? []]; try naive_solver congruence.
Qed.
Lemma eq_val_eq v1 v2 :
  v1 = v2 →
  val_eq v1 v2.
Proof.
  destruct v1 as [| | [] ? []]; naive_solver.
Qed.

Definition unop_eval op v :=
  match op, v with
  | UnopNeg, ValBool b =>
      Some $ ValBool (negb b)
  | UnopMinus, ValInt n =>
      Some $ ValInt (- n)
  | _, _ =>
      None
  end.
#[global] Arguments unop_eval !_ !_ / : assert.

Definition binop_eval_int op n1 n2 :=
  match op with
  | BinopPlus =>
      Some $ LiteralInt (n1 + n2)
  | BinopMinus =>
      Some $ LiteralInt (n1 - n2)
  | BinopMult =>
      Some $ LiteralInt (n1 * n2)
  | BinopQuot =>
      Some $ LiteralInt (n1 `quot` n2)
  | BinopRem =>
      Some $ LiteralInt (n1 `rem` n2)
  | BinopLe =>
      Some $ LiteralBool (bool_decide (n1 ≤ n2))
  | BinopLt =>
      Some $ LiteralBool (bool_decide (n1 < n2))
  | BinopGe =>
      Some $ LiteralBool (bool_decide (n1 >= n2))
  | BinopGt =>
      Some $ LiteralBool (bool_decide (n1 > n2))
  | _ =>
      None
  end%Z.
#[global] Arguments binop_eval_int !_ _ _ / : assert.
Definition binop_eval op v1 v2 :=
  match v1, v2 with
  | ValInt n1, ValInt n2 =>
      ValLiteral <$> binop_eval_int op n1 n2
  | ValLoc l, ValInt n =>
      if decide (op = BinopOffset) then
        Some $ ValLoc (l +ₗ n)
      else
        None
  | _, _ =>
      None
  end.
#[global] Arguments binop_eval !_ !_ !_ / : assert.

Fixpoint subst (x : string) v e :=
  match e with
  | Val _ =>
      e
  | Var y =>
      if decide (x = y) then
        Val v
      else
        Var y
  | Rec f y e =>
      Rec f y
        ( if decide (BNamed x ≠ f ∧ BNamed x ≠ y) then
            subst x v e
          else
            e
        )
  | App e1 e2 =>
      App
        (subst x v e1)
        (subst x v e2)
  | Unop op e =>
      Unop op
        (subst x v e)
  | Binop op e1 e2 =>
      Binop op
        (subst x v e1)
        (subst x v e2)
  | Equal e1 e2 =>
      Equal
        (subst x v e1)
        (subst x v e2)
  | If e0 e1 e2 =>
      If
      (subst x v e0)
      (subst x v e1)
      (subst x v e2)
  | Constr tag es =>
      Constr tag
        (subst x v <$> es)
  | Proj proj e =>
      Proj proj
        (subst x v e)
  | Match e0 y e1 brs =>
      Match
        (subst x v e0)
        y
        (subst x v e1)
        ( ( λ br,
              ( br.1,
                if decide (
                  Forall (BNamed x ≠.) br.1.(pattern_fields) ∧
                  BNamed x ≠ br.1.(pattern_as)
                ) then
                  subst x v br.2
                else
                  br.2
              )
          ) <$> brs
        )
  | Reveal e =>
      Reveal
        (subst x v e)
  | For e1 e2 e3 =>
      For
        (subst x v e1)
        (subst x v e2)
        (subst x v e3)
  | Record es =>
      Record
        (subst x v <$> es)
  | Alloc e1 e2 =>
      Alloc
        (subst x v e1)
        (subst x v e2)
  | Load e =>
      Load
        (subst x v e)
  | Store e1 e2 =>
      Store
        (subst x v e1)
        (subst x v e2)
  | Xchg e1 e2 =>
      Xchg
        (subst x v e1)
        (subst x v e2)
  | Cas e0 e1 e2 =>
      Cas
        (subst x v e0)
        (subst x v e1)
        (subst x v e2)
  | Faa e1 e2 =>
      Faa
        (subst x v e1)
        (subst x v e2)
  | Fork e =>
      Fork
        (subst x v e)
  | Yield =>
      Yield
  | Proph =>
      Proph
  | Resolve e0 e1 e2 =>
      Resolve
        (subst x v e0)
        (subst x v e1)
        (subst x v e2)
  end.
#[global] Arguments subst _ _ !_ / : assert.
Definition subst' x v :=
  match x with
  | BNamed x =>
      subst x v
  | BAnon =>
      id
  end.
#[global] Arguments subst' !_ _ / _ : assert.
Fixpoint subst_list xs vs e :=
  match xs, vs with
  | x :: xs, v :: vs =>
      subst' x v (subst_list xs vs e)
  | _, _ =>
      e
  end.
#[global] Arguments subst_list !_ !_ _ / : assert.

Fixpoint match_apply cid tag vs x e brs :=
  match brs with
  | [] =>
      subst' x (ValConstr cid tag vs) e
  | br :: brs =>
      let pat := br.1 in
      if decide (pat.(pattern_tag) = tag) then
        subst_list pat.(pattern_fields) vs $
        subst' pat.(pattern_as) (ValConstr cid tag vs) br.2
      else
        match_apply cid tag vs x e brs
  end.
#[global] Arguments match_apply _ _ _ _ _ !_ / : assert.

Record state : Type := {
  state_heap : gmap location val ;
  state_prophets : gset prophet_id ;
}.
Implicit Types σ : state.

Canonical stateO :=
  leibnizO state.

Definition state_update_heap f σ : state :=
  {|state_heap := f σ.(state_heap) ;
    state_prophets := σ.(state_prophets) ;
  |}.
#[global] Arguments state_update_heap _ !_ / : assert.
Definition state_update_prophets f σ : state :=
  {|state_heap := σ.(state_heap) ;
    state_prophets := f σ.(state_prophets) ;
  |}.
#[global] Arguments state_update_prophets _ !_ / : assert.

#[global] Instance state_inhabited : Inhabited state :=
  populate
    {|state_heap := inhabitant ;
      state_prophets := inhabitant ;
    |}.

Fixpoint heap_array l vs : gmap location val :=
  match vs with
  | [] =>
      ∅
  | v :: vs =>
      <[l := v]> (heap_array (l +ₗ 1) vs)
  end.

Lemma heap_array_singleton l v :
  heap_array l [v] = {[l := v]}.
Proof.
  rewrite /heap_array insert_empty //.
Qed.
Lemma heap_array_lookup l vs w k :
  heap_array l vs !! k = Some w ↔
    ∃ j,
    (0 ≤ j)%Z ∧
    k = l +ₗ j ∧
    vs !! (Z.to_nat j) = Some w.
Proof.
  revert k l; induction vs as [|v' vs IH]=> l' l /=.
  { rewrite lookup_empty. naive_solver lia. }
  rewrite lookup_insert_Some IH. split.
  - intros [[-> ?] | (Hl & j & ? & -> & ?)].
    { eexists 0. rewrite location_add_0. naive_solver lia. }
    eexists (1 + j)%Z. rewrite location_add_assoc !Z.add_1_l Z2Nat.inj_succ; auto with lia.
  - intros (j & ? & -> & Hil). destruct (decide (j = 0)); simplify_eq/=.
    { rewrite location_add_0; eauto. }
    right. split.
    { rewrite -{1}(location_add_0 l). intros ?%(inj (location_add _)); lia. }
    assert (Z.to_nat j = S (Z.to_nat (j - 1))) as Hj.
    { rewrite -Z2Nat.inj_succ; last lia. f_equal; lia. }
    rewrite Hj /= in Hil.
    eexists (j - 1)%Z. rewrite location_add_assoc Z.add_sub_assoc Z.add_simpl_l. auto with lia.
Qed.
Lemma heap_array_map_disjoint h l vs :
  ( ∀ i,
    (0 ≤ i)%Z →
    (i < length vs)%Z →
    h !! (l +ₗ i) = None
  ) →
  heap_array l vs ##ₘ h.
Proof.
  intros Hdisj. apply map_disjoint_spec=> l' v1 v2.
  intros (j & ? & ? & Hj%lookup_lt_Some%inj_lt)%heap_array_lookup.
  rewrite Z2Nat.id // in Hj. naive_solver.
Qed.

Definition state_init_heap l vs σ :=
  state_update_heap (λ h, heap_array l vs ∪ h) σ.

Definition observation : Set :=
  prophet_id * (val * val).

Inductive base_step : expr → state → list observation → expr → state → list expr → Prop → Prop :=
  | base_step_rec f x e σ :
      base_step
        (Rec f x e)
        σ
        []
        (Val $ ValRec f x e)
        σ
        []
        True
  | base_step_beta f x e v e' σ :
      e' = subst' f (ValRec f x e) (subst' x v e) →
      base_step
        (App (Val $ ValRec f x e) (Val v))
        σ
        []
        e'
        σ
        []
        True
  | base_step_unop op v v' σ :
      unop_eval op v = Some v' →
      base_step
        (Unop op $ Val v)
        σ
        []
        (Val v')
        σ
        []
        True
  | base_step_binop op v1 v2 v' σ :
      binop_eval op v1 v2 = Some v' →
      base_step
        (Binop op (Val v1) (Val v2))
        σ
        []
        (Val v')
        σ
        []
        True
  | base_step_equal_fail v1 v2 σ :
      val_physical v1 →
      val_physical v2 →
      val_neq v1 v2 →
      base_step
        (Equal (Val v1) (Val v2))
        σ
        []
        (Val $ ValBool false)
        σ
        []
        True
  | base_step_equal_suc v1 v2 σ :
      val_physical v1 →
      val_eq v1 v2 →
      base_step
        (Equal (Val v1) (Val v2))
        σ
        []
        (Val $ ValBool true)
        σ
        []
        (val_consistency v1 v2)
  | base_step_if_true e1 e2 σ :
      base_step
        (If (Val $ ValBool true) e1 e2)
        σ
        []
        e1
        σ
        []
        True
  | base_step_if_false e1 e2 σ :
      base_step
        (If (Val $ ValBool false) e1 e2)
        σ
        []
        e2
        σ
        []
        True
  | base_step_constr tag es vs σ :
      es = of_vals vs →
      base_step
        (Constr tag es)
        σ
        []
        (Val $ ValConstr None tag vs)
        σ
        []
        True
  | base_step_proj proj cid tag vs v σ :
      vs !! proj = Some v →
      base_step
        (Proj proj $ Val $ ValConstr cid tag vs)
        σ
        []
        (Val v)
        σ
        []
        True
  | base_step_match cid tag vs x e brs σ :
      base_step
        (Match (Val $ ValConstr cid tag vs) x e brs)
        σ
        []
        (match_apply cid tag vs x e brs)
        σ
        []
        True
  | base_step_reveal cid tag vs σ :
      base_step
        (Reveal $ Val $ ValConstr None tag vs)
        σ
        []
        (Val $ ValConstr (Some cid) tag vs)
        σ
        []
        True
  | base_step_for n1 n2 e σ :
      base_step
        (For (Val $ ValInt n1) (Val $ ValInt n2) e)
        σ
        []
        (if decide (n2 ≤ n1)%Z then Unit else Seq (App e (Val $ ValInt n1)) (For (Val $ ValInt (1 + n1)) (Val $ ValInt n2) e))
        σ
        []
        True
  | base_step_record es vs σ l :
      0 < length es →
      es = of_vals vs →
      ( ∀ i,
        (0 ≤ i < length es)%Z →
        σ.(state_heap) !! (l +ₗ i) = None
      ) →
      base_step
        (Record es)
        σ
        []
        (Val $ ValLoc l)
        (state_init_heap l vs σ)
        []
        True
  | base_step_alloc n v σ l :
      (0 < n)%Z →
      ( ∀ i,
        (0 ≤ i < n)%Z →
        σ.(state_heap) !! (l +ₗ i) = None
      ) →
      base_step
        (Alloc (Val $ ValInt n) (Val v))
        σ
        []
        (Val $ ValLoc l)
        (state_init_heap l (replicate (Z.to_nat n) v) σ)
        []
        True
  | base_step_load l v σ :
      σ.(state_heap) !! l = Some v →
      base_step
        (Load $ Val $ ValLoc l)
        σ
        []
        (Val v)
        σ
        []
        True
  | base_step_store l v w σ :
      σ.(state_heap) !! l = Some w →
      base_step
        (Store (Val $ ValLoc l) (Val v))
        σ
        []
        Unit
        (state_update_heap <[l := v]> σ)
        []
        True
  | base_step_xchg l v w σ :
      σ.(state_heap) !! l = Some w →
      base_step
        (Xchg (Val $ ValLoc l) (Val v))
        σ
        []
        (Val w)
        (state_update_heap <[l := v]> σ)
        []
        True
  | base_step_cas_fail l v1 v2 v σ :
      σ.(state_heap) !! l = Some v →
      val_physical v →
      val_physical v1 →
      val_neq v v1 →
      base_step
        (Cas (Val $ ValLoc l) (Val v1) (Val v2))
        σ
        []
        (Val $ ValBool false)
        σ
        []
        True
  | base_step_cas_suc l v1 v2 v σ :
      σ.(state_heap) !! l = Some v →
      val_physical v →
      val_eq v v1 →
      base_step
        (Cas (Val $ ValLoc l) (Val v1) (Val v2))
        σ
        []
        (Val $ ValBool true)
        (state_update_heap <[l := v2]> σ)
        []
        (val_consistency v v1)
  | base_step_faa l n m σ :
      σ.(state_heap) !! l = Some $ ValInt m →
      base_step
        (Faa (Val $ ValLoc l) (Val $ ValInt n))
        σ
        []
        (Val $ ValInt m)
        (state_update_heap <[l := ValInt (m + n)]> σ)
        []
        True
  | base_step_fork e σ :
      base_step
        (Fork e)
        σ
        []
        Unit
        σ
        [e]
        True
  | base_step_yield σ :
      base_step
        Yield
        σ
        []
        Unit
        σ
        []
        True
  | base_step_proph σ pid :
      pid ∉ σ.(state_prophets) →
      base_step
        Proph
        σ
        []
        (Val $ ValProphecy pid)
        (state_update_prophets ({[pid]} ∪.) σ)
        []
        True
  | base_step_resolve e pid v σ κ w σ' es ϕ :
      base_step e σ κ (Val w) σ' es ϕ →
      base_step
        (Resolve e (Val $ ValProphecy pid) (Val v))
        σ
        (κ ++ [(pid, (w, v))])
        (Val w)
        σ'
        es
        ϕ.

Lemma base_step_reveal' tag vs σ :
  base_step
    (Reveal $ Val $ ValConstr None tag vs)
    σ
    []
    (Val $ ValConstr (Some inhabitant) tag vs)
    σ
    []
    True.
Proof.
  apply base_step_reveal.
Qed.
Lemma base_step_record' es vs σ :
  let l := location_fresh (dom σ.(state_heap)) in
  0 < length es →
  es = of_vals vs →
  base_step
    (Record es)
    σ
    []
    (Val $ ValLoc l)
    (state_init_heap l vs σ)
    []
    True.
Proof.
  intros. apply base_step_record; [done.. |].
  intros. apply not_elem_of_dom, location_fresh_fresh. naive_solver.
Qed.
Lemma base_step_alloc' v n σ :
  let l := location_fresh (dom σ.(state_heap)) in
  (0 < n)%Z →
  base_step
    (Alloc ((Val $ ValInt n)) (Val v))
    σ
    []
    (Val $ ValLoc l)
    (state_init_heap l (replicate (Z.to_nat n) v) σ)
    []
    True.
Proof.
  intros. apply base_step_alloc; first done.
  intros. apply not_elem_of_dom, location_fresh_fresh. naive_solver.
Qed.
Lemma base_step_proph' σ :
  let pid := fresh σ.(state_prophets) in
  base_step
    Proph
    σ
    []
    (Val $ ValProphecy pid)
    (state_update_prophets ({[pid]} ∪.) σ)
    []
    True.
Proof.
  constructor. apply is_fresh.
Qed.

Lemma val_base_stuck e1 σ1 κ e2 σ2 es ϕ :
  base_step e1 σ1 κ e2 σ2 es ϕ →
  to_val e1 = None.
Proof.
  destruct 1; naive_solver.
Qed.

Inductive ectxi :=
  | CtxApp1 v2
  | CtxApp2 e1
  | CtxUnop (op : unop)
  | CtxBinop1 (op : binop) v2
  | CtxBinop2 (op : binop) e1
  | CtxEqual1 v2
  | CtxEqual2 e1
  | CtxIf e1 e2
  | CtxConstr tag vs es
  | CtxProj proj
  | CtxMatch x e1 brs
  | CtxReveal
  | CtxFor1 e2 e3
  | CtxFor2 v1 e3
  | CtxRecord vs es
  | CtxAlloc1 v2
  | CtxAlloc2 e1
  | CtxLoad
  | CtxStore1 v2
  | CtxStore2 e1
  | CtxXchg1 v2
  | CtxXchg2 e1
  | CtxCas0 v1 v2
  | CtxCas1 e0 v2
  | CtxCas2 e0 e1
  | CtxFaa1 v2
  | CtxFaa2 e1
  | CtxResolve0 (k : ectxi) v1 v2
  | CtxResolve1 e0 v2
  | CtxResolve2 e0 e1.
Implicit Types k : ectxi.

Notation CtxLet x e2 := (
  CtxApp2 (ValLam x e2)
)(only parsing
).

Notation CtxSeq e2 := (
  CtxLet BAnon e2
)(only parsing
).

Fixpoint ectxi_fill k e : expr :=
  match k with
  | CtxApp1 v2 =>
      App e $ Val v2
  | CtxApp2 e1 =>
      App e1 e
  | CtxUnop op =>
      Unop op e
  | CtxBinop1 op v2 =>
      Binop op e $ Val v2
  | CtxBinop2 op e1 =>
      Binop op e1 e
  | CtxEqual1 v2 =>
      Equal e $ Val v2
  | CtxEqual2 e1 =>
      Equal e1 e
  | CtxIf e1 e2 =>
      If e e1 e2
  | CtxConstr tag vs es =>
      Constr tag $ of_vals vs ++ e :: es
  | CtxProj proj =>
      Proj proj e
  | CtxMatch x e1 brs =>
      Match e x e1 brs
  | CtxReveal =>
      Reveal e
  | CtxFor1 e2 e3 =>
      For e e2 e3
  | CtxFor2 v1 e3 =>
      For (Val v1) e e3
  | CtxRecord vs es =>
      Record $ of_vals vs ++ e :: es
  | CtxAlloc1 v2 =>
      Alloc e $ Val v2
  | CtxAlloc2 e1 =>
      Alloc e1 e
  | CtxLoad =>
      Load e
  | CtxStore1 v2 =>
      Store e $ Val v2
  | CtxStore2 e1 =>
      Store e1 e
  | CtxXchg1 v2 =>
      Xchg e $ Val v2
  | CtxXchg2 e1 =>
      Xchg e1 e
  | CtxCas0 v1 v2 =>
      Cas e (Val v1) (Val v2)
  | CtxCas1 e0 v2 =>
      Cas e0 e $ Val v2
  | CtxCas2 e0 e1 =>
      Cas e0 e1 e
  | CtxFaa1 v2 =>
      Faa e $ Val v2
  | CtxFaa2 e1 =>
      Faa e1 e
  | CtxResolve0 k v1 v2 =>
      Resolve (ectxi_fill k e) (Val v1) (Val v2)
  | CtxResolve1 e0 v2 =>
      Resolve e0 e $ Val v2
  | CtxResolve2 e0 e1 =>
      Resolve e0 e1 e
  end.
#[global] Arguments ectxi_fill !_ _ / : assert.

#[global] Instance ectxi_fill_inj k :
  Inj (=) (=) (ectxi_fill k).
Proof.
  induction k; intros ? ? ?; simplify; auto with f_equal.
Qed.
Lemma ectxi_fill_val k e :
  is_Some (to_val (ectxi_fill k e)) →
  is_Some (to_val e).
Proof.
  intros (v & ?). induction k; simplify_option_eq; eauto.
Qed.
Lemma ectxi_fill_no_val_inj k1 e1 k2 e2 :
  to_val e1 = None →
  to_val e2 = None →
  ectxi_fill k1 e1 = ectxi_fill k2 e2 →
  k1 = k2.
Proof.
  move: k1.
  induction k2; intros k1; induction k1; try naive_solver eauto with f_equal.
  all: move=> /= H1 H2 H; injection H => {H} H' *; subst.
  all: apply app_inj_1 in H'; first naive_solver.
  all: clear- H1 H2 H'.
  all:
    match goal with |- length (of_vals ?vs1) = length (of_vals ?vs2) =>
      move: vs2 H'; induction vs1; intros []; naive_solver
    end.
Qed.
Lemma base_step_ectxi_fill_val k e σ1 κ e2 σ2 es ϕ :
  base_step (ectxi_fill k e) σ1 κ e2 σ2 es ϕ →
  is_Some (to_val e).
Proof.
  move: κ e2 ϕ.
  induction k; try by (inversion_clear 1; simplify_option_eq; eauto).
  all: inversion_clear 1.
  all:
    match goal with H: of_vals ?vs' ++ _ = of_vals ?vs |- _ =>
      clear- H; move: vs H; induction vs'; intros []; naive_solver
    end.
Qed.

Definition ectx :=
  list ectxi.
