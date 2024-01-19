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
Implicit Types n m : Z.
Implicit Types l : loc.
Implicit Types lit : literal.
Implicit Types e : expr.
Implicit Types v w : val.
Implicit Types vs : list val.

Definition literal_physical lit :=
  match lit with
  | LiteralUnit
  | LiteralBool _
  | LiteralInt _
  | LiteralLoc _ =>
      True
  | LiteralProphecy _
  | LiteralPoison =>
      False
  end.
#[global] Arguments literal_physical !_ / : assert.

Definition val_physical v :=
  match v with
  | ValLiteral lit =>
      literal_physical lit
  | _ =>
      True
  end.
#[global] Arguments val_physical !_ / : assert.

Lemma val_not_literal_physical v :
  val_not_literal v →
  val_physical v.
Proof.
  destruct v; done.
Qed.

Definition val_physically_distinct v1 v2 :=
  match v1, v2 with
  | ValLiteral lit1, ValLiteral lit2 =>
      lit1 ≠ lit2
  | _, _ =>
      True
  end.
#[global] Arguments val_physically_distinct !_ !_ / : assert.

Lemma val_not_literal_physically_distinct v1 v2 :
  val_not_literal v1 ∨ val_not_literal v2 →
  val_physically_distinct v1 v2.
Proof.
  destruct v1, v2; naive_solver.
Qed.

Definition unop_eval op v :=
  match op, v with
  | UnopNeg, ValLiteral (LiteralBool b) =>
      Some $ ValLiteral $ LiteralBool (negb b)
  | UnopMinus, ValLiteral (LiteralInt n) =>
      Some $ ValLiteral $ LiteralInt (- n)
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
  | ValLiteral (LiteralInt n1), ValLiteral (LiteralInt n2) =>
      ValLiteral <$> binop_eval_int op n1 n2
  | ValLiteral (LiteralLoc l), ValLiteral (LiteralInt n) =>
      if decide (op = BinopOffset) then
        Some $ ValLiteral $ LiteralLoc (l +ₗ n)
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
      if decide (x = y) then Val v else Var y
  | Rec f y e =>
     Rec f y $ if decide (BNamed x ≠ f ∧ BNamed x ≠ y) then subst x v e else e
  | App e1 e2 =>
      App (subst x v e1) (subst x v e2)
  | Unop op e =>
      Unop op (subst x v e)
  | Binop op e1 e2 =>
      Binop op (subst x v e1) (subst x v e2)
  | Equal e1 e2 =>
      Equal (subst x v e1) (subst x v e2)
  | If e0 e1 e2 =>
      If (subst x v e0) (subst x v e1) (subst x v e2)
  | Pair e1 e2 =>
      Pair (subst x v e1) (subst x v e2)
  | Fst e =>
      Fst (subst x v e)
  | Snd e =>
      Snd (subst x v e)
  | Injl e =>
      Injl (subst x v e)
  | Injr e =>
      Injr (subst x v e)
  | Case e0 e1 e2 =>
      Case (subst x v e0) (subst x v e1) (subst x v e2)
  | Alloc e1 e2 =>
      Alloc (subst x v e1) (subst x v e2)
  | Load e =>
      Load (subst x v e)
  | Store e1 e2 =>
      Store (subst x v e1) (subst x v e2)
  | Cas e0 e1 e2 =>
      Cas (subst x v e0) (subst x v e1) (subst x v e2)
  | Faa e1 e2 =>
      Faa (subst x v e1) (subst x v e2)
  | Fork e =>
      Fork (subst x v e)
  | Proph =>
      Proph
  | Resolve e0 e1 e2 =>
      Resolve (subst x v e0) (subst x v e1) (subst x v e2)
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

Record state : Type := {
  state_heap : gmap loc val ;
  state_prophs : gset prophecy_id ;
}.
Implicit Types σ : state.

Canonical stateO :=
  leibnizO state.

#[global] Instance state_inhabited : Inhabited state :=
  populate
    {|state_heap := inhabitant ;
      state_prophs := inhabitant ;
    |}.

Definition state_update_heap f σ : state :=
  {|state_heap := f σ.(state_heap) ;
    state_prophs := σ.(state_prophs) ;
  |}.
#[global] Arguments state_update_heap _ !_ / : assert.
Definition state_update_prophs f σ : state :=
  {|state_heap := σ.(state_heap) ;
    state_prophs := f σ.(state_prophs) ;
  |}.
#[global] Arguments state_update_prophs _ !_ / : assert.

Fixpoint heap_array l vs : gmap loc val :=
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
    { eexists 0. rewrite loc_add_0. naive_solver lia. }
    eexists (1 + j)%Z. rewrite loc_add_assoc !Z.add_1_l Z2Nat.inj_succ; auto with lia.
  - intros (j & ? & -> & Hil). destruct (decide (j = 0)); simplify_eq/=.
    { rewrite loc_add_0; eauto. }
    right. split.
    { rewrite -{1}(loc_add_0 l). intros ?%(inj (loc_add _)); lia. }
    assert (Z.to_nat j = S (Z.to_nat (j - 1))) as Hj.
    { rewrite -Z2Nat.inj_succ; last lia. f_equal; lia. }
    rewrite Hj /= in Hil.
    eexists (j - 1)%Z. rewrite loc_add_assoc Z.add_sub_assoc Z.add_simpl_l. auto with lia.
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

Definition state_init_heap l n v σ :=
  state_update_heap (λ h, heap_array l (replicate (Z.to_nat n) v) ∪ h) σ.

Lemma state_init_heap_singleton l v σ :
  state_init_heap l 1 v σ = state_update_heap <[l := v]> σ.
Proof.
  destruct σ as [h p]. rewrite /state_init_heap /=. f_equiv.
  rewrite insert_empty insert_union_singleton_l //.
Qed.

Definition observation : Set :=
  prophecy_id * (val * val).

Inductive head_step : expr → state → list observation → expr → state → list expr → Prop :=
  | head_step_rec f x e σ :
      head_step
        (Rec f x e) σ
        []
        (Val $ ValRec f x e) σ
        []
  | head_step_beta f x e v e' σ :
      e' = subst' f (ValRec f x e) (subst' x v e) →
      head_step
        (App (Val $ ValRec f x e) (Val v)) σ
        []
        e' σ
        []
  | head_step_unop op v v' σ :
      unop_eval op v = Some v' →
      head_step
        (Unop op $ Val v) σ
        []
        (Val v') σ
        []
  | head_step_binop op v1 v2 v' σ :
      binop_eval op v1 v2 = Some v' →
      head_step
        (Binop op (Val v1) (Val v2)) σ
        []
        (Val v') σ
        []
  | head_step_equal_fail v1 v2 σ :
      val_physical v1 →
      val_physical v2 →
      val_physically_distinct v1 v2 →
      head_step
        (Equal (Val v1) (Val v2)) σ
        []
        (Val $ ValLiteral $ LiteralBool false) σ
        []
  | head_step_equal_suc v1 v2 σ :
      val_physical v1 →
      v1 = v2 →
      head_step
        (Equal (Val v1) (Val v2)) σ
        []
        (Val $ ValLiteral $ LiteralBool true) σ
        []
  | head_step_if_true e1 e2 σ :
      head_step
        (If (Val $ ValLiteral $ LiteralBool true) e1 e2) σ
        []
        e1 σ
        []
  | head_step_if_false e1 e2 σ :
      head_step
        (If (Val $ ValLiteral $ LiteralBool false) e1 e2) σ
        []
        e2 σ
        []
  | head_step_pair v1 v2 σ :
      head_step
        (Pair (Val v1) (Val v2)) σ
        []
        (Val $ ValPair v1 v2) σ
        []
  | head_step_fst v1 v2 σ :
      head_step
        (Fst $ Val $ ValPair v1 v2) σ
        []
        (Val v1) σ
        []
  | head_step_snd v1 v2 σ :
      head_step
        (Snd $ Val $ ValPair v1 v2) σ
        []
        (Val v2) σ
        []
  | head_step_injl v σ :
      head_step
        (Injl $ Val v) σ
        []
        (Val $ ValInjl v) σ
        []
  | head_step_injr v σ :
      head_step
        (Injr $ Val v) σ
        []
        (Val $ ValInjr v) σ
        []
  | head_step_case_1 v e1 e2 σ :
      head_step
        (Case (Val $ ValInjl v) e1 e2) σ
        []
        (App e1 (Val v)) σ
        []
  | head_step_case_2 v e1 e2 σ :
      head_step
        (Case (Val $ ValInjr v) e1 e2) σ
        []
        (App e2 (Val v)) σ
        []
  | head_step_alloc n v σ l :
      (0 < n)%Z →
      ( ∀ i,
        (0 ≤ i)%Z →
        (i < n)%Z →
        σ.(state_heap) !! (l +ₗ i) = None
      ) →
      head_step
        (Alloc (Val $ ValLiteral $ LiteralInt n) (Val v)) σ
        []
        (Val $ ValLiteral $ LiteralLoc l) (state_init_heap l n v σ)
        []
  | head_step_load l v σ :
      σ.(state_heap) !! l = Some v →
      head_step
        (Load $ Val $ ValLiteral $ LiteralLoc l) σ
        []
        (Val v) σ
        []
  | head_step_store l v w σ :
      σ.(state_heap) !! l = Some w →
      head_step
        (Store (Val $ ValLiteral $ LiteralLoc l) (Val v)) σ
        []
        (Val $ ValLiteral LiteralUnit) (state_update_heap <[l := v]> σ)
        []
  | head_step_cas_fail l v1 v2 v σ :
      σ.(state_heap) !! l = Some v →
      val_physical v →
      val_physical v1 →
      val_physically_distinct v v1 →
      head_step
        (Cas (Val $ ValLiteral $ LiteralLoc l) (Val v1) (Val v2)) σ
        []
        (Val $ ValLiteral $ LiteralBool false) σ
        []
  | head_step_cas_suc l v1 v2 v σ :
      σ.(state_heap) !! l = Some v →
      val_physical v →
      v = v1 →
      head_step
        (Cas (Val $ ValLiteral $ LiteralLoc l) (Val v1) (Val v2)) σ
        []
        (Val $ ValLiteral $ LiteralBool true) (state_update_heap <[l := v2]> σ)
        []
  | head_step_faa l n m σ :
      σ.(state_heap) !! l = Some $ ValLiteral $ LiteralInt m →
      head_step
        (Faa (Val $ ValLiteral $ LiteralLoc l) (Val $ ValLiteral $ LiteralInt n)) σ
        []
        (Val $ ValLiteral $ LiteralInt m) (state_update_heap <[l := ValLiteral $ LiteralInt (m + n)]> σ)
        []
  | head_step_fork e σ :
      head_step
        (Fork e) σ
        []
        (Val $ ValLiteral LiteralUnit) σ
        [e]
  | head_step_proph σ p :
      p ∉ σ.(state_prophs) →
      head_step
        Proph σ
        []
        (Val $ ValLiteral $ LiteralProphecy p) (state_update_prophs ({[p]} ∪.) σ)
        []
  | head_step_resolve e p v σ κ w σ' es :
      head_step e σ κ (Val w) σ' es →
      head_step
        (Resolve e (Val $ ValLiteral $ LiteralProphecy p) (Val v)) σ
        (κ ++ [(p, (w, v))])
        (Val w) σ'
        es.

Lemma head_step_alloc' v n σ :
  let l := loc_fresh (dom σ.(state_heap)) in
  (0 < n)%Z →
  head_step
    (Alloc ((Val $ ValLiteral $ LiteralInt $ n)) (Val v)) σ
    []
    (Val $ ValLiteral $ LiteralLoc l) (state_init_heap l n v σ)
    [].
Proof.
  intros. apply head_step_alloc; first done.
  intros. apply not_elem_of_dom, loc_fresh_fresh. done.
Qed.
Lemma head_step_proph' σ :
  let p := fresh σ.(state_prophs) in
  head_step
    Proph σ
    []
    (Val $ ValLiteral $ LiteralProphecy p) (state_update_prophs ({[p]} ∪.) σ)
    [].
Proof.
  constructor. apply is_fresh.
Qed.

Lemma val_head_stuck e1 σ1 κ e2 σ2 es :
  head_step e1 σ1 κ e2 σ2 es →
  to_val e1 = None.
Proof.
  destruct 1; naive_solver.
Qed.

Inductive ectxi :=
  | CtxAppL v2
  | CtxAppR e1
  | CtxUnop (op : unop)
  | CtxBinopL (op : binop) v2
  | CtxBinopR (op : binop) e1
  | CtxEqualL v2
  | CtxEqualR e1
  | CtxIf e1 e2
  | CtxPairL v2
  | CtxPairR e1
  | CtxFst
  | CtxSnd
  | CtxInjl
  | CtxInjr
  | CtxCase e1 e2
  | CtxAllocL v2
  | CtxAllocR e1
  | CtxLoad
  | CtxStoreL v2
  | CtxStoreR e1
  | CtxCasL v1 v2
  | CtxCasM e0 v2
  | CtxCasR e0 e1
  | CtxFaaL v2
  | CtxFaaR e1
  | CtxResolveL (k : ectxi) v1 v2
  | CtxResolveM e0 v2
  | CtxResolveR e0 e1.
Implicit Types k : ectxi.

Fixpoint ectxi_fill k e : expr :=
  match k with
  | CtxAppL v2 =>
      App e (Val v2)
  | CtxAppR e1 =>
      App e1 e
  | CtxUnop op =>
      Unop op e
  | CtxBinopL op v2 =>
      Binop op e (Val v2)
  | CtxBinopR op e1 =>
      Binop op e1 e
  | CtxEqualL v2 =>
      Equal e (Val v2)
  | CtxEqualR e1 =>
      Equal e1 e
  | CtxIf e1 e2 =>
      If e e1 e2
  | CtxPairL v2 =>
      Pair e (Val v2)
  | CtxPairR e1 =>
      Pair e1 e
  | CtxFst =>
      Fst e
  | CtxSnd =>
      Snd e
  | CtxInjl =>
      Injl e
  | CtxInjr =>
      Injr e
  | CtxCase e1 e2 =>
      Case e e1 e2
  | CtxAllocL v2 =>
      Alloc e (Val v2)
  | CtxAllocR e1 =>
      Alloc e1 e
  | CtxLoad =>
      Load e
  | CtxStoreL v2 =>
      Store e (Val v2)
  | CtxStoreR e1 =>
      Store e1 e
  | CtxCasL v1 v2 =>
      Cas e (Val v1) (Val v2)
  | CtxCasM e0 v2 =>
      Cas e0 e (Val v2)
  | CtxCasR e0 e1 =>
      Cas e0 e1 e
  | CtxFaaL v2 =>
      Faa e (Val v2)
  | CtxFaaR e1 =>
      Faa e1 e
  | CtxResolveL k v1 v2 =>
      Resolve (ectxi_fill k e) (Val v1) (Val v2)
  | CtxResolveM e0 v2 =>
      Resolve e0 e (Val v2)
  | CtxResolveR e0 e1 =>
      Resolve e0 e1 e
  end.
#[global] Arguments ectxi_fill !_ _ / : assert.

#[global] Instance ectxi_fill_inj k :
  Inj (=) (=) (ectxi_fill k).
Proof.
  induction k; intros ? ? ?; simplify_eq/=; auto with f_equal.
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
  revert k1. induction k2; intros k1; induction k1; naive_solver eauto with f_equal.
Qed.
Lemma head_step_ectxi_fill_val k e σ1 κ e2 σ2 es :
  head_step (ectxi_fill k e) σ1 κ e2 σ2 es →
  is_Some (to_val e).
Proof.
  revert κ e2. induction k; inversion_clear 1; simplify_option_eq; eauto.
Qed.

Definition ectx :=
  list ectxi.
