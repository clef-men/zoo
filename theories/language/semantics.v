(* Important notice:

   In this semantics, we assume expressions are syntactically or semantically well-typed:
   - operands of boolean operators are booleans;
   - operands of integer operators are integers;
   - physically compared values in [Equal] and [CAS] are loosely compatible:
     + a boolean may be compared with another boolean or a location;
     + an integer may be compared with another integer or a location;
     + an abstract block may be compared with another abstract block or a location.

   This means we never physically compare, e.g., a boolean and an integer, an integer and an abstract block.
   If we wanted to allow it, we would have to extend the semantics of physical comparison to account for conflicts in the memory representation of values.

   This also means a location may be compared with anything.
   In particular, comparing a location [Val (ValLoc l)] and an abstract block [ValBlock tag vs] is allowed, since [Block phys tag es] may yield a physical block ([phys] = [Physical]) or an abstract block ([phys] = [Abstract]).
*)

From stdpp Require Import
  gmap.

From iris.algebra Require Import
  ofe.

From zoo Require Import
  prelude.
From zoo.language Require Export
  syntax.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types tag proj : nat.
Implicit Types n m : Z.
Implicit Types l : location.
Implicit Types phys : physicality.
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
  match v1 with
  | ValLiteral lit1 =>
      match v2 with
      | ValLiteral lit2 =>
          lit1 ≠ lit2
      | _ =>
          True
      end
  | ValBlock tag1 vs1 =>
      match v2 with
      | ValBlock tag2 vs2 =>
          match vs1, vs2 with
          | [], [] =>
              tag1 ≠ tag2
          | _, _ =>
              True
          end
      | _ =>
          True
      end
  | _ =>
      True
  end.
#[global] Arguments val_neq !_ !_ / : assert.

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
      Unop
        op
        (subst x v e)
  | Binop op e1 e2 =>
      Binop
        op
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
  | Block phys tag es =>
      Block
        phys tag
        (subst x v <$> es)
  | Proj proj e =>
      Proj
        proj
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
  | For e1 e2 e3 =>
      For
        (subst x v e1)
        (subst x v e2)
        (subst x v e3)
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
  | CAS e0 e1 e2 =>
      CAS
        (subst x v e0)
        (subst x v e1)
        (subst x v e2)
  | FAA e1 e2 =>
      FAA
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
  match xs with
  | [] =>
      Some e
  | x :: xs =>
      match vs with
      | [] =>
          None
      | v :: vs =>
          subst' x v <$> subst_list xs vs e
      end
  end.
#[global] Arguments subst_list !_ !_ _ / : assert.

Fixpoint match_apply' subj tag vs x e brs :=
  match brs with
  | [] =>
      Some $ subst' x subj e
  | br :: brs =>
      let pat := br.1 in
      if decide (pat.(pattern_tag) = tag) then
        subst_list pat.(pattern_fields) vs $
        subst' pat.(pattern_as) subj br.2
      else
        match_apply' subj tag vs x e brs
  end.
#[global] Arguments match_apply' _ _ _ _ _ !_ / : assert.
Definition match_apply (l : option location) tag vs x e brs :=
  let subj := from_option (λ l, ValLoc l) (ValBlock tag vs) l in
  match_apply' subj tag vs x e brs.

Record header := Header {
  header_tag : nat ;
  header_size : nat ;
}.
Add Printing Constructor header.

Record state := {
  state_headers : gmap location header ;
  state_heap : gmap location val ;
  state_prophets : gset prophet_id ;
}.
Implicit Types σ : state.

Canonical state_O :=
  leibnizO state.

Definition state_update_heap f σ : state :=
  {|state_headers := σ.(state_headers) ;
    state_heap := f σ.(state_heap) ;
    state_prophets := σ.(state_prophets) ;
  |}.
#[global] Arguments state_update_heap _ !_ / : assert.
Definition state_update_headers f σ : state :=
  {|state_headers := f σ.(state_headers) ;
    state_heap := σ.(state_heap) ;
    state_prophets := σ.(state_prophets) ;
  |}.
#[global] Arguments state_update_headers _ !_ / : assert.
Definition state_update_prophets f σ : state :=
  {|state_headers := σ.(state_headers) ;
    state_heap := σ.(state_heap) ;
    state_prophets := f σ.(state_prophets) ;
  |}.
#[global] Arguments state_update_prophets _ !_ / : assert.

#[global] Instance state_inhabited : Inhabited state :=
  populate
    {|state_headers := inhabitant ;
      state_heap := inhabitant ;
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
    i < length vs →
    h !! (l +ₗ i) = None
  ) →
  heap_array l vs ##ₘ h.
Proof.
  intros Hdisj. apply map_disjoint_spec=> l' v1 v2.
  intros (j & ? & -> & ?%lookup_lt_Some%inj_lt)%heap_array_lookup ?.
  ospecialize* (Hdisj (Z.to_nat j)); first lia.
  rewrite Z2Nat.id // in Hdisj. naive_solver.
Qed.

Definition state_alloc l hdr vs σ :=
  {|state_headers := <[l := hdr]> σ.(state_headers) ;
    state_heap := heap_array l vs ∪ σ.(state_heap) ;
    state_prophets := σ.(state_prophets) ;
  |}.

Definition observation : Set :=
  prophet_id * (val * val).

Inductive base_step : expr → state → list observation → expr → state → list expr → Prop :=
  | base_step_rec f x e σ :
      base_step
        (Rec f x e)
        σ
        []
        (Val $ ValRec f x e)
        σ
        []
  | base_step_beta f x e v e' σ :
      e' = subst' f (ValRec f x e) (subst' x v e) →
      base_step
        (App (Val $ ValRec f x e) (Val v))
        σ
        []
        e'
        σ
        []
  | base_step_unop op v v' σ :
      unop_eval op v = Some v' →
      base_step
        (Unop op $ Val v)
        σ
        []
        (Val v')
        σ
        []
  | base_step_binop op v1 v2 v' σ :
      binop_eval op v1 v2 = Some v' →
      base_step
        (Binop op (Val v1) (Val v2))
        σ
        []
        (Val v')
        σ
        []
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
  | base_step_equal_suc v1 v2 σ :
      val_physical v1 →
      v1 = v2 →
      base_step
        (Equal (Val v1) (Val v2))
        σ
        []
        (Val $ ValBool true)
        σ
        []
  | base_step_if b e1 e2 σ :
      base_step
        (If (Val $ ValBool b) e1 e2)
        σ
        []
        (if b then e1 else e2)
        σ
        []
  | base_step_block_physical tag es vs σ l :
      0 < length es →
      es = of_vals vs →
      σ.(state_headers) !! l = None →
      ( ∀ i,
        i < length es →
        σ.(state_heap) !! (l +ₗ i) = None
      ) →
      base_step
        (Block Physical tag es)
        σ
        []
        (Val $ ValLoc l)
        (state_alloc l (Header tag (length es)) vs σ)
        []
  | base_step_block_abstract tag es vs σ :
      es = of_vals vs →
      base_step
        (Block Abstract tag es)
        σ
        []
        (Val $ ValBlock tag vs)
        σ
        []
  | base_step_proj proj tag vs v σ :
      vs !! proj = Some v →
      base_step
        (Proj proj $ Val $ ValBlock tag vs)
        σ
        []
        (Val v)
        σ
        []
  | base_step_match_physical l hdr vs x e brs e' σ :
      σ.(state_headers) !! l = Some hdr →
      length vs = hdr.(header_size) →
      ( ∀ (i : nat) v,
        vs !! i = Some v →
        σ.(state_heap) !! (l +ₗ i) = Some v
      ) →
      match_apply (Some l) hdr.(header_tag) vs x e brs = Some e' →
      base_step
        (Match (Val $ ValLoc l) x e brs)
        σ
        []
        e'
        σ
        []
  | base_step_match_abstract tag vs x e brs e' σ :
      match_apply None tag vs x e brs = Some e' →
      base_step
        (Match (Val $ ValBlock tag vs) x e brs)
        σ
        []
        e'
        σ
        []
  | base_step_for n1 n2 e σ :
      base_step
        (For (Val $ ValInt n1) (Val $ ValInt n2) e)
        σ
        []
        (if decide (n2 ≤ n1)%Z then Unit else Seq (App e (Val $ ValInt n1)) (For (Val $ ValInt (1 + n1)) (Val $ ValInt n2) e))
        σ
        []
  | base_step_alloc n v σ l :
      (0 < n)%Z →
      σ.(state_headers) !! l = None →
      ( ∀ i,
        i < Z.to_nat n →
        σ.(state_heap) !! (l +ₗ i) = None
      ) →
      base_step
        (Alloc (Val $ ValInt n) (Val v))
        σ
        []
        (Val $ ValLoc l)
        (state_alloc l (Header 0 (Z.to_nat n)) (replicate (Z.to_nat n) v) σ)
        []
  | base_step_load l v σ :
      σ.(state_heap) !! l = Some v →
      base_step
        (Load $ Val $ ValLoc l)
        σ
        []
        (Val v)
        σ
        []
  | base_step_store l v w σ :
      σ.(state_heap) !! l = Some w →
      base_step
        (Store (Val $ ValLoc l) (Val v))
        σ
        []
        Unit
        (state_update_heap <[l := v]> σ)
        []
  | base_step_xchg l v w σ :
      σ.(state_heap) !! l = Some w →
      base_step
        (Xchg (Val $ ValLoc l) (Val v))
        σ
        []
        (Val w)
        (state_update_heap <[l := v]> σ)
        []
  | base_step_cas_fail l v1 v2 v σ :
      σ.(state_heap) !! l = Some v →
      val_physical v →
      val_physical v1 →
      val_neq v v1 →
      base_step
        (CAS (Val $ ValLoc l) (Val v1) (Val v2))
        σ
        []
        (Val $ ValBool false)
        σ
        []
  | base_step_cas_suc l v1 v2 v σ :
      σ.(state_heap) !! l = Some v →
      val_physical v →
      v = v1 →
      base_step
        (CAS (Val $ ValLoc l) (Val v1) (Val v2))
        σ
        []
        (Val $ ValBool true)
        (state_update_heap <[l := v2]> σ)
        []
  | base_step_faa l n m σ :
      σ.(state_heap) !! l = Some $ ValInt m →
      base_step
        (FAA (Val $ ValLoc l) (Val $ ValInt n))
        σ
        []
        (Val $ ValInt m)
        (state_update_heap <[l := ValInt (m + n)]> σ)
        []
  | base_step_fork e σ :
      base_step
        (Fork e)
        σ
        []
        Unit
        σ
        [e]
  | base_step_yield σ :
      base_step
        Yield
        σ
        []
        Unit
        σ
        []
  | base_step_proph σ pid :
      pid ∉ σ.(state_prophets) →
      base_step
        Proph
        σ
        []
        (Val $ ValProphecy pid)
        (state_update_prophets ({[pid]} ∪.) σ)
        []
  | base_step_resolve e pid v σ κ w σ' es :
      base_step e σ κ (Val w) σ' es →
      base_step
        (Resolve e (Val $ ValProphecy pid) (Val v))
        σ
        (κ ++ [(pid, (w, v))])
        (Val w)
        σ'
        es.

Lemma base_step_block_physical' tag es vs σ :
  let l := location_fresh (dom σ.(state_headers) ∪ dom σ.(state_heap)) in
  0 < length es →
  es = of_vals vs →
  base_step
    (Block Physical tag es)
    σ
    []
    (Val $ ValLoc l)
    (state_alloc l (Header tag (length es)) vs σ)
    [].
Proof.
  intros l Hn ->.
  pose proof (location_fresh_fresh (dom σ.(state_headers) ∪ dom σ.(state_heap))) as Hfresh.
  setoid_rewrite not_elem_of_union in Hfresh.
  apply base_step_block_physical; [done.. | |].
  all: intros; apply not_elem_of_dom.
  - rewrite -(location_add_0 l). naive_solver.
  - apply Hfresh. lia.
Qed.
Lemma base_step_alloc' v n σ :
  let l := location_fresh (dom σ.(state_headers) ∪ dom σ.(state_heap)) in
  (0 < n)%Z →
  base_step
    (Alloc ((Val $ ValInt n)) (Val v))
    σ
    []
    (Val $ ValLoc l)
    (state_alloc l (Header 0 (Z.to_nat n)) (replicate (Z.to_nat n) v) σ)
    [].
Proof.
  intros l Hn.
  pose proof (location_fresh_fresh (dom σ.(state_headers) ∪ dom σ.(state_heap))) as Hfresh.
  setoid_rewrite not_elem_of_union in Hfresh.
  apply base_step_alloc; first done.
  all: intros; apply not_elem_of_dom.
  - rewrite -(location_add_0 l). naive_solver.
  - apply Hfresh. lia.
Qed.
Lemma base_step_proph' σ :
  let pid := fresh σ.(state_prophets) in
  base_step
    Proph
    σ
    []
    (Val $ ValProphecy pid)
    (state_update_prophets ({[pid]} ∪.) σ)
    [].
Proof.
  constructor. apply is_fresh.
Qed.

Lemma val_base_stuck e1 σ1 κ e2 σ2 es :
  base_step e1 σ1 κ e2 σ2 es →
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
  | CtxBlock phys tag vs es
  | CtxProj proj
  | CtxMatch x e1 brs
  | CtxFor1 e2 e3
  | CtxFor2 v1 e3
  | CtxAlloc1 v2
  | CtxAlloc2 e1
  | CtxLoad
  | CtxStore1 v2
  | CtxStore2 e1
  | CtxXchg1 v2
  | CtxXchg2 e1
  | CtxCAS0 v1 v2
  | CtxCAS1 e0 v2
  | CtxCAS2 e0 e1
  | CtxFAA1 v2
  | CtxFAA2 e1
  | CtxResolve0 (k : ectxi) v1 v2
  | CtxResolve1 e0 v2
  | CtxResolve2 e0 e1.
Implicit Types k : ectxi.

Notation CtxLet x e2 := (
  CtxApp2 (ValFun x e2)
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
  | CtxBlock phys tag vs es =>
      Block phys tag $ of_vals vs ++ e :: es
  | CtxProj proj =>
      Proj proj e
  | CtxMatch x e1 brs =>
      Match e x e1 brs
  | CtxFor1 e2 e3 =>
      For e e2 e3
  | CtxFor2 v1 e3 =>
      For (Val v1) e e3
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
  | CtxCAS0 v1 v2 =>
      CAS e (Val v1) (Val v2)
  | CtxCAS1 e0 v2 =>
      CAS e0 e $ Val v2
  | CtxCAS2 e0 e1 =>
      CAS e0 e1 e
  | CtxFAA1 v2 =>
      FAA e $ Val v2
  | CtxFAA2 e1 =>
      FAA e1 e
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
  induction k; intros ?*; naive_solver.
Qed.
Lemma ectxi_fill_val k e :
  is_Some (to_val (ectxi_fill k e)) →
  is_Some (to_val e).
Proof.
  intros (v & ?). destruct k; done.
Qed.
Lemma ectxi_fill_no_val_inj k1 e1 k2 e2 :
  to_val e1 = None →
  to_val e2 = None →
  ectxi_fill k1 e1 = ectxi_fill k2 e2 →
  k1 = k2.
Proof.
  move: k1.
  induction k2; intros k1; destruct k1; try naive_solver.
  move=> /= H1 H2 H; injection H => {H} H' *; subst.
  apply app_inj_1 in H'; first naive_solver.
  clear- H1 H2 H'.
  match goal with |- length (of_vals ?vs1) = length (of_vals ?vs2) =>
    move: vs2 H'; induction vs1; intros []; naive_solver
  end.
Qed.
Lemma base_step_ectxi_fill_val k e σ1 κ e2 σ2 es :
  base_step (ectxi_fill k e) σ1 κ e2 σ2 es →
  is_Some (to_val e).
Proof.
  move: κ e2.
  induction k; try (inversion_clear 1; eauto || done).
  all: inversion_clear 1.
  all:
    match goal with H: of_vals ?vs' ++ _ = of_vals ?vs |- _ =>
      clear- H; move: vs H; induction vs'; intros []; naive_solver
    end.
Qed.

Definition ectx :=
  list ectxi.
