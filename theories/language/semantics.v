(* Important notice:

   In this semantics, we assume expressions are syntactically or semantically well-typed:
   - operands of boolean operators are booleans;
   - operands of integer operators are integers;
   - physically compared values in [Equal] and [CAS] are loosely compatible:
     + a boolean may be compared with another boolean or a location;
     + an integer may be compared with another integer or a location;
     + an immutable block may be compared with another immutable block or a location.

   This means we never physically compare, e.g., a boolean and an integer, an integer and an immutable block.
   If we wanted to allow it, we would have to extend the semantics of physical comparison to account for conflicts in the memory representation of values.

   This also means a location may be compared with anything.
   In particular, comparing a location [Val (ValLoc l)] — as obtained with [Block Mutable tag es] — and an immutable block [ValBlock tag vs] — as obtained with [Block Immutable tag es] — is allowed.
*)

From stdpp Require Import
  gmap.

From iris.algebra Require Import
  ofe.

From zoo Require Import
  prelude.
From zoo.common Require Export
  option
  list.
From zoo.language Require Export
  metatheory.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types tag : nat.
Implicit Types n m : Z.
Implicit Types l : location.
Implicit Types mut : mutability.
Implicit Types lit : literal.
Implicit Types x : binder.
Implicit Types e : expr.
Implicit Types es : list expr.
Implicit Types v w : val.
Implicit Types vs : list val.
Implicit Types br : branch.
Implicit Types brs : list branch.
Implicit Types rec : recursive.
Implicit Types recs : list recursive.

Definition literal_physical lit :=
  match lit with
  | LitBool _
  | LitInt _
  | LitLoc _ =>
      True
  | LitProph _
  | LitPoison =>
      False
  end.
#[global] Arguments literal_physical !_ / : assert.

Definition val_physical v :=
  match v with
  | ValLit lit =>
      literal_physical lit
  | _ =>
      True
  end.
#[global] Arguments val_physical !_ / : assert.

Class ValPhysical v :=
  val_physical' : val_physical v.

Definition val_neq v1 v2 :=
  match v1 with
  | ValLit lit1 =>
      match v2 with
      | ValLit lit2 =>
          lit1 ≠ lit2
      | _ =>
          True
      end
  | ValBlock bid1 tag1 vs1 =>
      match v2 with
      | ValBlock bid2 tag2 vs2 =>
          match bid1, bid2 with
          | Some bid1, Some bid2 =>
              bid1 ≠ bid2
          | _, _ =>
              False
          end ∨
          tag1 ≠ tag2 ∨
          vs1 ≠ vs2
      | _ =>
          True
      end
  | _ =>
      True
  end.
#[global] Arguments val_neq !_ !_ / : assert.

Definition val_eq v1 v2 :=
  match v1, v2 with
  | ValLit lit1, ValLit lit2 =>
      lit1 = lit2
  | ValRecs i1 recs1, ValRecs i2 recs2 =>
      i1 = i2 ∧
      recs1 = recs2
  | ValBlock bid1 tag1 vs1, ValBlock bid2 tag2 vs2 =>
      match bid1, bid2 with
      | Some bid1, Some bid2 =>
          bid1 = bid2
      | _, _ =>
          True
      end ∧
      tag1 = tag2 ∧
      vs1 = vs2
  | _, _ =>
      False
  end.
#[global] Arguments val_eq !_ !_ / : assert.

#[global] Instance val_eq_reflexive :
  Reflexive val_eq.
Proof.
  intros [| | []] => //.
Qed.
#[global] Instance val_eq_sym :
  Symmetric val_eq.
Proof.
  do 2 intros [| | []]; naive_solver.
Qed.
Lemma val_eq_refl v1 v2 :
  v1 = v2 →
  val_eq v1 v2.
Proof.
  naive_solver.
Qed.

Definition eval_unop op v :=
  match op, v with
  | UnopNeg, ValBool b =>
      Some $ ValBool (negb b)
  | UnopMinus, ValInt n =>
      Some $ ValInt (- n)
  | _, _ =>
      None
  end.
#[global] Arguments eval_unop !_ !_ / : assert.

Definition eval_binop_int op n1 n2 :=
  match op with
  | BinopPlus =>
      LitInt (n1 + n2)
  | BinopMinus =>
      LitInt (n1 - n2)
  | BinopMult =>
      LitInt (n1 * n2)
  | BinopQuot =>
      LitInt (n1 `quot` n2)
  | BinopRem =>
      LitInt (n1 `rem` n2)
  | BinopLe =>
      LitBool (bool_decide (n1 ≤ n2))
  | BinopLt =>
      LitBool (bool_decide (n1 < n2))
  | BinopGe =>
      LitBool (bool_decide (n1 >= n2))
  | BinopGt =>
      LitBool (bool_decide (n1 > n2))
  end%Z.
#[global] Arguments eval_binop_int !_ _ _ / : assert.
Definition eval_binop op v1 v2 :=
  match v1, v2 with
  | ValInt n1, ValInt n2 =>
      Some $ ValLit $ eval_binop_int op n1 n2
  | _, _ =>
      None
  end.
#[global] Arguments eval_binop _ !_ !_ / : assert.

Definition eval_app recs x v e :=
  foldri (λ i rec, subst' rec.1.1 (ValRecs i recs)) (subst' x v e) recs.

Fixpoint eval_match bid tag sz (vs : location + list val) x_fb e_fb brs :=
  let subj :=
    match vs with
    | inl l =>
        ValLoc l
    | inr vs =>
        ValBlock bid tag vs
    end
  in
  match brs with
  | [] =>
      Some $ subst' x_fb subj e_fb
  | br :: brs =>
      let pat := br.1 in
      if Nat.eqb pat.(pattern_tag) tag && Nat.eqb (length pat.(pattern_fields)) sz then
        let res := subst' pat.(pattern_as) subj br.2 in
        match vs with
        | inl l =>
            if forallb (binder_eqb BAnon) pat.(pattern_fields) then
              Some res
            else
              None
        | inr vs =>
            Some $ subst_list pat.(pattern_fields) vs res
        end
      else
        eval_match bid tag sz vs x_fb e_fb brs
  end.
#[global] Arguments eval_match _ _ _ !_ _ _ !_ / : assert.

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

Definition state_update_heap f σ :=
  {|state_headers := σ.(state_headers) ;
    state_heap := f σ.(state_heap) ;
    state_prophets := σ.(state_prophets) ;
  |}.
Definition state_update_headers f σ :=
  {|state_headers := f σ.(state_headers) ;
    state_heap := σ.(state_heap) ;
    state_prophets := σ.(state_prophets) ;
  |}.
Definition state_update_prophets f σ :=
  {|state_headers := σ.(state_headers) ;
    state_heap := σ.(state_heap) ;
    state_prophets := f σ.(state_prophets) ;
  |}.

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
#[global] Arguments heap_array _ !_ / : assert.

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
Lemma heap_array_map_disjoint heap l vs :
  ( ∀ i,
    i < length vs →
    heap !! (l +ₗ i) = None
  ) →
  heap_array l vs ##ₘ heap.
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
  | base_step_app i recs rec v σ :
      recs !! i = Some rec →
      base_step
        (App (Val $ ValRecs i recs) (Val v))
        σ
        []
        (eval_app recs rec.1.2 v rec.2)
        σ
        []
  | base_step_let x v1 e2 σ :
      base_step
        (Let x (Val v1) e2)
        σ
        []
        (subst' x v1 e2)
        σ
        []
  | base_step_unop op v v' σ :
      eval_unop op v = Some v' →
      base_step
        (Unop op $ Val v)
        σ
        []
        (Val v')
        σ
        []
  | base_step_binop op v1 v2 v' σ :
      eval_binop op v1 v2 = Some v' →
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
      val_eq v1 v2 →
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
  | base_step_for n1 n2 e σ :
      base_step
        (For (Val $ ValInt n1) (Val $ ValInt n2) e)
        σ
        []
        (if decide (n2 ≤ n1)%Z then Unit else Seq (App e (Val $ ValInt n1)) (For (Val $ ValInt (n1 + 1)) (Val $ ValInt n2) e))
        σ
        []
  | base_step_alloc tag n σ l :
      (0 ≤ n)%Z →
      σ.(state_headers) !! l = None →
      ( ∀ i,
        i < Z.to_nat n →
        σ.(state_heap) !! (l +ₗ i) = None
      ) →
      base_step
        (Alloc (Val $ ValInt tag) (Val $ ValInt n))
        σ
        []
        (Val $ ValLoc l)
        (state_alloc l (Header tag (Z.to_nat n)) (replicate (Z.to_nat n) ValUnit) σ)
        []
  | base_step_block_mutable tag es vs σ l :
      0 < length es →
      es = of_vals vs →
      σ.(state_headers) !! l = None →
      ( ∀ i,
        i < length es →
        σ.(state_heap) !! (l +ₗ i) = None
      ) →
      base_step
        (Block Mutable tag es)
        σ
        []
        (Val $ ValLoc l)
        (state_alloc l (Header tag (length es)) vs σ)
        []
  | base_step_block_immutable tag es vs σ :
      es = of_vals vs →
      base_step
        (Block Immutable tag es)
        σ
        []
        (Val $ ValBlock None tag vs)
        σ
        []
  | base_step_reveal tag vs σ bid :
      base_step
        (Reveal $ Val $ ValBlock None tag vs)
        σ
        []
        (Val $ ValBlock (Some bid) tag vs)
        σ
        []
  | base_step_match_mutable l hdr x e brs e' σ :
      σ.(state_headers) !! l = Some hdr →
      eval_match None hdr.(header_tag) hdr.(header_size) (inl l) x e brs = Some e' →
      base_step
        (Match (Val $ ValLoc l) x e brs)
        σ
        []
        e'
        σ
        []
  | base_step_match_immutable bid tag vs x e brs e' σ :
      eval_match bid tag (length vs) (inr vs) x e brs = Some e' →
      base_step
        (Match (Val $ ValBlock bid tag vs) x e brs)
        σ
        []
        e'
        σ
        []
  | base_step_get_tag_mutable l hdr σ :
      σ.(state_headers) !! l = Some hdr →
      base_step
        (GetTag $ Val $ ValLoc l)
        σ
        []
        (Val $ ValInt hdr.(header_tag))
        σ
        []
  | base_step_get_tag_immutable cid tag vs σ :
      0 < length vs →
      base_step
        (GetTag $ Val $ ValBlock cid tag vs)
        σ
        []
        (Val $ ValInt tag)
        σ
        []
  | base_step_get_size_mutable l hdr σ :
      σ.(state_headers) !! l = Some hdr →
      base_step
        (GetSize $ Val $ ValLoc l)
        σ
        []
        (Val $ ValInt hdr.(header_size))
        σ
        []
  | base_step_get_size_immutable cid tag vs σ :
      0 < length vs →
      base_step
        (GetSize $ Val $ ValBlock cid tag vs)
        σ
        []
        (Val $ ValInt (length vs))
        σ
        []
  | base_step_get_field_mutable l fld v σ :
      σ.(state_heap) !! (l +ₗ fld) = Some v →
      base_step
        (Load (Val $ ValLoc l) (Val $ ValInt fld))
        σ
        []
        (Val v)
        σ
        []
  | base_step_get_field_immutable cid tag vs (fld : nat) v σ :
      vs !! fld = Some v →
      base_step
        (Load (Val $ ValBlock cid tag vs) (Val $ ValInt fld))
        σ
        []
        (Val v)
        σ
        []
  | base_step_set_field l fld v σ :
      is_Some (σ.(state_heap) !! (l +ₗ fld)) →
      base_step
        (Store (Val $ ValLoc l) (Val $ ValInt fld) (Val v))
        σ
        []
        Unit
        (state_update_heap <[l +ₗ fld := v]> σ)
        []
  | base_step_xchg l fld v w σ :
      σ.(state_heap) !! (l +ₗ fld) = Some w →
      base_step
        (Xchg (Val $ ValTuple [ValLoc l; ValInt fld]) (Val v))
        σ
        []
        (Val w)
        (state_update_heap <[l +ₗ fld := v]> σ)
        []
  | base_step_cas_fail l fld v1 v2 v σ :
      σ.(state_heap) !! (l +ₗ fld) = Some v →
      val_physical v →
      val_physical v1 →
      val_neq v v1 →
      base_step
        (CAS (Val $ ValTuple [ValLoc l; ValInt fld]) (Val v1) (Val v2))
        σ
        []
        (Val $ ValBool false)
        σ
        []
  | base_step_cas_suc l fld v1 v2 v σ :
      σ.(state_heap) !! (l +ₗ fld) = Some v →
      val_physical v →
      val_physical v1 →
      val_eq v v1 →
      base_step
        (CAS (Val $ ValTuple [ValLoc l; ValInt fld]) (Val v1) (Val v2))
        σ
        []
        (Val $ ValBool true)
        (state_update_heap <[l +ₗ fld := v2]> σ)
        []
  | base_step_faa l fld n m σ :
      σ.(state_heap) !! (l +ₗ fld) = Some $ ValInt m →
      base_step
        (FAA (Val $ ValTuple [ValLoc l; ValInt fld]) (Val $ ValInt n))
        σ
        []
        (Val $ ValInt m)
        (state_update_heap <[l +ₗ fld := ValInt (m + n)]> σ)
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
        (Val $ ValProph pid)
        (state_update_prophets ({[pid]} ∪.) σ)
        []
  | base_step_resolve e pid v σ κ w σ' es :
      base_step e σ κ (Val w) σ' es →
      base_step
        (Resolve e (Val $ ValProph pid) (Val v))
        σ
        (κ ++ [(pid, (w, v))])
        (Val w)
        σ'
        es.

Lemma base_step_alloc' tag n σ :
  let l := location_fresh (dom σ.(state_headers) ∪ dom σ.(state_heap)) in
  (0 ≤ n)%Z →
  base_step
    (Alloc (Val $ ValInt tag) (Val $ ValInt n))
    σ
    []
    (Val $ ValLoc l)
    (state_alloc l (Header tag (Z.to_nat n)) (replicate (Z.to_nat n) ValUnit) σ)
    [].
Proof.
  intros l Hn.
  pose proof (location_fresh_fresh (dom σ.(state_headers) ∪ dom σ.(state_heap))) as Hfresh.
  setoid_rewrite not_elem_of_union in Hfresh.
  apply base_step_alloc; first done.
  all: intros; apply not_elem_of_dom.
  1: rewrite -(location_add_0 l).
  all: apply Hfresh; lia.
Qed.
Lemma base_step_reveal' tag vs σ :
  base_step
    (Reveal $ Val $ ValBlock None tag vs)
    σ
    []
    (Val $ ValBlock (Some inhabitant) tag vs)
    σ
    [].
Proof.
  apply base_step_reveal.
Qed.
Lemma base_step_block_mutable' tag es vs σ :
  let l := location_fresh (dom σ.(state_headers) ∪ dom σ.(state_heap)) in
  0 < length es →
  es = of_vals vs →
  base_step
    (Block Mutable tag es)
    σ
    []
    (Val $ ValLoc l)
    (state_alloc l (Header tag (length es)) vs σ)
    [].
Proof.
  intros l Hn ->.
  pose proof (location_fresh_fresh (dom σ.(state_headers) ∪ dom σ.(state_heap))) as Hfresh.
  setoid_rewrite not_elem_of_union in Hfresh.
  apply base_step_block_mutable; [done.. | |].
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
    (Val $ ValProph pid)
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
  | CtxLet x e2
  | CtxUnop (op : unop)
  | CtxBinop1 (op : binop) v2
  | CtxBinop2 (op : binop) e1
  | CtxEqual1 v2
  | CtxEqual2 e1
  | CtxIf e1 e2
  | CtxFor1 e2 e3
  | CtxFor2 v1 e3
  | CtxAlloc1 v2
  | CtxAlloc2 e1
  | CtxBlock mut tag es vs
  | CtxReveal
  | CtxMatch x e1 brs
  | CtxGetTag
  | CtxGetSize
  | CtxLoad1 v2
  | CtxLoad2 e1
  | CtxStore1 v2 v3
  | CtxStore2 e1 v3
  | CtxStore3 e1 e2
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
  | CtxLet x e2 =>
      Let x e e2
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
  | CtxFor1 e2 e3 =>
      For e e2 e3
  | CtxFor2 v1 e3 =>
      For (Val v1) e e3
  | CtxAlloc1 v2 =>
      Alloc e $ Val v2
  | CtxAlloc2 e1 =>
      Alloc e1 e
  | CtxBlock mut tag es vs =>
      Block mut tag $ es ++ e :: of_vals vs
  | CtxReveal =>
      Reveal e
  | CtxMatch x e1 brs =>
      Match e x e1 brs
  | CtxGetTag =>
      GetTag e
  | CtxGetSize =>
      GetSize e
  | CtxLoad1 v2 =>
      Load e (Val v2)
  | CtxLoad2 e1 =>
      Load e1 e
  | CtxStore1 v2 v3 =>
      Store e (Val v2) (Val v3)
  | CtxStore2 e1 v3 =>
      Store e1 e (Val v3)
  | CtxStore3 e1 e2 =>
      Store e1 e2 e
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
  intros H1 H2 [= -> -> H%app_inj_2]; first naive_solver.
  simpl. do 3 f_equal.
  apply (f_equal reverse) in H.
  rewrite !reverse_app !reverse_cons -!fmap_reverse /= in H.
  match goal with |- ?vs1 = ?vs2 =>
    apply (inj reverse);
    remember (reverse vs1) as vs1'; remember (reverse vs2) as vs2';
    clear- H1 H2 H; move: vs2' H; induction vs1'; intros []; naive_solver
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
    match goal with H: _ ++ _ :: of_vals ?vs1 = of_vals ?vs2 |- _ =>
      apply (f_equal reverse) in H;
      rewrite reverse_app reverse_cons -!fmap_reverse /= in H;
      remember (reverse vs1) as vs1'; remember (reverse vs2) as vs2';
      clear- H; move: vs2' H; induction vs1'; intros []; naive_solver
    end.
Qed.

Definition ectx :=
  list ectxi.
