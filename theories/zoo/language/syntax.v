Require Import stdpp.countable.

Require Import iris.algebra.ofe.

Require Import zoo.prelude.
Require Export zoo.common.ascii.
Require Export zoo.common.binder.
Require Import zoo.common.list.
Require Export zoo.language.location.
Require Export zoo.language.tag.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type chr : ascii.
Implicit Type i : nat.
Implicit Type n : Z.
Implicit Type str : string.
Implicit Type tag : tag.
Implicit Type l : location.
Implicit Type f x : binder.

Definition block_id :=
  positive.
Implicit Type bid : option block_id.

Definition prophet_id :=
  positive.
Implicit Type pid : prophet_id.

Variant mutability :=
  | Mutable
  | ImmutableNongenerative
  | ImmutableGenerativeWeak
  | ImmutableGenerativeStrong.
Implicit Type mut : mutability.

Please derive EqDecision for mutability.
Please derive Countable for mutability.

Variant generativity :=
  | Generative bid
  | Nongenerative.
Implicit Type gen : generativity.

Please derive EqDecision for generativity.
Please derive Countable for generativity.

Variant literal :=
  | LitBool b
  | LitChar chr
  | LitInt n
  | LitString str
  | LitLoc l
  | LitProph pid.
Implicit Type lit : literal.

Abbreviation LitNat i := (
  LitInt (Z.of_nat i)
)(only parsing
).
Abbreviation LitTag tag := (
  LitNat (tag۰to_nat tag)
)(only parsing
).

Please derive EqDecision for literal.
Please derive Countable for literal.

Variant unop :=
  | UnopNeg
  | UnopMinus.

Please derive EqDecision for unop.
Please derive Countable for unop.

Variant binop :=
  | BinopPlus | BinopMinus | BinopMult | BinopQuot | BinopRem
  | BinopLand | BinopLor | BinopLsl | BinopLsr
  | BinopLe | BinopLt | BinopGe | BinopGt.

Please derive EqDecision for binop.
Please derive Countable for binop.

Variant primitive0 :=
  | LocalGet
  | Proph.

Please derive EqDecision for primitive0.
Please derive Countable for primitive0.

Variant primitive1 :=
  | Unop (op : unop)
  | IsImmediate
  | GetTag
  | GetSize
  | LocalSet.

Please derive EqDecision for primitive1.
Please derive Countable for primitive1.

Variant primitive2 :=
  | Binop (op : binop)
  | StringGet | StringEqual
  | Equal
  | Alloc
  | Load
  | Xchg
  | FAA.

Please derive EqDecision for primitive2.
Please derive Countable for primitive2.

Variant primitive3 :=
  | Store
  | CAS
  | ResolveErasure.

Please derive EqDecision for primitive3.
Please derive Countable for primitive3.

Record pattern :=
  { pattern۰tag : tag
  ; pattern۰fields : list binder
  ; pattern۰as : binder
  }.

Please derive Inhabited for pattern.
Please derive EqDecision for pattern.
Please derive Countable for pattern.

Unset Elimination Schemes.
Inductive expr :=
  | Val (v : val)
  | Var (x : string)
  | Rec f x (e : expr)
  | Apply (e1 e2 : expr)
  | Let x (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  | While (e0 e1 : expr)
  | For (e1 e2 e3 : expr)
  | Match (e0 : expr) x (e1 : expr) (brs : list (pattern * expr))
  | Primitive0 (prim : primitive0)
  | Primitive1 (prim : primitive1) (e : expr)
  | Primitive2 (prim : primitive2) (e1 e2 : expr)
  | Primitive3 (prim : primitive3) (e1 e2 e3 : expr)
  | Block mut tag (es : list expr)
  | Fork (e : expr)
  | Resolve (e0 e1 e2 : expr)
with val :=
  | ValLit lit
  | ValRecs i (recs : list (binder * binder * expr))
  | ValBlock gen tag (vs : list val).
Set Elimination Schemes.
Implicit Type e : expr.
Implicit Type es : list expr.
Implicit Type v : val.
Implicit Type vs : list val.

Abbreviation branch :=
  (pattern * expr)%type.
Implicit Type br : branch.
Implicit Type brs : list branch.

Abbreviation recursive :=
  (binder * binder * expr)%type.
Implicit Type rec : recursive.
Implicit Type recs : list recursive.

Section expr_ind.
  Variable P : expr → Prop.

  Variable HVal :
    ∀ v,
    P (Val v).
  Variable HVar :
    ∀ (x : string),
    P (Var x).
  Variable HRec :
    ∀ f x,
    ∀ e, P e →
    P (Rec f x e).
  Variable HApply :
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    P (Apply e1 e2).
  Variable HLet :
    ∀ x,
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    P (Let x e1 e2).
  Variable HIf :
    ∀ e0, P e0 →
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    P (If e0 e1 e2).
  Variable HWhile :
    ∀ e0, P e0 →
    ∀ e1, P e1 →
    P (While e0 e1).
  Variable HFor :
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    ∀ e3, P e3 →
    P (For e1 e2 e3).
  Variable HMatch :
    ∀ e0, P e0 →
    ∀ x,
    ∀ e1, P e1 →
    ∀ brs, Forall (λ br, P br.2) brs →
    P (Match e0 x e1 brs).
  Variable HPrimitive0 :
    ∀ prim,
    P (Primitive0 prim).
  Variable HPrimitive1 :
    ∀ prim,
    ∀ e, P e →
    P (Primitive1 prim e).
  Variable HPrimitive2 :
    ∀ prim,
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    P (Primitive2 prim e1 e2).
  Variable HPrimitive3 :
    ∀ prim,
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    ∀ e3, P e3 →
    P (Primitive3 prim e1 e2 e3).
  Variable HBlock :
    ∀ mut tag,
    ∀ es, Forall P es →
    P (Block mut tag es).
  Variable HFork :
    ∀ e, P e →
    P (Fork e).
  Variable HResolve :
    ∀ e0, P e0 →
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    P (Resolve e0 e1 e2).

  Fixpoint expr_ind e :=
    match e with
    | Val v =>
        HVal
          v
    | Var x =>
        HVar
          x
    | Rec f x e =>
        HRec
          f x
          e (expr_ind e)
    | Apply e1 e2 =>
        HApply
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    | Let x e1 e2 =>
        HLet
          x
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    | If e0 e1 e2 =>
        HIf
          e0 (expr_ind e0)
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    | While e0 e1 =>
        HWhile
          e0 (expr_ind e0)
          e1 (expr_ind e1)
    | For e1 e2 e3 =>
        HFor
          e1 (expr_ind e1)
          e2 (expr_ind e2)
          e3 (expr_ind e3)
    | Match e0 x e1 brs =>
        HMatch
          e0 (expr_ind e0)
          x
          e1 (expr_ind e1)
          brs (Forall_true (λ br, P br.2) brs (λ br, expr_ind br.2))
    | Primitive0 prim =>
        HPrimitive0
          prim
    | Primitive1 prim e =>
        HPrimitive1
          prim
          e (expr_ind e)
    | Primitive2 prim e1 e2 =>
        HPrimitive2
          prim
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    | Primitive3 prim e1 e2 e3 =>
        HPrimitive3
          prim
          e1 (expr_ind e1)
          e2 (expr_ind e2)
          e3 (expr_ind e3)
    | Block mut tag es =>
        HBlock
          mut tag
          es (Forall_true P es expr_ind)
    | Fork e =>
        HFork
          e (expr_ind e)
    | Resolve e0 e1 e2 =>
        HResolve
          e0 (expr_ind e0)
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    end.
End expr_ind.

Register Scheme expr_ind as ind_dep for expr.

Section val_ind.
  Variable P : val → Prop.

  Variable HValLit :
    ∀ lit,
    P (ValLit lit).
  Variable HValRecs :
    ∀ i recs,
    P (ValRecs i recs).
  Variable HValBlock :
    ∀ gen tag,
    ∀ vs, Forall P vs →
    P (ValBlock gen tag vs).

  Fixpoint val_ind v :=
    match v with
    | ValLit lit =>
        HValLit
          lit
    | ValRecs i recs =>
        HValRecs
          i recs
    | ValBlock gen tag vs =>
        HValBlock
          gen tag
          vs (Forall_true P vs val_ind)
    end.
End val_ind.

Register Scheme val_ind as ind_dep for val.

Section exprｰvalｰmutind.
  Variable Pexpr : expr → Prop.
  Variable Pval : val → Prop.

  Variable HVal :
    ∀ v, Pval v →
    Pexpr (Val v).
  Variable HVar :
    ∀ (x : string),
    Pexpr (Var x).
  Variable HRec :
    ∀ f x,
    ∀ e, Pexpr e →
    Pexpr (Rec f x e).
  Variable HApply :
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    Pexpr (Apply e1 e2).
  Variable HLet :
    ∀ x,
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    Pexpr (Let x e1 e2).
  Variable HIf :
    ∀ e0, Pexpr e0 →
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    Pexpr (If e0 e1 e2).
  Variable HWhile :
    ∀ e0, Pexpr e0 →
    ∀ e1, Pexpr e1 →
    Pexpr (While e0 e1).
  Variable HFor :
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    ∀ e3, Pexpr e3 →
    Pexpr (For e1 e2 e3).
  Variable HMatch :
    ∀ e0, Pexpr e0 →
    ∀ x,
    ∀ e1, Pexpr e1 →
    ∀ brs, Forall (λ br, Pexpr br.2) brs →
    Pexpr (Match e0 x e1 brs).
  Variable HPrimitive0 :
    ∀ prim,
    Pexpr (Primitive0 prim).
  Variable HPrimitive1 :
    ∀ prim,
    ∀ e, Pexpr e →
    Pexpr (Primitive1 prim e).
  Variable HPrimitive2 :
    ∀ prim,
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    Pexpr (Primitive2 prim e1 e2).
  Variable HPrimitive3 :
    ∀ prim,
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    ∀ e3, Pexpr e3 →
    Pexpr (Primitive3 prim e1 e2 e3).
  Variable HBlock :
    ∀ mut tag,
    ∀ es, Forall Pexpr es →
    Pexpr (Block mut tag es).
  Variable HFork :
    ∀ e, Pexpr e →
    Pexpr (Fork e).
  Variable HResolve :
    ∀ e0, Pexpr e0 →
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    Pexpr (Resolve e0 e1 e2).

  Variable HValLit :
    ∀ lit,
    Pval (ValLit lit).
  Variable HValRecs :
    ∀ i,
    ∀ recs, Forall (λ rec, Pexpr rec.2) recs →
    Pval (ValRecs i recs).
  Variable HValBlock :
    ∀ gen tag,
    ∀ vs, Forall Pval vs →
    Pval (ValBlock gen tag vs).

  Fixpoint exprｰvalｰind e :=
    match e with
    | Val v =>
        HVal
          v (valｰexprｰind v)
    | Var x =>
        HVar
          x
    | Rec f x e =>
        HRec
          f x
          e (exprｰvalｰind e)
    | Apply e1 e2 =>
        HApply
          e1 (exprｰvalｰind e1)
          e2 (exprｰvalｰind e2)
    | Let x e1 e2 =>
        HLet
          x
          e1 (exprｰvalｰind e1)
          e2 (exprｰvalｰind e2)
    | If e0 e1 e2 =>
        HIf
          e0 (exprｰvalｰind e0)
          e1 (exprｰvalｰind e1)
          e2 (exprｰvalｰind e2)
    | While e0 e1 =>
        HWhile
          e0 (exprｰvalｰind e0)
          e1 (exprｰvalｰind e1)
    | For e1 e2 e3 =>
        HFor
          e1 (exprｰvalｰind e1)
          e2 (exprｰvalｰind e2)
          e3 (exprｰvalｰind e3)
    | Match e0 x e1 brs =>
        HMatch
          e0 (exprｰvalｰind e0)
          x
          e1 (exprｰvalｰind e1)
          brs (Forall_true (λ br, Pexpr br.2) brs (λ br, exprｰvalｰind br.2))
    | Primitive0 prim =>
        HPrimitive0
          prim
    | Primitive1 prim e =>
        HPrimitive1
          prim
          e (exprｰvalｰind e)
    | Primitive2 prim e1 e2 =>
        HPrimitive2
          prim
          e1 (exprｰvalｰind e1)
          e2 (exprｰvalｰind e2)
    | Primitive3 prim e1 e2 e3 =>
        HPrimitive3
          prim
          e1 (exprｰvalｰind e1)
          e2 (exprｰvalｰind e2)
          e3 (exprｰvalｰind e3)
    | Block mut tag es =>
        HBlock
          mut tag
          es (Forall_true Pexpr es exprｰvalｰind)
    | Fork e =>
        HFork
          e (exprｰvalｰind e)
    | Resolve e0 e1 e2 =>
        HResolve
          e0 (exprｰvalｰind e0)
          e1 (exprｰvalｰind e1)
          e2 (exprｰvalｰind e2)
    end
  with valｰexprｰind v :=
    match v with
    | ValLit lit =>
        HValLit
          lit
    | ValRecs i recs =>
        HValRecs
          i
          recs (Forall_true (λ rec, Pexpr rec.2) recs (λ rec, exprｰvalｰind rec.2))
    | ValBlock gen tag vs =>
        HValBlock
          gen tag
          vs (Forall_true Pval vs valｰexprｰind)
    end.

  Definition exprｰvalｰmutind :=
    conj
      exprｰvalｰind
      valｰexprｰind.
End exprｰvalｰmutind.

Canonical val_O {SI : sidx} :=
  leibnizO val.
Canonical expr_O {SI : sidx} :=
  leibnizO expr.

Abbreviation Fun x e := (
  Rec BAnon x e
)(only parsing
).
Abbreviation ValRec f x e := (
  ValRecs 0
    ( @cons recursive
        ( @pair (prod binder binder) expr
            (@pair binder binder f x)
            e
        )
        (@nil recursive)
    )
)(only parsing
).
Abbreviation ValFun x e := (
  ValRecs 0
    ( @cons recursive
        ( @pair (prod binder binder) expr
            (@pair binder binder BAnon x)
            e
        )
        (@nil recursive)
    )
)(only parsing
).

Abbreviation Seq e1 e2 := (
  Let BAnon e1 e2
)(only parsing
).

Abbreviation ValBool b := (
  ValLit (LitBool b)
)(only parsing
).
Abbreviation ValChar chr := (
  ValLit (LitChar chr)
)(only parsing
).
Abbreviation ValInt n := (
  ValLit (LitInt n)
)(only parsing
).
Abbreviation ValNat i := (
  ValLit (LitNat i)
)(only parsing
).
Abbreviation ValTag tag := (
  ValLit (LitTag tag)
)(only parsing
).
Abbreviation ValString str := (
  ValLit (LitString str)
)(only parsing
).
Abbreviation ValLoc l := (
  ValLit (LitLoc l)
)(only parsing
).
Abbreviation ValProph pid := (
  ValLit (LitProph pid)
)(only parsing
).

Abbreviation Tuple := (
  Block ImmutableNongenerative Tag0
)(only parsing
).
Abbreviation ValTuple := (
  ValBlock Nongenerative Tag0
)(only parsing
).

Abbreviation ValUnit := (
  ValTuple []
)(only parsing
).
Abbreviation Unit := (
  Val ValUnit
)(only parsing
).

Abbreviation Fail := (
  Apply Unit Unit
).
Abbreviation Skip := (
  Apply (Val (ValFun BAnon Unit)) Unit
).

Definition val۰of_int :=
  ValLit ∘ LitInt.

Definition val۰to_int v :=
  match v with
  | ValInt n =>
      Some n
  | _ =>
      None
  end.
Definition val۰to_int' :=
  default inhabitant ∘ val۰to_int.
Definition val۰to_nat' :=
  Z.to_nat ∘ val۰to_int'.

Abbreviation expr۰of_val :=
  Val
( only parsing
).

Definition expr۰to_val e :=
  match e with
  | Val v =>
      Some v
  | _ =>
      None
  end.

Lemma expr۰to_valｰof_val v :
  expr۰to_val (expr۰of_val v) = Some v.
Proof.
  by destruct v.
Qed.
Lemma expr۰of_valｰto_val e v :
  expr۰to_val e = Some v →
  expr۰of_val v = e.
Proof.
  destruct e => //=. by intros [= <-].
Qed.
#[global] Instance expr۰of_valｰinj :
  Inj (=) (=) expr۰of_val.
Proof.
  intros ?*. congruence.
Qed.

Definition expr۰of_vals vs :=
  expr۰of_val <$> vs.

Fixpoint expr۰to_vals es :=
  match es with
  | [] =>
      Some []
  | e :: es =>
      v ← expr۰to_val e ;
      es ← expr۰to_vals es ;
      Some $ v :: es
  end.

Lemma expr۰to_valsｰof_vals vs :
  expr۰to_vals (expr۰of_vals vs) = Some vs.
Proof.
  induction vs as [| v vs IH]; first done.
  rewrite /= IH. naive.
Qed.
Lemma expr۰of_valsｰto_vals es vs :
  expr۰to_vals es = Some vs →
  expr۰of_vals vs = es.
Proof.
  revert vs. induction es as [| e es IH]; first naive. move=> [| v vs] /= H.
  all: destruct (expr۰to_val e) eqn:Heq, (expr۰to_vals es); try done.
  inv H.
  f_equal; last naive.
  destruct e; naive.
Qed.
#[global] Instance expr۰of_valsｰinj :
  Inj (=) (=) expr۰of_vals.
Proof.
  apply _.
Qed.
Lemma lengthｰexpr۰of_vals vs :
  length (expr۰of_vals vs) = length vs.
Proof.
  apply length_fmap.
Qed.
Hint Rewrite
  @lengthｰexpr۰of_vals
: simp_length.

Fixpoint expr۰to_vals_suffix es :=
  match es with
  | [] =>
      Ok []
  | e :: es =>
      match expr۰to_vals_suffix es with
      | Ok vs =>
          if expr۰to_val e is Some v then
            Ok (v :: vs)
          else
            Error ([], e, vs)
      | Error (es, eᵣ, vs) =>
          Error (e :: es, eᵣ, vs)
      end
  end.
#[global] Arguments expr۰to_vals_suffix !_ / : assert.

Lemma expr۰to_vals_suffixｰspec es :
  es =
    match expr۰to_vals_suffix es with
    | Ok vs =>
        expr۰of_vals vs
    | Error (es, e, vs) =>
        es ++ e :: expr۰of_vals vs
    end.
Proof.
  induction es as [| e es IH] => //=.
  destruct (expr۰to_vals_suffix es) as [vs | ((es', eᵣ), vs)] => /=.
  - destruct (expr۰to_val e) as [v |] eqn:He => /=.
    + apply expr۰of_valｰto_val in He.
      naive.
    + naive.
  - naive.
Qed.
Lemma expr۰to_vals_suffixｰOk es vs :
  expr۰to_vals_suffix es = Ok vs →
  es = expr۰of_vals vs.
Proof.
  intros Heq.
  have H := expr۰to_vals_suffixｰspec es.
  rewrite Heq // in H.
Qed.
Lemma expr۰to_vals_suffixｰError es es' e vs :
  expr۰to_vals_suffix es = Error (es', e, vs) →
  es = es' ++ e :: expr۰of_vals vs.
Proof.
  intros Heq.
  have H := expr۰to_vals_suffixｰspec es.
  rewrite Heq // in H.
Qed.

#[global] Instance valｰinhabited : Inhabited val :=
  populate ValUnit.
Please derive Inhabited for expr.
#[global] Instance exprｰeq_dec :
  EqDecision expr.
Proof.
  unshelve refine (
    fix go e1 e2 : Decision (e1 = e2) :=
      let fix go_list es1 es2 : Decision (es1 = es2) :=
        match es1, es2 with
        | [], [] =>
            left _
        | e1 :: es1, e2 :: es2 =>
            cast_if_and
              (decide (e1 = e2))
              (decide (es1 = es2))
        | _, _ =>
            right _
        end
      in
      let fix go_branches brs1 brs2 : Decision (brs1 = brs2) :=
        match brs1, brs2 with
        | [], [] =>
            left _
        | (pat1, e1) :: brs1, (pat2, e2) :: brs2 =>
            cast_if_and3
              (decide (pat1 = pat2))
              (decide (e1 = e2))
              (decide (brs1 = brs2))
        | _, _ =>
            right _
        end
      in
      match e1, e2 with
      | Val v1, Val v2 =>
          cast_if
            (decide (v1 = v2))
      | Var x1, Var x2 =>
          cast_if
            (decide (x1 = x2))
      | Rec f1 x1 e1, Rec f2 x2 e2 =>
         cast_if_and3
           (decide (f1 = f2))
           (decide (x1 = x2))
           (decide (e1 = e2))
      | Apply e11 e12, Apply e21 e22 =>
          cast_if_and
            (decide (e11 = e21))
            (decide (e12 = e22))
      | Let x1 e11 e12, Let x2 e21 e22 =>
          cast_if_and3
           (decide (x1 = x2))
           (decide (e11 = e21))
           (decide (e12 = e22))
      | If e10 e11 e12, If e20 e21 e22 =>
         cast_if_and3
           (decide (e10 = e20))
           (decide (e11 = e21))
           (decide (e12 = e22))
      | While e10 e11, While e20 e21 =>
          cast_if_and
            (decide (e10 = e20))
            (decide (e11 = e21))
      | For e11 e12 e13, For e21 e22 e23 =>
          cast_if_and3
            (decide (e11 = e21))
            (decide (e12 = e22))
            (decide (e13 = e23))
      | Match e10 x1 e11 brs1, Match e20 x2 e21 brs2 =>
          cast_if_and4
            (decide (e10 = e20))
            (decide (x1 = x2))
            (decide (e11 = e21))
            (decide (brs1 = brs2))
      | Primitive0 prim1, Primitive0 prim2 =>
          cast_if
            (decide (prim1 = prim2))
      | Primitive1 prim1 e1, Primitive1 prim2 e2 =>
          cast_if_and
            (decide (prim1 = prim2))
            (decide (e1 = e2))
      | Primitive2 prim1 e11 e12, Primitive2 prim2 e21 e22 =>
          cast_if_and3
            (decide (prim1 = prim2))
            (decide (e11 = e21))
            (decide (e12 = e22))
      | Primitive3 prim1 e11 e12 e13, Primitive3 prim2 e21 e22 e23 =>
          cast_if_and4
            (decide (prim1 = prim2))
            (decide (e11 = e21))
            (decide (e12 = e22))
            (decide (e13 = e23))
      | Block mut1 tag1 es1, Block mut2 tag2 es2 =>
          cast_if_and3
            (decide (mut1 = mut2))
            (decide (tag1 = tag2))
            (decide (es1 = es2))
      | Fork e1, Fork e2 =>
          cast_if
            (decide (e1 = e2))
      | Resolve e10 e11 e12, Resolve e20 e21 e22 =>
         cast_if_and3
           (decide (e10 = e20))
           (decide (e11 = e21))
           (decide (e12 = e22))
      | _, _ =>
          right _
      end
    with go_val v1 v2 : Decision (v1 = v2) :=
      let fix go_recursives recs1 recs2 : Decision (recs1 = recs2) :=
        match recs1, recs2 with
        | [], [] =>
            left _
        | (bdrs1, e1) :: recs1, (bdrs2, e2) :: recs2 =>
            cast_if_and3
              (decide (bdrs1 = bdrs2))
              (decide (e1 = e2))
              (decide (recs1 = recs2))
        | _, _ =>
            right _
        end
      in
      let fix go_list vs1 vs2 : Decision (vs1 = vs2) :=
        match vs1, vs2 with
        | [], [] =>
            left _
        | v1 :: vs1, v2 :: vs2 =>
            cast_if_and
              (decide (v1 = v2))
              (decide (vs1 = vs2))
        | _, _ =>
            right _
        end
      in
      match v1, v2 with
      | ValLit l1, ValLit l2 =>
          cast_if
            (decide (l1 = l2))
      | ValRecs i1 recs1, ValRecs i2 recs2 =>
          cast_if_and
            (decide (i1 = i2))
            (decide (recs1 = recs2))
      | ValBlock gen1 tag1 vs1, ValBlock gen2 tag2 vs2 =>
          cast_if_and3
            (decide (gen1 = gen2))
            (decide (tag1 = tag2))
            (decide (vs1 = vs2))
      | _, _ =>
          right _
      end
    for go
  ).
  all: try clear go_list.
  all: try clear go_branches.
  all: try clear go_recursives.
  all: clear go go_val.
  all: abstract congruence.
Defined.
#[global] Instance valｰeq_dec :
  EqDecision val.
Proof.
  unshelve refine (
    fix go_val v1 v2 : Decision (v1 = v2) :=
      let fix go_recursives recs1 recs2 : Decision (recs1 = recs2) :=
        match recs1, recs2 with
        | [], [] =>
            left _
        | (bdrs1, e1) :: recs1, (bdrs2, e2) :: recs2 =>
            cast_if_and3
              (decide (bdrs1 = bdrs2))
              (decide (e1 = e2))
              (decide (recs1 = recs2))
        | _, _ =>
            right _
        end
      in
      let fix go_list vs1 vs2 : Decision (vs1 = vs2) :=
        match vs1, vs2 with
        | [], [] =>
            left _
        | v1 :: vs1, v2 :: vs2 =>
            cast_if_and
              (decide (v1 = v2))
              (decide (vs1 = vs2))
        | _, _ =>
            right _
        end
      in
      match v1, v2 with
      | ValLit l1, ValLit l2 =>
          cast_if
            (decide (l1 = l2))
      | ValRecs i1 recs1, ValRecs i2 recs2 =>
          cast_if_and
            (decide (i1 = i2))
            (decide (recs1 = recs2))
      | ValBlock gen1 tag1 es1, ValBlock gen2 tag2 es2 =>
          cast_if_and3
            (decide (gen1 = gen2))
            (decide (tag1 = tag2))
            (decide (es1 = es2))
      | _, _ =>
          right _
      end
  ).
  all: clear go_recursives.
  all: try clear go_list.
  all: clear go_val.
  all: abstract congruence.
Defined.
Variant encode_leaf :=
  | EncodeNat i
  | EncodeTag tag
  | EncodeBinder x
  | EncodeGenerativity gen
  | EncodeMutability mut
  | EncodeLit lit
  | EncodePattern (pat : pattern)
  | EncodePrimitive0 (prim : primitive0)
  | EncodePrimitive1 (prim : primitive1)
  | EncodePrimitive2 (prim : primitive2)
  | EncodePrimitive3 (prim : primitive3).
#[local] Please derive EqDecision for encode_leaf.
#[local] Please derive Countable for encode_leaf.
Abbreviation EncodeString str := (
  EncodeBinder (BNamed str)
).
#[global] Instance exprｰcountable :
  Countable expr.
Proof.
  #[local] Abbreviation code_Val :=
    0.
  #[local] Abbreviation code_Rec :=
    1.
  #[local] Abbreviation code_Apply :=
    2.
  #[local] Abbreviation code_Let :=
    3.
  #[local] Abbreviation code_If :=
    4.
  #[local] Abbreviation code_While :=
    5.
  #[local] Abbreviation code_For :=
    6.
  #[local] Abbreviation code_Match :=
    7.
  #[local] Abbreviation code_branch :=
    8.
  #[local] Abbreviation code_Primitive0 :=
    9.
  #[local] Abbreviation code_Primitive1 :=
    10.
  #[local] Abbreviation code_Primitive2 :=
    11.
  #[local] Abbreviation code_Primitive3 :=
    12.
  #[local] Abbreviation code_Block :=
    13.
  #[local] Abbreviation code_Fork :=
    14.
  #[local] Abbreviation code_Resolve :=
    15.
  #[local] Abbreviation code_ValRecs :=
    0.
  #[local] Abbreviation code_recursive :=
    1.
  #[local] Abbreviation code_ValBlock :=
    2.
  pose encode :=
    fix go e :=
      let go_list :=
        map go
      in
      let go_branch '(pat, e) :=
        GenNode code_branch [GenLeaf (EncodePattern pat); go e]
      in
      let go_branches :=
        map go_branch
      in
      match e with
      | Val v =>
          GenNode code_Val [go_val v]
      | Var x =>
          GenLeaf (EncodeString x)
      | Rec f x e =>
          GenNode code_Rec [GenLeaf (EncodeBinder f); GenLeaf (EncodeBinder x); go e]
      | Apply e1 e2 =>
          GenNode code_Apply [go e1; go e2]
      | Let x e1 e2 =>
          GenNode code_Let [GenLeaf (EncodeBinder x); go e1; go e2]
      | If e0 e1 e2 =>
          GenNode code_If [go e0; go e1; go e2]
      | While e0 e1 =>
          GenNode code_While [go e0; go e1]
      | For e1 e2 e3 =>
          GenNode code_For [go e1; go e2; go e3]
      | Match e0 x e1 brs =>
          GenNode code_Match $ go e0 :: GenLeaf (EncodeBinder x) :: go e1 :: go_branches brs
      | Primitive0 prim =>
          GenNode code_Primitive0 [GenLeaf (EncodePrimitive0 prim)]
      | Primitive1 prim e =>
          GenNode code_Primitive1 [GenLeaf (EncodePrimitive1 prim); go e]
      | Primitive2 prim e1 e2 =>
          GenNode code_Primitive2 [GenLeaf (EncodePrimitive2 prim); go e1; go e2]
      | Primitive3 prim e1 e2 e3 =>
          GenNode code_Primitive3 [GenLeaf (EncodePrimitive3 prim); go e1; go e2; go e3]
      | Block mut tag es =>
          GenNode code_Block $ GenLeaf (EncodeMutability mut) :: GenLeaf (EncodeTag tag) :: go_list es
      | Fork e =>
          GenNode code_Fork [go e]
      | Resolve e0 e1 e2 =>
          GenNode code_Resolve [go e0; go e1; go e2]
      end
    with go_val v :=
      let go_recursive '((f, x), e) :=
        GenNode code_recursive [GenLeaf (EncodeBinder f); GenLeaf (EncodeBinder x); go e]
      in
      let go_recursives :=
        map go_recursive
      in
      let go_list :=
        map go_val
      in
      match v with
      | ValLit lit =>
          GenLeaf (EncodeLit lit)
      | ValRecs i recs =>
         GenNode code_ValRecs (GenLeaf (EncodeNat i) :: go_recursives recs)
      | ValBlock gen tag vs =>
          GenNode code_ValBlock $ GenLeaf (EncodeGenerativity gen) :: GenLeaf (EncodeTag tag) :: go_list vs
      end
    for go.
  pose decode :=
    fix go _e :=
      let go_list :=
        map go
      in
      let go_branch _br :=
        match _br with
        | GenNode code_branch [GenLeaf (EncodePattern pat); e] =>
            (pat, go e)
        | _ =>
            (@inhabitant _ patternｰinhabited, Unit)
        end
      in
      let go_branches :=
        map go_branch
      in
      match _e with
      | GenNode code_Val [v] =>
          Val $ go_val v
      | GenLeaf (EncodeString x) =>
          Var x
      | GenNode code_Rec [GenLeaf (EncodeBinder f); GenLeaf (EncodeBinder x); e] =>
          Rec f x $ go e
      | GenNode code_Apply [e1; e2] =>
          Apply (go e1) (go e2)
      | GenNode code_Let [GenLeaf (EncodeBinder x); e1; e2] =>
          Let x (go e1) (go e2)
      | GenNode code_If [e0; e1; e2] =>
          If (go e0) (go e1) (go e2)
      | GenNode code_While [e0; e1] =>
          While (go e0) (go e1)
      | GenNode code_For [e1; e2; e3] =>
          For (go e1) (go e2) (go e3)
      | GenNode code_Match (e0 :: GenLeaf (EncodeBinder x) :: e1 :: brs) =>
          Match (go e0) x (go e1) (go_branches brs)
      | GenNode code_Primitive0 [GenLeaf (EncodePrimitive0 prim)] =>
          Primitive0 prim
      | GenNode code_Primitive1 [GenLeaf (EncodePrimitive1 prim); e] =>
          Primitive1 prim (go e)
      | GenNode code_Primitive2 [GenLeaf (EncodePrimitive2 prim); e1; e2] =>
          Primitive2 prim (go e1) (go e2)
      | GenNode code_Primitive3 [GenLeaf (EncodePrimitive3 prim); e1; e2; e3] =>
          Primitive3 prim (go e1) (go e2) (go e3)
      | GenNode code_Block (GenLeaf (EncodeMutability mut) :: GenLeaf (EncodeTag tag) :: es) =>
          Block mut tag $ go_list es
      | GenNode code_Fork [e] =>
          Fork $ go e
      | GenNode code_Resolve [e0; e1; e2] =>
          Resolve (go e0) (go e1) (go e2)
      | _ =>
          @inhabitant _ exprｰinhabited
      end
    with go_val _v :=
      let go_recursive _rec :=
        match _rec with
        | GenNode code_recursive [GenLeaf (EncodeBinder f); GenLeaf (EncodeBinder x); e] =>
            (f, x, go e)
        | _ =>
            (BAnon, BAnon, Unit)
        end
      in
      let go_recursives :=
        map go_recursive
      in
      let go_list :=
        map go_val
      in
      match _v with
      | GenLeaf (EncodeLit lit) =>
          ValLit lit
      | GenNode code_ValRecs (GenLeaf (EncodeNat i) :: recs) =>
          ValRecs i (go_recursives recs)
      | GenNode code_ValBlock (GenLeaf (EncodeGenerativity gen) :: GenLeaf (EncodeTag tag) :: vs) =>
          ValBlock gen tag $ go_list vs
      | _ =>
          @inhabitant _ valｰinhabited
      end
    for go.
  refine (inj_countable' encode decode _).
  refine (fix go e := _ with go_val v := _ for go).
  - destruct e; simpl; f_equal; try done.
    + match goal with |- _ = ?v =>
        exact (go_val v)
      end.
    + induction brs as [| (? & ?) ?] => //=. repeat f_equal; done.
    + match goal with |- _ = ?es =>
        rewrite /map; induction es as [| ? ? ->] => /=; f_equal; done
      end.
  - destruct v; simpl; f_equal; try done.
    + induction recs as [| ((? & ?) & ?) ?] => //=. repeat f_equal; done.
    + match goal with |- _ = ?vs =>
        rewrite /map; induction vs as [| ? ? ->]; simpl; f_equal; done
      end.
Qed.
#[global] Instance valｰcountable :
  Countable val.
Proof.
  refine (inj_countable expr۰of_val expr۰to_val _); auto using expr۰to_valｰof_val.
Qed.

Definition expr۰is_resolve e :=
  if e is Resolve _ _ _ then
    True
  else
 False.

#[global] Instance expr۰is_resolveｰdec e :
  Decision (expr۰is_resolve e).
Proof.
  refine (
    if e is Resolve _ _ _ then
      left _
    else
      right _
  ).
  all: abstract naive.
Defined.

Lemma expr۰is_resolveｰalt e :
  expr۰is_resolve e →
    ∃ e0 e1 e2,
    e = Resolve e0 e1 e2.
Proof.
  destruct e; naive.
Qed.
