From stdpp Require Import
  countable.

From iris.algebra Require Import
  ofe.

From zoo Require Import
  prelude.
From zoo.common Require Import
  countable.
From zoo.common Require Export
  binder.
From zoo.language Require Export
  location.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types i tag : nat.
Implicit Types n : Z.
Implicit Types l : location.
Implicit Types f x : binder.

Definition block_id :=
  positive.
Implicit Types bid : option block_id.

Definition prophet_id :=
  positive.
Implicit Types pid : prophet_id.

Inductive mutability :=
  | Mutable
  | Immutable.
Implicit Types mut : mutability.

#[global] Instance mutability_eq_dec : EqDecision mutability :=
  ltac:(solve_decision).
#[global] Instance mutability_countable :
  Countable mutability.
Proof.
  pose encode mut :=
    match mut with
    | Mutable =>
        0
    | Immutable =>
        1
    end.
  pose decode _mut :=
    match _mut with
    | 0 =>
        Mutable
    | _ =>
        Immutable
    end.
  refine (inj_countable' encode decode _); intros []; done.
Qed.

Inductive literal :=
  | LitBool b
  | LitInt n
  | LitLoc l
  | LitProph pid
  | LitPoison.
Implicit Types lit : literal.

#[global] Instance literal_eq_dec : EqDecision literal :=
  ltac:(solve_decision).
#[global] Instance literal_countable :
  Countable literal.
Proof.
  pose encode lit :=
    match lit with
    | LitBool b =>
        inl $ inl $ inl $ inl b
    | LitInt n =>
        inl $ inl $ inl $ inr n
    | LitLoc l =>
        inl $ inl $ inr l
    | LitProph pid =>
        inl $ inr pid
    | LitPoison =>
        inr ()
    end.
  pose decode _lit :=
    match _lit with
    | inl (inl (inl (inl b))) =>
        LitBool b
    | inl (inl (inl (inr n))) =>
        LitInt n
    | inl (inl (inr l)) =>
        LitLoc l
    | inl (inr p) =>
        LitProph p
    | inr () =>
        LitPoison
    end.
  refine (inj_countable' encode decode _); intros []; done.
Qed.

Inductive unop :=
  | UnopNeg
  | UnopMinus.

#[global] Instance unop_eq_dec : EqDecision unop :=
  ltac:(solve_decision).
#[global] Instance unop_countable :
  Countable unop.
Proof.
  pose encode op :=
    match op with
    | UnopNeg =>
        0
    | UnopMinus =>
        1
    end.
  pose decode op :=
    match op with
    | 0 =>
        UnopNeg
    | _ =>
        UnopMinus
    end.
  refine (inj_countable' encode decode _); intros []; done.
Qed.

Inductive binop :=
  | BinopPlus | BinopMinus | BinopMult | BinopQuot | BinopRem
  | BinopLand | BinopLor | BinopLsl | BinopLsr
  | BinopLe | BinopLt | BinopGe | BinopGt.

#[global] Instance binop_eq_dec : EqDecision binop :=
  ltac:(solve_decision).
#[global] Instance binop_countable :
  Countable binop.
Proof.
  pose encode op :=
    match op with
    | BinopPlus => 0
    | BinopMinus => 1
    | BinopMult => 2
    | BinopQuot => 3
    | BinopRem => 4
    | BinopLand => 5
    | BinopLor => 6
    | BinopLsl => 7
    | BinopLsr => 8
    | BinopLe => 9
    | BinopLt => 10
    | BinopGe => 11
    | BinopGt => 12
  end.
  pose decode op :=
    match op with
    | 0 => BinopPlus
    | 1 => BinopMinus
    | 2 => BinopMult
    | 3 => BinopQuot
    | 4 => BinopRem
    | 5 => BinopLand
    | 6 => BinopLor
    | 7 => BinopLsl
    | 8 => BinopLsr
    | 9 => BinopLe
    | 10 => BinopLt
    | 11 => BinopGe
    | _ => BinopGt
  end.
  refine (inj_countable' encode decode _); intros []; done.
Qed.

Record pattern := {
  pattern_tag : nat ;
  pattern_fields : list binder ;
  pattern_as : binder ;
}.

#[global] Instance pattern_inhabited : Inhabited pattern :=
  populate {|
    pattern_tag := inhabitant ;
    pattern_fields := inhabitant ;
    pattern_as := inhabitant ;
  |}.
#[global] Instance pattern_eq_dec : EqDecision pattern :=
  ltac:(solve_decision).
#[global] Instance pattern_countable :
  Countable pattern.
Proof.
  solve_countable.
Qed.

Unset Elimination Schemes.
Inductive expr :=
  | Val (v : val)
  | Var (x : string)
  | Rec f x (e : expr)
  | App (e1 e2 : expr)
  | Let x (e1 e2 : expr)
  | Unop (op : unop) (e : expr)
  | Binop (op : binop) (e1 e2 : expr)
  | Equal (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  | For (e1 e2 e3 : expr)
  | Alloc (e1 e2 : expr)
  | Block mut tag (es : list expr)
  | Reveal (e : expr)
  | Match (e0 : expr) x (e1 : expr) (brs : list (pattern * expr))
  | GetTag (e : expr)
  | GetSize (e : expr)
  | Load (e1 e2 : expr)
  | Store (e1 e2 e3 : expr)
  | Xchg (e1 e2 : expr)
  | CAS (e0 e1 e2 : expr)
  | FAA (e1 e2 : expr)
  | Fork (e : expr)
  | Proph
  | Resolve (e0 e1 e2 : expr)
with val :=
  | ValLit lit
  | ValRecs i (recs : list (binder * binder * expr))
  | ValBlock bid tag (vs : list val).
Set Elimination Schemes.
Implicit Types e : expr.
Implicit Types es : list expr.
Implicit Types v : val.
Implicit Types vs : list val.

Notation branch :=
  (pattern * expr)%type.
Implicit Types br : branch.
Implicit Types brs : list branch.

Notation recursive :=
  (binder * binder * expr)%type.
Implicit Types rec : recursive.
Implicit Types recs : list recursive.

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
  Variable HApp :
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    P (App e1 e2).
  Variable HLet :
    ∀ x,
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    P (Let x e1 e2).
  Variable HUnop :
    ∀ op,
    ∀ e, P e →
    P (Unop op e).
  Variable HBinop :
    ∀ op,
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    P (Binop op e1 e2).
  Variable HEqual :
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    P (Equal e1 e2).
  Variable HIf :
    ∀ e0, P e0 →
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    P (If e0 e1 e2).
  Variable HFor :
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    ∀ e3, P e3 →
    P (For e1 e2 e3).
  Variable HAlloc :
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    P (Alloc e1 e2).
  Variable HBlock :
    ∀ mut tag,
    ∀ es, Forall P es →
    P (Block mut tag es).
  Variable HReveal :
    ∀ e, P e →
    P (Reveal e).
  Variable HMatch :
    ∀ e0, P e0 →
    ∀ x,
    ∀ e1, P e1 →
    ∀ brs, Forall (λ br, P br.2) brs →
    P (Match e0 x e1 brs).
  Variable HGetTag :
    ∀ e, P e →
    P (GetTag e).
  Variable HGetSize :
    ∀ e, P e →
    P (GetSize e).
  Variable HLoad :
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    P (Load e1 e2).
  Variable HStore :
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    ∀ e3, P e3 →
    P (Store e1 e2 e3).
  Variable HXchg :
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    P (Xchg e1 e2).
  Variable HCAS :
    ∀ e0, P e0 →
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    P (CAS e0 e1 e2).
  Variable HFAA :
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    P (FAA e1 e2).
  Variable HFork :
    ∀ e, P e →
    P (Fork e).
  Variable HProph :
    P Proph.
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
    | App e1 e2 =>
        HApp
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    | Let x e1 e2 =>
        HLet
          x
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    | Unop op e =>
        HUnop
          op
          e (expr_ind e)
    | Binop op e1 e2 =>
        HBinop
          op
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    | Equal e1 e2 =>
        HEqual
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    | If e0 e1 e2 =>
        HIf
          e0 (expr_ind e0)
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    | For e1 e2 e3 =>
        HFor
          e1 (expr_ind e1)
          e2 (expr_ind e2)
          e3 (expr_ind e3)
    | Alloc e1 e2 =>
        HAlloc
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    | Block mut tag es =>
        HBlock
          mut tag
          es (Forall_true P es expr_ind)
    | Reveal e =>
        HReveal
          e (expr_ind e)
    | Match e0 x e1 brs =>
        HMatch
          e0 (expr_ind e0)
          x
          e1 (expr_ind e1)
          brs (Forall_true (λ br, P br.2) brs (λ br, expr_ind br.2))
    | GetTag e =>
        HGetTag
          e (expr_ind e)
    | GetSize e =>
        HGetSize
          e (expr_ind e)
    | Load e1 e2 =>
        HLoad
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    | Store e1 e2 e3 =>
        HStore
          e1 (expr_ind e1)
          e2 (expr_ind e2)
          e3 (expr_ind e3)
    | Xchg e1 e2 =>
        HXchg
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    | CAS e0 e1 e2 =>
        HCAS
          e0 (expr_ind e0)
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    | FAA e1 e2 =>
        HFAA
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    | Fork e =>
        HFork
          e (expr_ind e)
    | Proph =>
        HProph
    | Resolve e0 e1 e2 =>
        HResolve
          e0 (expr_ind e0)
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    end.
End expr_ind.

Section val_ind.
  Variable P : val → Prop.

  Variable HValLit :
    ∀ lit,
    P (ValLit lit).
  Variable HValRecs :
    ∀ i recs,
    P (ValRecs i recs).
  Variable HValBlock :
    ∀ bid tag,
    ∀ vs, Forall P vs →
    P (ValBlock bid tag vs).

  Fixpoint val_ind v :=
    match v with
    | ValLit lit =>
        HValLit
          lit
    | ValRecs i recs =>
        HValRecs
          i recs
    | ValBlock bid tag vs =>
        HValBlock
          bid tag
          vs (Forall_true P vs val_ind)
    end.
End val_ind.

Section expr_val_ind.
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
  Variable HApp :
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    Pexpr (App e1 e2).
  Variable HLet :
    ∀ x,
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    Pexpr (Let x e1 e2).
  Variable HUnop :
    ∀ op,
    ∀ e, Pexpr e →
    Pexpr (Unop op e).
  Variable HBinop :
    ∀ op,
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    Pexpr (Binop op e1 e2).
  Variable HEqual :
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    Pexpr (Equal e1 e2).
  Variable HIf :
    ∀ e0, Pexpr e0 →
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    Pexpr (If e0 e1 e2).
  Variable HFor :
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    ∀ e3, Pexpr e3 →
    Pexpr (For e1 e2 e3).
  Variable HAlloc :
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    Pexpr (Alloc e1 e2).
  Variable HBlock :
    ∀ mut tag,
    ∀ es, Forall Pexpr es →
    Pexpr (Block mut tag es).
  Variable HReveal :
    ∀ e, Pexpr e →
    Pexpr (Reveal e).
  Variable HMatch :
    ∀ e0, Pexpr e0 →
    ∀ x,
    ∀ e1, Pexpr e1 →
    ∀ brs, Forall (λ br, Pexpr br.2) brs →
    Pexpr (Match e0 x e1 brs).
  Variable HGetTag :
    ∀ e, Pexpr e →
    Pexpr (GetTag e).
  Variable HGetSize :
    ∀ e, Pexpr e →
    Pexpr (GetSize e).
  Variable HLoad :
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    Pexpr (Load e1 e2).
  Variable HStore :
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    ∀ e3, Pexpr e3 →
    Pexpr (Store e1 e2 e3).
  Variable HXchg :
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    Pexpr (Xchg e1 e2).
  Variable HCAS :
    ∀ e0, Pexpr e0 →
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    Pexpr (CAS e0 e1 e2).
  Variable HFAA :
    ∀ e1, Pexpr e1 →
    ∀ e2, Pexpr e2 →
    Pexpr (FAA e1 e2).
  Variable HFork :
    ∀ e, Pexpr e →
    Pexpr (Fork e).
  Variable HProph :
    Pexpr Proph.
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
    ∀ bid tag,
    ∀ vs, Forall Pval vs →
    Pval (ValBlock bid tag vs).

  Fixpoint expr_val_ind e :=
    match e with
    | Val v =>
        HVal
          v (val_expr_ind v)
    | Var x =>
        HVar
          x
    | Rec f x e =>
        HRec
          f x
          e (expr_val_ind e)
    | App e1 e2 =>
        HApp
          e1 (expr_val_ind e1)
          e2 (expr_val_ind e2)
    | Let x e1 e2 =>
        HLet
          x
          e1 (expr_val_ind e1)
          e2 (expr_val_ind e2)
    | Unop op e =>
        HUnop
          op
          e (expr_val_ind e)
    | Binop op e1 e2 =>
        HBinop
          op
          e1 (expr_val_ind e1)
          e2 (expr_val_ind e2)
    | Equal e1 e2 =>
        HEqual
          e1 (expr_val_ind e1)
          e2 (expr_val_ind e2)
    | If e0 e1 e2 =>
        HIf
          e0 (expr_val_ind e0)
          e1 (expr_val_ind e1)
          e2 (expr_val_ind e2)
    | For e1 e2 e3 =>
        HFor
          e1 (expr_val_ind e1)
          e2 (expr_val_ind e2)
          e3 (expr_val_ind e3)
    | Alloc e1 e2 =>
        HAlloc
          e1 (expr_val_ind e1)
          e2 (expr_val_ind e2)
    | Block mut tag es =>
        HBlock
          mut tag
          es (Forall_true Pexpr es expr_val_ind)
    | Reveal e =>
        HReveal
          e (expr_val_ind e)
    | Match e0 x e1 brs =>
        HMatch
          e0 (expr_val_ind e0)
          x
          e1 (expr_val_ind e1)
          brs (Forall_true (λ br, Pexpr br.2) brs (λ br, expr_val_ind br.2))
    | GetTag e =>
        HGetTag
          e (expr_val_ind e)
    | GetSize e =>
        HGetSize
          e (expr_val_ind e)
    | Load e1 e2 =>
        HLoad
          e1 (expr_val_ind e1)
          e2 (expr_val_ind e2)
    | Store e1 e2 e3 =>
        HStore
          e1 (expr_val_ind e1)
          e2 (expr_val_ind e2)
          e3 (expr_val_ind e3)
    | Xchg e1 e2 =>
        HXchg
          e1 (expr_val_ind e1)
          e2 (expr_val_ind e2)
    | CAS e0 e1 e2 =>
        HCAS
          e0 (expr_val_ind e0)
          e1 (expr_val_ind e1)
          e2 (expr_val_ind e2)
    | FAA e1 e2 =>
        HFAA
          e1 (expr_val_ind e1)
          e2 (expr_val_ind e2)
    | Fork e =>
        HFork
          e (expr_val_ind e)
    | Proph =>
        HProph
    | Resolve e0 e1 e2 =>
        HResolve
          e0 (expr_val_ind e0)
          e1 (expr_val_ind e1)
          e2 (expr_val_ind e2)
    end
  with val_expr_ind v :=
    match v with
    | ValLit lit =>
        HValLit
          lit
    | ValRecs i recs =>
        HValRecs
          i
          recs (Forall_true (λ rec, Pexpr rec.2) recs (λ rec, expr_val_ind rec.2))
    | ValBlock bid tag vs =>
        HValBlock
          bid tag
          vs (Forall_true Pval vs val_expr_ind)
    end.
End expr_val_ind.

Canonical val_O :=
  leibnizO val.
Canonical expr_O :=
  leibnizO expr.

Notation Fun x e := (
  Rec BAnon x e
)(only parsing
).
Notation ValRec f x e := (
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
Notation ValFun x e := (
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

Notation Seq e1 e2 := (
  Let BAnon e1 e2
)(only parsing
).

Notation ValBool b := (
  ValLit (LitBool b)
)(only parsing
).
Notation ValInt n := (
  ValLit (LitInt n)
)(only parsing
).
Notation ValNat i := (
  ValLit (LitInt (Z.of_nat i))
)(only parsing
).
Notation ValLoc l := (
  ValLit (LitLoc l)
)(only parsing
).
Notation ValProph pid := (
  ValLit (LitProph pid)
)(only parsing
).
Notation ValPoison := (
  ValLit LitPoison
)(only parsing
).

Notation Tuple := (
  Block Immutable 0
)(only parsing
).
Notation ValTuple := (
  ValBlock None 0
)(only parsing
).

Notation ValUnit := (
  ValTuple []
)(only parsing
).
Notation Unit := (
  Val ValUnit
)(only parsing
).

Notation Fail := (
  App Unit Unit
).

Notation of_val :=
  Val
( only parsing
).
Definition to_val e :=
  match e with
  | Val v =>
      Some v
  | _ =>
      None
  end.

Lemma to_of_val v :
  to_val (of_val v) = Some v.
Proof.
  by destruct v.
Qed.
Lemma of_to_val e v :
  to_val e = Some v →
  of_val v = e.
Proof.
  destruct e => //=. by intros [= <-].
Qed.
#[global] Instance of_val_inj :
  Inj (=) (=) of_val.
Proof.
  intros ?*. congruence.
Qed.

Definition of_vals vs :=
  of_val <$> vs.
Fixpoint to_vals es :=
  match es with
  | [] =>
      Some []
  | e :: es =>
      v ← to_val e ;
      es ← to_vals es ;
      mret $ v :: es
  end.

Lemma to_of_vals vs :
  to_vals (of_vals vs) = Some vs.
Proof.
  induction vs as [| v vs IH]; first done.
  rewrite /= IH. naive_solver.
Qed.
Lemma of_to_vals es vs :
  to_vals es = Some vs →
  of_vals vs = es.
Proof.
  revert vs. induction es as [| e es IH]; first naive_solver. move=> [| v vs] /= H.
  all: destruct (to_val e) eqn:Heq, (to_vals es); try done.
  invert H.
  f_equal; last naive_solver.
  destruct e; naive_solver.
Qed.
#[global] Instance of_vals_inj :
  Inj (=) (=) of_vals.
Proof.
  apply _.
Qed.
Lemma length_of_vals vs :
  length (of_vals vs) = length vs.
Proof.
  rewrite length_map //.
Qed.

#[global] Instance val_inhabited : Inhabited val :=
  populate ValUnit.
#[global] Instance expr_inhabited : Inhabited expr :=
  populate (Val inhabitant).
#[global] Instance expr_eq_dec : EqDecision expr.
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
      | App e11 e12, App e21 e22 =>
          cast_if_and
            (decide (e11 = e21))
            (decide (e12 = e22))
      | Let x1 e11 e12, Let x2 e21 e22 =>
          cast_if_and3
           (decide (x1 = x2))
           (decide (e11 = e21))
           (decide (e12 = e22))
      | Unop op1 e1, Unop op2 e2 =>
          cast_if_and
            (decide (op1 = op2))
            (decide (e1 = e2))
      | Binop op1 e11 e12, Binop op2 e21 e22 =>
         cast_if_and3
           (decide (op1 = op2))
           (decide (e11 = e21))
           (decide (e12 = e22))
      | Equal e11 e12, Equal e21 e22 =>
          cast_if_and
            (decide (e11 = e21))
            (decide (e12 = e22))
      | If e10 e11 e12, If e20 e21 e22 =>
         cast_if_and3
           (decide (e10 = e20))
           (decide (e11 = e21))
           (decide (e12 = e22))
      | For e11 e12 e13, For e21 e22 e23 =>
          cast_if_and3
            (decide (e11 = e21))
            (decide (e12 = e22))
            (decide (e13 = e23))
      | Alloc e11 e12, Alloc e21 e22 =>
         cast_if_and
           (decide (e11 = e21))
           (decide (e12 = e22))
      | Block mut1 tag1 es1, Block mut2 tag2 es2 =>
          cast_if_and3
            (decide (mut1 = mut2))
            (decide (tag1 = tag2))
            (decide (es1 = es2))
      | Reveal e1, Reveal e2 =>
          cast_if
            (decide (e1 = e2))
      | Match e10 x1 e11 brs1, Match e20 x2 e21 brs2 =>
          cast_if_and4
            (decide (e10 = e20))
            (decide (x1 = x2))
            (decide (e11 = e21))
            (decide (brs1 = brs2))
      | GetTag e1, GetTag e2 =>
          cast_if
            (decide (e1 = e2))
      | GetSize e1, GetSize e2 =>
          cast_if
            (decide (e1 = e2))
      | Load e11 e12, Load e21 e22 =>
          cast_if_and
            (decide (e11 = e21))
            (decide (e12 = e22))
      | Store e11 e12 e13, Store e21 e22 e23 =>
         cast_if_and3
           (decide (e11 = e21))
           (decide (e12 = e22))
           (decide (e13 = e23))
      | Xchg e11 e12, Xchg e21 e22 =>
          cast_if_and
            (decide (e11 = e21))
            (decide (e12 = e22))
      | CAS e10 e11 e12, CAS e20 e21 e22 =>
         cast_if_and3
           (decide (e10 = e20))
           (decide (e11 = e21))
           (decide (e12 = e22))
      | FAA e11 e12, FAA e21 e22 =>
         cast_if_and
           (decide (e11 = e21))
           (decide (e12 = e22))
      | Fork e1, Fork e2 =>
          cast_if
            (decide (e1 = e2))
      | Proph, Proph =>
          left _
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
      | ValBlock bid1 tag1 vs1, ValBlock bid2 tag2 vs2 =>
          cast_if_and3
            (decide (bid1 = bid2))
            (decide (tag1 = tag2))
            (decide (vs1 = vs2))
      | _, _ =>
          right _
      end
    for go
  );
  try clear go_list;
  try clear go_branches;
  try clear go_recursives;
  clear go go_val;
  abstract intuition congruence.
Defined.
#[global] Instance val_eq_dec : EqDecision val.
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
      | ValBlock bid1 tag1 es1, ValBlock bid2 tag2 es2 =>
          cast_if_and3
            (decide (bid1 = bid2))
            (decide (tag1 = tag2))
            (decide (es1 = es2))
      | _, _ =>
          right _
      end
  );
  clear go_recursives;
  try clear go_list;
  clear go_val;
  abstract intuition congruence.
Defined.
Variant encode_leaf :=
  | EncodeNat tag
  | EncodeBinder x
  | EncodeBlockId bid
  | EncodeMutability mut
  | EncodeLit lit
  | EncodeUnop (op : unop)
  | EncodeBinop (op : binop)
  | EncodePattern (pat : pattern).
#[local] Instance encode_leaf_eq_dec : EqDecision encode_leaf :=
  ltac:(solve_decision).
#[local] Instance encode_leaf_countable :
  Countable encode_leaf.
Proof.
  pose encode leaf :=
    match leaf with
    | EncodeNat tag =>
        inl $ inl $ inl $ inl $ inl $ inl $ inl tag
    | EncodeBinder bdr =>
        inl $ inl $ inl $ inl $ inl $ inl $ inr bdr
    | EncodeBlockId bid =>
        inl $ inl $ inl $ inl $ inl $ inr bid
    | EncodeMutability mut =>
        inl $ inl $ inl $ inl $ inr mut
    | EncodeLit lit =>
        inl $ inl $ inl $ inr lit
    | EncodeUnop op =>
        inl $ inl $ inr op
    | EncodeBinop op =>
        inl $ inr op
    | EncodePattern pat =>
        inr pat
    end.
  pose decode leaf :=
    match leaf with
    | inl (inl (inl (inl (inl (inl (inl tag)))))) =>
        EncodeNat tag
    | inl (inl (inl (inl (inl (inl (inr bdr)))))) =>
        EncodeBinder bdr
    | inl (inl (inl (inl (inl (inr bid))))) =>
        EncodeBlockId bid
    | inl (inl (inl (inl (inr mut)))) =>
        EncodeMutability mut
    | inl (inl (inl (inr lit))) =>
        EncodeLit lit
    | inl (inl (inr op)) =>
        EncodeUnop op
    | inl (inr op) =>
        EncodeBinop op
    | inr pat =>
        EncodePattern pat
    end.
  refine (inj_countable' encode decode _). intros []; done.
Qed.
Notation EncodeString str := (
  EncodeBinder (BNamed str)
).
#[global] Instance expr_countable :
  Countable expr.
Proof.
  #[local] Notation code_Val :=
    0.
  #[local] Notation code_Rec :=
    1.
  #[local] Notation code_App :=
    2.
  #[local] Notation code_Let :=
    3.
  #[local] Notation code_Unop :=
    4.
  #[local] Notation code_Binop :=
    5.
  #[local] Notation code_Equal :=
    6.
  #[local] Notation code_If :=
    7.
  #[local] Notation code_For :=
    8.
  #[local] Notation code_Alloc :=
    9.
  #[local] Notation code_Block :=
    10.
  #[local] Notation code_Reveal :=
    11.
  #[local] Notation code_Match :=
    12.
  #[local] Notation code_branch :=
    13.
  #[local] Notation code_GetTag :=
    14.
  #[local] Notation code_GetSize :=
    15.
  #[local] Notation code_Load :=
    16.
  #[local] Notation code_Store :=
    17.
  #[local] Notation code_Xchg :=
    18.
  #[local] Notation code_CAS :=
    19.
  #[local] Notation code_FAA :=
    20.
  #[local] Notation code_Fork :=
    21.
  #[local] Notation code_Proph :=
    22.
  #[local] Notation code_Resolve :=
    23.
  #[local] Notation code_ValRecs :=
    0.
  #[local] Notation code_recursive :=
    1.
  #[local] Notation code_ValBlock :=
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
      | App e1 e2 =>
          GenNode code_App [go e1; go e2]
      | Let x e1 e2 =>
          GenNode code_Let [GenLeaf (EncodeBinder x); go e1; go e2]
      | Unop op e =>
          GenNode code_Unop [GenLeaf (EncodeUnop op); go e]
      | Binop op e1 e2 =>
          GenNode code_Binop [GenLeaf (EncodeBinop op); go e1; go e2]
      | Equal e1 e2 =>
          GenNode code_Equal [go e1; go e2]
      | If e0 e1 e2 =>
          GenNode code_If [go e0; go e1; go e2]
      | For e1 e2 e3 =>
          GenNode code_For [go e1; go e2; go e3]
      | Alloc e1 e2 =>
          GenNode code_Alloc [go e1; go e2]
      | Block mut tag es =>
          GenNode code_Block $ GenLeaf (EncodeMutability mut) :: GenLeaf (EncodeNat tag) :: go_list es
      | Reveal e =>
          GenNode code_Reveal [go e]
      | Match e0 x e1 brs =>
          GenNode code_Match $ go e0 :: GenLeaf (EncodeBinder x) :: go e1 :: go_branches brs
      | GetTag e =>
          GenNode code_GetTag [go e]
      | GetSize e =>
          GenNode code_GetSize [go e]
      | Load e1 e2 =>
          GenNode code_Load [go e1; go e2]
      | Store e1 e2 e3 =>
          GenNode code_Store [go e1; go e2; go e3]
      | Xchg e1 e2 =>
          GenNode code_Xchg [go e1; go e2]
      | CAS e0 e1 e2 =>
          GenNode code_CAS [go e0; go e1; go e2]
      | FAA e1 e2 =>
          GenNode code_FAA [go e1; go e2]
      | Fork e =>
          GenNode code_Fork [go e]
      | Proph =>
          GenNode code_Proph []
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
      | ValBlock bid tag vs =>
          GenNode code_ValBlock $ GenLeaf (EncodeBlockId bid) :: GenLeaf (EncodeNat tag) :: go_list vs
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
            (@inhabitant _ pattern_inhabited, Unit)
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
      | GenNode code_App [e1; e2] =>
          App (go e1) (go e2)
      | GenNode code_Let [GenLeaf (EncodeBinder x); e1; e2] =>
          Let x (go e1) (go e2)
      | GenNode code_Unop [GenLeaf (EncodeUnop op); e] =>
          Unop op $ go e
      | GenNode code_Binop [GenLeaf (EncodeBinop op); e1; e2] =>
          Binop op (go e1) (go e2)
      | GenNode code_Equal [e1; e2] =>
          Equal (go e1) (go e2)
      | GenNode code_If [e0; e1; e2] =>
          If (go e0) (go e1) (go e2)
      | GenNode code_For [e1; e2; e3] =>
          For (go e1) (go e2) (go e3)
      | GenNode code_Alloc [e1; e2] =>
          Alloc (go e1) (go e2)
      | GenNode code_Block (GenLeaf (EncodeMutability mut) :: GenLeaf (EncodeNat tag) :: es) =>
          Block mut tag $ go_list es
      | GenNode code_Reveal [e] =>
          Reveal (go e)
      | GenNode code_Match (e0 :: GenLeaf (EncodeBinder x) :: e1 :: brs) =>
          Match (go e0) x (go e1) (go_branches brs)
      | GenNode code_GetTag [e] =>
          GetTag (go e)
      | GenNode code_GetSize [e] =>
          GetSize (go e)
      | GenNode code_Load [e1; e2] =>
          Load (go e1) (go e2)
      | GenNode code_Store [e1; e2; e3] =>
          Store (go e1) (go e2) (go e3)
      | GenNode code_Xchg [e1; e2] =>
          Xchg (go e1) (go e2)
      | GenNode code_CAS [e0; e1; e2] =>
          CAS (go e0) (go e1) (go e2)
      | GenNode code_FAA [e1; e2] =>
          FAA (go e1) (go e2)
      | GenNode code_Fork [e] =>
          Fork $ go e
      | GenNode code_Proph [] =>
          Proph
      | GenNode code_Resolve [e0; e1; e2] =>
          Resolve (go e0) (go e1) (go e2)
      | _ =>
          @inhabitant _ expr_inhabited
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
      | GenNode code_ValBlock (GenLeaf (EncodeBlockId bid) :: GenLeaf (EncodeNat tag) :: vs) =>
          ValBlock bid tag $ go_list vs
      | _ =>
          @inhabitant _ val_inhabited
      end
    for go.
  refine (inj_countable' encode decode _).
  refine (fix go e := _ with go_val v := _ for go).
  - destruct e; simpl; f_equal; try done.
    + match goal with |- _ = ?v =>
        exact (go_val v)
      end.
    + match goal with |- _ = ?es =>
        rewrite /map; induction es as [| ? ? ->] => /=; f_equal; done
      end.
    + induction brs as [| (? & ?) ?] => //=. repeat f_equal; done.
  - destruct v; simpl; f_equal; try done.
    + induction recs as [| ((? & ?) & ?) ?] => //=. repeat f_equal; done.
    + match goal with |- _ = ?vs =>
        rewrite /map; induction vs as [| ? ? ->]; simpl; f_equal; done
      end.
Qed.
#[global] Instance val_countable :
  Countable val.
Proof.
  refine (inj_countable of_val to_val _); auto using to_of_val.
Qed.
