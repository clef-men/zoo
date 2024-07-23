From stdpp Require Import
  countable.
From stdpp Require Export
  binders.

From iris.algebra Require Import
  ofe.

From zoo Require Import
  prelude.
From zoo.language Require Export
  location.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types i tag proj : nat.
Implicit Types n : Z.
Implicit Types l : location.
Implicit Types f x : binder.

Definition prophet_id :=
  positive.
Implicit Types pid : prophet_id.

Definition constr_id :=
  positive.
Implicit Types cid : option constr_id.

Inductive literal :=
  | LiteralBool b
  | LiteralInt n
  | LiteralLoc l
  | LiteralProphecy pid
  | LiteralPoison.
Implicit Types lit : literal.

#[global] Instance literal_eq_dec : EqDecision literal :=
  ltac:(solve_decision).
#[global] Instance literal_countable :
  Countable literal.
Proof.
  pose encode lit :=
    match lit with
    | LiteralBool b =>
        inl $ inl $ inl $ inl b
    | LiteralInt n =>
        inl $ inl $ inl $ inr n
    | LiteralLoc l =>
        inl $ inl $ inr l
    | LiteralProphecy pid =>
        inl $ inr pid
    | LiteralPoison =>
        inr ()
    end.
  pose decode _lit :=
    match _lit with
    | inl (inl (inl (inl b))) =>
        LiteralBool b
    | inl (inl (inl (inr n))) =>
        LiteralInt n
    | inl (inl (inr l)) =>
        LiteralLoc l
    | inl (inr p) =>
        LiteralProphecy p
    | inr () =>
        LiteralPoison
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
  | BinopLe | BinopLt | BinopGe | BinopGt
  | BinopOffset.

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
    | BinopLe => 5
    | BinopLt => 6
    | BinopGe => 7
    | BinopGt => 8
    | BinopOffset => 9
  end.
  pose decode op :=
    match op with
    | 0 => BinopPlus
    | 1 => BinopMinus
    | 2 => BinopMult
    | 3 => BinopQuot
    | 4 => BinopRem
    | 5 => BinopLe
    | 6 => BinopLt
    | 7 => BinopGe
    | 8 => BinopGt
    | _ => BinopOffset
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
  pose encode pat := (
    pat.(pattern_tag),
    pat.(pattern_fields),
    pat.(pattern_as)
  ).
  pose decode := λ '(tag, fields, as_), {|
    pattern_tag := tag ;
    pattern_fields := fields ;
    pattern_as := as_ ;
  |}.
  refine (inj_countable' encode decode _); intros []. done.
Qed.

Unset Elimination Schemes.
Inductive expr :=
  | Val (v : val)
  | Var (x : string)
  | Rec f x (e : expr)
  | App (e1 e2 : expr)
  | Unop (op : unop) (e : expr)
  | Binop (op : binop) (e1 e2 : expr)
  | Equal (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  | Constr tag (es : list expr)
  | Proj proj (e : expr)
  | Match (e0 : expr) x (e1 : expr) (brs : list (pattern * expr))
  | Reveal (e : expr)
  | For (e1 e2 e3 : expr)
  | Record (es : list expr)
  | Alloc (e1 e2 : expr)
  | Load (e : expr)
  | Store (e1 e2 : expr)
  | Xchg (e1 e2 : expr)
  | Cas (e0 e1 e2 : expr)
  | Faa (e1 e2 : expr)
  | Fork (e : expr)
  | Yield
  | Proph
  | Resolve (e0 e1 e2 : expr)
with val :=
  | ValLiteral lit
  | ValRec f x (e : expr)
  | ValConstr cid tag (vs : list val).
Set Elimination Schemes.
Implicit Types e : expr.
Implicit Types es : list expr.
Implicit Types v : val.
Implicit Types vs : list val.

Notation branch :=
  (pattern * expr)%type.
Implicit Types br : branch.
Implicit Types brs : list branch.

Section val_ind.
  Variable P : val → Prop.

  Variable HValLiteral :
    ∀ lit,
    P (ValLiteral lit).
  Variable HValRec :
    ∀ f x e,
    P (ValRec f x e).
  Variable HValConstr :
    ∀ cid tag,
    ∀ vs, Forall P vs →
    P (ValConstr cid tag vs).

  Fixpoint val_ind v :=
    match v with
    | ValLiteral lit =>
        HValLiteral lit
    | ValRec f x e =>
        HValRec f x e
    | ValConstr cid tag vs =>
        HValConstr cid tag
          vs (Forall_true P vs val_ind)
    end.
End val_ind.

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
  Variable HConstr :
    ∀ tag,
    ∀ es, Forall P es →
    P (Constr tag es).
  Variable HProj :
    ∀ proj,
    ∀ e, P e →
    P (Proj proj e).
  Variable HMatch :
    ∀ e0, P e0 →
    ∀ x,
    ∀ e1, P e1 →
    ∀ brs, Forall (λ br, P br.2) brs →
    P (Match e0 x e1 brs).
  Variable HReveal :
    ∀ e, P e →
    P (Reveal e).
  Variable HFor :
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    ∀ e3, P e3 →
    P (For e1 e2 e3).
  Variable HRecord :
    ∀ es, Forall P es →
    P (Record es).
  Variable HAlloc :
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    P (Alloc e1 e2).
  Variable HLoad :
    ∀ e, P e →
    P (Load e).
  Variable HStore :
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    P (Store e1 e2).
  Variable HXchg :
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    P (Xchg e1 e2).
  Variable HCas :
    ∀ e0, P e0 →
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    P (Cas e0 e1 e2).
  Variable HFaa :
    ∀ e1, P e1 →
    ∀ e2, P e2 →
    P (Faa e1 e2).
  Variable HFork :
    ∀ e, P e →
    P (Fork e).
  Variable HYield :
    P Yield.
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
    | Constr tag es =>
        HConstr
          tag
          es (Forall_true P es expr_ind)
    | Proj proj e =>
        HProj
          proj
          e (expr_ind e)
    | Match e0 x e1 brs =>
        HMatch
          e0 (expr_ind e0)
          x
          e1 (expr_ind e1)
          brs (Forall_true (λ br, P br.2) brs (λ br, expr_ind br.2))
    | Reveal e =>
        HReveal
          e (expr_ind e)
    | For e1 e2 e3 =>
        HFor
          e1 (expr_ind e1)
          e2 (expr_ind e2)
          e3 (expr_ind e3)
    | Record es =>
        HRecord
          es (Forall_true P es expr_ind)
    | Alloc e1 e2 =>
        HAlloc
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    | Load e =>
        HLoad
          e (expr_ind e)
    | Store e1 e2 =>
        HStore
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    | Xchg e1 e2 =>
        HXchg
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    | Cas e0 e1 e2 =>
        HCas
          e0 (expr_ind e0)
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    | Faa e1 e2 =>
        HFaa
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    | Fork e =>
        HFork
          e (expr_ind e)
    | Yield =>
        HYield
    | Proph =>
        HProph
    | Resolve e0 e1 e2 =>
        HResolve
          e0 (expr_ind e0)
          e1 (expr_ind e1)
          e2 (expr_ind e2)
    end.
End expr_ind.

Canonical valO :=
  leibnizO val.
Canonical exprO :=
  leibnizO expr.

Notation ValBool b := (
  ValLiteral (LiteralBool b)
)(only parsing
).
Notation ValInt n := (
  ValLiteral (LiteralInt n)
)(only parsing
).
Notation ValLoc l := (
  ValLiteral (LiteralLoc l)
)(only parsing
).
Notation ValProphecy pid := (
  ValLiteral (LiteralProphecy pid)
)(only parsing
).

Notation Tuple := (
  Constr None 0
)(only parsing
).
Notation ValTuple := (
  ValConstr None 0
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

Notation Lam x e := (
  Rec BAnon x e
)(only parsing
).
Notation ValLam x e := (
  ValRec BAnon x e
)(only parsing
).

Notation Let x e1 e2 := (
  App (Lam x e2) e1
)(only parsing
).

Notation Seq e1 e2 := (
  Let BAnon e1 e2
)(only parsing
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
Lemma of_vals_length vs :
  length (of_vals vs) = length vs.
Proof.
  rewrite map_length //.
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
      | Constr tag1 es1, Constr tag2 es2 =>
          cast_if_and
            (decide (tag1 = tag2))
            (decide (es1 = es2))
      | Proj proj1 e1, Proj proj2 e2 =>
          cast_if_and
            (decide (proj1 = proj2))
            (decide (e1 = e2))
      | Match e10 x1 e11 brs1, Match e20 x2 e21 brs2 =>
          cast_if_and4
            (decide (e10 = e20))
            (decide (x1 = x2))
            (decide (e11 = e21))
            (decide (brs1 = brs2))
      | Reveal e1, Reveal e2 =>
          cast_if
            (decide (e1 = e2))
      | For e11 e12 e13, For e21 e22 e23 =>
          cast_if_and3
            (decide (e11 = e21))
            (decide (e12 = e22))
            (decide (e13 = e23))
      | Record es1, Record es2 =>
          cast_if
            (decide (es1 = es2))
      | Alloc e11 e12, Alloc e21 e22 =>
         cast_if_and
           (decide (e11 = e21))
           (decide (e12 = e22))
      | Load e1, Load e2 =>
          cast_if
            (decide (e1 = e2))
      | Store e11 e12, Store e21 e22 =>
         cast_if_and
           (decide (e11 = e21))
           (decide (e12 = e22))
      | Xchg e11 e12, Xchg e21 e22 =>
          cast_if_and
            (decide (e11 = e21))
            (decide (e12 = e22))
      | Cas e10 e11 e12, Cas e20 e21 e22 =>
         cast_if_and3
           (decide (e10 = e20))
           (decide (e11 = e21))
           (decide (e12 = e22))
      | Faa e11 e12, Faa e21 e22 =>
         cast_if_and
           (decide (e11 = e21))
           (decide (e12 = e22))
      | Fork e1, Fork e2 =>
          cast_if
            (decide (e1 = e2))
      | Yield, Yield =>
          left _
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
      | ValLiteral l1, ValLiteral l2 =>
          cast_if
            (decide (l1 = l2))
      | ValRec f1 x1 e1, ValRec f2 x2 e2 =>
          cast_if_and3
            (decide (f1 = f2))
            (decide (x1 = x2))
            (decide (e1 = e2))
      | ValConstr cid1 tag1 es1, ValConstr cid2 tag2 es2 =>
          cast_if_and3
            (decide (cid1 = cid2))
            (decide (tag1 = tag2))
            (decide (es1 = es2))
      | _, _ =>
          right _
      end
    for go
  );
  try clear go_branches; clear go go_val go_list;
  abstract intuition congruence.
Defined.
#[global] Instance val_eq_dec : EqDecision val.
Proof.
  unshelve refine (
    fix go_val v1 v2 : Decision (v1 = v2) :=
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
      | ValLiteral l1, ValLiteral l2 =>
          cast_if
            (decide (l1 = l2))
      | ValRec f1 x1 e1, ValRec f2 x2 e2 =>
          cast_if_and3
            (decide (f1 = f2))
            (decide (x1 = x2))
            (decide (e1 = e2))
      | ValConstr cid1 tag1 es1, ValConstr cid2 tag2 es2 =>
          cast_if_and3
            (decide (cid1 = cid2))
            (decide (tag1 = tag2))
            (decide (es1 = es2))
      | _, _ =>
          right _
      end
  );
  clear go_val go_list; abstract intuition congruence.
Defined.
Variant encode_leaf :=
  | EncodeBinder x
  | EncodeUnop (op : unop)
  | EncodeBinop (op : binop)
  | EncodeProjection proj
  | EncodeConstrId cid
  | EncodeConstrTag tag
  | EncodePattern (pat : pattern)
  | EncodeLiteral lit.
#[local] Instance encode_leaf_eq_dec : EqDecision encode_leaf :=
  ltac:(solve_decision).
#[local] Instance encode_leaf_countable :
  Countable encode_leaf.
Proof.
  pose encode leaf :=
    match leaf with
    | EncodeBinder x =>
        inl $ inl $ inl $ inl $ inl $ inl $ inl x
    | EncodeUnop op =>
        inl $ inl $ inl $ inl $ inl $ inl $ inr op
    | EncodeBinop op =>
        inl $ inl $ inl $ inl $ inl $ inr op
    | EncodeProjection proj =>
        inl $ inl $ inl $ inl $ inr proj
    | EncodeConstrId cid =>
        inl $ inl $ inl $ inr cid
    | EncodeConstrTag tag =>
        inl $ inl $ inr tag
    | EncodePattern pat =>
        inl $ inr pat
    | EncodeLiteral lit =>
        inr lit
    end.
  pose decode leaf :=
    match leaf with
    | inl (inl (inl (inl (inl (inl (inl x)))))) =>
        EncodeBinder x
    | inl (inl (inl (inl (inl (inl (inr op)))))) =>
        EncodeUnop op
    | inl (inl (inl (inl (inl (inr op))))) =>
        EncodeBinop op
    | inl (inl (inl (inl (inr proj)))) =>
        EncodeProjection proj
    | inl (inl (inl (inr cid))) =>
        EncodeConstrId cid
    | inl (inl (inr tag)) =>
        EncodeConstrTag tag
    | inl (inr pat) =>
        EncodePattern pat
    | inr lit =>
        EncodeLiteral lit
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
  #[local] Notation code_Unop :=
    3.
  #[local] Notation code_Binop :=
    4.
  #[local] Notation code_Equal :=
    5.
  #[local] Notation code_If :=
    6.
  #[local] Notation code_Constr :=
    7.
  #[local] Notation code_Proj :=
    8.
  #[local] Notation code_Match :=
    9.
  #[local] Notation code_Reveal :=
    10.
  #[local] Notation code_For :=
    11.
  #[local] Notation code_branch :=
    12.
  #[local] Notation code_Record :=
    13.
  #[local] Notation code_Alloc :=
    14.
  #[local] Notation code_Load :=
    15.
  #[local] Notation code_Store :=
    16.
  #[local] Notation code_Xchg :=
    17.
  #[local] Notation code_Cas :=
    18.
  #[local] Notation code_Faa :=
    19.
  #[local] Notation code_Fork :=
    20.
  #[local] Notation code_Yield :=
    21.
  #[local] Notation code_Proph :=
    22.
  #[local] Notation code_Resolve :=
    23.
  #[local] Notation code_ValRec :=
    0.
  #[local] Notation code_ValConstr :=
    1.
  pose encode :=
    fix go e :=
      let go_list := map go in
      let go_branch '(pat, e) :=
        GenNode code_branch [GenLeaf (EncodePattern pat); go e]
      in
      let go_branches := map go_branch in
      match e with
      | Val v =>
          GenNode code_Val [go_val v]
      | Var x =>
          GenLeaf (EncodeString x)
      | Rec f x e =>
          GenNode code_Rec [GenLeaf (EncodeBinder f); GenLeaf (EncodeBinder x); go e]
      | App e1 e2 =>
          GenNode code_App [go e1; go e2]
      | Unop op e =>
          GenNode code_Unop [GenLeaf (EncodeUnop op); go e]
      | Binop op e1 e2 =>
          GenNode code_Binop [GenLeaf (EncodeBinop op); go e1; go e2]
      | Equal e1 e2 =>
          GenNode code_Equal [go e1; go e2]
      | If e0 e1 e2 =>
          GenNode code_If [go e0; go e1; go e2]
      | Constr tag es =>
          GenNode code_Constr $ GenLeaf (EncodeConstrTag tag) :: go_list es
      | Proj proj e =>
          GenNode code_Proj [GenLeaf (EncodeProjection proj); go e]
      | Match e0 x e1 brs =>
          GenNode code_Match $ go e0 :: GenLeaf (EncodeBinder x) :: go e1 :: go_branches brs
      | Reveal e =>
          GenNode code_Reveal [go e]
      | For e1 e2 e3 =>
          GenNode code_For [go e1; go e2; go e3]
      | Record es =>
          GenNode code_Record $ go_list es
      | Alloc e1 e2 =>
          GenNode code_Alloc [go e1; go e2]
      | Load e =>
          GenNode code_Load [go e]
      | Store e1 e2 =>
          GenNode code_Store [go e1; go e2]
      | Xchg e1 e2 =>
          GenNode code_Xchg [go e1; go e2]
      | Cas e0 e1 e2 =>
          GenNode code_Cas [go e0; go e1; go e2]
      | Faa e1 e2 =>
          GenNode code_Faa [go e1; go e2]
      | Fork e =>
          GenNode code_Fork [go e]
      | Yield =>
          GenNode code_Yield []
      | Proph =>
          GenNode code_Proph []
      | Resolve e0 e1 e2 =>
          GenNode code_Resolve [go e0; go e1; go e2]
      end
    with go_val v :=
      let go_list := map go_val in
      match v with
      | ValLiteral lit =>
          GenLeaf (EncodeLiteral lit)
      | ValRec f x e =>
         GenNode code_ValRec [GenLeaf (EncodeBinder f); GenLeaf (EncodeBinder x); go e]
      | ValConstr cid tag vs =>
          GenNode code_ValConstr $ GenLeaf (EncodeConstrId cid) :: GenLeaf (EncodeConstrTag tag) :: go_list vs
      end
    for go.
  pose decode :=
    fix go _e :=
      let go_list := map go in
      let go_branch _br :=
        match _br with
        | GenNode code_branch [GenLeaf (EncodePattern pat); e] =>
            (pat, go e)
        | _ =>
            (@inhabitant _ pattern_inhabited, Unit)
        end
      in
      let go_branches := map go_branch in
      match _e with
      | GenNode code_Val [v] =>
          Val $ go_val v
      | GenLeaf (EncodeString x) =>
          Var x
      | GenNode code_Rec [GenLeaf (EncodeBinder f); GenLeaf (EncodeBinder x); e] =>
          Rec f x $ go e
      | GenNode code_App [e1; e2] =>
          App (go e1) (go e2)
      | GenNode code_Unop [GenLeaf (EncodeUnop op); e] =>
          Unop op $ go e
      | GenNode code_Binop [GenLeaf (EncodeBinop op); e1; e2] =>
          Binop op (go e1) (go e2)
      | GenNode code_Equal [e1; e2] =>
          Equal (go e1) (go e2)
      | GenNode code_If [e0; e1; e2] =>
          If (go e0) (go e1) (go e2)
      | GenNode code_Constr (GenLeaf (EncodeConstrTag tag) :: es) =>
          Constr tag $ go_list es
      | GenNode code_Proj [GenLeaf (EncodeProjection proj); e] =>
          Proj proj $ go e
      | GenNode code_Match (e0 :: GenLeaf (EncodeBinder x) :: e1 :: brs) =>
          Match (go e0) x (go e1) (go_branches brs)
      | GenNode code_Reveal [e] =>
          Reveal (go e)
      | GenNode code_For [e1; e2; e3] =>
          For (go e1) (go e2) (go e3)
      | GenNode code_Record es =>
          Record $ go_list es
      | GenNode code_Alloc [e1; e2] =>
          Alloc (go e1) (go e2)
      | GenNode code_Load [e] =>
          Load $ go e
      | GenNode code_Store [e1; e2] =>
          Store (go e1) (go e2)
      | GenNode code_Xchg [e1; e2] =>
          Xchg (go e1) (go e2)
      | GenNode code_Cas [e0; e1; e2] =>
          Cas (go e0) (go e1) (go e2)
      | GenNode code_Faa [e1; e2] =>
          Faa (go e1) (go e2)
      | GenNode code_Fork [e] =>
          Fork $ go e
      | GenNode code_Yield [] =>
          Yield
      | GenNode code_Proph [] =>
          Proph
      | GenNode code_Resolve [e0; e1; e2] =>
          Resolve (go e0) (go e1) (go e2)
      | _ =>
          @inhabitant _ expr_inhabited
      end
    with go_val _v :=
      let go_list := map go_val in
      match _v with
      | GenLeaf (EncodeLiteral lit) =>
          ValLiteral lit
      | GenNode code_ValRec [GenLeaf (EncodeBinder f); GenLeaf (EncodeBinder x); e] =>
          ValRec f x (go e)
      | GenNode code_ValConstr (GenLeaf (EncodeConstrId cid) :: GenLeaf (EncodeConstrTag tag) :: vs) =>
          ValConstr cid tag $ go_list vs
      | _ =>
          @inhabitant _ val_inhabited
      end
    for go.
  refine (inj_countable' encode decode _).
  refine (fix go e := _ with go_val v := _ for go).
  - destruct e; simpl; f_equal; try done.
    1:
      match goal with |- _ = ?v =>
        exact (go_val v)
      end.
    all:
      try match goal with |- _ = ?es =>
        rewrite /map; induction es as [| ? ? ->] => /=; f_equal; done
      end.
    induction brs as [| (? & ?) ?] => //=. repeat f_equal; done.
  - destruct v; simpl; f_equal; try done.
    all:
      match goal with |- _ = ?vs =>
        rewrite /map; induction vs as [| ? ? ->]; simpl; f_equal; done
      end.
Qed.
#[global] Instance val_countable :
  Countable val.
Proof.
  refine (inj_countable of_val to_val _); auto using to_of_val.
Qed.
