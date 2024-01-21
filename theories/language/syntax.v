From stdpp Require Import
  countable.
From stdpp Require Export
  binders.

From iris.algebra Require Import
  ofe.

From zebre Require Import
  prelude.
From zebre.language Require Export
  loc.
From zebre Require Import
  options.

Implicit Types b : bool.
Implicit Types n : Z.
Implicit Types l : loc.
Implicit Types f x : binder.

Definition prophecy_id :=
  positive.
Implicit Types p : prophecy_id.

Inductive literal :=
  | LiteralUnit
  | LiteralBool b
  | LiteralInt n
  | LiteralLoc l
  | LiteralProphecy p
  | LiteralPoison.
Implicit Types lit : literal.

#[global] Instance literal_eq_dec : EqDecision literal :=
  ltac:(solve_decision).
#[global] Instance literal_countable :
  Countable literal.
Proof.
  pose encode lit :=
    match lit with
    | LiteralUnit =>
        (inr (inl false), None)
    | LiteralBool b =>
        (inl (inr b), None)
    | LiteralInt n =>
        (inl (inl n), None)
    | LiteralLoc l =>
        (inr (inr l), None)
    | LiteralProphecy p =>
        (inr (inl false), Some p)
    | LiteralPoison =>
        (inr (inl true), None)
    end.
  pose decode _lit :=
    match _lit with
    | (inr (inl false), None) =>
        LiteralUnit
    | (inl (inr b), None) =>
        LiteralBool b
    | (inl (inl n), None) =>
        LiteralInt n
    | (inr (inr l), None) =>
        LiteralLoc l
    | (_, Some p) =>
        LiteralProphecy p
    | (inr (inl true), None) =>
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
    | UnopNeg => 0
    | UnopMinus => 1
    end.
  pose decode op :=
    match op with
    | 0 => UnopNeg
    | _ => UnopMinus
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

Inductive expr :=
  | Val (v : val)
  | Var (x : string)
  | Rec f x (e : expr)
  | App (e1 e2 : expr)
  | Unop (op : unop) (e : expr)
  | Binop (op : binop) (e1 e2 : expr)
  | Equal (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  | Constr b (e : expr)
  | Case (e0 e1 e2 : expr)
  | Alloc (e1 e2 : expr)
  | Load (e : expr)
  | Store (e1 e2 : expr)
  | Xchg (e1 e2 : expr)
  | Cas (e0 e1 e2 : expr)
  | Faa (e1 e2 : expr)
  | Fork (e : expr)
  | Proph
  | Resolve (e0 e1 e2 : expr)
with val :=
  | ValLiteral lit
  | ValRec f x (e : expr)
  | ValPair (v1 v2 : val)
  | ValConstr b (v : val).
Implicit Types e : expr.
Implicit Types v : val.

Canonical valO :=
  leibnizO val.
Canonical exprO :=
  leibnizO expr.

Notation Injl := (
  Constr true
).
Notation Injr := (
  Constr false
).
Definition ValInjl := (
  ValConstr true
).
Definition ValInjr := (
  ValConstr false
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

#[global] Instance val_inhabited : Inhabited val :=
  populate (ValLiteral LiteralUnit).
#[global] Instance expr_inhabited : Inhabited expr :=
  populate (Val inhabitant).
#[global] Instance expr_eq_dec : EqDecision expr.
Proof.
  refine (
    fix go e1 e2 : Decision (e1 = e2) :=
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
      | Pair e11 e12, Pair e21 e22 =>
         cast_if_and
           (decide (e11 = e21))
           (decide (e12 = e22))
      | Fst e1, Fst e2 =>
          cast_if
            (decide (e1 = e2))
      | Snd e1, Snd e2 =>
          cast_if
            (decide (e1 = e2))
      | Constr b1 e1, Constr b2 e2 =>
          cast_if_and
            (decide (b1 = b2))
            (decide (e1 = e2))
      | Case e10 e11 e12, Case e20 e21 e22 =>
          cast_if_and3
            (decide (e10 = e20))
            (decide (e11 = e21))
            (decide (e12 = e22))
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
    with gov v1 v2 : Decision (v1 = v2) :=
      match v1, v2 with
      | ValLiteral l1, ValLiteral l2 =>
          cast_if
            (decide (l1 = l2))
      | ValRec f1 x1 e1, ValRec f2 x2 e2 =>
          cast_if_and3
            (decide (f1 = f2))
            (decide (x1 = x2))
            (decide (e1 = e2))
      | ValPair e11 e12, ValPair e21 e22 =>
          cast_if_and
            (decide (e11 = e21))
            (decide (e12 = e22))
      | ValConstr b1 e1, ValConstr b2 e2 =>
          cast_if_and
            (decide (b1 = b2))
            (decide (e1 = e2))
      | _, _ =>
          right _
      end
    for go
  );
  clear go gov; abstract intuition congruence.
Defined.
#[global] Instance val_eq_dec : EqDecision val :=
  ltac:(solve_decision).
Variant encode_leaf :=
  | EncodeString (x : string)
  | EncodeBinder x
  | EncodeUnop (op : unop)
  | EncodeBinop (op : binop)
  | EncodeBool b
  | EncodeLiteral lit.
#[local] Instance encode_leaf_eq_dec : EqDecision encode_leaf :=
  ltac:(solve_decision).
#[local] Instance encode_leaf_countable :
  Countable encode_leaf.
Proof.
  pose encode leaf :=
    match leaf with
    | EncodeString x =>
        inl $ inl $ inl $ inl $ inl x
    | EncodeBinder x =>
        inl $ inl $ inl $ inl $ inr x
    | EncodeUnop op =>
        inl $ inl $ inl $ inr op
    | EncodeBinop op =>
        inl $ inl $ inr op
    | EncodeBool b =>
        inl $ inr b
    | EncodeLiteral lit =>
        inr lit
    end.
  pose decode leaf :=
    match leaf with
    | inl (inl (inl (inl (inl x)))) =>
        EncodeString x
    | inl (inl (inl (inl (inr x)))) =>
        EncodeBinder x
    | inl (inl (inl (inr op))) =>
        EncodeUnop op
    | inl (inl (inr op)) =>
        EncodeBinop op
    | inl (inr b) =>
        EncodeBool b
    | inr lit =>
        EncodeLiteral lit
    end.
  refine (inj_countable' encode decode _); intros []; done.
Qed.
#[global] Instance expr_countable :
  Countable expr.
Proof.
  Notation tag_Val :=
    0.
  Notation tag_Rec :=
    1.
  Notation tag_App :=
    2.
  Notation tag_Unop :=
    3.
  Notation tag_Binop :=
    4.
  Notation tag_Equal :=
    5.
  Notation tag_If :=
    6.
  Notation tag_Pair :=
    7.
  Notation tag_Fst :=
    8.
  Notation tag_Snd :=
    9.
  Notation tag_Constr :=
    10.
  Notation tag_Case :=
    11.
  Notation tag_Alloc :=
    12.
  Notation tag_Load :=
    13.
  Notation tag_Store :=
    14.
  Notation tag_Xchg :=
    15.
  Notation tag_Cas :=
    16.
  Notation tag_Faa :=
    17.
  Notation tag_Fork :=
    18.
  Notation tag_Proph :=
    19.
  Notation tag_Resolve :=
    20.
  Notation tag_ValRec :=
    0.
  Notation tag_ValPair :=
    1.
  Notation tag_ValConstr :=
    2.
  pose encode :=
    fix go e :=
      match e with
      | Val v =>
          GenNode tag_Val [val_go v]
      | Var x =>
          GenLeaf (EncodeString x)
      | Rec f x e =>
          GenNode tag_Rec [GenLeaf (EncodeBinder f); GenLeaf (EncodeBinder x); go e]
      | App e1 e2 =>
          GenNode tag_App [go e1; go e2]
      | Unop op e =>
          GenNode tag_Unop [GenLeaf (EncodeUnop op); go e]
      | Binop op e1 e2 =>
          GenNode tag_Binop [GenLeaf (EncodeBinop op); go e1; go e2]
      | Equal e1 e2 =>
          GenNode tag_Equal [go e1; go e2]
      | If e0 e1 e2 =>
          GenNode tag_If [go e0; go e1; go e2]
      | Pair e1 e2 =>
          GenNode tag_Pair [go e1; go e2]
      | Fst e =>
          GenNode tag_Fst [go e]
      | Snd e =>
          GenNode tag_Snd [go e]
      | Constr b e =>
          GenNode tag_Constr [GenLeaf (EncodeBool b); go e]
      | Case e0 e1 e2 =>
          GenNode tag_Case [go e0; go e1; go e2]
      | Alloc e1 e2 =>
          GenNode tag_Alloc [go e1; go e2]
      | Load e =>
          GenNode tag_Load [go e]
      | Store e1 e2 =>
          GenNode tag_Store [go e1; go e2]
      | Xchg e1 e2 =>
          GenNode tag_Xchg [go e1; go e2]
      | Cas e0 e1 e2 =>
          GenNode tag_Cas [go e0; go e1; go e2]
      | Faa e1 e2 =>
          GenNode tag_Faa [go e1; go e2]
      | Fork e =>
          GenNode tag_Fork [go e]
      | Proph =>
          GenNode tag_Proph []
      | Resolve e0 e1 e2 =>
          GenNode tag_Resolve [go e0; go e1; go e2]
      end
    with val_go v :=
      match v with
      | ValLiteral lit =>
          GenLeaf (EncodeLiteral lit)
      | ValRec f x e =>
         GenNode tag_ValRec [GenLeaf (EncodeBinder f); GenLeaf (EncodeBinder x); go e]
      | ValPair v1 v2 =>
          GenNode tag_ValPair [val_go v1; val_go v2]
      | ValConstr b v =>
          GenNode tag_ValConstr [GenLeaf (EncodeBool b); val_go v]
      end
    for go.
  pose decode :=
    fix go _e :=
      match _e with
      | GenNode tag_Val [v] =>
          Val (val_go v)
      | GenLeaf (EncodeString x) =>
          Var x
      | GenNode tag_Rec [GenLeaf (EncodeBinder f); GenLeaf (EncodeBinder x); e] =>
          Rec f x (go e)
      | GenNode tag_App [e1; e2] =>
          App (go e1) (go e2)
      | GenNode tag_Unop [GenLeaf (EncodeUnop op); e] =>
          Unop op (go e)
      | GenNode tag_Binop [GenLeaf (EncodeBinop op); e1; e2] =>
          Binop op (go e1) (go e2)
      | GenNode tag_Equal [e1; e2] =>
          Equal (go e1) (go e2)
      | GenNode tag_If [e0; e1; e2] =>
          If (go e0) (go e1) (go e2)
      | GenNode tag_Pair [e1; e2] =>
          Pair (go e1) (go e2)
      | GenNode tag_Fst [e] =>
          Fst (go e)
      | GenNode tag_Snd [e] =>
          Snd (go e)
      | GenNode tag_Constr [GenLeaf (EncodeBool b); e] =>
          Constr b (go e)
      | GenNode tag_Case [e0; e1; e2] =>
          Case (go e0) (go e1) (go e2)
      | GenNode tag_Alloc [e1; e2] =>
          Alloc (go e1) (go e2)
      | GenNode tag_Load [e] =>
          Load (go e)
      | GenNode tag_Store [e1; e2] =>
          Store (go e1) (go e2)
      | GenNode tag_Xchg [e1; e2] =>
          Xchg (go e1) (go e2)
      | GenNode tag_Cas [e0; e1; e2] =>
          Cas (go e0) (go e1) (go e2)
      | GenNode tag_Faa [e1; e2] =>
          Faa (go e1) (go e2)
      | GenNode tag_Fork [e] =>
          Fork (go e)
      | GenNode tag_Proph [] =>
          Proph
      | GenNode tag_Resolve [e0; e1; e2] =>
          Resolve (go e0) (go e1) (go e2)
      | _ =>
          Val (ValLiteral LiteralUnit)
      end
    with val_go _v :=
      match _v with
      | GenLeaf (EncodeLiteral lit) =>
          ValLiteral lit
      | GenNode tag_ValRec [GenLeaf (EncodeBinder f); GenLeaf (EncodeBinder x); e] =>
          ValRec f x (go e)
      | GenNode tag_ValPair [v1; v2] =>
          ValPair (val_go v1) (val_go v2)
      | GenNode tag_ValConstr [GenLeaf (EncodeBool b); v] =>
          ValConstr b (val_go v)
      | _ =>
          ValLiteral LiteralUnit
      end
    for go.
  refine (inj_countable' encode decode _).
  refine (fix go e := _ with val_go v := _ for go).
  - destruct e; simpl; f_equal; [| done..].
    match goal with |- _ = ?v => exact (val_go v) end.
  - destruct v; f_equal; done.
Qed.
#[global] Instance val_countable :
  Countable val.
Proof.
  refine (inj_countable of_val to_val _); auto using to_of_val.
Qed.
