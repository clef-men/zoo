From zebre Require Import
  prelude.
From zebre.language Require Export
  language.
From zebre Require Import
  options.

Coercion LiteralBool : bool >-> literal.
Coercion LiteralInt : Z >-> literal.
Coercion LiteralLoc : loc >-> literal.
Coercion LiteralProphecy : prophecy_id >-> literal.

Coercion Val : val >-> expr.
Coercion Var : string >-> expr.
Coercion App : expr >-> Funclass.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Notation Fail := (
  App (Val ValUnit) (Val ValUnit)
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
Notation CtxLet x e2 := (
  CtxAppR (ValLam x e2)
)(only parsing
).

Notation Seq e1 e2 := (
  Let BAnon e1 e2
)(only parsing
).
Notation CtxSeq e2 := (
  CtxLet BAnon e2
)(only parsing
).

Notation Match e0 x11 x12 e1 x21 x22 e2 := (
  Case e0 (Lam x11 (Lam x12 e1)) (Lam x21 (Lam x22 e2))
)(only parsing
).
Notation Match' e0 x1 e1 x2 e2 := (
  Match e0 x1 BAnon e1 x2 BAnon e2
)(only parsing
).

Notation "# l" := (
  ValLiteral l%Z%V%stdpp
)(at level 8,
  format "# l"
).

Notation "'rec:' f x := e" := (
  Rec f%binder x%binder e%E
)(at level 200,
  f, x at level 1,
  e at level 200,
  format "'[' 'rec:'  f  x  :=  '/  ' e ']'"
) : expr_scope.
Notation "'rec:' f x := e" := (
  ValRec f%binder x%binder e%E
)(at level 200,
  f, x at level 1,
  e at level 200,
  format "'[' 'rec:'  f  x  :=  '/  ' e ']'"
) : val_scope.
Notation "'rec:' f x0 x1 .. xn := e" := (
  Rec f%binder x0%binder (Lam x1%binder .. (Lam xn%binder e%E) ..)
)(at level 200,
  f, x0, x1, xn at level 1,
  e at level 200,
  format "'[' 'rec:'  f  x0  x1  ..  xn  :=  '/  ' e ']'"
) : expr_scope.
Notation "'rec:' f x0 x1 .. xn := e" := (
  ValRec f%binder x0%binder (Lam x1%binder .. (Lam xn%binder e%E) ..)
)(at level 200,
  f, x0, x1, xn at level 1,
  e at level 200,
  format "'[' 'rec:'  f  x0  x1  ..  xn  :=  '/  ' e ']'"
) : val_scope.

Notation "λ: x , e" := (
  Lam x%binder e%E
)(at level 200,
  x at level 1,
  e at level 200,
  format "'[' 'λ:'  x ,  '/  ' e ']'"
) : expr_scope.
Notation "λ: x0 x1 .. xn , e" := (
  Lam x0%binder (Lam x1%binder .. (Lam xn%binder e%E) ..)
)(at level 200,
  x0, x1, xn at level 1,
  e at level 200,
  format "'[' 'λ:'  x0  x1  ..  xn ,  '/  ' e ']'"
) : expr_scope.
Notation "λ: x , e" := (
  ValLam x%binder e%E
)(at level 200,
  x at level 1,
  e at level 200,
  format "'[' 'λ:'  x ,  '/  ' e ']'"
) : val_scope.
Notation "λ: x0 x1 .. xn , e" := (
  ValLam x0%binder (Lam x1%binder .. (Lam xn%binder e%E) .. )
)(at level 200,
  x0, x1, xn at level 1,
  e at level 200,
  format "'[' 'λ:'  x0  x1  ..  xn ,  '/  ' e ']'"
) : val_scope.

Notation "'let:' x := e1 'in' e2" := (
  App (Lam x%binder e2%E) e1%E
)(at level 200,
  x at level 1,
  e1, e2 at level 200,
  format "'[' 'let:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'"
) : expr_scope.
Notation "'let:' f x := e1 'in' e2" := (
  App (Lam f%binder e2%E) (Rec f%binder x%binder e1%E)
)(at level 200,
  f, x at level 1,
  e1, e2 at level 200,
  only parsing
) : expr_scope.
Notation "'let:' f x0 x1 .. xn := e1 'in' e2" := (
  App (Lam f%binder e2%E) (Rec f%binder x0%binder (Lam x1%binder .. (Lam xn%binder e1%E) ..))
)(at level 200,
  f, x0, x1, xn at level 1,
  e1, e2 at level 200,
  only parsing
) : expr_scope.

Notation "e1 ;; e2" := (
  App (Lam BAnon e2%E) e1%E
)(at level 100,
  e2 at level 200,
  format "'[' '[hv' '[' e1 ']'  ;;  ']' '/' e2 ']'"
) : expr_scope.

Notation "~ e" := (
  Unop UnopNeg e%E
)(at level 75,
  right associativity
) : expr_scope.
Notation "- e" := (
  Unop UnopMinus e%E
)(at level 35,
  right associativity
) : expr_scope.

Notation "e1 + e2" := (
  Binop BinopPlus e1%E e2%E
)(at level 50,
  left associativity
) : expr_scope.
Notation "e1 - e2" := (
  Binop BinopMinus e1%E e2%E
)(at level 50,
  left associativity
) : expr_scope.
Notation "e1 * e2" := (
  Binop BinopMult e1%E e2%E
)(at level 40,
  left associativity
) : expr_scope.
Notation "e1 `quot` e2" := (
  Binop BinopQuot e1%E e2%E
)(at level 35
) : expr_scope.
Notation "e1 `rem` e2" := (
  Binop BinopRem e1%E e2%E
)(at level 35
) : expr_scope.
Notation "e1 ≤ e2" := (
  Binop BinopLe e1%E e2%E
)(at level 70,
  no associativity
) : expr_scope.
Notation "e1 < e2" := (
  Binop BinopLt e1%E e2%E
)(at level 70,
  no associativity
) : expr_scope.
Notation "e1 ≥ e2" := (
  Binop BinopGe e1%E e2%E
)(at level 70,
  no associativity
) : expr_scope.
Notation "e1 > e2" := (
  Binop BinopGt e1%E e2%E
)(at level 70,
  no associativity
) : expr_scope.
Notation "e1 +ₗ e2" := (
  Binop BinopOffset e1%E e2%E
)(at level 50,
  left associativity
) : expr_scope.
Notation "e .[ fld ]" := (
  Binop BinopOffset e%E (Val (ValLiteral (LiteralInt (Z.of_nat fld))))
)(at level 2,
  fld custom zebre_field
) : expr_scope.
Notation "e1 = e2" := (
  Equal e1%E e2%E
)(at level 70,
  no associativity
) : expr_scope.
Notation "e1 ≠ e2" := (
  Unop UnopNeg (Equal e1%E e2%E)
)(at level 70,
  no associativity
) : expr_scope.
Notation "e1 && e2" := (
  If e1%E e2%E (ValLiteral (LiteralBool false))
)(at level 40,
  left associativity,
  only parsing
) : expr_scope.
Notation "e1 || e2" := (
  If e1%E (ValLiteral (LiteralBool true)) e2%E
)(at level 50,
  left associativity,
  only parsing
) : expr_scope.

Notation "'if:' e0 'then' e1 'else' e2" := (
  If e0%E e1%E e2%E
)(at level 1,
  e0, e1 at level 200,
  e2 at level 1,
  only parsing
) : expr_scope.
Notation "'if:' e0 'then' ( e1 ) 'else' ( e2 )" := (
  If e0%E e1%E e2%E
)(at level 1,
  e0, e1, e2 at level 200,
  only printing,
  format "'[hv' if:  e0  then  ( '/  ' '[' e1 ']' '/' )  else  ( '/  ' '[' e2 ']' '/' ) ']'"
) : expr_scope.
Notation "'if:' e0 'then' e1" := (
  If e0%E e1%E (Val ValUnit)
)(at level 1,
  e0, e1 at level 200,
  only parsing
) : expr_scope.
Notation "'ifnot:' e0 'then' e2" := (
  If e0%E (Val ValUnit) e2%E
)(at level 1,
  e0, e2 at level 200,
  only parsing
) : expr_scope.

Notation "()" := (
  Val ValUnit
) : expr_scope.
Notation "( e1 , e2 , .. , en )" := (
  Tuple (@cons expr e1%E (@cons expr e2%E .. (@cons expr en%E (@nil expr)) ..))
)(at level 0
) : expr_scope.
Notation "()" :=
  ValUnit
: val_scope.
Notation "( v1 , v2 , .. , vn )" := (
  ValTuple (@cons val v1%V (@cons val v2%V .. (@cons val vn%V (@nil val)) ..))
)(at level 0
) : val_scope.

Declare Custom Entry zebre_proj.
Notation "0" :=
  0
( in custom zebre_proj
).
Notation "1" :=
  1
( in custom zebre_proj
).
Notation "2" :=
  2
( in custom zebre_proj
).
Notation "3" :=
  3
( in custom zebre_proj
).
Notation "4" :=
  4
( in custom zebre_proj
).
Notation "5" :=
  5
( in custom zebre_proj
).
Notation "6" :=
  6
( in custom zebre_proj
).
Notation "7" :=
  7
( in custom zebre_proj
).
Notation "8" :=
  8
( in custom zebre_proj
).
Notation "9" :=
  9
( in custom zebre_proj
).
Notation "e .< proj >" := (
  Proj proj e
)(at level 2,
  proj custom zebre_proj,
  format "e .< proj >"
) : expr_scope.

Notation "'match:' e0 'with' | 'Injl' x11 'as' x12 => e1 | 'Injr' x21 'as' x22 => e2 'end'" := (
  Match e0 x11%binder x12%binder e1 x21%binder x22%binder e2
)(e0, x11, x12, e1, x21, x22, e2 at level 200,
  format "'[hv' 'match:'  e0  'with'  '/' '[' |  'Injl'  x11  'as'  x12  =>  '/    ' e1 ']'  '/' '[' |  'Injr'  x21  'as'  x22  =>  '/    ' e2 ']'  '/' 'end' ']'"
) : expr_scope.
Notation "'match:' e0 'with' 'Injl' x11 'as' x12 => e1 | 'Injr' x21 'as' x22 => e2 'end'" := (
  Match e0 x11%binder x12%binder e1 x21%binder x22%binder e2
)(e0, x11, x12, e1, x21, x22, e2 at level 200,
  only parsing
) : expr_scope.
Notation "'match:' e0 'with' | 'Injl' x1 => e1 | 'Injr' x2 => e2 'end'" := (
  Match' e0 x1%binder e1 x2%binder e2
)(e0, x1, e1, x2, e2 at level 200,
  format "'[hv' 'match:'  e0  'with'  '/' '[' |  'Injl'  x1  =>  '/    ' e1 ']'  '/' '[' |  'Injr'  x2  =>  '/    ' e2 ']'  '/' 'end' ']'"
) : expr_scope.
Notation "'match:' e0 'with' 'Injl' x1 => e1 | 'Injr' x2 => e2 'end'" := (
  Match' e0 x1%binder e1 x2%binder e2
)(e0, x1, e1, x2, e2 at level 200,
  only parsing
) : expr_scope.

Notation "{ e1 ; .. ; en }" := (
  Record (@cons expr e1%E .. (@cons expr en%E (@nil expr)) ..)
)(e1, en at level 200,
  format "'[hv' {  '[' e1 ']' '/' ;  .. '/' ;  '[' en ']'  '/' } ']'"
) : expr_scope.

Notation "'ref' e" := (
  Alloc (Val (ValLiteral (LiteralInt 1))) e
)(at level 10
) : expr_scope.

Notation "! e" := (
  Load e%E
)(at level 9,
  right associativity
) : expr_scope.
Notation "e .{ fld }" := (
  Load (Binop BinopOffset e%E (Val (ValLiteral (LiteralInt (Z.of_nat fld)))))
)(at level 2,
  fld custom zebre_field,
  format "e .{ fld }"
) : expr_scope.

Notation "e1 <- e2" := (
  Store e1%E e2%E
)(at level 80
) : expr_scope.
Notation "e1 <-{ fld } e2" := (
  Store (Binop BinopOffset e1%E (Val (ValLiteral (LiteralInt (Z.of_nat fld))))) e2%E
)(at level 80,
  fld custom zebre_field,
  format "e1  <-{ fld }  e2"
) : expr_scope.
