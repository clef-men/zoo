From zoo Require Import
  prelude.
From zoo.language Require Export
  language.
From zoo Require Import
  options.

Definition in_type (_ : string) (n : nat) :=
  n.
#[global] Arguments in_type : simpl never.

Coercion LiteralBool : bool >-> literal.
Coercion LiteralInt : Z >-> literal.
Coercion LiteralLoc : location >-> literal.
Coercion LiteralProphecy : prophet_id >-> literal.

Coercion Val : val >-> expr.
Coercion Var : string >-> expr.
Coercion App : expr >-> Funclass.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Notation "# l" := (
  ValLiteral l%Z%V%stdpp
)(at level 8,
  format "# l"
).
Notation "'#@{' X }" := (
  λ x : X, ValLiteral x
)(only parsing
).

Notation "'rec:' f x := e" := (
  Rec f%binder x%binder e%E
)(at level 200,
  f, x at level 1,
  e at level 200,
  format "'[hv' 'rec:'  f  x  :=  '/  ' '[' e ']' ']'"
) : expr_scope.
Notation "'rec:' f x := e" := (
  ValRec f%binder x%binder e%E
)(at level 200,
  f, x at level 1,
  e at level 200,
  format "'[hv' 'rec:'  f  x  :=  '/  ' '[' e ']' ']'"
) : val_scope.
Notation "'rec:' f x0 x1 .. xn := e" := (
  Rec f%binder x0%binder (Lam x1%binder .. (Lam xn%binder e%E) ..)
)(at level 200,
  f, x0, x1, xn at level 1,
  e at level 200,
  format "'[hv' 'rec:'  f  x0  x1  ..  xn  :=  '/  ' '[' e ']' ']'"
) : expr_scope.
Notation "'rec:' f x0 x1 .. xn := e" := (
  ValRec f%binder x0%binder (Lam x1%binder .. (Lam xn%binder e%E) ..)
)(at level 200,
  f, x0, x1, xn at level 1,
  e at level 200,
  format "'[hv' 'rec:'  f  x0  x1  ..  xn  :=  '/  ' '[' e ']' ']'"
) : val_scope.

Notation "λ: x , e" := (
  Lam x%binder e%E
)(at level 200,
  x at level 1,
  e at level 200,
  format "'[hv' 'λ:'  x ,  '/  ' '[' e ']' ']'"
) : expr_scope.
Notation "λ: x0 x1 .. xn , e" := (
  Lam x0%binder (Lam x1%binder .. (Lam xn%binder e%E) ..)
)(at level 200,
  x0, x1, xn at level 1,
  e at level 200,
  format "'[hv' 'λ:'  x0  x1  ..  xn ,  '/  ' '[' e ']' ']'"
) : expr_scope.
Notation "λ: x , e" := (
  ValLam x%binder e%E
)(at level 200,
  x at level 1,
  e at level 200,
  format "'[hv' 'λ:'  x ,  '/  ' '[' e ']' ']'"
) : val_scope.
Notation "λ: x0 x1 .. xn , e" := (
  ValLam x0%binder (Lam x1%binder .. (Lam xn%binder e%E) .. )
)(at level 200,
  x0, x1, xn at level 1,
  e at level 200,
  format "'[hv' 'λ:'  x0  x1  ..  xn ,  '/  ' '[' e ']' ']'"
) : val_scope.

Notation "'letrec:' f x := e1 'in' e2" := (
  App (Lam f%binder e2%E) (Rec f%binder x%binder e1%E)
)(at level 200,
  f, x at level 1,
  e1, e2 at level 200,
  format "'[v' '[hv' 'letrec:'  f  x  :=  '/  ' '[' e1 ']'  '/' 'in'  ']' '/' e2 ']'"
) : expr_scope.
Notation "'letrec:' f x0 x1 .. xn := e1 'in' e2" := (
  App (Lam f%binder e2%E) (Rec f%binder x0%binder (Lam x1%binder .. (Lam xn%binder e1%E) ..))
)(at level 200,
  f, x0, x1, xn at level 1,
  e1, e2 at level 200,
  format "'[v' '[hv' 'letrec:'  f  x0  x1  ..  xn  :=  '/  ' '[' e1 ']'  '/' 'in'  ']' '/' e2 ']'"
) : expr_scope.

Notation "'let:' x := e1 'in' e2" := (
  App (Lam x%binder e2%E) e1%E
)(at level 200,
  x at level 1,
  e1, e2 at level 200,
  format "'[v' '[hv' 'let:'  x  :=  '/  ' '[' e1 ']'  '/' 'in'  ']' '/' e2 ']'"
) : expr_scope.
Notation "'let:' f x := e1 'in' e2" := (
  App (Lam f%binder e2%E) (Lam x%binder e1%E)
)(at level 200,
  f, x at level 1,
  e1, e2 at level 200,
  format "'[v' '[hv' 'let:'  f  x  :=  '/  ' '[' e1 ']'  '/' 'in'  ']' '/' e2 ']'"
) : expr_scope.
Notation "'let:' f x0 x1 .. xn := e1 'in' e2" := (
  App (Lam f%binder e2%E) (Lam x0%binder (Lam x1%binder .. (Lam xn%binder e1%E) ..))
)(at level 200,
  f, x0, x1, xn at level 1,
  e1, e2 at level 200,
  format "'[v' '[hv' 'let:'  f  x0  x1  ..  xn  :=  '/  ' '[' e1 ']'  '/' 'in'  ']' '/' e2 ']'"
) : expr_scope.

Notation "e1 ;; e2" := (
  App (Lam BAnon e2%E) e1%E
)(at level 100,
  e2 at level 200,
  format "'[v' '[' e1 ']'  ;;  '/' e2 ']'"
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
Notation "e1 'and' e2" := (
  If e1%E e2%E (ValBool false)
)(at level 76,
  left associativity,
  only parsing
) : expr_scope.
Notation "e1 'or' e2" := (
  If e1%E (ValBool true) e2%E
)(at level 77,
  left associativity,
  only parsing
) : expr_scope.

Declare Custom Entry zoo_field.
Notation "l .[ fld ]" := (
  location_add l (Z.of_nat fld)
)(at level 2,
  fld custom zoo_field,
  format "l .[ fld ]"
) : stdpp_scope.
Notation "e .[ fld ]" := (
  Binop BinopOffset e%E (Val (ValInt (Z.of_nat fld)))
)(at level 2,
  fld custom zoo_field
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
  format "'[hv' '[hv' if:  '/  ' '[' e0 ']'  '/' then  ( ']' '/  ' '[' e1 ']' '/' )  else  ( '/  ' '[' e2 ']' '/' ) ']'"
) : expr_scope.
Notation "'if:' e0 'then' e1" := (
  If e0%E e1%E Unit
)(at level 1,
  e0, e1 at level 200,
  only parsing
) : expr_scope.
Notation "'ifnot:' e0 'then' e2" := (
  If e0%E Unit e2%E
)(at level 1,
  e0, e2 at level 200,
  only parsing
) : expr_scope.

Declare Custom Entry zoo_tag.
Notation "‘ tag { e1 , .. , en }" := (
  Constr tag%core (@cons expr e1%E .. (@cons expr en%E (@nil expr)) ..)
)(at level 2,
  tag custom zoo_tag,
  e1, en at level 200,
  format "'[hv' ‘ tag {  '/  ' '[' e1 ']' '/' ,  .. '/' ,  '[' en ']'  '/' } ']'"
).
Notation "’ tag @{ cid }{ v1 , .. , vn }" := (
  ValConstr (Some cid) tag%core (@cons val v1%V .. (@cons val vn%V (@nil val)) ..)
)(at level 2,
  tag custom zoo_tag,
  cid at level 200,
  v1, vn at level 200,
  format "'[hv' ’ tag @{ cid }{  '/  ' '[' v1 ']' '/' ,  .. '/' ,  '[' vn ']'  '/' } ']'"
).
Notation "’ tag { v1 , .. , vn }" := (
  ValConstr None tag%core (@cons val v1%V .. (@cons val vn%V (@nil val)) ..)
)(at level 2,
  tag custom zoo_tag,
  v1, vn at level 200,
  format "'[hv' ’ tag {  '/  ' '[' v1 ']' '/' ,  .. '/' ,  '[' vn ']'  '/' } ']'"
).
Notation "§ tag @{ cid }" := (
  ValConstr (Some cid) tag%core (@nil val)
)(at level 2,
  tag custom zoo_tag,
  cid at level 200,
  format "§ tag @{ cid }"
).
Notation "§ tag" := (
  ValConstr None tag%core (@nil val)
)(at level 2,
  tag custom zoo_tag,
  format "§ tag"
).

Notation "( e1 , e2 , .. , en )" := (
  Constr 0 (@cons expr e1%E (@cons expr e2%E .. (@cons expr en%E (@nil expr)) ..))
)(at level 0
) : expr_scope.
Notation "( v1 , v2 , .. , vn )" := (
  ValConstr None 0 (@cons val v1%V (@cons val v2%V .. (@cons val vn%V (@nil val)) ..))
)(at level 0
) : val_scope.
Notation "()" := (
  Unit
) : expr_scope.
Notation "()" :=
  ValUnit
: val_scope.

Declare Custom Entry zoo_proj.
Notation "0" :=
  0
( in custom zoo_proj
).
Notation "1" :=
  1
( in custom zoo_proj
).
Notation "2" :=
  2
( in custom zoo_proj
).
Notation "3" :=
  3
( in custom zoo_proj
).
Notation "4" :=
  4
( in custom zoo_proj
).
Notation "5" :=
  5
( in custom zoo_proj
).
Notation "6" :=
  6
( in custom zoo_proj
).
Notation "7" :=
  7
( in custom zoo_proj
).
Notation "8" :=
  8
( in custom zoo_proj
).
Notation "9" :=
  9
( in custom zoo_proj
).
Notation "e .< proj >" := (
  Proj proj e
)(at level 2,
  proj custom zoo_proj,
  format "e .< proj >"
) : expr_scope.

Declare Custom Entry zoo_branch.
Notation "tag => e" := (
  @pair pattern expr
    (Build_pattern tag%core (@nil binder) BAnon)
    e%E
)(in custom zoo_branch at level 200,
  tag custom zoo_tag,
  e constr at level 200,
  format "tag  =>  '/    ' '[' e ']'"
).
Notation "tag 'as' x => e" := (
  @pair pattern expr
    (Build_pattern tag%core (@nil binder) (BNamed x%string))
    e%E
)(in custom zoo_branch at level 200,
  tag custom zoo_tag,
  x constr at level 1,
  e constr at level 200,
  format "tag  as  x  =>  '/    ' '[' e ']'"
).
Notation "tag 'as:' x => e" := (
  @pair pattern expr
    (Build_pattern tag%core (@nil binder) x%binder)
    e%E
)(in custom zoo_branch at level 200,
  tag custom zoo_tag,
  x constr at level 1,
  e constr at level 200,
  format "tag  as:  x  =>  '/    ' '[' e ']'"
).
Notation "tag x1 .. xn => e" := (
  @pair pattern expr
    (Build_pattern tag%core (@cons binder x1%binder .. (@cons binder xn%binder (@nil binder)) ..) BAnon)
    e%E
)(in custom zoo_branch at level 200,
  tag custom zoo_tag,
  x1 constr at level 1, xn constr at level 1,
  e constr at level 200,
  format "tag  x1  ..  xn  =>  '/    ' '[' e ']'"
).
Notation "tag x1 .. xn 'as' y => e" := (
  @pair pattern expr
    (Build_pattern tag%core (@cons binder x1%binder .. (@cons binder xn%binder (@nil binder)) ..) (BNamed y%string))
    e%E
)(in custom zoo_branch at level 200,
  tag custom zoo_tag,
  x1 constr at level 1, xn constr at level 1,
  y constr at level 1,
  e constr at level 200,
  format "tag  x1  ..  xn  as  y  =>  '/    ' '[' e ']'"
).
Notation "tag x1 .. xn 'as:' y => e" := (
  @pair pattern expr
    (Build_pattern tag%core (@cons binder x1%binder .. (@cons binder xn%binder (@nil binder)) ..) y%binder)
    e%E
)(in custom zoo_branch at level 200,
  tag custom zoo_tag,
  x1 constr at level 1, xn constr at level 1,
  y constr at level 1,
  e constr at level 200,
  format "tag  x1  ..  xn  as:  y  =>  '/    ' '[' e ']'"
).
Notation "'match:' e 'with' | br_1 | .. | br_n 'end'" := (
  Match
    e%E
    BAnon
    Fail
    (@cons branch br_1 (.. (@cons branch br_n (@nil branch)) ..))
)(e at level 200,
  br_1 custom zoo_branch at level 200, br_n custom zoo_branch at level 200,
  format "'[v' '[hv' match:  '/  ' '[' e ']'  '/' with  ']' '/' |  br_1  '/' |  ..  '/' |  br_n  '/' end ']'"
) : expr_scope.
Notation "'match:' e 'with' br_1 | .. | br_n 'end'" := (
  Match
    e%E
    BAnon
    Fail
    (@cons branch br_1 (.. (@cons branch br_n (@nil branch)) ..))
)(e at level 200,
  br_1 custom zoo_branch at level 200, br_n custom zoo_branch at level 200,
  only parsing
) : expr_scope.
Notation "'match:' e0 'with' | br_1 | .. | br_n |_ => e1 'end'" := (
  Match
    e0%E
    BAnon
    e1%E
    (@cons branch br_1 (.. (@cons branch br_n (@nil branch)) ..))
)(e0, e1 at level 200,
  br_1 custom zoo_branch at level 200, br_n custom zoo_branch at level 200,
  format "'[v' '[hv' match:  '/  ' '[' e0 ']'  '/' with  ']' '/' |  br_1  '/' |  ..  '/' |  br_n  '/' |_  =>  '/    ' '[' e1 ']'  '/' end ']'"
) : expr_scope.
Notation "'match:' e0 'with' br_1 | .. | br_n |_ => e1 'end'" := (
  Match
    e0%E
    BAnon
    e1%E
    (@cons branch br_1 (.. (@cons branch br_n (@nil branch)) ..))
)(e0, e1 at level 200,
  br_1 custom zoo_branch at level 200, br_n custom zoo_branch at level 200,
  only parsing
) : expr_scope.
Notation "'match:' e0 'with' | br_1 | .. | br_n |_ 'as' x => e1 'end'" := (
  Match
    e0%E
    (BNamed x%string)
    e1%E
    (@cons branch br_1 (.. (@cons branch br_n (@nil branch)) ..))
)(e0, e1 at level 200,
  br_1 custom zoo_branch at level 200, br_n custom zoo_branch at level 200,
  x at level 1,
  format "'[v' '[hv' match:  '/  ' '[' e0 ']'  '/' with  ']' '/' |  br_1  '/' |  ..  '/' |  br_n  '/' |_  as  x  =>  '/    ' '[' e1 ']'  '/' end ']'"
) : expr_scope.
Notation "'match:' e0 'with' br_1 | .. | br_n |_ 'as' x => e1 'end'" := (
  Match
    e0%E
    (BNamed x%string)
    e1%E
    (@cons branch br_1 (.. (@cons branch br_n (@nil branch)) ..))
)(e0, e1 at level 200,
  br_1 custom zoo_branch at level 200, br_n custom zoo_branch at level 200,
  x at level 1,
  only parsing
) : expr_scope.
Notation "'match:' e0 'with' | br_1 | .. | br_n |_ 'as:' x => e1 'end'" := (
  Match
    e0%E
    x%binder
    e1%E
    (@cons branch br_1 (.. (@cons branch br_n (@nil branch)) ..))
)(e0, e1 at level 200,
  br_1 custom zoo_branch at level 200, br_n custom zoo_branch at level 200,
  x at level 1,
  format "'[v' '[hv' match:  '/  ' '[' e0 ']'  '/' with  ']' '/' |  br_1  '/' |  ..  '/' |  br_n  '/' |_  as:  x  =>  '/    ' '[' e1 ']'  '/' end ']'"
) : expr_scope.
Notation "'match:' e0 'with' br_1 | .. | br_n |_ 'as:' x => e1 'end'" := (
  Match
    e0%E
    x%binder
    e1%E
    (@cons branch br_1 (.. (@cons branch br_n (@nil branch)) ..))
)(e0, e1 at level 200,
  br_1 custom zoo_branch at level 200, br_n custom zoo_branch at level 200,
  x at level 1,
  only parsing
) : expr_scope.

Notation "'let:' ‘ tag x1 .. xn := e1 'in' e2" := (
  Match
    e1%E
    BAnon
    Fail
    ( @cons branch
      ( @pair pattern expr
        ( Build_pattern
          tag%core
          (@cons binder x1%binder .. (@cons binder xn%binder (@nil binder)) ..)
          BAnon
        )
        e2%E
      )
      (@nil branch)
    )
)(at level 200,
  tag custom zoo_tag,
  x1, xn at level 1,
  e1, e2 at level 200,
  format "'[v' '[hv' 'let:'  ‘ tag  x1  ..  xn  :=  '/  ' '[' e1 ']'  '/' 'in'  ']' '/' e2 ']'"
) : expr_scope.
Notation "'let:' x0 , x1 , .. , xn := e1 'in' e2" := (
  Match
    e1%E
    BAnon
    Fail
    ( @cons branch
      ( @pair pattern expr
        ( Build_pattern
          0
          (@cons binder x0%binder (@cons binder x1%binder .. (@cons binder xn%binder (@nil binder)) ..))
          BAnon
        )
        e2%E
      )
      (@nil branch)
    )
)(at level 200,
  x0, x1, xn at level 1,
  e1, e2 at level 200,
  format "'[v' '[hv' 'let:'  x0 ,  x1 ,  .. ,  xn  :=  '/  ' '[' e1 ']'  '/' 'in'  ']' '/' e2 ']'"
) : expr_scope.

Notation "'for:' x := e1 'to' e2 'begin' e3 'end'" := (
  For e1%E e2%E (Lam x%binder e3%E)
)(x at level 1,
  e1, e2, e3 at level 200,
  format "'[v' '[hv' for:  x  :=  '/  ' '[' e1 ']'  '/' to  '/  ' '[' e2 ']'  '/' begin  ']' '/  ' '[' e3 ']'  '/' end ']'"
) : expr_scope.

Notation "{ e1 , .. , en }" := (
  Record (@cons expr e1%E .. (@cons expr en%E (@nil expr)) ..)
)(e1, en at level 200,
  format "'[hv' {  '[' e1 ']' '/' ,  .. '/' ,  '[' en ']'  '/' } ']'"
) : expr_scope.

Notation "'ref' e" := (
  Alloc (Val (ValInt 1)) e
)(at level 10
) : expr_scope.

Notation "! e" := (
  Load e%E
)(at level 9,
  right associativity,
  format "! e"
) : expr_scope.
Notation "e .{ fld }" := (
  Load (Binop BinopOffset e%E (Val (ValInt (Z.of_nat fld))))
)(at level 2,
  fld custom zoo_field,
  format "e .{ fld }"
) : expr_scope.

Notation "e1 <- e2" := (
  Store e1%E e2%E
)(at level 80,
  format "'[hv' '[hv' '[' e1 ']'  '/  ' <-  ']' '/  ' '[' e2 ']' ']'"
) : expr_scope.
Notation "e1 <-{ fld } e2" := (
  Store (Binop BinopOffset e1%E (Val (ValInt (Z.of_nat fld)))) e2%E
)(at level 80,
  fld custom zoo_field,
  format "'[hv' '[hv' '[' e1 ']'  '/  ' <-{ fld }  ']' '/  ' '[' e2 ']' ']'"
) : expr_scope.
