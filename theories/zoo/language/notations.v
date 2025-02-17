From zoo Require Import
  prelude.
From zoo.language Require Export
  language.
From zoo Require Import
  options.

Definition in_type (_ : string) (n : nat) :=
  n.
#[global] Arguments in_type : simpl never.

Coercion LitBool : bool >-> literal.
Coercion LitInt : Z >-> literal.
Coercion LitLoc : location >-> literal.
Coercion LitProph : prophet_id >-> literal.

Coercion Val : val >-> expr.
Coercion Var : string >-> expr.
Coercion App : expr >-> Funclass.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Declare Custom Entry zoo_rec.
Declare Scope zoo_recs_scope.
Delimit Scope zoo_recs_scope with zoo_recs.

Declare Custom Entry zoo_field.
Declare Custom Entry zoo_tag.
Declare Custom Entry zoo_proj.
Declare Custom Entry zoo_branch.

Notation "0" :=
  0
( in custom zoo_field
).
Notation "1" :=
  1
( in custom zoo_field
).
Notation "2" :=
  2
( in custom zoo_field
).
Notation "3" :=
  3
( in custom zoo_field
).
Notation "4" :=
  4
( in custom zoo_field
).
Notation "5" :=
  5
( in custom zoo_field
).
Notation "6" :=
  6
( in custom zoo_field
).
Notation "7" :=
  7
( in custom zoo_field
).
Notation "8" :=
  8
( in custom zoo_field
).
Notation "9" :=
  9
( in custom zoo_field
).

Notation "0" :=
  0
( in custom zoo_tag
).

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

Notation "# l" := (
  ValLit l%Z%V%stdpp
)(at level 8,
  format "# l"
).
Notation "'#@{' X }" := (
  λ x : X, ValLit x
)(only parsing
).

Notation "f x => e" := (
  @pair (prod binder binder) expr
    (@pair binder binder f%binder x%binder)
    e%E
)(in custom zoo_rec at level 200,
  f constr at level 1,
  x constr at level 1,
  e constr at level 200,
  format "f  x  =>  '/  ' '[' e ']'"
).
Notation "f x0 x1 .. xn => e" := (
  @pair (prod binder binder) expr
    (@pair binder binder f%binder x0%binder)
    (Fun x1%binder .. (Fun xn%binder e%E) ..)
)(in custom zoo_rec at level 200,
  f constr at level 1,
  x0 constr at level 1,
  x1 constr at level 1,
  xn constr at level 1,
  e constr at level 200,
  format "f  x0  x1  ..  xn  =>  '/  ' '[' e ']'"
).
Notation "'recs:' rec1 'and:' .. 'and:' recn" := (
  @cons recursive rec1 (.. (@cons recursive recn (@nil recursive)) ..)
)(at level 200,
  rec1 custom zoo_rec,
  recn custom zoo_rec,
  format "'[v' recs:  rec1 '/' and:  .. '/' and:  recn ']'"
) : zoo_recs_scope.

Notation "'rec:' f x => e" := (
  Rec f%binder x%binder e%E
)(at level 200,
  f, x at level 1,
  e at level 200,
  format "'[hv' 'rec:'  f  x  =>  '/  ' '[' e ']' ']'"
) : expr_scope.
Notation "'rec:' f x => e" := (
  ValRec f%binder x%binder e%E
)(at level 200,
  f, x at level 1,
  e at level 200,
  format "'[hv' 'rec:'  f  x  =>  '/  ' '[' e ']' ']'"
) : val_scope.
Notation "'rec:' f x0 x1 .. xn => e" := (
  Rec f%binder x0%binder (Fun x1%binder .. (Fun xn%binder e%E) ..)
)(at level 200,
  f, x0, x1, xn at level 1,
  e at level 200,
  format "'[hv' 'rec:'  f  x0  x1  ..  xn  =>  '/  ' '[' e ']' ']'"
) : expr_scope.
Notation "'rec:' f x0 x1 .. xn => e" := (
  ValRec f%binder x0%binder (Fun x1%binder .. (Fun xn%binder e%E) ..)
)(at level 200,
  f, x0, x1, xn at level 1,
  e at level 200,
  format "'[hv' 'rec:'  f  x0  x1  ..  xn  =>  '/  ' '[' e ']' ']'"
) : val_scope.

Notation "'fun:' x => e" := (
  Fun x%binder e%E
)(at level 200,
  x at level 1,
  e at level 200,
  format "'[hv' 'fun:'  x  =>  '/  ' '[' e ']' ']'"
) : expr_scope.
Notation "'fun:' x0 x1 .. xn => e" := (
  Fun x0%binder (Fun x1%binder .. (Fun xn%binder e%E) ..)
)(at level 200,
  x0, x1, xn at level 1,
  e at level 200,
  format "'[hv' 'fun:'  x0  x1  ..  xn  =>  '/  ' '[' e ']' ']'"
) : expr_scope.
Notation "'fun:' x => e" := (
  ValFun x%binder e%E
)(at level 200,
  x at level 1,
  e at level 200,
  format "'[hv' 'fun:'  x  =>  '/  ' '[' e ']' ']'"
) : val_scope.
Notation "'fun:' x0 x1 .. xn => e" := (
  ValFun x0%binder (Fun x1%binder .. (Fun xn%binder e%E) .. )
)(at level 200,
  x0, x1, xn at level 1,
  e at level 200,
  format "'[hv' 'fun:'  x0  x1  ..  xn  =>  '/  ' '[' e ']' ']'"
) : val_scope.

Notation "'letrec:' f x := e1 'in' e2" := (
  Let f%binder (Rec f%binder x%binder e1%E) e2%E
)(at level 200,
  f, x at level 1,
  e1, e2 at level 200,
  format "'[v' '[hv' 'letrec:'  f  x  :=  '/  ' '[' e1 ']'  '/' 'in'  ']' '/' e2 ']'"
) : expr_scope.
Notation "'letrec:' f x0 x1 .. xn := e1 'in' e2" := (
  Let f%binder (Rec f%binder x0%binder (Fun x1%binder .. (Fun xn%binder e1%E) ..)) e2%E
)(at level 200,
  f, x0, x1, xn at level 1,
  e1, e2 at level 200,
  format "'[v' '[hv' 'letrec:'  f  x0  x1  ..  xn  :=  '/  ' '[' e1 ']'  '/' 'in'  ']' '/' e2 ']'"
) : expr_scope.

Notation "'let:' x := e1 'in' e2" := (
  Let x%binder e1%E e2%E
)(at level 200,
  x at level 1,
  e1, e2 at level 200,
  format "'[v' '[hv' 'let:'  x  :=  '/  ' '[' e1 ']'  '/' 'in'  ']' '/' e2 ']'"
) : expr_scope.
Notation "'let:' f x := e1 'in' e2" := (
  Let f%binder (Fun x%binder e1%E) e2%E
)(at level 200,
  f, x at level 1,
  e1, e2 at level 200,
  format "'[v' '[hv' 'let:'  f  x  :=  '/  ' '[' e1 ']'  '/' 'in'  ']' '/' e2 ']'"
) : expr_scope.
Notation "'let:' f x0 x1 .. xn := e1 'in' e2" := (
  Let f%binder (Fun x0%binder (Fun x1%binder .. (Fun xn%binder e1%E) ..)) e2%E
)(at level 200,
  f, x0, x1, xn at level 1,
  e1, e2 at level 200,
  format "'[v' '[hv' 'let:'  f  x0  x1  ..  xn  :=  '/  ' '[' e1 ']'  '/' 'in'  ']' '/' e2 ']'"
) : expr_scope.

Notation "e1 ;; e2" := (
  Let BAnon e1%E e2%E
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
Notation "e1 `land` e2" := (
  Binop BinopLand e1%E e2%E
)(at level 31,
  left associativity
) : expr_scope.
Notation "e1 `lor` e2" := (
  Binop BinopLor e1%E e2%E
)(at level 32,
  left associativity
) : expr_scope.
Notation "e1 `lsl` e2" := (
  Binop BinopLsl e1%E e2%E
)(at level 30,
  right associativity
) : expr_scope.
Notation "e1 `lsr` e2" := (
  Binop BinopLsr e1%E e2%E
)(at level 30,
  right associativity
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
Notation "e1 == e2" := (
  Equal e1%E e2%E
)(at level 70,
  no associativity
) : expr_scope.
Notation "e1 != e2" := (
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
  format "'[v' '[hv' if:  '/  ' '[' e0 ']'  '/' then  ( ']' '/  ' '[' e1 ']' '/' )  else  ( '/  ' '[' e2 ']' '/' ) ']'"
) : expr_scope.
Notation "'if:' e0 'then' e1" := (
  If e0%E e1%E Unit
)(at level 1,
  e0, e1 at level 200,
  only parsing
) : expr_scope.

Notation "'for:' x := e1 'to' e2 'begin' e3 'end'" := (
  For e1%E e2%E (Fun x%binder e3%E)
)(x at level 1,
  e1, e2, e3 at level 200,
  format "'[v' '[hv' for:  x  :=  '/  ' '[' e1 ']'  '/' to  '/  ' '[' e2 ']'  '/' begin  ']' '/  ' '[' e3 ']'  '/' end ']'"
) : expr_scope.

Notation "{ e1 , .. , en }" := (
  Block Mutable 0 (@cons expr e1%E .. (@cons expr en%E (@nil expr)) ..)
)(e1, en at level 200,
  format "'[hv' {  '[' e1 ']' '/' ,  .. '/' ,  '[' en ']'  '/' } ']'"
) : expr_scope.

Notation "‘ tag { e1 , .. , en }" := (
  Block Mutable tag%core (@cons expr e1%E .. (@cons expr en%E (@nil expr)) ..)
)(at level 2,
  tag custom zoo_tag,
  e1, en at level 200,
  format "'[hv' ‘ tag {  '/  ' '[' e1 ']' '/' ,  .. '/' ,  '[' en ']'  '/' } ']'"
) : expr_scope.

Notation "§ tag" := (
  tag
)(at level 2,
  tag custom zoo_tag,
  format "§ tag"
) : stdpp_scope.
Notation "§ tag" := (
  Val (ValBlock Nongenerative tag%core (@nil val))
)(at level 2,
  tag custom zoo_tag,
  format "§ tag"
) : expr_scope.
Notation "§ tag" := (
  ValBlock Nongenerative tag%core (@nil val)
)(at level 2,
  tag custom zoo_tag,
  format "§ tag"
) : val_scope.

Notation "‘ tag ( e1 , .. , en )" := (
  Block (Immutable Nongenerative) tag%core (@cons expr e1%E .. (@cons expr en%E (@nil expr)) ..)
)(at level 2,
  tag custom zoo_tag,
  e1, en at level 200,
  format "'[hv' ‘ tag (  '/  ' '[' e1 ']' '/' ,  .. '/' ,  '[' en ']'  '/' ) ']'"
) : expr_scope.
Notation "’ tag ( v1 , .. , vn )" := (
  Val (ValBlock Nongenerative tag%core (@cons val v1%V .. (@cons val vn%V (@nil val)) ..))
)(at level 2,
  tag custom zoo_tag,
  v1, vn at level 200,
  format "'[hv' ’ tag (  '/  ' '[' v1 ']' '/' ,  .. '/' ,  '[' vn ']'  '/' ) ']'"
): expr_scope.
Notation "‘ tag ( v1 , .. , vn )" := (
  ValBlock Nongenerative tag%core (@cons val v1%V .. (@cons val vn%V (@nil val)) ..)
)(at level 2,
  tag custom zoo_tag,
  v1, vn at level 200,
  format "'[hv' ‘ tag (  '/  ' '[' v1 ']' '/' ,  .. '/' ,  '[' vn ']'  '/' ) ']'"
): val_scope.

Notation "‘ tag [ e1 , .. , en ]" := (
  Block (Immutable Generative) tag%core (@cons expr e1%E .. (@cons expr en%E (@nil expr)) ..)
)(at level 2,
  tag custom zoo_tag,
  e1, en at level 200,
  format "'[hv' ‘ tag [  '/  ' '[' e1 ']' '/' ,  .. '/' ,  '[' en ']'  '/' ] ']'"
) : expr_scope.
Notation "’ tag [ v1 , .. , vn ]" := (
  Val (ValBlock Generative tag%core (@cons val v1%V .. (@cons val vn%V (@nil val)) ..))
)(at level 2,
  tag custom zoo_tag,
  v1, vn at level 200,
  format "'[hv' ’ tag [  '/  ' '[' v1 ']' '/' ,  .. '/' ,  '[' vn ']'  '/' ] ']'"
): expr_scope.
Notation "‘ tag [ v1 , .. , vn ]" := (
  ValBlock Generative tag%core (@cons val v1%V .. (@cons val vn%V (@nil val)) ..)
)(at level 2,
  tag custom zoo_tag,
  v1, vn at level 200,
  format "'[hv' ‘ tag [  '/  ' '[' v1 ']' '/' ,  .. '/' ,  '[' vn ']'  '/' ] ']'"
): val_scope.

Notation "( v1 , v2 , .. , vn )" := (
  Val (ValBlock Nongenerative 0 (@cons val v1%V (@cons val v2%V .. (@cons val vn%V (@nil val)) ..)))
)(at level 0,
  only printing
) : expr_scope.
Notation "( e1 , e2 , .. , en )" := (
  Block (Immutable Nongenerative) 0 (@cons expr e1%E (@cons expr e2%E .. (@cons expr en%E (@nil expr)) ..))
)(at level 0
) : expr_scope.
Notation "( v1 , v2 , .. , vn )" := (
  ValBlock Nongenerative 0 (@cons val v1%V (@cons val v2%V .. (@cons val vn%V (@nil val)) ..))
)(at level 0
) : val_scope.
Notation "()" := (
  Unit
) : expr_scope.
Notation "()" :=
  ValUnit
: val_scope.

Notation "[ ] => e" := (
  @pair pattern expr
    ( Build_pattern
        (in_type "__list__" 0)
        (@nil binder)
        BAnon
    )
    e%E
)(in custom zoo_branch at level 200,
  e constr at level 200,
  format "[ ]  =>  '/    ' '[' e ']'"
).
Notation "[ ] 'as' x => e" := (
  @pair pattern expr
    ( Build_pattern
        (in_type "__list__" 0)
        (@nil binder)
        (BNamed x%string)
    )
    e%E
)(in custom zoo_branch at level 200,
  x constr at level 1,
  e constr at level 200,
  format "[ ]  as  x  =>  '/    ' '[' e ']'"
).
Notation "x1 :: x2 => e" := (
  @pair pattern expr
    ( Build_pattern
        (in_type "__list__" 1)
        (@cons binder x1%binder (@cons binder x2%binder (@nil binder)))
        BAnon
    )
    e%E
)(in custom zoo_branch at level 200,
  x1 constr at level 1,
  x2 constr at level 1,
  e constr at level 200,
  format "x1  ::  x2  =>  '/    ' '[' e ']'"
).
Notation "x1 :: x2 'as' y => e" := (
  @pair pattern expr
    ( Build_pattern
        (in_type "__list__" 1)
        (@cons binder x1%binder (@cons binder x2%binder (@nil binder)))
        (BNamed y%string)
    )
    e%E
)(in custom zoo_branch at level 200,
  x1 constr at level 1,
  x2 constr at level 1,
  y constr at level 1,
  e constr at level 200,
  format "x1  ::  x2  as  y  =>  '/    ' '[' e ']'"
).
Notation "tag => e" := (
  @pair pattern expr
    ( Build_pattern
        tag%core
        (@nil binder)
        BAnon
    )
    e%E
)(in custom zoo_branch at level 200,
  tag custom zoo_tag,
  e constr at level 200,
  format "tag  =>  '/    ' '[' e ']'"
).
Notation "tag 'as' x => e" := (
  @pair pattern expr
    ( Build_pattern
        tag%core
        (@nil binder)
        (BNamed x%string)
    )
    e%E
)(in custom zoo_branch at level 200,
  tag custom zoo_tag,
  x constr at level 1,
  e constr at level 200,
  format "tag  as  x  =>  '/    ' '[' e ']'"
).
Notation "tag 'as:' x => e" := (
  @pair pattern expr
    ( Build_pattern
        tag%core
        (@nil binder)
        x%binder
    )
    e%E
)(in custom zoo_branch at level 200,
  tag custom zoo_tag,
  x constr at level 1,
  e constr at level 200,
  format "tag  as:  x  =>  '/    ' '[' e ']'"
).
Notation "tag x1 .. xn => e" := (
  @pair pattern expr
    ( Build_pattern
        tag%core
        (@cons binder x1%binder .. (@cons binder xn%binder (@nil binder)) ..)
        BAnon
    )
    e%E
)(in custom zoo_branch at level 200,
  tag custom zoo_tag,
  x1 constr at level 1,
  xn constr at level 1,
  e constr at level 200,
  format "tag  x1  ..  xn  =>  '/    ' '[' e ']'"
).
Notation "tag x1 .. xn 'as' y => e" := (
  @pair pattern expr
    ( Build_pattern
        tag%core
        (@cons binder x1%binder .. (@cons binder xn%binder (@nil binder)) ..)
        (BNamed y%string)
    )
    e%E
)(in custom zoo_branch at level 200,
  tag custom zoo_tag,
  x1 constr at level 1,
  xn constr at level 1,
  y constr at level 1,
  e constr at level 200,
  format "tag  x1  ..  xn  as  y  =>  '/    ' '[' e ']'"
).
Notation "tag x1 .. xn 'as:' y => e" := (
  @pair pattern expr
    ( Build_pattern
        tag%core
        (@cons binder x1%binder .. (@cons binder xn%binder (@nil binder)) ..)
        y%binder
    )
    e%E
)(in custom zoo_branch at level 200,
  tag custom zoo_tag,
  x1 constr at level 1,
  xn constr at level 1,
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
  br_1 custom zoo_branch at level 200,
  br_n custom zoo_branch at level 200,
  format "'[v' '[hv' match:  '/  ' '[' e ']'  '/' with  ']' '/' |  br_1  '/' |  ..  '/' |  br_n  '/' end ']'"
) : expr_scope.
Notation "'match:' e 'with' br_1 | .. | br_n 'end'" := (
  Match
    e%E
    BAnon
    Fail
    (@cons branch br_1 (.. (@cons branch br_n (@nil branch)) ..))
)(e at level 200,
  br_1 custom zoo_branch at level 200,
  br_n custom zoo_branch at level 200,
  only parsing
) : expr_scope.
Notation "'match:' e0 'with' | br_1 | .. | br_n |_ => e1 'end'" := (
  Match
    e0%E
    BAnon
    e1%E
    (@cons branch br_1 (.. (@cons branch br_n (@nil branch)) ..))
)(e0, e1 at level 200,
  br_1 custom zoo_branch at level 200,
  br_n custom zoo_branch at level 200,
  format "'[v' '[hv' match:  '/  ' '[' e0 ']'  '/' with  ']' '/' |  br_1  '/' |  ..  '/' |  br_n  '/' |_  =>  '/    ' '[' e1 ']'  '/' end ']'"
) : expr_scope.
Notation "'match:' e0 'with' br_1 | .. | br_n |_ => e1 'end'" := (
  Match
    e0%E
    BAnon
    e1%E
    (@cons branch br_1 (.. (@cons branch br_n (@nil branch)) ..))
)(e0, e1 at level 200,
  br_1 custom zoo_branch at level 200,
  br_n custom zoo_branch at level 200,
  only parsing
) : expr_scope.
Notation "'match:' e0 'with' | br_1 | .. | br_n |_ 'as' x => e1 'end'" := (
  Match
    e0%E
    (BNamed x%string)
    e1%E
    (@cons branch br_1 (.. (@cons branch br_n (@nil branch)) ..))
)(e0, e1 at level 200,
  br_1 custom zoo_branch at level 200,
  br_n custom zoo_branch at level 200,
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
  br_1 custom zoo_branch at level 200,
  br_n custom zoo_branch at level 200,
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
  br_1 custom zoo_branch at level 200,
  br_n custom zoo_branch at level 200,
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
  br_1 custom zoo_branch at level 200,
  br_n custom zoo_branch at level 200,
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

Notation "e .{ fld }" := (
  Load e%E (Val (ValInt (Z.of_nat fld)))
)(at level 2,
  fld custom zoo_field,
  left associativity,
  format "e .{ fld }"
) : expr_scope.

Notation "e .< proj >" := (
  Load e%E (Val (ValInt (Z.of_nat proj)))
)(at level 2,
  proj custom zoo_proj,
  format "e .< proj >"
) : expr_scope.

Notation "e1 <-{ fld } e2" := (
  Store e1%E (Val (ValInt (Z.of_nat fld))) e2%E
)(at level 80,
  fld custom zoo_field,
  format "'[hv' '[hv' '[' e1 ']'  '/  ' <-{ fld }  ']' '/  ' '[' e2 ']' ']'"
) : expr_scope.

Notation "l .[ fld ]" := (
  location_add l (Z.of_nat fld)
)(at level 2,
  fld custom zoo_field,
  left associativity,
  format "l .[ fld ]"
) : stdpp_scope.
Notation "v .[ fld ]" := (
  Val
    ( ValBlock Nongenerative (in_type "__atomic_loc__" 0)
        ( @cons val v%V
            ( @cons val (ValInt (Z.of_nat fld))
                (@nil val)
            )
        )
    )
)(at level 2,
  fld custom zoo_field,
  only printing,
  left associativity,
  format "v .[ fld ]"
) : expr_scope.
Notation "e .[ fld ]" := (
  Block
    (Immutable Nongenerative)
    (in_type "__atomic_loc__" 0)
    ( @cons expr e%E
        ( @cons expr (Val (ValInt (Z.of_nat fld)))
            (@nil expr)
        )
    )
)(at level 2,
  fld custom zoo_field,
  left associativity,
  format "e .[ fld ]"
) : expr_scope.
Notation "v .[ fld ]" := (
  ValBlock Nongenerative (in_type "__atomic_loc__" 0)
    ( @cons val v%V
        ( @cons val (ValInt (Z.of_nat fld))
            (@nil val)
        )
    )
)(at level 2,
  fld custom zoo_field,
  left associativity,
  format "v .[ fld ]"
) : val_scope.

Notation "'contents'" := (
  in_type "__ref__" 0
)(in custom zoo_field
).
Notation "'ref' e" := (
  Block Mutable (in_type "__ref__" 0) (@cons expr e%E (@nil expr))
)(at level 10
) : expr_scope.
Notation "! e" := (
  Load e%E (Val (ValInt (Z.of_nat (in_type "__ref__" 0))))
)(at level 9,
  right associativity,
  format "! e"
) : expr_scope.
Notation "e1 <- e2" := (
  Store e1%E (Val (ValInt (Z.of_nat (in_type "__ref__" 0)))) e2%E
)(at level 80,
  format "'[hv' '[hv' '[' e1 ']'  '/  ' <-  ']' '/  ' '[' e2 ']' ']'"
) : expr_scope.

Notation "'None'" := (
  in_type "option" 0
)(in custom zoo_tag
).
Notation "'Some'" := (
  in_type "option" 1
)(in custom zoo_tag
).

Notation "[ ]" := (
  Val (ValBlock Nongenerative (in_type "__list__" 0) (@nil val))
)(format "[ ]"
) : expr_scope.
Notation "[ ]" := (
  ValBlock Nongenerative (in_type "__list__" 0) (@nil val)
)(format "[ ]"
) : val_scope.
Notation "e1 :: e2" := (
  Block (Immutable Nongenerative) (in_type "__list__" 1)
    ( @cons expr e1%E
        ( @cons expr e2%E
            (@nil expr)
        )
    )
)(at level 60,
  right associativity,
  format "e1  ::  e2"
) : expr_scope.
Notation "v1 :: v2" := (
  ValBlock Nongenerative (in_type "__list__" 1)
    ( @cons val v1%V
        ( @cons val v2%V
            (@nil val)
        )
    )
)(at level 60,
  right associativity,
  format "v1  ::  v2"
) : val_scope.
