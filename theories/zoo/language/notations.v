Require Import zoo.prelude.
Require Export zoo.language.language.
Require Import zoo.options.

Definition in_type {X} (_ : string) (x : X) :=
  x.
#[global] Arguments in_type : simpl never.

Coercion LitBool : bool >-> literal.
Coercion LitInt : Z >-> literal.
Coercion LitLoc : location >-> literal.
Coercion LitProph : prophet_id >-> literal.

Coercion Val : val >-> expr.
Coercion Var : string >-> expr.
Coercion App : expr >-> Funclass.

Declare Custom Entry zoo_rec.
Declare Scope zoo_recs_scope.
Delimit Scope zoo_recs_scope with zoo_recs.

Declare Custom Entry zoo_field.
Declare Custom Entry zoo_tag.
Declare Custom Entry zoo_proj.
Declare Custom Entry zoo_branch.

Number Notation
  val
  val۰of_int
  val۰to_int
: expr_scope.
Number Notation
  val
  val۰of_int
  val۰to_int
: val_scope.

Notation "'𝗮𝗹𝗹𝗼𝗰'" :=
  Alloc
: expr_scope.
Notation "'𝗰𝗮𝘀'" :=
  CAS
: expr_scope.
Notation "'𝗳𝗮𝗮'" :=
  FAA
: expr_scope.
Notation "'𝗳𝗮𝗶𝗹'" :=
  Fail
: expr_scope.
Notation "'𝗳𝗼𝗿𝗸'" :=
  Fork
: expr_scope.
Notation "'𝗹𝗼𝗰𝗮𝗹'" :=
  LocalGet
: expr_scope.
Notation "'𝗶𝗺𝗺𝗲𝗱𝗶𝗮𝘁𝗲'" :=
  IsImmediate
: expr_scope.
Notation "'𝗹𝗼𝗮𝗱'" :=
  Load
: expr_scope.
Notation "'𝗽𝗿𝗼𝗽𝗵'" :=
  Proph
: expr_scope.
Notation "'𝗿𝗲𝘀𝗼𝗹𝘃𝗲'" :=
  Resolve
: expr_scope.
Notation "'𝘀𝗲𝘁𝗹𝗼𝗰𝗮𝗹'" :=
  LocalSet
: expr_scope.
Notation "'𝘀𝗶𝘇𝗲'" :=
  GetSize
: expr_scope.
Notation "'𝘀𝗸𝗶𝗽'" :=
  Skip
: expr_scope.
Notation "'𝘀𝘁𝗼𝗿𝗲'" :=
  Store
: expr_scope.
Notation "'𝘁𝗮𝗴'" :=
  GetTag
: expr_scope.
Notation "'𝘅𝗰𝗵𝗴'" :=
  Xchg
: expr_scope.

Notation "'true'" := (
  Corelib.Init.Datatypes.true
) : core_scope.
Notation "'true'" := (
  Val (ValLit (LitBool true))
) : expr_scope.
Notation "'true'" := (
  ValLit (LitBool true)
) : val_scope.

Notation "'false'" := (
  Corelib.Init.Datatypes.false
) : core_scope.
Notation "'false'" := (
  Val (ValLit (LitBool false))
) : expr_scope.
Notation "'false'" := (
  ValLit (LitBool false)
) : val_scope.

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
  Tag0
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
Notation "'#*@{' X }" := (
  @fmap _ _ X val (λ x : X, ValLit x)
)(only parsing
).

Notation "f x -> e" := (
  @pair (prod binder binder) expr
    (@pair binder binder f%binder x%binder)
    e%E
)(in custom zoo_rec at level 200,
  f constr at level 1,
  x constr at level 1,
  e constr at level 200,
  format "f  x  ->  '/  ' '[' e ']'"
).
Notation "f x0 x1 .. xn -> e" := (
  @pair (prod binder binder) expr
    (@pair binder binder f%binder x0%binder)
    (Fun x1%binder .. (Fun xn%binder e%E) ..)
)(in custom zoo_rec at level 200,
  f constr at level 1,
  x0 constr at level 1,
  x1 constr at level 1,
  xn constr at level 1,
  e constr at level 200,
  format "f  x0  x1  ..  xn  ->  '/  ' '[' e ']'"
).
Notation "'𝗿𝗲𝗰𝘀' rec_1 '𝘄𝗶𝘁𝗵' .. '𝘄𝗶𝘁𝗵' rec_n" := (
  @cons recursive rec_1 (.. (@cons recursive rec_n (@nil recursive)) ..)
)(at level 200,
  rec_1 custom zoo_rec,
  rec_n custom zoo_rec,
  format "'[v' 𝗿𝗲𝗰𝘀  rec_1 '/' '𝘄𝗶𝘁𝗵'  .. '/' '𝘄𝗶𝘁𝗵'  rec_n ']'"
) : zoo_recs_scope.

Notation "'𝗿𝗲𝗰' f x -> e" := (
  Rec f%binder x%binder e%E
)(at level 200,
  f, x at level 1,
  e at level 200,
  format "'[hv' '𝗿𝗲𝗰'  f  x  ->  '/  ' '[' e ']' ']'"
) : expr_scope.
Notation "'𝗿𝗲𝗰' f x -> e" := (
  ValRec f%binder x%binder e%E
)(at level 200,
  f, x at level 1,
  e at level 200,
  format "'[hv' '𝗿𝗲𝗰'  f  x  ->  '/  ' '[' e ']' ']'"
) : val_scope.
Notation "'𝗿𝗲𝗰' f x0 x1 .. xn -> e" := (
  Rec f%binder x0%binder (Fun x1%binder .. (Fun xn%binder e%E) ..)
)(at level 200,
  f, x0, x1, xn at level 1,
  e at level 200,
  format "'[hv' '𝗿𝗲𝗰'  f  x0  x1  ..  xn  ->  '/  ' '[' e ']' ']'"
) : expr_scope.
Notation "'𝗿𝗲𝗰' f x0 x1 .. xn -> e" := (
  ValRec f%binder x0%binder (Fun x1%binder .. (Fun xn%binder e%E) ..)
)(at level 200,
  f, x0, x1, xn at level 1,
  e at level 200,
  format "'[hv' '𝗿𝗲𝗰'  f  x0  x1  ..  xn  ->  '/  ' '[' e ']' ']'"
) : val_scope.

Notation "'𝗳𝘂𝗻' x -> e" := (
  Fun x%binder e%E
)(at level 200,
  x at level 1,
  e at level 200,
  format "'[hv' '𝗳𝘂𝗻'  x  ->  '/  ' '[' e ']' ']'"
) : expr_scope.
Notation "'𝗳𝘂𝗻' x0 x1 .. xn -> e" := (
  Fun x0%binder (Fun x1%binder .. (Fun xn%binder e%E) ..)
)(at level 200,
  x0, x1, xn at level 1,
  e at level 200,
  format "'[hv' '𝗳𝘂𝗻'  x0  x1  ..  xn  ->  '/  ' '[' e ']' ']'"
) : expr_scope.
Notation "'𝗳𝘂𝗻' x -> e" := (
  ValFun x%binder e%E
)(at level 200,
  x at level 1,
  e at level 200,
  format "'[hv' '𝗳𝘂𝗻'  x  ->  '/  ' '[' e ']' ']'"
) : val_scope.
Notation "'𝗳𝘂𝗻' x0 x1 .. xn -> e" := (
  ValFun x0%binder (Fun x1%binder .. (Fun xn%binder e%E) .. )
)(at level 200,
  x0, x1, xn at level 1,
  e at level 200,
  format "'[hv' '𝗳𝘂𝗻'  x0  x1  ..  xn  ->  '/  ' '[' e ']' ']'"
) : val_scope.

Notation "'𝗹𝗲𝘁𝗿𝗲𝗰' f x = e1 '𝗶𝗻' e2" := (
  Let f%binder (Rec f%binder x%binder e1%E) e2%E
)(at level 200,
  f, x at level 1,
  e1, e2 at level 200,
  format "'[v' '[hv' '𝗹𝗲𝘁𝗿𝗲𝗰'  f  x  =  '/  ' '[' e1 ']'  '/' '𝗶𝗻'  ']' '/' e2 ']'"
) : expr_scope.
Notation "'𝗹𝗲𝘁𝗿𝗲𝗰' f x0 x1 .. xn = e1 '𝗶𝗻' e2" := (
  Let f%binder (Rec f%binder x0%binder (Fun x1%binder .. (Fun xn%binder e1%E) ..)) e2%E
)(at level 200,
  f, x0, x1, xn at level 1,
  e1, e2 at level 200,
  format "'[v' '[hv' '𝗹𝗲𝘁𝗿𝗲𝗰'  f  x0  x1  ..  xn  =  '/  ' '[' e1 ']'  '/' '𝗶𝗻'  ']' '/' e2 ']'"
) : expr_scope.

Notation "'𝗹𝗲𝘁' x = e1 '𝗶𝗻' e2" := (
  Let x%binder e1%E e2%E
)(at level 200,
  x at level 1,
  e1, e2 at level 200,
  format "'[v' '[hv' '𝗹𝗲𝘁'  x  =  '/  ' '[' e1 ']'  '/' '𝗶𝗻'  ']' '/' e2 ']'"
) : expr_scope.
Notation "'𝗹𝗲𝘁' f x = e1 '𝗶𝗻' e2" := (
  Let f%binder (Fun x%binder e1%E) e2%E
)(at level 200,
  f, x at level 1,
  e1, e2 at level 200,
  format "'[v' '[hv' '𝗹𝗲𝘁'  f  x  =  '/  ' '[' e1 ']'  '/' '𝗶𝗻'  ']' '/' e2 ']'"
) : expr_scope.
Notation "'𝗹𝗲𝘁' f x0 x1 .. xn = e1 '𝗶𝗻' e2" := (
  Let f%binder (Fun x0%binder (Fun x1%binder .. (Fun xn%binder e1%E) ..)) e2%E
)(at level 200,
  f, x0, x1, xn at level 1,
  e1, e2 at level 200,
  format "'[v' '[hv' '𝗹𝗲𝘁'  f  x0  x1  ..  xn  =  '/  ' '[' e1 ']'  '/' '𝗶𝗻'  ']' '/' e2 ']'"
) : expr_scope.

Notation "e1 ⍮ e2" := (
  Let BAnon e1%E e2%E
)(at level 100,
  e2 at level 200,
  format "'[v' '[' e1 ']'  ⍮  '/' e2 ']'"
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
Notation "e1 '𝗾𝘂𝗼𝘁' e2" := (
  Binop BinopQuot e1%E e2%E
)(at level 35
) : expr_scope.
Notation "e1 '𝗿𝗲𝗺' e2" := (
  Binop BinopRem e1%E e2%E
)(at level 35
) : expr_scope.
Notation "e1 '𝗹𝗮𝗻𝗱' e2" := (
  Binop BinopLand e1%E e2%E
)(at level 31,
  left associativity
) : expr_scope.
Notation "e1 '𝗹𝗼𝗿' e2" := (
  Binop BinopLor e1%E e2%E
)(at level 32,
  left associativity
) : expr_scope.
Notation "e1 '𝗹𝘀𝗹' e2" := (
  Binop BinopLsl e1%E e2%E
)(at level 30,
  right associativity
) : expr_scope.
Notation "e1 '𝗹𝘀𝗿' e2" := (
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
Notation "e1 '𝗮𝗻𝗱' e2" := (
  If e1%E e2%E (ValBool false)
)(at level 76,
  left associativity,
  only parsing
) : expr_scope.
Notation "e1 '𝗼𝗿' e2" := (
  If e1%E (ValBool true) e2%E
)(at level 77,
  left associativity,
  only parsing
) : expr_scope.

Notation "'𝗶𝗳' e0 '𝘁𝗵𝗲𝗻' e1 '𝗲𝗹𝘀𝗲' e2" := (
  If e0%E e1%E e2%E
)(at level 1,
  e0, e1 at level 200,
  e2 at level 1,
  only parsing
) : expr_scope.
Notation "'𝗶𝗳' e0 '𝘁𝗵𝗲𝗻' ( e1 ) '𝗲𝗹𝘀𝗲' ( e2 )" := (
  If e0%E e1%E e2%E
)(at level 1,
  e0, e1, e2 at level 200,
  only printing,
  format "'[v' '[hv' '𝗶𝗳'  '/  ' '[' e0 ']'  '/' '𝘁𝗵𝗲𝗻'  ( ']' '/  ' '[' e1 ']' '/' )  '𝗲𝗹𝘀𝗲'  ( '/  ' '[' e2 ']' '/' ) ']'"
) : expr_scope.
Notation "'𝗶𝗳' e0 '𝘁𝗵𝗲𝗻' e1" := (
  If e0%E e1%E Unit
)(at level 1,
  e0, e1 at level 200,
  only parsing
) : expr_scope.

Notation "'𝗳𝗼𝗿' x = e1 '𝘁𝗼' e2 '𝗱𝗼' e3 '𝗱𝗼𝗻𝗲'" := (
  For e1%E e2%E (Fun x%binder e3%E)
)(x at level 1,
  e1, e2, e3 at level 200,
  format "'[v' '[hv' '𝗳𝗼𝗿'  x  =  '/  ' '[' e1 ']'  '/' '𝘁𝗼'  '/  ' '[' e2 ']'  '/' '𝗱𝗼'  ']' '/  ' '[' e3 ']'  '/' '𝗱𝗼𝗻𝗲' ']'"
) : expr_scope.

Notation "{ e1 , .. , en }" := (
  Block
    Mutable
    Tag0
    (@cons expr e1%E .. (@cons expr en%E (@nil expr)) ..)
)(e1, en at level 200,
  format "'[hv' {  '[' e1 ']' '/' ,  .. '/' ,  '[' en ']'  '/' } ']'"
) : expr_scope.

Notation "‘ tag { e1 , .. , en }" := (
  Block
    Mutable
    tag
    (@cons expr e1%E .. (@cons expr en%E (@nil expr)) ..)
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
  Val (
    ValBlock
    Nongenerative
    tag
    (@nil val)
  )
)(at level 2,
  tag custom zoo_tag,
  format "§ tag"
) : expr_scope.
Notation "§ tag" := (
  ValBlock
    Nongenerative
    tag
    (@nil val)
)(at level 2,
  tag custom zoo_tag,
  format "§ tag"
) : val_scope.

Notation "‘ tag ( e1 , .. , en )" := (
  Block
    ImmutableNongenerative
    tag
    (@cons expr e1%E .. (@cons expr en%E (@nil expr)) ..)
)(at level 2,
  tag custom zoo_tag,
  e1, en at level 200,
  format "'[hv' ‘ tag (  '/  ' '[' e1 ']' '/' ,  .. '/' ,  '[' en ']'  '/' ) ']'"
) : expr_scope.
Notation "’ tag ( v1 , .. , vn )" := (
  Val (
    ValBlock
      Nongenerative
      tag
      (@cons val v1%V .. (@cons val vn%V (@nil val)) ..)
  )
)(at level 2,
  tag custom zoo_tag,
  v1, vn at level 200,
  format "'[hv' ’ tag (  '/  ' '[' v1 ']' '/' ,  .. '/' ,  '[' vn ']'  '/' ) ']'"
): expr_scope.
Notation "‘ tag ( v1 , .. , vn )" := (
  ValBlock
    Nongenerative
    tag
    (@cons val v1%V .. (@cons val vn%V (@nil val)) ..)
)(at level 2,
  tag custom zoo_tag,
  v1, vn at level 200,
  format "'[hv' ‘ tag (  '/  ' '[' v1 ']' '/' ,  .. '/' ,  '[' vn ']'  '/' ) ']'"
): val_scope.

Notation "‘ tag [ e1 , .. , en ]" := (
  Block
    ImmutableGenerativeWeak
    tag
    (@cons expr e1%E .. (@cons expr en%E (@nil expr)) ..)
)(at level 2,
  tag custom zoo_tag,
  e1, en at level 200,
  format "'[hv' ‘ tag [  '/  ' '[' e1 ']' '/' ,  .. '/' ,  '[' en ']'  '/' ] ']'"
) : expr_scope.
Notation "’ tag [ v1 , .. , vn ]" := (
  Val (
    ValBlock
      (Generative None)
      tag
      (@cons val v1%V .. (@cons val vn%V (@nil val)) ..)
  )
)(at level 2,
  tag custom zoo_tag,
  v1, vn at level 200,
  format "'[hv' ’ tag [  '/  ' '[' v1 ']' '/' ,  .. '/' ,  '[' vn ']'  '/' ] ']'"
): expr_scope.
Notation "‘ tag [ v1 , .. , vn ]" := (
  ValBlock
    (Generative None)
    tag
    (@cons val v1%V .. (@cons val vn%V (@nil val)) ..)
)(at level 2,
  tag custom zoo_tag,
  v1, vn at level 200,
  format "'[hv' ‘ tag [  '/  ' '[' v1 ']' '/' ,  .. '/' ,  '[' vn ']'  '/' ] ']'"
): val_scope.

Notation "‘ tag '@[' e1 , .. , en ]" := (
  Block
    ImmutableGenerativeStrong
    tag
    (@cons expr e1%E .. (@cons expr en%E (@nil expr)) ..)
)(at level 2,
  tag custom zoo_tag,
  e1, en at level 200,
  format "'[hv' ‘ tag @[  '/  ' '[' e1 ']' '/' ,  .. '/' ,  '[' en ']'  '/' ] ']'"
) : expr_scope.
Notation "’ tag @ bid [ v1 , .. , vn ]" := (
  Val (
    ValBlock
      (Generative (Some bid))
      tag
      (@cons val v1%V .. (@cons val vn%V (@nil val)) ..)
  )
)(at level 2,
  tag custom zoo_tag,
  bid at level 1,
  v1, vn at level 200,
  format "'[hv' ’ tag @ bid [  '/  ' '[' v1 ']' '/' ,  .. '/' ,  '[' vn ']'  '/' ] ']'"
): expr_scope.
Notation "‘ tag @ bid [ v1 , .. , vn ]" := (
  ValBlock
    (Generative (Some bid))
    tag
    (@cons val v1%V .. (@cons val vn%V (@nil val)) ..)
)(at level 2,
  tag custom zoo_tag,
  bid at level 1,
  v1, vn at level 200,
  format "'[hv' ‘ tag @ bid [  '/  ' '[' v1 ']' '/' ,  .. '/' ,  '[' vn ']'  '/' ] ']'"
): val_scope.

Notation "( v1 , v2 , .. , vn )" := (
  Val (
    ValBlock
      Nongenerative
      Tag0
      (@cons val v1%V (@cons val v2%V .. (@cons val vn%V (@nil val)) ..))
  )
)(at level 0,
  only printing
) : expr_scope.
Notation "( e1 , e2 , .. , en )" := (
  Block
    ImmutableNongenerative
    Tag0
    (@cons expr e1%E (@cons expr e2%E .. (@cons expr en%E (@nil expr)) ..))
)(at level 0
) : expr_scope.
Notation "( v1 , v2 , .. , vn )" := (
  ValBlock
    Nongenerative
    Tag0
    (@cons val v1%V (@cons val v2%V .. (@cons val vn%V (@nil val)) ..))
)(at level 0
) : val_scope.
Notation "()" := (
  Unit
) : expr_scope.
Notation "()" :=
  ValUnit
: val_scope.

Notation "[ ] -> e" := (
  @pair pattern expr
    ( Build_pattern
        (in_type "list" Tag0)
        (@nil binder)
        BAnon
    )
    e%E
)(in custom zoo_branch at level 200,
  e constr at level 200,
  format "[ ]  ->  '/    ' '[' e ']'"
).
Notation "[ ] '𝗮𝘀' x -> e" := (
  @pair pattern expr
    ( Build_pattern
        (in_type "list" Tag0)
        (@nil binder)
        (BNamed x%string)
    )
    e%E
)(in custom zoo_branch at level 200,
  x constr at level 1,
  e constr at level 200,
  format "[ ]  '𝗮𝘀'  x  ->  '/    ' '[' e ']'"
).
Notation "x1 :: x2 -> e" := (
  @pair pattern expr
    ( Build_pattern
        (in_type "list" Tag1)
        (@cons binder x1%binder (@cons binder x2%binder (@nil binder)))
        BAnon
    )
    e%E
)(in custom zoo_branch at level 200,
  x1 constr at level 1,
  x2 constr at level 1,
  e constr at level 200,
  format "x1  ::  x2  ->  '/    ' '[' e ']'"
).
Notation "x1 :: x2 '𝗮𝘀' y -> e" := (
  @pair pattern expr
    ( Build_pattern
        (in_type "list" Tag1)
        (@cons binder x1%binder (@cons binder x2%binder (@nil binder)))
        (BNamed y%string)
    )
    e%E
)(in custom zoo_branch at level 200,
  x1 constr at level 1,
  x2 constr at level 1,
  y constr at level 1,
  e constr at level 200,
  format "x1  ::  x2  '𝗮𝘀'  y  ->  '/    ' '[' e ']'"
).
Notation "tag -> e" := (
  @pair pattern expr
    ( Build_pattern
        tag
        (@nil binder)
        BAnon
    )
    e%E
)(in custom zoo_branch at level 200,
  tag custom zoo_tag,
  e constr at level 200,
  format "tag  ->  '/    ' '[' e ']'"
).
Notation "tag '𝗮𝘀' x -> e" := (
  @pair pattern expr
    ( Build_pattern
        tag
        (@nil binder)
        (BNamed x%string)
    )
    e%E
)(in custom zoo_branch at level 200,
  tag custom zoo_tag,
  x constr at level 1,
  e constr at level 200,
  format "tag  '𝗮𝘀'  x  ->  '/    ' '[' e ']'"
).
Notation "tag '𝗮𝘀:' x -> e" := (
  @pair pattern expr
    ( Build_pattern
        tag
        (@nil binder)
        x%binder
    )
    e%E
)(in custom zoo_branch at level 200,
  tag custom zoo_tag,
  x constr at level 1,
  e constr at level 200,
  format "tag  '𝗮𝘀:'  x  ->  '/    ' '[' e ']'"
).
Notation "tag x1 .. xn -> e" := (
  @pair pattern expr
    ( Build_pattern
        tag
        (@cons binder x1%binder .. (@cons binder xn%binder (@nil binder)) ..)
        BAnon
    )
    e%E
)(in custom zoo_branch at level 200,
  tag custom zoo_tag,
  x1 constr at level 1,
  xn constr at level 1,
  e constr at level 200,
  format "tag  x1  ..  xn  ->  '/    ' '[' e ']'"
).
Notation "tag x1 .. xn '𝗮𝘀' y -> e" := (
  @pair pattern expr
    ( Build_pattern
        tag
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
  format "tag  x1  ..  xn  '𝗮𝘀'  y  ->  '/    ' '[' e ']'"
).
Notation "tag x1 .. xn '𝗮𝘀:' y -> e" := (
  @pair pattern expr
    ( Build_pattern
        tag
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
  format "tag  x1  ..  xn  '𝗮𝘀:'  y  ->  '/    ' '[' e ']'"
).

Notation "'𝗺𝗮𝘁𝗰𝗵' e '𝘄𝗶𝘁𝗵' | br_1 | .. | br_n '𝗲𝗻𝗱'" := (
  Match
    e%E
    BAnon
    Fail
    (@cons branch br_1 (.. (@cons branch br_n (@nil branch)) ..))
)(e at level 200,
  br_1 custom zoo_branch at level 200,
  br_n custom zoo_branch at level 200,
  format "'[v' '[hv' '𝗺𝗮𝘁𝗰𝗵'  '/  ' '[' e ']'  '/' '𝘄𝗶𝘁𝗵'  ']' '/' |  br_1  '/' |  ..  '/' |  br_n  '/' '𝗲𝗻𝗱' ']'"
) : expr_scope.
Notation "'𝗺𝗮𝘁𝗰𝗵' e '𝘄𝗶𝘁𝗵' br_1 | .. | br_n '𝗲𝗻𝗱'" := (
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
Notation "'𝗺𝗮𝘁𝗰𝗵' e0 '𝘄𝗶𝘁𝗵' | br_1 | .. | br_n | ⎽ -> e1 '𝗲𝗻𝗱'" := (
  Match
    e0%E
    BAnon
    e1%E
    (@cons branch br_1 (.. (@cons branch br_n (@nil branch)) ..))
)(e0, e1 at level 200,
  br_1 custom zoo_branch at level 200,
  br_n custom zoo_branch at level 200,
  format "'[v' '[hv' 𝗺𝗮𝘁𝗰𝗵  '/  ' '[' e0 ']'  '/' '𝘄𝗶𝘁𝗵'  ']' '/' |  br_1  '/' |  ..  '/' |  br_n  '/' |  ⎽  ->  '/    ' '[' e1 ']'  '/' '𝗲𝗻𝗱' ']'"
) : expr_scope.
Notation "'𝗺𝗮𝘁𝗰𝗵' e0 '𝘄𝗶𝘁𝗵' br_1 | .. | br_n | ⎽ -> e1 '𝗲𝗻𝗱'" := (
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
Notation "'𝗺𝗮𝘁𝗰𝗵' e0 '𝘄𝗶𝘁𝗵' | br_1 | .. | br_n | ⎽ '𝗮𝘀' x -> e1 '𝗲𝗻𝗱'" := (
  Match
    e0%E
    (BNamed x%string)
    e1%E
    (@cons branch br_1 (.. (@cons branch br_n (@nil branch)) ..))
)(e0, e1 at level 200,
  br_1 custom zoo_branch at level 200,
  br_n custom zoo_branch at level 200,
  x at level 1,
  format "'[v' '[hv' 𝗺𝗮𝘁𝗰𝗵  '/  ' '[' e0 ']'  '/' '𝘄𝗶𝘁𝗵'  ']' '/' |  br_1  '/' |  ..  '/' |  br_n  '/' |  ⎽  '𝗮𝘀'  x  ->  '/    ' '[' e1 ']'  '/' '𝗲𝗻𝗱' ']'"
) : expr_scope.
Notation "'𝗺𝗮𝘁𝗰𝗵' e0 '𝘄𝗶𝘁𝗵' br_1 | .. | br_n | ⎽ 'as' x -> e1 '𝗲𝗻𝗱'" := (
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
Notation "'𝗺𝗮𝘁𝗰𝗵' e0 '𝘄𝗶𝘁𝗵' | br_1 | .. | br_n | ⎽ '𝗮𝘀:' x -> e1 '𝗲𝗻𝗱'" := (
  Match
    e0%E
    x%binder
    e1%E
    (@cons branch br_1 (.. (@cons branch br_n (@nil branch)) ..))
)(e0, e1 at level 200,
  br_1 custom zoo_branch at level 200,
  br_n custom zoo_branch at level 200,
  x at level 1,
  format "'[v' '[hv' 𝗺𝗮𝘁𝗰𝗵  '/  ' '[' e0 ']'  '/' '𝘄𝗶𝘁𝗵'  ']' '/' |  br_1  '/' |  ..  '/' |  br_n  '/' |  ⎽  '𝗮𝘀:'  x  ->  '/    ' '[' e1 ']'  '/' '𝗲𝗻𝗱' ']'"
) : expr_scope.
Notation "'𝗺𝗮𝘁𝗰𝗵' e0 '𝘄𝗶𝘁𝗵' br_1 | .. | br_n | ⎽ '𝗮𝘀:' x -> e1 '𝗲𝗻𝗱'" := (
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

Notation "'𝗹𝗲𝘁' ‘ tag x1 .. xn = e1 '𝗶𝗻' e2" := (
  Match
    e1%E
    BAnon
    Fail
    ( @cons branch
        ( @pair pattern expr
            ( Build_pattern
                tag
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
  format "'[v' '[hv' '𝗹𝗲𝘁'  ‘ tag  x1  ..  xn  =  '/  ' '[' e1 ']'  '/' '𝗶𝗻'  ']' '/' e2 ']'"
) : expr_scope.
Notation "'𝗹𝗲𝘁' x0 , x1 , .. , xn = e1 '𝗶𝗻' e2" := (
  Match
    e1%E
    BAnon
    Fail
    ( @cons branch
        ( @pair pattern expr
            ( Build_pattern
                Tag0
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
  format "'[v' '[hv' '𝗹𝗲𝘁'  x0 ,  x1 ,  .. ,  xn  =  '/  ' '[' e1 ']'  '/' '𝗶𝗻'  ']' '/' e2 ']'"
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
  location۰add l (Z.of_nat fld)
)(at level 2,
  fld custom zoo_field,
  left associativity,
  format "l .[ fld ]"
) : stdpp_scope.
Notation "v .[ fld ]" := (
  Val
    ( ValBlock
        Nongenerative
        (in_type "atomic_loc" Tag0)
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
    ImmutableNongenerative
    (in_type "atomic_loc" Tag0)
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
  ValBlock
    Nongenerative
    (in_type "atomic_loc" Tag0)
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
  in_type "ref" 0
)(in custom zoo_field
).
Notation "'𝗿𝗲𝗳' e" := (
  Block
    Mutable
    (in_type "ref" Tag0)
    (@cons expr e%E (@nil expr))
)(at level 10
) : expr_scope.
Notation "! e" := (
  Load e%E (Val (ValInt (Z.of_nat (in_type "ref" 0))))
)(at level 9,
  right associativity,
  format "! e"
) : expr_scope.
Notation "e1 <- e2" := (
  Store e1%E (Val (ValInt (Z.of_nat (in_type "ref" 0)))) e2%E
)(at level 80,
  format "'[hv' '[hv' '[' e1 ']'  '/  ' <-  ']' '/  ' '[' e2 ']' ']'"
) : expr_scope.

Notation "'None'" := (
  in_type "option" Tag0
)(in custom zoo_tag
).
Notation "'Some'" := (
  in_type "option" Tag1
)(in custom zoo_tag
).

Notation "[ ]" := (
  Val (
    ValBlock
      Nongenerative
      (in_type "list" Tag0)
      (@nil val)
  )
)(format "[ ]"
) : expr_scope.
Notation "[ ]" := (
  ValBlock
    Nongenerative
    (in_type "list" Tag0)
    (@nil val)
)(format "[ ]"
) : val_scope.
Notation "e1 :: e2" := (
  Block
    ImmutableNongenerative
    (in_type "list" Tag1)
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
  ValBlock
    Nongenerative
    (in_type "list" Tag1)
    ( @cons val v1%V
        ( @cons val v2%V
            (@nil val)
        )
    )
)(at level 60,
  right associativity,
  format "v1  ::  v2"
) : val_scope.
