type variable =
  string

type binder =
  variable option

type field =
  string

type tag =
  string

type rec_flag =
  Asttypes.rec_flag

type concreteness =
  | Concrete
  | Abstract

type typ =
  | Type_product of field list
  | Type_record of field list
  | Type_variant of tag list

type pattern =
  | Pat_var of variable
  | Pat_tuple of binder list
  | Pat_constr of tag * binder list

type unop =
  | Unop_neg
  | Unop_minus

type binop =
  | Binop_plus | Binop_minus | Binop_mult | Binop_quot | Binop_rem
  | Binop_eq | Binop_ne | Binop_le | Binop_lt | Binop_ge | Binop_gt

type expression =
  | Global of variable
  | Local of variable
  | Bool of bool
  | Int of int
  | Let of pattern * expression * expression
  | Letrec of rec_flag * variable * binder list * expression * expression
  | Seq of expression * expression
  | Fun of binder list * expression
  | Apply of expression * expression list
  | Unop of unop * expression
  | Binop of binop * expression * expression
  | If of expression * expression * expression option
  | For of binder * expression * expression * expression
  | Alloc of expression * expression
  | Tuple of expression list
  | Ref of expression
  | Record of expression array
  | Constr of concreteness * tag * expression list
  | Proj of expression * field
  | Match of expression * branch list * fallback option
  | Ref_get of expression
  | Ref_set of expression * expression
  | Record_get of expression * field
  | Record_set of expression * field * expression
  | Get_tag of expression
  | Get_size of expression
  | Load of expression * expression
  | Store of expression * expression * expression
  | Fail
  | Yield
  | Proph
  | Resolve of expression * expression * expression
and branch =
  { branch_tag: tag;
    branch_binders: binder list;
    branch_as: binder;
    branch_expr: expression;
  }
and fallback =
  { fallback_as: binder;
    fallback_expr: expression;
  }

type value =
  | Val_int of int
  | Val_rec of binder * binder list * expression
  | Val_opaque

type definition =
  | Type of typ
  | Val of value

type structure =
  { modname: string;
    dependencies: string list;
    definitions: (variable * definition) list;
  }

val structure_types :
  structure -> (variable * typ) list
val structure_values :
  structure -> (variable * value) list
