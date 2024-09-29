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
  | Revealed

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
  | Binop_and | Binop_or
  | Binop_structeq | Binop_structne

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
  | Record of expression list
  | Constr of concreteness * tag * expression list
  | Proj of expression * field
  | Match of expression * branch list * fallback option
  | Ref_get of expression
  | Ref_set of expression * expression
  | Record_get of expression * field
  | Record_set of expression * field * expression
  | Get_tag of expression
  | Get_size of expression
  | Atomic_loc of expression * field
  | Load of expression * expression
  | Store of expression * expression * expression
  | Xchg of expression * expression
  | Cas of expression * expression * expression
  | Faa of expression * expression
  | Fail
  | Yield
  | Proph
  | Resolve of expression * expression * expression
  | Id
and branch =
  { branch_tag: tag;
    branch_fields: binder list;
    branch_as: binder;
    branch_expr: expression;
  }
and fallback =
  { fallback_as: binder;
    fallback_expr: expression;
  }

type value =
  | Val_expr of expression
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

let rec expression_is_value = function
  | Global _
  | Bool _
  | Int _
  | Fun _ ->
      true
  | Tuple exprs
  | Constr (Abstract, _, exprs) ->
      List.for_all expression_is_value exprs
  | Local _
  | Let _
  | Letrec _
  | Seq _
  | Apply _
  | Unop _
  | Binop _
  | If _
  | For _
  | Alloc _
  | Ref _
  | Record _
  | Constr (_, _, _)
  | Proj _
  | Match _
  | Ref_get _
  | Ref_set _
  | Record_get _
  | Record_set _
  | Get_tag _
  | Get_size _
  | Atomic_loc _
  | Load _
  | Store _
  | Xchg _
  | Cas _
  | Faa _
  | Fail
  | Yield
  | Proph
  | Resolve _
  | Id ->
      false

let structure_types str =
  List.filter_map (fun (var, def) -> match def with Type ty -> Some (var, ty) | _ -> None) str.definitions
let structure_values str =
  List.filter_map (fun (var, def) -> match def with Val val_ -> Some (var, val_) | _ -> None) str.definitions
