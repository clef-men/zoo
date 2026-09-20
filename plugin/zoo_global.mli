type kind =
  | Iris
  | Zoo

type field =
  { name: string
  ; theory: Libnames.qualid
  ; arguments: Constrexpr.constr_expr list
  ; kind: kind
  }

type spec =
  { base: Libnames.qualid
  ; parameters: Constrexpr.local_binder_expr list
  ; fields: field list
  }

val default_base :
  Libnames.qualid

val main :
  spec -> unit
