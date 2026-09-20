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
  { parameters: Constrexpr.local_binder_expr list
  ; fields: field list
  }

val main :
  spec -> unit
