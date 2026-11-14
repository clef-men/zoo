type field_kind =
  | Normal
  | Sharp

type field =
  { kind: field_kind
  ; name: string
  ; typ: Constrexpr.constr_expr
  }

val interp :
  locality:Hints.hint_locality ->
  field list ->
  unit
