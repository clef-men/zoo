type mutability =
  | Immutable
  | Mutable

type declaration =
  | Record of mutability * string list
  | Variant of string list

val synterp :
  locality:Hints.hint_locality ->
  qualified:bool ->
  Libnames.qualid ->
  declaration ->
  Metasyntax.notation_interpretation_decl list

val interp :
  locality:Hints.hint_locality ->
  Metasyntax.notation_interpretation_decl list ->
  unit
