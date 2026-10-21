open Ltac_plugin

module Kind : sig
  type t =
    | Timeless
    | Persistent
end

module Modifier : sig
  type t =
    | None
    | Discarded
end

val interp :
  locality:Hints.hint_locality ->
  kind:Kind.t ->
  modifier:Modifier.t ->
  Libnames.qualid ->
  unit
