[@@@zoo.ignore]

val for_ :
  Pool.context ->
  int ->
  int ->
  int ->
  (Pool.context -> int -> unit) ->
  unit

val divide :
  Pool.context ->
  int ->
  int ->
  (Pool.context -> int -> int -> unit) ->
  unit

val fold :
  Pool.context ->
  int ->
  int ->
  int ->
  ('a -> 'a -> 'a) ->
  (Pool.context -> int -> 'a) ->
  'a ->
  'a

val find :
  Pool.context ->
  int ->
  int ->
  int ->
  (Pool.context -> int -> bool) ->
  int option
