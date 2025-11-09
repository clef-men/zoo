val for_ :
  Pool.context ->
  int ->
  int ->
  int option ->
  (int -> int -> unit) Pool.task ->
  unit

val for_each :
  Pool.context ->
  int ->
  int ->
  int option ->
  (int -> unit) Pool.task ->
  unit

val fold :
  Pool.context ->
  int ->
  int ->
  int option ->
  (int -> 'a) Pool.task ->
  ('a -> 'a -> 'a) ->
  'a ->
  'a

val find :
  Pool.context ->
  int ->
  int ->
  int option ->
  (int -> bool) Pool.task ->
  int option
