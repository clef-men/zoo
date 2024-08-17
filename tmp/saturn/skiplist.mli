type ('k, 'v) t

val create :
  int -> ('k -> 'k -> int) -> ('k, 'v) t

val find :
  ('k, 'v) t -> 'k -> 'v option

val mem :
  ('k, 'v) t -> 'k -> bool

val add :
  ('k, 'v) t -> 'k -> 'v -> bool

val remove :
  ('k, 'v) t -> 'k -> bool
