[@@@zoo.ignore]

type ('k, 'v) t

val create :
  ('k -> int) -> ('k -> 'k -> bool) -> ('k, 'v) t

val find :
  ('k, 'v) t -> 'k -> 'v option

val mem :
  ('k, 'v) t -> 'k -> bool

val add :
  ('k, 'v) t -> 'k -> 'v -> bool

val remove :
  ('k, 'v) t -> 'k -> bool
