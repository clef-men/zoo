type ('k, 'v) t

val create :
  hash:('k -> int) -> equal:('k -> 'k -> bool) -> ('k, 'v) t

val mem :
  ('k, 'v) t -> 'k -> bool

val find :
  ('k, 'v) t -> 'k -> 'v option

val add :
  ('k, 'v) t -> 'k -> 'v -> bool

val remove :
  ('k, 'v) t -> 'k -> bool
