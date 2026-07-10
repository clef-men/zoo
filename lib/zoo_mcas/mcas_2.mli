type 'a loc

val make :
  'a -> 'a loc

val get :
  'a loc -> 'a

val mcas :
  ('a loc * 'a) list -> ('a loc * 'a * 'a) list -> bool
