type 'a loc

val get :
  'a loc -> 'a

val cas :
  ('a loc * 'a * 'a) list -> bool
