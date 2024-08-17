type 'a t

val create :
  unit → 'a t

val make :
  int → 'a → 'a t

val initi :
  int → (int → 'a) → 'a t

val size :
  'a t → int
val capacity :
  'a t → int

val is_empty :
  'a t → bool

val get :
  'a t → int → 'a
val set :
  'a t → int → 'a → unit

val reserve :
  'a t → int → unit
val reserve_extra :
  'a t → int → unit

val push :
  'a t → 'a → unit

val pop :
  'a t → 'a

val fit_capacity :
  'a t → unit

val reset :
  'a t → unit
