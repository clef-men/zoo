include module type of struct
  include Stdlib.Option
end

val get_lazy :
  (unit -> 'a) -> 'a t -> 'a
