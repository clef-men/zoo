include module type of struct
  include Vernacstate
end

val freeze_full_state_and_try :
  (t -> unit) -> unit
