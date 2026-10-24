include Stdlib.String

let starts_with_uppercase t =
  Char.is_uppercase (get t 0)
