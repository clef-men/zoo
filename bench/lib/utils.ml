let get_int_param p =
  match int_of_string (Unix.getenv p) with
  | n -> Some n
  | exception _ -> None
