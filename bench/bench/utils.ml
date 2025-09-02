let get_int_param p ~default =
  try int_of_string (Unix.getenv p)
  with _ -> default
