let current_unit () =
  Lib.library_dp ()
  |> Names.DirPath.repr
  |> List.hd
  |> Names.Id.to_string
