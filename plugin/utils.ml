let current_unit () =
  Lib.library_dp ()
  |> Names.DirPath.repr
  |> List.hd
  |> Names.Id.to_string

let locality_to_string (locality : Libobject.locality) =
  match locality with
  | Local ->
      "local"
  | Export ->
      "export"
  | SuperGlobal ->
      "global"
