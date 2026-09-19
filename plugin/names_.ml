include Names

let lname_of_string str =
  str
  |> Names.Id.of_string
  |> Names.Name.mk_name
  |> CAst.make
