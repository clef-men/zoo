include Names

module Id = struct
  include Id

  let map fn t =
    t
    |> Names.Id.to_string
    |> fn
    |> Names.Id.of_string
end

let lident_of_string str =
  str
  |> Names.Id.of_string
  |> CAst.make

let lname_of_ident id =
  id
  |> Names.Name.mk_name
  |> CAst.make
let lname_of_string str =
  str
  |> Names.Id.of_string
  |> lname_of_ident
