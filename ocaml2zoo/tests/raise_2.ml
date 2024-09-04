let test1 b =
  if not b then
    raise (Invalid_argument "")

let test2 b =
  if not b then
    invalid_arg ""

let test3 b =
  if not b then
    failwith ""
