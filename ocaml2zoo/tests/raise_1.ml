let test1 () =
  raise (Invalid_argument "")

let test2 () =
  invalid_arg ""

let test3 () =
  failwith ""
