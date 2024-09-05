include Stdlib.List

let rec make n v =
  if n <= 0 then
    []
  else
    v :: make (n - 1) v
