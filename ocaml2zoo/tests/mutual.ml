let rec test3 x =
  x
and test4 x =
  x

let rec test5 x =
  test6 x
and test6 x =
  test5 x
