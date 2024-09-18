let test1 =
  ()
[@@zoo.overwrite
  fun () -> ()
]

let test2 =
  ()
[@@zoo.overwrite_rec
  fun () -> test2 ()
]
