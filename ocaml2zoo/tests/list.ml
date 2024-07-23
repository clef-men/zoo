let test1 () =
  let _ = [] in
  let _ = 0 :: [] in
  let _ = [1] in
  ()

let test2 xs =
  match xs with
  | [] ->
      ()
  | x :: xs ->
      let _ = x in
      let _ = xs in
      ()
