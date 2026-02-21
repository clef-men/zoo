(* ocamlopt fib_sequential.ml -o fib_sequential.ml.exe *)

let rec fib acc n =
  if n < 2 then (acc + n)
  else
    let acc = fib acc (n - 1) in
    fib acc (n - 2)

let () =
 let n =
   try int_of_string Sys.argv.(1)
   with _ ->
     prerr_endline "Missing a command-line integer argument (N)";
     exit 2
 in
 let res = fib 0 n in
 Printf.printf "%d\n" res
