(* ocamlopt fib_sequential.ml -o fib_sequential.ml.exe *)

let rec fib n =
  if n < 2 then n
  else fib (n - 1) + fib (n - 2)

let () =
 let n =
   try int_of_string Sys.argv.(1)
   with _ ->
     prerr_endline "Missing a command-line integer argument (N)";
     exit 2
 in
 let res = fib n in
 Printf.printf "%d\n" res
