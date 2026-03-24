open Bench

(* the C++ compiler (clang++) compiles fibonacci
   in accumulator-passing style for performance,
   so we use this style manually in the OCaml
   version for fair comparison. *)
let rec fib_aps acc n =
  if n < 2 then (acc + n)
  else
    let acc = fib_aps acc (n - 1) in
    fib_aps acc (n - 2)

let fib_seq n = fib_aps 0 n

module Make
  (Pool : Pool.S)
= struct
  let rec main ~cutoff n ctx =
    if n <= cutoff then
      fib_seq n
    else
      let fut1 = Pool.async ctx @@ main ~cutoff (n - 1) in
      let res2 = main ~cutoff (n - 2) ctx in
      Pool.wait ctx fut1 + res2
end

let impl = Sys.argv.(1)

let num_domain =
  let default = Domain.recommended_domain_count () - 1 in
  Option.value ~default (Utils.get_int_param "EXTRA_DOMAINS")

let cutoff =
  match Utils.get_int_param "CUTOFF" with
    | None -> invalid_arg "This program expects a CUTOFF environment variable"
    | Some n -> n

let input =
  int_of_string Sys.argv.(2)

let () =
  match impl with
  | "taskflow" ->
     let ocamlrunparam = Option.value ~default:"" (Sys.getenv_opt "OCAMLRUNPARAM") in
     UnixLabels.execve
       ~prog:"/tmp/fibonacci-taskflow.exe"
       ~args:[|Sys.argv.(0); string_of_int input|]
       ~env:[|
         Printf.sprintf "OCAMLRUNPARAM=%s" ocamlrunparam;
         Printf.sprintf "CUTOFF=%d" cutoff;
         Printf.sprintf "NUM_THREADS=%d" (num_domain + 1);
       |]
  | pool ->
    let (module Pool) = Pool.impl_of_string pool in
    let module M = Make(Pool) in
    let pool = Pool.create ~num_domain () in
    let _ = Pool.run pool (M.main ~cutoff input) in
    Pool.kill pool
