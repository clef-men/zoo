open Bench

let rec seq n =
  if n <= 1 then
    n
  else
    seq (n - 1) + seq (n - 2)

module Make
  (Pool : Pool.S)
= struct
  let rec main ~cutoff n ctx =
    if n <= cutoff then
      seq n
    else
      let fut1 = Pool.async ctx @@ main ~cutoff (n - 1) in
      let fut2 = Pool.async ctx @@ main ~cutoff (n - 2) in
      Pool.wait ctx fut1 + Pool.wait ctx fut2
end

let pool : (module Pool.S) =
  let open Pool in
  match Sys.argv.(1) with
  | "parabs" ->
      (module Parabs)
  | "domainslib" ->
      (module Domainslib)
  | "moonpool-fifo" ->
      (module Moonpool_fifo)
  | "moonpool-ws" ->
      (module Moonpool_ws)
  | _ ->
      failwith "illegal method"

let cutoff =
  int_of_string Sys.argv.(2)

let input =
  int_of_string Sys.argv.(3)

let num_domains =
  match Sys.argv.(4) with
  | num_domains ->
      int_of_string num_domains
  | exception Invalid_argument _ ->
      Domain.recommended_domain_count () - 1

let () =
  let (module Pool) = pool in
  let module M = Make(Pool) in
  let pool = Pool.create ~num_domains () in
  let _ = Pool.run pool (M.main ~cutoff input) in
  Pool.kill pool
