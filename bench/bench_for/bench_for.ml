open Bench

let work _ctx _i =
  for _ = 1 to 100 do
    ()
  done

module Make
  (Pool : Pool.S)
= struct
  let par ~cutoff n ctx =
    Pool.for_ ctx work ~beg:0 ~end_:n ~chunk:cutoff
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
  let _ = Pool.run pool (M.par ~cutoff input) in
  Pool.kill pool
