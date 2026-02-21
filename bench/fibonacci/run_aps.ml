open Bench

let rec fib_aps acc n =
  if n < 2 then (acc + n)
  else
    let acc = fib_aps acc (n - 1) in
    fib_aps acc (n - 2)

module Make
  (Pool : Pool.S)
= struct
  let rec main ~cutoff n ctx =
    if n <= cutoff then
      fib_aps 0 n
    else
      let fut1 = Pool.async ctx @@ main ~cutoff (n - 1) in
      let res2 = main ~cutoff (n - 2) ctx in
      Pool.wait ctx fut1 + res2
end

let pool =
  Pool.impl_of_string Sys.argv.(1)

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
  let (module Pool) = pool in
  let module M = Make(Pool) in
  let pool = Pool.create ~num_domain () in
  let _ = Pool.run pool (M.main ~cutoff input) in
  Pool.kill pool
