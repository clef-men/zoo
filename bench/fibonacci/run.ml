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

let pool =
  Pool.impl_of_string Sys.argv.(1)

let cutoff =
  int_of_string Sys.argv.(2)

let input =
  int_of_string Sys.argv.(3)

let num_domains =
  let default = Domain.recommended_domain_count () - 1 in
  Option.value ~default (Utils.get_int_param "EXTRA_DOMAINS")

let () =
  let (module Pool) = pool in
  let module M = Make(Pool) in
  let pool = Pool.create ~num_domains () in
  let _ = Pool.run pool (M.main ~cutoff input) in
  Pool.kill pool
