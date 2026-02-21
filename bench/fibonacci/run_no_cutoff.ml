open Bench

module Make
  (Pool : Pool.S)
= struct
  let rec main n ctx =
    if n <= 2 then
      n
    else
      let fut1 = Pool.async ctx @@ main (n - 1) in
      let res2 = main (n - 2) ctx in
      Pool.wait ctx fut1 + res2
end

let pool =
  Pool.impl_of_string Sys.argv.(1)

let num_domain =
  let default = Domain.recommended_domain_count () - 1 in
  Option.value ~default (Utils.get_int_param "EXTRA_DOMAINS")

let input =
  int_of_string Sys.argv.(2)

let () =
  let (module Pool) = pool in
  let module M = Make(Pool) in
  let pool = Pool.create ~num_domain () in
  let _ = Pool.run pool (M.main input) in
  Pool.kill pool
