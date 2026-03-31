open Bench

module Make
  (Pool : Pool.S)
= struct
  let miniwork _ctx _i =
    Unix.sleepf (1. /. 1_000_000.); (* 1us *)
    ()

  let main n ctx =
    for _i = 1 to n do
      (* wake many workers up *)
      for _w = 1 to 16 do
        ignore (Pool.async ctx miniwork)
      done;
      (* then they can go back to sleep *)
      Unix.sleepf (1. /. 1000.); (* 1ms *)
    done;
end

let pool =
  Pool.impl_of_string Sys.argv.(1)

let input =
  int_of_string Sys.argv.(2)

let num_domain =
  let default = Domain.recommended_domain_count () - 1 in
  Option.value ~default (Utils.get_int_param "EXTRA_DOMAINS")

let () =
  let (module Pool) = pool in
  let module M = Make(Pool) in
  let pool = Pool.create ~num_domain () in
  let _ = Pool.run pool (M.main input) in
  Pool.kill pool
