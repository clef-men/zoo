open Bench

module Make
  (Pool : Pool.S)
= struct
  let main n ctx =
    let fut = Pool.async ctx (fun _ctx -> Unix.sleepf 1.) in
    for _i = 1 to n do
      Pool.async ctx (fun ctx -> Pool.wait ctx fut) |> ignore;
    done;
    Pool.wait ctx fut
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
