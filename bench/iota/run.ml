open Bench

module Make
  (Pool : Pool.S)
= struct
  let main ~size ?cutoff ctx =
    let arr = Array.make size 0 in
    for _ = 1 to 100 do
      Pool.for_each ctx ~beg:0 ~end_:size ?chunk:cutoff @@ fun _ctx i ->
        Array.unsafe_set arr i i
    done
end

let pool =
  Pool.impl_of_string Sys.argv.(1)

let size =
  int_of_string Sys.argv.(2)

let num_worker =
  let default = Domain.recommended_domain_count () - 1 in
  Option.value ~default (Utils.get_int_param "EXTRA_DOMAINS")

let cutoff = Utils.get_int_param "CUTOFF"

let () =
  let (module Pool) = pool in
  let module M = Make(Pool) in
  Pool.run ~num_worker (M.main ~size ?cutoff)
