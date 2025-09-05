open Bench

module Make
  (Pool : Pool.S)
= struct
  let main ~sz ?cutoff ctx =
    let arr = Array.make sz 0 in
    for _ = 1 to 100 do
      Pool.for_ ctx ?chunk:cutoff ~beg:0 ~end_:sz @@ fun _ctx i ->
        Array.unsafe_set arr i i
    done
end

let pool =
  Pool.impl_of_string Sys.argv.(1)

let size =
  int_of_string Sys.argv.(2)

let num_domains =
  let default = Domain.recommended_domain_count () - 1 in
  Utils.get_int_param "EXTRA_DOMAINS" ~default

let cutoff =
  match Utils.get_int_param "CUTOFF" ~default:0 with
    | 0 -> None
    | n -> assert (n > 0); Some n

let () =
  let (module Pool) = pool in
  let module M = Make(Pool) in
  let pool = Pool.create ~num_domains () in
  let _ = Pool.run pool (M.main ~sz:size ?cutoff) in
  Pool.kill pool
