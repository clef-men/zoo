open Bench

module Make
  (Pool : Pool.S)
= struct
  let miniwork _ctx _i =
    for _ = 1 to 1024 do
      Sys.opaque_identity ()
    done

  let main n ctx =
    for _i = 1 to n do
      (* wake many workers up *)
      Pool.for_each ctx ~beg:0 ~end_:42 ~chunk:1 miniwork;
      (* then they can go back to sleep *)
      for _ = 1 to 10 do
        miniwork ctx ()
      done
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
