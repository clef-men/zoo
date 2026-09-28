include Vernacinterp

let interp ~state vernac =
  interp
    ~intern:fs_intern
    ~verbosely:(not !Flags.quiet)
    ~st:state
    vernac

let interp ~state vernacs =
  List.fold_left (fun state (locality, vernac) ->
    let vernac = Vernacexpr.VernacSynPure vernac in
    let vernac =
      let locality =
        locality |> Option.map @@ fun locality ->
          ( locality |> Utils.locality_to_string
          , Attributes.VernacFlagEmpty
          ) |> CAst.make
      in
      let attrs = locality |> Stdlib.Option.to_list in
      Vernacexpr.{ control= []; attrs; expr= vernac }
    in
    let vernac = vernac |> CAst.make in
    interp ~state vernac
  ) state vernacs
