include Stdlib.Option

let get_lazy default = function
  | None ->
      default ()
  | Some x ->
      x
