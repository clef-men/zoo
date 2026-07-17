type dummy =
  unit ref

let dummy =
  ref ()

type _ proph =
  dummy

let[@inline] proph () =
  dummy
let[@inline] resolve_with x _ _ =
  x
let[@inline] resolve_silent proph v_proph =
  resolve_with ((fun () -> ()) ()) proph v_proph
let[@inline] resolve proph v_proph =
  resolve_silent proph v_proph ;
  v_proph

type id =
  dummy

let[@inline] id () =
  dummy
