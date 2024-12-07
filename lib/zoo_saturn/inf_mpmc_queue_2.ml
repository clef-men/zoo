type 'a t =
  { data: 'a Optional.t Inf_array.t;
    mutable front: int [@atomic];
    mutable back: int [@atomic];
  }

let create () =
  { data= Inf_array.create Optional.Nothing;
    front= 0;
    back= 0;
  }

let rec push t v =
  let i = Atomic.Loc.fetch_and_add [%atomic.loc t.back] 1 in
  if not @@ Inf_array.cas t.data i Nothing (Something v) then
    push t v

let rec pop t =
  let i = Atomic.Loc.fetch_and_add [%atomic.loc t.front] 1 in
  match Inf_array.xchg t.data i Anything with
  | Nothing ->
      Domain.cpu_relax () ;
      pop t
  | Anything ->
      assert false
  | Something v ->
      Inf_array.set t.data i Anything ;
      v
