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

let push t v =
  let i = Atomic.Loc.fetch_and_add [%atomic.loc t.back] 1 in
  Inf_array.set t.data i (Something v)

let rec pop t i =
  match Inf_array.get t.data i with
  | Nothing ->
      Domain.cpu_relax () ;
      pop t i
  | Anything ->
      assert false
  | Something v ->
      Inf_array.set t.data i Anything ;
      v
let pop t =
  let i = Atomic.Loc.fetch_and_add [%atomic.loc t.front] 1 in
  pop t i
