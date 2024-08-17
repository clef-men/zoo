type t =
  { random: Random.t;
    array: int array;
    index: int;
  }

let create sz =
  { random= Random.create ();
    array= Array.initi sz (fun i -> i);
    index= sz;
  }

let reset t =
  t.index <- Array.size t.array

let next t =
  let arr = t.array in
  let i = t.index in
  let j = Random.gen t.random i in
  let res = Array.unsafe_get arr j in
  let i = i - 1 in
  Array.unsafe_set arr j (Array.unsafe_get arr i) ;
  Array.unsafe_set arr i res ;
  t.index <- i ;
  res
