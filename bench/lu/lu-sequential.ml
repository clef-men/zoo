(* ocamlopt lu-sequential.ml -o lu-sequential.ml.exe *)

let create_rand sz =
  Array.init sz @@ fun _ ->
  Array.init sz @@ fun _ ->
  float (Random.bits ())

let lu m sz =
  for k = 0 to sz - 2 do
    for i = k + 1 to sz - 1 do
      let factor = m.(i).(k) in
      for j = k + 1 to sz - 1 do
        m.(i).(j) <- m.(i).(j) -. factor *. m.(k).(j);
      done;
      m.(i).(k) <- factor;
    done
  done

let () =
  let sz =
    try int_of_string Sys.argv.(1)
    with _ ->
      Printf.eprintf "Missing a command-line integer argument (size)\n";
      exit 2
  in
  let m = create_rand sz in
  lu m sz
