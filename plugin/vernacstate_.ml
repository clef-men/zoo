include Vernacstate

let freeze_full_state_and_try fn =
  let state = freeze_full_state () in
  try
    fn state
  with exn ->
    unfreeze_full_state state ;
    raise exn
