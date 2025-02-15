type 'a t =
  | Gnothing
  | Ganything
  | Gsomething of 'a [@generative]
