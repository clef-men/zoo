type 'a t =
  | Gnone
  | Gsome of 'a [@generative]
