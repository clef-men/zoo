type 'a t =
  { mutable prev: 'a t
  ; mutable next: 'a t
  ; mutable data: 'a
  }
