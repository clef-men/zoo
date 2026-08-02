type 'a t =
  { mutable next: 'a t
  ; mutable data: 'a
  }
