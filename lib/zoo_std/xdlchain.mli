type 'a t =
  { mutable xdlchain_prev: 'a t;
    mutable xdlchain_next: 'a t;
    mutable xdlchain_data: 'a;
  }
