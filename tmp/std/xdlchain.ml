type 'a t =
  { xdlchain_prev: 'a t;
    xdlchain_next: 'a t;
    xdlchain_data: 'a;
  }
