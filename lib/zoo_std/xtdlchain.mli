type 'a t =
  { mutable xtdlchain_prev: 'a t;
    mutable xtdlchain_next: 'a t;
    mutable xtdlchain_data: 'a;
  }
