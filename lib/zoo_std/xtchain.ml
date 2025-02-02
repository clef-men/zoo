type 'a t =
  { mutable xtchain_next: 'a t;
    mutable xtchain_data: 'a;
  }
