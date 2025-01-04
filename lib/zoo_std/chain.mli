type 'a t =
  { mutable chain_next: 'a t;
    mutable chain_data: 'a;
  }
