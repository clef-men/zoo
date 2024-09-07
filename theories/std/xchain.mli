type 'a t =
  { mutable xchain_next: 'a t;
    mutable xchain_data: 'a;
  }
