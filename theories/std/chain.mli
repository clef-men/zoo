type 'a t =
  { mutable chain_head: 'a;
    mutable chain_tail: 'a t;
  }
