From iris.bi Require Import
  telescopes.

From zoo Require Import
  prelude.
From zoo.iris.program_logic Require Export
  atomic.
From zoo.program_logic Require Export
  wp.
From zoo Require Import
  options.

Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e tid E '<<<' ∃∃ y1 .. yn , β | z1 .. zn , 'RET' v ; Q '>>>'" := (
  atomic_triple
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) ..))
    (TP := TeleS (λ z1, .. (TeleS (λ zn, TeleO)) ..))
    e%E
    tid
    E
    P%I
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, β%I) ..) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app $ λ z1, .. (λ zn, Q%I) ..) ..) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app $ λ z1, .. (λ zn, (v%V : val)) ..) ..) ..)
)(at level 20,
  P, α, e, β, v, Q at level 200,
  tid custom wp_thread_id at level 200,
  E custom atomic_triple_mask at level 200,
  x1 binder,
  xn binder,
  y1 binder,
  yn binder,
  z1 binder,
  zn binder,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  ∀∀  x1  ..  xn ,  '/  ' '[' α ']'  '/' >>>  '/  ' '[' e ']'  tid E '/' <<<  '/  ' ∃∃  y1  ..  yn ,  '/  ' '[' β ']'  '/' |  z1  ..  zn ,  '/  ' RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.
Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e tid E '<<<' ∃∃ y1 .. yn , β | 'RET' v ; Q '>>>'" := (
  atomic_triple
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) ..))
    (TP := TeleO)
    e%E
    tid
    E
    P%I
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, β%I) ..) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app Q%I) ..) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app (v%V : val)) ..) ..)
)(at level 20,
  P, α, e, β, v, Q at level 200,
  tid custom wp_thread_id at level 200,
  E custom atomic_triple_mask at level 200,
  x1 binder,
  xn binder,
  y1 binder,
  yn binder,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  ∀∀  x1  ..  xn ,  '/  ' '[' α ']'  '/' >>>  '/  ' '[' e ']'  tid E '/' <<<  '/  ' ∃∃  y1  ..  yn ,  '/  ' '[' β ']'  '/' |  RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.
Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e tid E '<<<' β | z1 .. zn , 'RET' v ; Q '>>>'" := (
  atomic_triple
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
    (TB := TeleO)
    (TP := TeleS (λ z1, .. (TeleS (λ zn, TeleO)) ..))
    e%E
    tid
    E
    P%I
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app β%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app $ λ z1, .. (λ zn, Q%I) ..) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app $ λ z1, .. (λ zn, (v%V : val)) ..) ..)
)(at level 20,
  P, α, e, β, v, Q at level 200,
  tid custom wp_thread_id at level 200,
  E custom atomic_triple_mask at level 200,
  x1 binder,
  xn binder,
  z1 binder,
  zn binder,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  ∀∀  x1  ..  xn ,  '/  ' '[' α ']'  '/' >>>  '/  ' '[' e ']'  tid E '/' <<<  '/  ' '[' β ']'  '/' |  z1  ..  zn ,  '/  ' RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.
Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e tid E '<<<' β | 'RET' v ; Q '>>>'" := (
  atomic_triple
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
    (TB := TeleO)
    (TP := TeleO)
    e%E
    tid
    E
    P%I
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app β%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app Q%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app (v%V : val)) ..)
)(at level 20,
  P, α, e, β, v, Q at level 200,
  tid custom wp_thread_id at level 200,
  E custom atomic_triple_mask at level 200,
  x1 binder,
  xn binder,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  ∀∀  x1  ..  xn ,  '/  ' '[' α ']'  '/' >>>  '/  ' '[' e ']'  tid E '/' <<<  '/  ' '[' β ']'  '/' |  RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.
Notation "'<<<' P | α '>>>' e tid E '<<<' ∃∃ y1 .. yn , β | z1 .. zn , 'RET' v ; Q '>>>'" := (
  atomic_triple
    (TA := TeleO)
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) ..))
    (TP := TeleS (λ z1, .. (TeleS (λ zn, TeleO)) ..))
    e%E
    tid
    E
    P%I
    (tele_app α%I)
    (tele_app $ tele_app $ λ y1, .. (λ yn, β%I) ..)
    (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app $ λ z1, .. (λ zn, Q%I) ..) ..)
    (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app (v%V : val)) ..)
)(at level 20,
  P, α, e, β, v, Q at level 200,
  tid custom wp_thread_id at level 200,
  E custom atomic_triple_mask at level 200,
  y1 binder,
  yn binder,
  z1 binder,
  zn binder,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  '[' α ']'  '/' >>>  '/  ' '[' e ']'  tid E '/' <<<  '/  ' ∃∃  y1  ..  yn ,  '/  ' '[' β ']'  '/' |  z1  ..  zn ,  '/  ' RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.
Notation "'<<<' P | α '>>>' e tid E '<<<' ∃∃ y1 .. yn , β | 'RET' v ; Q '>>>'" := (
  atomic_triple
    (TA := TeleO)
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) ..))
    (TP := TeleO)
    e%E
    tid
    E
    P%I
    (tele_app α%I)
    (tele_app $ tele_app $ λ y1, .. (λ yn, β%I) ..)
    (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app Q%I) ..)
    (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app (v%V : val)) ..)
)(at level 20,
  P, α, e, β, v, Q at level 200,
  tid custom wp_thread_id at level 200,
  E custom atomic_triple_mask at level 200,
  y1 binder,
  yn binder,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  '[' α ']'  '/' >>>  '/  ' '[' e ']'  tid E '/' <<<  '/  ' ∃∃  y1  ..  yn ,  '/  ' '[' β ']'  '/' |  RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.
Notation "'<<<' P | α '>>>' e tid E '<<<' β | z1 .. zn , 'RET' v ; Q '>>>'" := (
  atomic_triple
    (TA := TeleO)
    (TB := TeleO)
    (TP := TeleS (λ z1, .. (TeleS (λ zn, TeleO)) ..))
    e%E
    tid
    E
    P%I
    (tele_app α%I)
    (tele_app $ tele_app β%I)
    (tele_app $ tele_app $ tele_app $ λ z1, .. (λ zn, Q%I) ..)
    (tele_app $ tele_app $ tele_app $ λ z1, .. (λ zn, (v%V : val)) ..)
)(at level 20,
  P, α, e, β, v, Q at level 200,
  tid custom wp_thread_id at level 200,
  E custom atomic_triple_mask at level 200,
  z1 binder,
  zn binder,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  '[' α ']'  '/' >>>  '/  ' '[' e ']'  tid E '/' <<<  '/  ' '[' β ']'  '/' |  z1  ..  zn ,  '/  ' RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.
Notation "'<<<' P | α '>>>' e tid E '<<<' β | 'RET' v ; Q '>>>'" := (
  atomic_triple
    (TA := TeleO)
    (TB := TeleO)
    (TP := TeleO)
    e%E
    tid
    E
    P%I
    (tele_app α%I)
    (tele_app $ tele_app β%I)
    (tele_app $ tele_app $ tele_app Q%I)
    (tele_app $ tele_app $ tele_app (v%V : val))
)(at level 20,
  P, α, e, β, v, Q at level 200,
  tid custom wp_thread_id at level 200,
  E custom atomic_triple_mask at level 200,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  '[' α ']'  '/' >>>  '/  ' '[' e ']'  tid E '/' <<<  '/  ' '[' β ']'  '/' |  RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.

Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e tid E '<<<' ∃∃ y1 .. yn , β | z1 .. zn , 'RET' v ; Q '>>>'" := (
  ⊢ atomic_triple
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) ..))
    (TP := TeleS (λ z1, .. (TeleS (λ zn, TeleO)) ..))
    e%E
    tid
    E
    P%I
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, β%I) ..) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app $ λ z1, .. (λ zn, Q%I) ..) ..) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app $ λ z1, .. (λ zn, (v%V : val)) ..) ..) ..)
) : stdpp_scope.
Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e tid E '<<<' ∃∃ y1 .. yn , β | 'RET' v ; Q '>>>'" := (
  ⊢ atomic_triple
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) ..))
    (TP := TeleO)
    e%E
    tid
    E
    P%I
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, β%I) ..) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app Q%I) ..) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app (v%V : val)) ..) ..)
) : stdpp_scope.
Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e tid E '<<<' β | z1 .. zn , 'RET' v ; Q '>>>'" := (
  ⊢ atomic_triple
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
    (TB := TeleO)
    (TP := TeleS (λ z1, .. (TeleS (λ zn, TeleO)) ..))
    e%E
    tid
    E
    P%I
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app β%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app $ λ z1, .. (λ zn, Q%I) ..) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app $ λ z1, .. (λ zn, (v%V : val)) ..) ..)
) : stdpp_scope.
Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e tid E '<<<' β | 'RET' v ; Q '>>>'" := (
  ⊢ atomic_triple
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
    (TB := TeleO)
    (TP := TeleO)
    e%E
    tid
    E
    P%I
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app β%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app Q%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app (v%V : val)) ..)
) : stdpp_scope.
Notation "'<<<' P | α '>>>' e tid E '<<<' ∃∃ y1 .. yn , β | z1 .. zn , 'RET' v ; Q '>>>'" := (
  ⊢ atomic_triple
    (TA := TeleO)
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) ..))
    (TP := TeleS (λ z1, .. (TeleS (λ zn, TeleO)) ..))
    e%E
    tid
    E
    P%I
    (tele_app α%I)
    (tele_app $ tele_app $ λ y1, .. (λ yn, β%I) ..)
    (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app $ λ z1, .. (λ zn, Q%I) ..) ..)
    (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app (v%V : val)) ..)
) : stdpp_scope.
Notation "'<<<' P | α '>>>' e tid E '<<<' ∃∃ y1 .. yn , β | 'RET' v ; Q '>>>'" := (
  ⊢ atomic_triple
    (TA := TeleO)
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) ..))
    (TP := TeleO)
    e%E
    tid
    E
    P%I
    (tele_app α%I)
    (tele_app $ tele_app $ λ y1, .. (λ yn, β%I) ..)
    (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app Q%I) ..)
    (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app (v%V : val)) ..)
) : stdpp_scope.
Notation "'<<<' P | α '>>>' e tid E '<<<' β | z1 .. zn , 'RET' v ; Q '>>>'" := (
  ⊢ atomic_triple
    (TA := TeleO)
    (TB := TeleO)
    (TP := TeleS (λ z1, .. (TeleS (λ zn, TeleO)) ..))
    e%E
    tid
    E
    P%I
    (tele_app α%I)
    (tele_app $ tele_app β%I)
    (tele_app $ tele_app $ tele_app $ λ z1, .. (λ zn, Q%I) ..)
    (tele_app $ tele_app $ tele_app $ λ z1, .. (λ zn, (v%V : val)) ..)
) : stdpp_scope.
Notation "'<<<' P | α '>>>' e tid E '<<<' β | 'RET' v ; Q '>>>'" := (
  ⊢ atomic_triple
    (TA := TeleO)
    (TB := TeleO)
    (TP := TeleO)
    e%E
    tid
    E
    P%I
    (tele_app α%I)
    (tele_app $ tele_app β%I)
    (tele_app $ tele_app $ tele_app Q%I)
    (tele_app $ tele_app $ tele_app (v%V : val))
) : stdpp_scope.
