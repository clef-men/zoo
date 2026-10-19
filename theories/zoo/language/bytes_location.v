Require Import stdpp.infinite.

Require Import zoo.prelude.
Require Import zoo.options.

Record bytes_location := BytesLocation
  { bytes_location۰car : positive
  }.
Add Printing Constructor bytes_location.

Please derive Inhabited for bytes_location.
Please derive EqDecision for bytes_location.
Please derive Countable for bytes_location.

#[global] Instance bytes_locationｰinfinite : Infinite bytes_location :=
  inj_infinite
    BytesLocation
    (Some ∘ bytes_location۰car)
    (λ _, eq_refl).
