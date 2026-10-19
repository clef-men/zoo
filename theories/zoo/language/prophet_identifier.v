Require Import stdpp.infinite.

Require Import zoo.prelude.
Require Import zoo.options.

Record prophet_identifier := ProphetIdentifier
  { prophet_identifier۰car : positive
  }.
Add Printing Constructor prophet_identifier.

Please derive Inhabited for prophet_identifier.
Please derive EqDecision for prophet_identifier.
Please derive Countable for prophet_identifier.

#[global] Instance prophet_identifierｰinfinite : Infinite prophet_identifier :=
  inj_infinite
    ProphetIdentifier
    (Some ∘ prophet_identifier۰car)
    (λ _, eq_refl).
