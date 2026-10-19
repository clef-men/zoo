Require Import zoo.prelude.
Require Import zoo.options.

Record block_identifier := BlockIdentifier
  { block_identifier۰car : positive
  }.
Add Printing Constructor block_identifier.

Please derive Inhabited for block_identifier.
Please derive EqDecision for block_identifier.
Please derive Countable for block_identifier.
