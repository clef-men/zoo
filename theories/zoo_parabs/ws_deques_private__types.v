From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  deque
  atomic_array
  array
  random_round
  domain.
From zoo Require Import
  options.

Notation "'Blocked'" := (
  in_type "zoo_parabs.ws_deques_private.request" 0
)(in custom zoo_tag
).
Notation "'No_request'" := (
  in_type "zoo_parabs.ws_deques_private.request" 1
)(in custom zoo_tag
).
Notation "'Request'" := (
  in_type "zoo_parabs.ws_deques_private.request" 2
)(in custom zoo_tag
).

Notation "'No_response'" := (
  in_type "zoo_parabs.ws_deques_private.response" 0
)(in custom zoo_tag
).
Notation "'No'" := (
  in_type "zoo_parabs.ws_deques_private.response" 1
)(in custom zoo_tag
).
Notation "'Yes'" := (
  in_type "zoo_parabs.ws_deques_private.response" 2
)(in custom zoo_tag
).

Notation "'deques'" := (
  in_type "zoo_parabs.ws_deques_private.t" 0
)(in custom zoo_proj
).
Notation "'flags'" := (
  in_type "zoo_parabs.ws_deques_private.t" 1
)(in custom zoo_proj
).
Notation "'requests'" := (
  in_type "zoo_parabs.ws_deques_private.t" 2
)(in custom zoo_proj
).
Notation "'responses'" := (
  in_type "zoo_parabs.ws_deques_private.t" 3
)(in custom zoo_proj
).
