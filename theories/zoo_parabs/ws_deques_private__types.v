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
  in_type "zoo_parabs.ws_deques_private.status" 0
)(in custom zoo_tag
).
Notation "'Nonblocked'" := (
  in_type "zoo_parabs.ws_deques_private.status" 1
)(in custom zoo_tag
).

Notation "'RequestBlocked'" := (
  in_type "zoo_parabs.ws_deques_private.request" 0
)(in custom zoo_tag
).
Notation "'RequestNone'" := (
  in_type "zoo_parabs.ws_deques_private.request" 1
)(in custom zoo_tag
).
Notation "'RequestSome'" := (
  in_type "zoo_parabs.ws_deques_private.request" 2
)(in custom zoo_tag
).

Notation "'ResponseWaiting'" := (
  in_type "zoo_parabs.ws_deques_private.response" 0
)(in custom zoo_tag
).
Notation "'ResponseNone'" := (
  in_type "zoo_parabs.ws_deques_private.response" 1
)(in custom zoo_tag
).
Notation "'ResponseSome'" := (
  in_type "zoo_parabs.ws_deques_private.response" 2
)(in custom zoo_tag
).

Notation "'size'" := (
  in_type "zoo_parabs.ws_deques_private.t" 0
)(in custom zoo_field
).
Notation "'deques'" := (
  in_type "zoo_parabs.ws_deques_private.t" 1
)(in custom zoo_field
).
Notation "'statuses'" := (
  in_type "zoo_parabs.ws_deques_private.t" 2
)(in custom zoo_field
).
Notation "'requests'" := (
  in_type "zoo_parabs.ws_deques_private.t" 3
)(in custom zoo_field
).
Notation "'responses'" := (
  in_type "zoo_parabs.ws_deques_private.t" 4
)(in custom zoo_field
).
Notation "'force_mutable'" := (
  in_type "zoo_parabs.ws_deques_private.t" 5
)(in custom zoo_field
).
