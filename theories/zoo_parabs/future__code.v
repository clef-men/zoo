Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_parabs.pool.
Require Import zoo_std.ivar_4.
Require Import zoo.options.

Definition future٠return : val :=
  ivar_4٠make.

Definition future٠set : val :=
  𝗳𝘂𝗻 "ctx" "t" "res" ->
    ivar_4٠notify "t" "ctx" "res".

Definition future٠async : val :=
  𝗳𝘂𝗻 "ctx" "task" ->
    𝗹𝗲𝘁 "t" = ivar_4٠create () 𝗶𝗻
    pool٠async
      "ctx"
      (𝗳𝘂𝗻 "ctx" -> future٠set "ctx" "t" ("task" "ctx")) ⍮
    "t".

Definition future٠wait : val :=
  𝗳𝘂𝗻 "ctx" "t" ->
    pool٠wait_ivar "ctx" "t" ⍮
    ivar_4٠get "t".

Definition future٠iter : val :=
  𝗳𝘂𝗻 "ctx" "t" "task" ->
    𝗺𝗮𝘁𝗰𝗵 ivar_4٠wait "t" "task" 𝘄𝗶𝘁𝗵
    | None ->
        ()
    | Some "res" ->
        "task" "ctx" "res"
    𝗲𝗻𝗱.

Definition future٠map : val :=
  𝗳𝘂𝗻 "ctx" "t1" "task" ->
    𝗹𝗲𝘁 "t2" = ivar_4٠create () 𝗶𝗻
    future٠iter
      "ctx"
      "t1"
      (𝗳𝘂𝗻 "ctx" "res1" ->
         pool٠async "ctx"
           (𝗳𝘂𝗻 "ctx" ->
              future٠set "ctx" "t2" ("task" "ctx" "res1"))) ⍮
    "t2".
