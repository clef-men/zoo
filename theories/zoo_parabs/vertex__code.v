Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_parabs.pool.
Require Import zoo_saturn.mpmc_stack_2.
Require Import zoo_std.clist.
Require Import zoo.options.

Notation "'vertex٠task'" := (
  in_type "zoo_parabs.vertex.t" 0
)(in custom zoo_field
).
Notation "'vertex٠preds'" := (
  in_type "zoo_parabs.vertex.t" 1
)(in custom zoo_field
).
Notation "'vertex٠succs'" := (
  in_type "zoo_parabs.vertex.t" 2
)(in custom zoo_field
).

Definition vertex٠create : val :=
  𝗳𝘂𝗻 "task" ->
    𝗹𝗲𝘁 "task" =
      𝗺𝗮𝘁𝗰𝗵 "task" 𝘄𝗶𝘁𝗵
      | Some "task" ->
          "task"
      | None ->
          𝗳𝘂𝗻 ⎽ -> true
      𝗲𝗻𝗱
    𝗶𝗻
    { "task", 1, mpmc_stack_2٠create () }.

Definition vertex٠create' : val :=
  𝗳𝘂𝗻 "task" ->
    vertex٠create ‘Some( 𝗳𝘂𝗻 "ctx" -> "task" "ctx" ⍮
                                                  true ).

Definition vertex٠task : val :=
  𝗳𝘂𝗻 "t" ->
    "t".{vertex٠task}.

Definition vertex٠set_task : val :=
  𝗳𝘂𝗻 "t" "task" ->
    "t" <-{vertex٠task} "task".

Definition vertex٠precede : val :=
  𝗳𝘂𝗻 "t1" "t2" ->
    𝗹𝗲𝘁 "succs1" = "t1".{vertex٠succs} 𝗶𝗻
    𝗶𝗳 ~ mpmc_stack_2٠is_closed "succs1" 𝘁𝗵𝗲𝗻 (
      𝗳𝗮𝗮 "t2".[vertex٠preds] 1 ⍮
      𝗶𝗳 mpmc_stack_2٠push "succs1" "t2" 𝘁𝗵𝗲𝗻 (
        𝗳𝗮𝗮 "t2".[vertex٠preds] (-1) ⍮
        ()
      )
    ).

#[local] Definition __zoo_recs_0 :=
  ( 𝗿𝗲𝗰𝘀 "release" "ctx" "t" ->
      𝗶𝗳 𝗳𝗮𝗮 "t".[vertex٠preds] (-1) == 1 𝘁𝗵𝗲𝗻 (
        "run" "ctx" "t"
      )
    𝘄𝗶𝘁𝗵 "run" "ctx" "t" ->
      pool٠async "ctx"
        (𝗳𝘂𝗻 "ctx" ->
           "t" <-{vertex٠preds} 1 ⍮
           𝗶𝗳 "t".{vertex٠task} "ctx" 𝘁𝗵𝗲𝗻 (
             𝗹𝗲𝘁 "succs" =
               mpmc_stack_2٠close "t".{vertex٠succs}
             𝗶𝗻
             clist٠iter
               (𝗳𝘂𝗻 "succ" -> "release" "ctx" "succ")
               "succs"
           ) 𝗲𝗹𝘀𝗲 (
             "release" "ctx" "t"
           ))
  )%zoo_recs.
Definition vertex٠release :=
  ValRecs 0 __zoo_recs_0.
Definition vertex٠run :=
  ValRecs 1 __zoo_recs_0.
#[global] Instance :
  AsValRecs' vertex٠release 0 __zoo_recs_0 [
    vertex٠release ;
    vertex٠run
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' vertex٠run 1 __zoo_recs_0 [
    vertex٠release ;
    vertex٠run
  ].
Proof.
  done.
Qed.

Definition vertex٠yield : val :=
  𝗳𝘂𝗻 "vtx" "task" ->
    vertex٠set_task "vtx" "task" ⍮
    false.
