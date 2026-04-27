From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  condition
  mutex.
From zoo_std Require Import
  ivar_2__types.
From zoo Require Import
  options.

Definition ivar_2٠create : val :=
  fun: <> =>
    { mutex٠create (), condition٠create (), §None }.

Definition ivar_2٠make : val :=
  fun: "v" =>
    { mutex٠create (), condition٠create (), ‘Some( "v" ) }.

Definition ivar_2٠try_get : val :=
  fun: "t" =>
    "t".{result}.

Definition ivar_2٠is_unset : val :=
  fun: "t" =>
    ivar_2٠try_get "t" == §None.

Definition ivar_2٠is_set : val :=
  fun: "t" =>
    ~ ivar_2٠is_unset "t".

Definition ivar_2٠get : val :=
  fun: "t" =>
    match: ivar_2٠try_get "t" with
    | Some "v" =>
        mutex٠synchronize "t".{mutex} ;;
        "v"
    | None =>
        let: "mtx" := "t".{mutex} in
        let: "cond" := "t".{condition} in
        mutex٠protect
          "mtx"
          (fun: <> =>
             condition٠wait_while
               "cond"
               "mtx"
               (fun: <> => "t".{result} == §None)) ;;
        match: "t".{result} with
        | Some "v" =>
            "v"
        | None =>
            Fail
        end
    end.

Definition ivar_2٠set : val :=
  fun: "t" "v" =>
    mutex٠protect "t".{mutex} (fun: <> => "t" <-{result} ‘Some( "v" )) ;;
    condition٠notify_all "t".{condition}.
