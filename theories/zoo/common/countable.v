From stdpp Require Export
  countable.

From zoo Require Import
  prelude.
From zoo.ltac2 Require Import
  Array
  Constr
  Control
  Env
  List
  Option
  Std
  String
  Notations.
From zoo Require Import
  options.

#[local] Ltac2 error msg :=
  let msg := String.app "error: " msg in
  Control.throw_invalid_argument msg.

#[local] Ltac2 prod () :=
  match Env.expand [@prod] with
  | IndRef ind :: _ =>
      ind
  | _ =>
      error "cannot find [prod]"
  end.
#[local] Ltac2 pair () :=
  match Env.expand [@pair] with
  | ref_ :: _ =>
      ref_
  | _ =>
      error "cannot find [pair]"
  end.
#[local] Ltac2 unit () :=
  match Env.expand [@unit] with
  | ref_ :: _ =>
      Constr.Unsafe.make_app (Env.instantiate ref_) Array.empty
  | _ =>
      error "cannot find [unit]"
  end.
#[local] Ltac2 tt () :=
  match Env.expand [@tt] with
  | ref_ :: _ =>
      Constr.Unsafe.make_app (Env.instantiate ref_) Array.empty
  | _ =>
      error "cannot find [tt]"
  end.

#[local] Ltac2 rec parameters constr :=
  match Constr.Unsafe.kind constr with
  | Constr.Unsafe.Prod bdr constr =>
      let param := Constr.Binder.type bdr in
      param :: parameters constr
  | _ =>
      []
  end.
#[local] Ltac2 record_fields data inst :=
  let ctor := Constr.Unsafe.make_constructor (Ind.get_constructor data 0) inst in
  parameters (Constr.type ctor).

#[local] Ltac2 solve_countable_0 rcd ind data inst :=
  let flds := record_fields data inst in
  let num_fld := List.length flds in
  let prod := prod () in
  let pair := pair () in
  let unit := unit () in
  let tt := tt () in
  let tpl :=
    List.fold_right (fun fld acc =>
      Constr.Unsafe.make_app
        (Env.instantiate (IndRef prod))
        [|fld; acc|]
    ) flds unit
  in
  let encode :=
    Constr.Unsafe.make_lambda
      (Constr.Binder.make None rcd)
      ( Constr.Unsafe.make_case_simple
        ind
        rcd
        tpl
        (Constr.Unsafe.make_rel 1)
        ( List.fold_right
          ( fun fld acc =>
            Constr.Unsafe.make_lambda
              (Constr.Binder.make None fld)
              acc
          )
          flds
          ( List.fold_righti (fun i fld acc =>
              Constr.Unsafe.make_app
                (Env.instantiate pair)
                [|fld
                ; '_
                ; Constr.Unsafe.make_rel (Int.sub num_fld i)
                ; acc
                |]
            ) flds tt
          )
        )
      )
  in
  let decode :=
    Constr.Unsafe.make_lambda
      (Constr.Binder.make None tpl)
      ( fst (List.fold_right
        ( fun fld acc =>
          let ty :=
            Constr.Unsafe.make_app
              (Env.instantiate (IndRef prod))
              [|fld; snd acc|]
          in
          ( Constr.Unsafe.make_case_simple
              prod
              ty
              rcd
              (Constr.Unsafe.make_rel 1)
              ( Constr.Unsafe.make_lambdas
                [ Constr.Binder.make None fld
                ; Constr.Binder.make None (snd acc)
                ]
                (fst acc)
              )
          , ty
          )
        )
        flds
        ( Constr.Unsafe.make_app'
          ( Constr.Unsafe.make_constructor
            (Ind.get_constructor data 0)
            inst
          )
          ( List.mapi (fun i _fld =>
              Constr.Unsafe.make_rel (Int.mul 2 (Int.sub num_fld i))
            ) flds
          )
        , unit
        )
      ))
  in
  refine (
    Constr.Unsafe.make_app
      '@inj_countable'
      [|'_; '_; '_; '_; '_; encode; decode; '_|]
  ) ;
  Control.focus 1 2 (fun () => apply _);
  solve [intros []; auto].
#[local] Ltac2 solve_countable_1 rcd :=
  match Constr.Unsafe.kind rcd with
  | Constr.Unsafe.Ind ind inst =>
      let data := Ind.data ind in
      if Bool.neg (Int.equal 1 (Ind.nconstructors data)) then
        error "not a record type"
      else
        solve_countable_0 rcd ind data inst
  | _ =>
      Control.throw (Invalid_argument (Some (Message.of_constr rcd)))
  end.
#[local] Ltac2 solve_countable () :=
  match! goal with [|- Countable ?rcd] =>
    solve_countable_1 rcd
  end.
Ltac solve_countable :=
  ltac2:(solve_countable ()).
