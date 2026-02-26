From stdpp Require Export
  countable.

From zoo Require Import
  prelude.
From zoo.ltac2 Require
  Array
  Constr
  Control
  Ind
  List
  String
  Notations.
From zoo Require Import
  options.

Module solve_countable.
  Import Ltac2.Init.
  Import Ltac2.Notations.

  Ltac2 Type error :=
    [ Goal_invalid
    | Type_not_inductive
    | Type_empty
    | Internal_error
    ].

  Ltac2 error_to_string err :=
    match err with
    | Goal_invalid  =>
        "invalid goal"
    | Type_not_inductive =>
        "not an inductive type"
    | Type_empty =>
        "empty inductive type"
    | Internal_error =>
        "internal error"
    end.
  Ltac2 error err :=
    let err := error_to_string err in
    let err := String.app "solve_countable: " err in
    Control.throw_invalid_argument err.

  Ltac2 Type info :=
    { info_type : constr ;
      info_inductive : inductive ;
      info_data : Ind.data ;
      info_instance : instance ;
      info_indices : constr array ;
      info_number_constructor : int ;
      info_constructors : constructor array ;
      info_fieldss : constr array array ;
      info_sum_inductive : inductive ;
      info_prod_inductive : inductive ;
    }.

  Ltac2 info_constructor info i :=
    Array.get (info.(info_constructors)) i.
  Ltac2 info_constructor_constr info i :=
    let ctor := info_constructor info i in
    Constr.Unsafe.make_constructor ctor (info.(info_instance)).
  Ltac2 info_fields info i :=
    Array.get (info.(info_fieldss)) i.
  Ltac2 info_arity info i :=
    Array.length (info_fields info i).

  Ltac2 info ty :=
    let (ind, indices) := Constr.head_tail ty in
    let (ind, inst) :=
      match Constr.Unsafe.kind ind with
      | Constr.Unsafe.Ind ind inst =>
          ind, inst
      | _ =>
          error Type_not_inductive
      end
    in
    let data := Ind.data ind in
    let num_ctor := Ind.nconstructors data in
    if Int.equal num_ctor 0 then
      error Type_empty
    else
      let ctors :=
        Array.init num_ctor (fun i =>
          Ind.get_constructor data i
        )
      in
      let fldss :=
        Array.map (fun ctor =>
          let ctor :=
            Constr.Unsafe.make_app
              (Constr.Unsafe.make_constructor ctor inst)
              indices
          in
          let ctor_ty := Constr.type ctor in
          let flds := Constr.product_parameters ctor_ty in
          Array.of_list flds
        ) ctors
      in
      let sum_ind :=
        match Constr.Unsafe.kind '@sum with
        | Constr.Unsafe.Ind ind _ =>
            ind
        | _ =>
            error Internal_error
        end
      in
      let prod_ind :=
        match Constr.Unsafe.kind '@prod with
        | Constr.Unsafe.Ind ind _ =>
            ind
        | _ =>
            error Internal_error
        end
      in
      { info_type := ty ;
        info_inductive := ind ;
        info_data := data ;
        info_instance := inst ;
        info_indices := indices ;
        info_number_constructor := num_ctor ;
        info_constructors := ctors ;
        info_fieldss := fldss ;
        info_sum_inductive := sum_ind ;
        info_prod_inductive := prod_ind ;
      }.

  Ltac2 encode_branch info i :=
    let flds := info_fields info i in
    let num_fld := Array.length flds in
    let bdrs :=
      Array.map (fun fld =>
        Constr.Binder.make None fld
      ) flds
    in
    let bdrs := Array.to_list bdrs in
    let body :=
      List.init_foldl (fun acc i =>
        let fld := Constr.Unsafe.make_rel (Int.sub num_fld i) in
        Constr.Unsafe.make_app
          '@pair
          [|'_; '_; acc; fld|]
      ) 'tt num_fld
    in
    let body :=
      let ty := if Int.equal i 0 then 'unit else '_ in
      Constr.Unsafe.make_app
        '@inr
        [|ty; '_; body|]
    in
    let body :=
      List.init_foldl (fun acc _ =>
        Constr.Unsafe.make_app
          '@inl
          [|'_; '_; acc|]
      ) body (Int.sub (Int.sub (info.(info_number_constructor)) i) 1)
    in
    Constr.Unsafe.make_lambdas bdrs body.
  Ltac2 encode_case info :=
    Constr.Unsafe.make_case_simple
      (info.(info_inductive))
      (info.(info_type))
      '_
      (Constr.Unsafe.make_rel 1)
      ( Array.init
          (info.(info_number_constructor))
          (encode_branch info)
      ).
  Ltac2 encode info :=
    Constr.Unsafe.make_lambda
      (Constr.Binder.make None (info.(info_type)))
      (encode_case info).

  Ltac2 extract_arguments_2 ty :=
    match Constr.Unsafe.kind ty with
    | Constr.Unsafe.App _ tys =>
        if Bool.neg (Int.equal (Array.length tys) 2) then
          error Internal_error
        else
          Array.get tys 0, Array.get tys 1
    | _ =>
        error Internal_error
    end.
  Ltac2 rec decode_branch' info i j ty' :=
    if Int.equal j 0 then
      Constr.Unsafe.make_app
        '@Some
        [|info.(info_type)
        ; Constr.Unsafe.make_app
            (info_constructor_constr info i)
            ( Array.append
                (info.(info_indices))
                ( Array.init (info_arity info i) (fun j =>
                    Constr.Unsafe.make_rel (Int.add (Int.mul 2 j) 1)
                  )
                )
            )
        |]
    else
      let ty := info.(info_type) in
      let (ty'_1, ty'_2) := extract_arguments_2 ty' in
      (* for some reason, we have to reconstruct [ty'], otherwise we might get an exception [Constr.DestKO] *)
      let ty' := Constr.Unsafe.make_app '@prod [|ty'_1; ty'_2|] in
      Constr.Unsafe.make_case_simple
        (info.(info_prod_inductive))
        ty'
        '(option $ty)
        (Constr.Unsafe.make_rel 2)
        [|Constr.Unsafe.make_lambdas
            [ Constr.Binder.make None ty'_1
            ; Constr.Binder.make None ty'_2
            ]
            (decode_branch' info i (Int.sub j 1) ty'_1)
        |].
  Ltac2 decode_branch info i ty' :=
    Constr.Unsafe.make_lambda
      (Constr.Binder.make None ty')
      ( Constr.Unsafe.make_let
          (Constr.Binder.make None 'unit)
          'tt
          (decode_branch' info i (info_arity info i) ty')
      ).
  Ltac2 rec decode_case' info i ty' :=
    let ty := info.(info_type) in
    if Int.equal i (-1) then
      '(@None $ty)
    else
      let (ty'_l, ty'_r) := extract_arguments_2 ty' in
      (* for some reason, we have to reconstruct [ty'], otherwise we might get an exception [Constr.DestKO] *)
      let ty' := Constr.Unsafe.make_app '@sum [|ty'_l; ty'_r|] in
      Constr.Unsafe.make_case_simple
        (info.(info_sum_inductive))
        ty'
        '(option $ty)
        (Constr.Unsafe.make_rel 1)
        [|Constr.Unsafe.make_lambda
            (Constr.Binder.make None ty'_l)
            (decode_case' info (Int.sub i 1) ty'_l)
        ; decode_branch info i ty'_r
        |].
  Ltac2 decode_case info ty' :=
    decode_case'
      info
      (Int.sub (info.(info_number_constructor)) 1)
      ty'.
  Ltac2 decode info ty' :=
    Constr.Unsafe.make_lambda
      (Constr.Binder.make None ty')
      (decode_case info ty').

  Ltac2 main' info :=
    let encode := encode info in
    let ty' := Constr.product_result (Constr.type encode) in
    let decode := decode info ty' in
    let _ := Constr.type decode in
    refine (
      Constr.Unsafe.make_app
        '@inj_countable
        [|'_; '_; '_; '_; '_; encode; decode; '_|]
    ) ;
    Control.focus 1 2 (fun () => apply _);
    solve [intros []; auto].
  Ltac2 main () :=
    lazy_match! goal with
    | [|- Countable ?ty] =>
        main' (info ty)
    | [|- _] =>
        error Goal_invalid
    end.
End solve_countable.

Ltac solve_countable :=
  ltac2:(solve_countable.main ()).

Module tests.
  Record test_1 := {
    test_1_1 : nat ;
  }.
  #[local] Instance test_1_eq_dec : EqDecision test_1 :=
    ltac:(solve_decision).
  #[local] Instance test_1_countable :
    Countable test_1.
  Proof.
    solve_countable.
  Qed.

  Record test_2 A1 A2 A3 := {
    test_2_1 : A1 ;
    test_2_2 : A2 ;
    test_2_3 : A3 ;
  }.
  #[local] Instance test_2_eq_dec `{!EqDecision A1, !EqDecision A2, !EqDecision A3} : EqDecision (test_2 A1 A2 A3) :=
    ltac:(solve_decision).
  #[local] Instance test_2_countable `{Countable A1, Countable A2, Countable A3} :
    Countable (test_2 A1 A2 A3).
  Proof.
    solve_countable.
  Qed.

  Inductive test_3 :=
    | Test31 : test_3
    | Test32 : nat → test_3
    | Test33 : nat → bool → test_3.
  #[local] Instance test_3_eq_dec : EqDecision test_3 :=
    ltac:(solve_decision).
  #[local] Instance test_3_countable :
    Countable test_3.
  Proof.
    solve_countable.
  Qed.

  Inductive test_4 A1 A2 A3 :=
    | Test41 : test_4 A1 A2 A3
    | Test42 : nat → test_4 A1 A2 A3
    | Test43 : nat → bool → test_4 A1 A2 A3
    | Test44 : A1 → test_4 A1 A2 A3
    | Test45 : A2 → test_4 A1 A2 A3
    | Test46 : A3 → test_4 A1 A2 A3
    | Test47 : A1 → A2 → test_4 A1 A2 A3
    | Test48 : A1 → A3 → test_4 A1 A2 A3
    | Test49 : A2 → A3 → test_4 A1 A2 A3
    | Test410 : A1 → A2 → A3 → test_4 A1 A2 A3.
  #[local] Instance test_4_eq_dec `{!EqDecision A1, !EqDecision A2, !EqDecision A3} : EqDecision (test_4 A1 A2 A3) :=
    ltac:(solve_decision).
  #[local] Instance test_4_countable `{Countable A1, Countable A2, Countable A3} :
    Countable (test_4 A1 A2 A3).
  Proof.
    solve_countable.
  Qed.
End tests.
