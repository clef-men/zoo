From Ltac2 Require Export
  Constr
  Init.

From zoo Require Import
  prelude.
From zoo.ltac2 Require Import
  Array
  List.
From zoo Require Import
  options.

Module Unsafe.
  Export Unsafe.

  Ltac2 make_rel i :=
    make (Rel i).
  Ltac2 make_var id :=
    make (Var id).
  Ltac2 make_meta meta :=
    make (Meta meta).
  Ltac2 make_evar evar constrs :=
    make (Evar evar constrs).
  Ltac2 make_sort sort :=
    make (Sort sort).
  Ltac2 make_cast constr cast ty :=
    make (Cast constr cast ty).
  Ltac2 make_prod bdr constr :=
    make (Prod bdr constr).
  Ltac2 make_lambda bdr constr :=
    make (Lambda bdr constr).
  Ltac2 make_let bdr constr1 constr2 :=
    make (LetIn bdr constr1 constr2).
  Ltac2 make_app constr constrs :=
    make (App constr constrs).
  Ltac2 make_constant const inst :=
    make (Constant const inst).
  Ltac2 make_ind ind inst :=
    make (Ind ind inst).
  Ltac2 make_constructor ctor inst :=
    make (Constructor ctor inst).
  Ltac2 make_case case info inv constr brs :=
    make (Case case info inv constr brs).
  Ltac2 make_fix structs i bdrs constrs :=
    make (Fix structs i bdrs constrs).
  Ltac2 make_cofix i bdrs constrs :=
    make (CoFix i bdrs constrs).
  Ltac2 make_proj proj relevance constr :=
    make (Proj proj relevance constr).
  Ltac2 make_uint63 n :=
    make (Uint63 n).
  Ltac2 make_float f :=
    make (Float f).
  Ltac2 make_string str :=
    make (String str).
  Ltac2 make_array inst constrs constr1 constr2 :=
    make (Array inst constrs constr1 constr2).

  Ltac2 make_lambdas bdrs constr :=
    List.fold_right make_lambda bdrs constr.

  Ltac2 make_app' constr constrs :=
    make_app constr (Array.of_list constrs).

  Ltac2 make_case_simple ind ty1 ty2 constr br :=
    make_case
      (case ind)
      ( ( Constr.Unsafe.make_lambda
          (Constr.Binder.make None ty1)
          ty2
        ),
        Constr.Binder.Relevant
      )
      Constr.Unsafe.NoInvert
      constr
      (Array.make 1 br).
End Unsafe.
