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
  Ltac2 make_evar evar ts :=
    make (Evar evar ts).
  Ltac2 make_sort sort :=
    make (Sort sort).
  Ltac2 make_cast t cast ty :=
    make (Cast t cast ty).
  Ltac2 make_prod bdr t :=
    make (Prod bdr t).
  Ltac2 make_lambda bdr t :=
    make (Lambda bdr t).
  Ltac2 make_let bdr t1 t2 :=
    make (LetIn bdr t1 t2).
  Ltac2 make_app t ts :=
    make (App t ts).
  Ltac2 make_constant const inst :=
    make (Constant const inst).
  Ltac2 make_ind ind inst :=
    make (Ind ind inst).
  Ltac2 make_constructor ctor inst :=
    make (Constructor ctor inst).
  Ltac2 make_case case info inv t brs :=
    make (Case case info inv t brs).
  Ltac2 make_fix structs i bdrs ts :=
    make (Fix structs i bdrs ts).
  Ltac2 make_cofix i bdrs ts :=
    make (CoFix i bdrs ts).
  Ltac2 make_proj proj relevance t :=
    make (Proj proj relevance t).
  Ltac2 make_uint63 n :=
    make (Uint63 n).
  Ltac2 make_float f :=
    make (Float f).
  Ltac2 make_string str :=
    make (String str).
  Ltac2 make_array inst ts t1 t2 :=
    make (Array inst ts t1 t2).

  Ltac2 make_lambdas bdrs t :=
    List.fold_right make_lambda bdrs t.

  Ltac2 make_app' t ts :=
    make_app t (Array.of_list ts).

  Ltac2 make_case_simple ind ty1 ty2 t brs :=
    make_case
      (case ind)
      ( ( make_lambda
          (Binder.make None ty1)
          ty2
        ),
        Binder.Relevant
      )
      NoInvert
      t
      brs.
End Unsafe.

Ltac2 rec head t :=
  match Unsafe.kind t with
  | Unsafe.App t _ =>
      head t
  | _ =>
      t
  end.

#[local] Ltac2 rec head_tail' t acc :=
  match Unsafe.kind t with
  | Unsafe.App t ts =>
      let acc := Array.append ts acc in
      head_tail' t acc
  | _ =>
      t, acc
  end.
Ltac2 head_tail t :=
  head_tail' t Array.empty.

Ltac2 tail t :=
  let (_, tl) := head_tail t in
  tl.

Ltac2 rec product_arity t :=
  match Unsafe.kind t with
  | Unsafe.Prod _ t =>
      Int.add (product_arity t) 1
  | _ =>
      0
  end.

#[local] Ltac2 rec product_decompose' t acc :=
  match Unsafe.kind t with
  | Unsafe.Prod bdr t =>
      let ty := Binder.type bdr in
      product_decompose' t (ty :: acc)
  | _ =>
      List.rev acc, t
  end.
Ltac2 product_decompose t :=
  product_decompose' t [].

Ltac2 product_parameters t :=
  let (params, _) := product_decompose t in
  params.

Ltac2 rec product_result t :=
  match Unsafe.kind t with
  | Unsafe.Prod _ t =>
      product_result t
  | _ =>
      t
  end.
