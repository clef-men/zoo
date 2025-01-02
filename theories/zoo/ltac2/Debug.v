From zoo Require Import
  prelude.
From zoo.ltac2 Require
  Message
  Constr.
From zoo Require Import
  options.

Ltac2 rec dump constr :=
  match Constr.Unsafe.kind constr with
  | Constr.Unsafe.Rel i =>
      Message.print (Message.concat (Message.of_string "Rel ") (Message.of_int i))
  | Constr.Unsafe.Var _ =>
      Message.print_string "Var"
  | Constr.Unsafe.Meta _ =>
      Message.print_string "Meta"
  | Constr.Unsafe.Evar _ _ =>
      Message.print_string "Evar"
  | Constr.Unsafe.Sort _ =>
      Message.print_string "Sort"
  | Constr.Unsafe.Cast _ _ _ =>
      Message.print_string "Cast"
  | Constr.Unsafe.Prod _ _ =>
      Message.print_string "Prod"
  | Constr.Unsafe.Lambda bdr constr =>
      Message.print_string "Lambda" ;
      dump (Constr.Binder.type bdr) ;
      dump constr
  | Constr.Unsafe.LetIn _ _ _ =>
      Message.print_string "LetIn"
  | Constr.Unsafe.App _ constrs =>
      Message.print_string "App" ;
      Array.iter dump constrs
  | Constr.Unsafe.Constant _ _ =>
      Message.print_string "Constant"
  | Constr.Unsafe.Ind _ind _inst =>
      Message.print_string "Ind"
  | Constr.Unsafe.Constructor _ _ =>
      Message.print_string "Constructor"
  | Constr.Unsafe.Case _ (constr1, _) inv constr2 brs =>
      Message.print_string "Case" ;
      dump constr1 ;
      match inv with
      | Constr.Unsafe.NoInvert =>
          Message.print_string "NoInvert"
      | Constr.Unsafe.CaseInvert constrs =>
          Message.print_string "CaseInvert" ;
          Array.iter dump constrs
      end ;
      dump constr2 ;
      Array.iter dump brs
  | Constr.Unsafe.Fix _ _ _ _ =>
      Message.print_string "Fix"
  | Constr.Unsafe.CoFix _ _ _ =>
      Message.print_string "CoFix"
  | Constr.Unsafe.Proj _ _ _ =>
      Message.print_string "Proj"
  | Constr.Unsafe.Uint63 _ =>
      Message.print_string "Uint63"
  | Constr.Unsafe.Float _ =>
      Message.print_string "Float"
  | Constr.Unsafe.String _ =>
      Message.print_string "String"
  | Constr.Unsafe.Array _ _ _ _ =>
      Message.print_string "Array"
  end.
