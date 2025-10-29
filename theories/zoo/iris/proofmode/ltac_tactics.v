From stdpp Require Import
  namespaces
  hlist
  pretty.

From iris.bi Require Export
  bi
  telescopes.
From iris.proofmode Require Import
  base
  spec_patterns
  sel_patterns
  coq_tactics
  reduction
  string_ident.
From iris.proofmode Require Export
  classes
  notation.
From iris.prelude Require Import
  options.

From zoo.common Require Import
  format.
From zoo.iris.proofmode Require Import
  intro_patterns.

Export ident.

Section custom_ipat.
  Implicit Types custom : string.

  Class CustomIpat custom :=
    custom_ipat : string → option string.
  #[global] Arguments custom_ipat custom {CustomIpat} arg : rename.
  #[global] Hint Mode CustomIpat + : typeclass_instances.

  Class CustomIpat0 custom :=
    custom_ipat_0 : string.
  #[global] Arguments custom_ipat_0 custom {CustomIpat0} : rename.
  #[global] Hint Mode CustomIpat0 + : typeclass_instances.

  #[global] Instance custom_ipat_0_ipat `{!CustomIpat0 custom} : CustomIpat custom | 100 :=
    λ _,
      Some (custom_ipat_0 custom).

  Class CustomIpat1 custom :=
    custom_ipat_1 : string.
  #[global] Arguments custom_ipat_1 custom {CustomIpat1} : rename.
  #[global] Hint Mode CustomIpat1 + : typeclass_instances.

  #[global] Instance custom_ipat_1_ipat `{!CustomIpat1 custom} : CustomIpat custom | 100 :=
    λ arg,
      format (custom_ipat_1 custom) {["" := arg]}.

  Class CustomIpatFormat custom :=
    custom_ipat_format : string.
  #[global] Arguments custom_ipat_format custom {CustomIpatFormat} : rename.
  #[global] Hint Mode CustomIpatFormat + : typeclass_instances.

  #[global] Instance custom_ipat_format_ipat `{!CustomIpatFormat custom} : CustomIpat custom | 100 :=
    λ arg,
      format (custom_ipat_format custom) (format_env_of_string arg).
End custom_ipat.

(** Tactic used for solving side-conditions arising from TC resolution in [iMod]
and [iInv]. *)
Ltac iSolveSideCondition :=
  lazymatch goal with
  | |- pm_error ?err => fail "" err
  | _ => split_and?; try solve [ fast_done | solve_ndisj | tc_solve ]
  end.

(** Used for printing [string]s and [ident]s. *)
Ltac pretty_ident H :=
  lazymatch H with
  | INamed ?H => H
  | ?H => H
  end.

(** * Misc *)

Ltac iGetCtx :=
  lazymatch goal with
  | |- envs_entails ?Δ _ => Δ
  | |- context[ envs_split _ _ ?Δ ] => Δ
  end.

Ltac iMissingHypsCore Δ Hs :=
  let Hhyps := pm_eval (envs_dom Δ) in
  eval vm_compute in (list_difference Hs Hhyps).

Ltac iMissingHyps Hs :=
  let Δ := iGetCtx in
  iMissingHypsCore Δ Hs.

Ltac iTypeOf H :=
  let Δ := match goal with |- envs_entails ?Δ _ => Δ end in
  pm_eval (envs_lookup H Δ).

Ltac iBiOfGoal :=
  match goal with |- @envs_entails ?PROP _ _ => PROP end.

Tactic Notation "iMatchHyp" tactic1(tac) :=
  match goal with
  | |- context[ environments.Esnoc _ ?x ?P ] => tac x P
  end.

Tactic Notation "iSelect" open_constr(pat) tactic1(tac) :=
  lazymatch goal with
  | |- context[ environments.Esnoc _ ?x pat ] =>
    (* Before runnig [tac] on the hypothesis name [x] we must first unify the
       pattern [pat] with the term it matched against. This forces every evar
       coming from [pat] (and in particular from the [_] it contains and from
       the implicit arguments it uses) to be instantiated. If we do not do so
       then shelved goals are produced for every such evar. *)
    lazymatch iTypeOf x with
    | Some (_,?T) => unify T pat; tac x
    end
  end.

(** * Start a proof *)
Tactic Notation "iStartProof" :=
  lazymatch goal with
  | |- (let _ := _ in _) => fail "iStartProof: goal is a `let`, use `simpl`,"
                                 "`intros x`, `iIntros (x)`, or `iIntros ""%x"""
  | |- envs_entails _ _ => idtac
  | |- ?φ => notypeclasses refine (as_emp_valid_2 φ _ _);
               [tc_solve || fail "iStartProof: goal" φ "not a BI assertion"
               |notypeclasses refine (tac_start _ _)]
  end.

(* Same as above, with 2 differences :
   - We can specify a BI in which we want the proof to be done
   - If the goal starts with a let or a ∀, they are automatically
     introduced. *)
Tactic Notation "iStartProof" uconstr(PROP) :=
  lazymatch goal with
  | |- @envs_entails ?PROP' _ _ =>
    (* This cannot be shared with the other [iStartProof], because
    type_term has a non-negligible performance impact. *)
    let x := type_term (eq_refl : @eq Type PROP PROP') in idtac

  (* We eta-expand [as_emp_valid_2], in order to make sure that
     [iStartProof PROP] works even if [PROP] is the carrier type. In
     this case, typing this expression will end up unifying PROP with
     [bi_car _], and hence trigger the canonical structures mechanism
     to find the corresponding bi. *)
  | |- ?φ => notypeclasses refine ((λ P : PROP, @as_emp_valid_2 φ _ P) _ _ _);
               [tc_solve || fail "iStartProof: goal" φ "not a" PROP "assertion"
               |apply tac_start]
  end.

Tactic Notation "iStopProof" :=
  lazymatch goal with
  | |- envs_entails _ _ => apply tac_stop; pm_reduce
  | |- _ => fail "iStopProof: proofmode not started"
  end.

(** * Generate a fresh identifier *)
(** The tactic [iFresh] bumps the fresh name counter in the proof mode
environment and returns the old value.

Note that we use [Ltac] instead of [Tactic Notation] since [Tactic Notation]
tactics can only have side-effects, but cannot return terms. *)
Ltac iFresh :=
  (* We make use of an Ltac hack to allow the [iFresh] tactic to both have a
  side-effect (i.e. to bump the counter) and to return a value (the fresh name).
  We do this by wrapped the side-effect under a [match] in a let-binding. See
  https://stackoverflow.com/a/46178884 *)
  let start :=
    lazymatch goal with
    | _ => iStartProof
    end in
  let c :=
    lazymatch goal with
    | |- envs_entails (Envs _ _ ?c) _ => c
    end in
  let inc :=
    lazymatch goal with
    | |- envs_entails (Envs ?Δp ?Δs _) ?Q =>
      let c' := eval vm_compute in (Pos.succ c) in
      change_no_check (envs_entails (Envs Δp Δs c') Q)
    end in
  constr:(IAnon c).

(** * Context manipulation *)
Tactic Notation "iRename" constr(H1) "into" constr(H2) :=
  eapply tac_rename with H1 H2 _ _; (* (i:=H1) (j:=H2) *)
    [pm_reflexivity ||
     let H1 := pretty_ident H1 in
     fail "iRename:" H1 "not found"
    |pm_reduce;
     lazymatch goal with
       | |- False =>
         let H2 := pretty_ident H2 in
         fail "iRename:" H2 "not fresh"
       | _ => idtac (* subgoal *)
     end].

Tactic Notation "iRename" "select" open_constr(pat) "into" constr(n) :=
  iSelect pat ltac:(fun H => iRename H into n).

(** Elaborated selection patterns, unlike the type [sel_pat], contains
only specific identifiers, and no wildcards like `#` (with the
exception of the pure selection pattern `%`) *)
Inductive esel_pat :=
  | ESelPure
  | ESelIdent : (* whether the ident is intuitionistic *) bool → ident → esel_pat.

Local Ltac iElaborateSelPat_go pat Δ Hs :=
  lazymatch pat with
  | [] => eval cbv in Hs
  | SelPure :: ?pat =>  iElaborateSelPat_go pat Δ (ESelPure :: Hs)
  | SelIntuitionistic :: ?pat =>
    let Hs' := pm_eval (env_dom (env_intuitionistic Δ)) in
    let Δ' := pm_eval (envs_clear_intuitionistic Δ) in
    iElaborateSelPat_go pat Δ' ((ESelIdent true <$> Hs') ++ Hs)
  | SelSpatial :: ?pat =>
    let Hs' := pm_eval (env_dom (env_spatial Δ)) in
    let Δ' := pm_eval (envs_clear_spatial Δ) in
    iElaborateSelPat_go pat Δ' ((ESelIdent false <$> Hs') ++ Hs)
  | SelIdent ?H :: ?pat =>
    lazymatch pm_eval (envs_lookup_delete false H Δ) with
    | Some (?p,_,?Δ') =>  iElaborateSelPat_go pat Δ' (ESelIdent p H :: Hs)
    | None =>
      let H := pretty_ident H in
      fail "iElaborateSelPat:" H "not found"
    end
  end.
(** Converts a selection pattern (given as a string) to a list of
elaborated selection patterns. *)
Ltac iElaborateSelPat pat :=
  lazymatch goal with
  | |- envs_entails ?Δ _ =>
    let pat := sel_pat.parse pat in iElaborateSelPat_go pat Δ (@nil esel_pat)
  end.

Ltac _iClearHyp H :=
  eapply tac_clear with H _ _; (* (i:=H) *)
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iClear:" H "not found"
    |pm_reduce; tc_solve ||
     let H := pretty_ident H in
     let P := match goal with |- TCOr (Affine ?P) _ => P end in
     fail "iClear:" H ":" P "not affine and the goal not absorbing"
    |pm_reduce].

Local Ltac iClear_go Hs :=
  lazymatch Hs with
  | [] => idtac
  | ESelPure :: ?Hs => clear; iClear_go Hs
  | ESelIdent _ ?H :: ?Hs => _iClearHyp H; iClear_go Hs
  end.
Tactic Notation "iClear" constr(Hs) :=
  iStartProof; let Hs := iElaborateSelPat Hs in iClear_go Hs.

Tactic Notation "iClear" "(" ident_list(xs) ")" constr(Hs) :=
  iClear Hs; clear xs.

Tactic Notation "iClear" "select" open_constr(pat) :=
  iSelect pat ltac:(fun H => iClear H).

(** ** Simplification *)
Tactic Notation "iEval" tactic3(t) :=
  iStartProof;
  eapply tac_eval;
    [let x := fresh in intros x; t; unfold x; reflexivity
    |].

Local Ltac iEval_go t Hs :=
  lazymatch Hs with
  | [] => idtac
  | ESelPure :: ?Hs => fail "iEval: %: unsupported selection pattern"
  | ESelIdent _ ?H :: ?Hs =>
    eapply tac_eval_in with H _ _ _;
      [pm_reflexivity || let H := pretty_ident H in fail "iEval:" H "not found"
      |let x := fresh in intros x; t; unfold x; reflexivity
      |pm_reduce; iEval_go t Hs]
  end.

Tactic Notation "iEval" tactic3(t) "in" constr(Hs) :=
  iStartProof; let Hs := iElaborateSelPat Hs in iEval_go t Hs.

Tactic Notation "iSimpl" := iEval (simpl).
Tactic Notation "iSimpl" "in" constr(H) := iEval (simpl) in H.

Ltac _iUnfold r := iEval (unfold r).
Tactic Notation "iUnfold" ne_reference_list_sep(ids,",") :=
  ltac1_list_iter _iUnfold ids.

Ltac _iUnfold_in r H := iEval (unfold r) in H.
Tactic Notation "iUnfold" ne_reference_list_sep(ids,",") "in" constr(H) :=
  ltac1_list_iter ltac:(fun r => _iUnfold_in r H) ids.

(* It would be nice to also have an `iSsrRewrite`, however, for this we need to
pass arguments to Ssreflect's `rewrite` like `/= foo /bar` in Ltac, see:

  https://sympa.inria.fr/sympa/arc/coq-club/2018-01/msg00000.html

PMP told me (= Robbert) in person that this is not possible with the current
Ltac, but it may be possible in Ltac2. *)

(** * Assumptions *)
Tactic Notation "iExact" constr(H) :=
  eapply tac_assumption with H _ _; (* (i:=H) *)
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iExact:" H "not found"
    |tc_solve ||
     let H := pretty_ident H in
     let P := match goal with |- FromAssumption _ ?P _ => P end in
     fail "iExact:" H ":" P "does not match goal"
    |pm_reduce; tc_solve ||
     let H := pretty_ident H in
     fail "iExact: remaining hypotheses not affine and the goal not absorbing"].

Tactic Notation "iAssumptionCore" :=
  let rec find Γ i P :=
    lazymatch Γ with
    | Esnoc ?Γ ?j ?Q => first [unify P Q; unify i j|find Γ i P]
    end in
  match goal with
  | |- envs_lookup ?i (Envs ?Γp ?Γs _) = Some (_, ?P) =>
     first [is_evar i; fail 1 | pm_reflexivity]
  | |- envs_lookup ?i (Envs ?Γp ?Γs _) = Some (_, ?P) =>
     is_evar i; first [find Γp i P | find Γs i P]; pm_reflexivity
  | |- envs_lookup_delete _ ?i (Envs ?Γp ?Γs _) = Some (_, ?P, _) =>
     first [is_evar i; fail 1 | pm_reflexivity]
  | |- envs_lookup_delete _ ?i (Envs ?Γp ?Γs _) = Some (_, ?P, _) =>
     is_evar i; first [find Γp i P | find Γs i P]; pm_reflexivity
  end.

Tactic Notation "iAssumptionCoq" :=
  let Hass := fresh in
  match goal with
  | H : ⊢ ?P |- envs_entails _ ?Q =>
     pose proof (_ : FromAssumption false P Q) as Hass;
     notypeclasses refine (tac_assumption_coq _ P _ H _ _);
       [exact Hass
       |pm_reduce; tc_solve ||
        fail 2 "iAssumption: remaining hypotheses not affine and the goal not absorbing"]
  end.

Tactic Notation "iAssumption" :=
  let Hass := fresh in
  let rec find p Γ Q :=
    lazymatch Γ with
    | Esnoc ?Γ ?j ?P => first
       [pose proof (_ : FromAssumption p P Q) as Hass;
        eapply (tac_assumption _ j p P);
          [pm_reflexivity
          |exact Hass
          |pm_reduce; tc_solve ||
           fail 2 "iAssumption: remaining hypotheses not affine and the goal not absorbing"]
       |assert_fails (is_evar P);
        assert (P = False%I) as Hass by reflexivity;
        apply (tac_false_destruct _ j p P);
          [pm_reflexivity
          |exact Hass]
       |find p Γ Q]
    end in
  lazymatch goal with
  | |- envs_entails (Envs ?Γp ?Γs _) ?Q =>
     first [find true Γp Q
           |find false Γs Q
           |iAssumptionCoq
           |fail "iAssumption:" Q "not found"]
  end.

(** * False *)
Tactic Notation "iExFalso" :=
  iStartProof;
  apply tac_ex_falso.

(** * Making hypotheses intuitionistic or pure *)
Ltac _iIntuitionistic H H' :=
  eapply tac_intuitionistic with H H' _ _ _; (* (i:=H) (j:=H') *)
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iIntuitionistic:" H "not found"
    |tc_solve ||
     let P := match goal with |- IntoPersistent _ ?P _ => P end in
     fail "iIntuitionistic:" P "not persistent"
    |pm_reduce; tc_solve ||
     let P := match goal with |- TCOr (Affine ?P) _ => P end in
     fail "iIntuitionistic:" P "not affine and the goal not absorbing"
    |pm_reduce;
     lazymatch goal with
     | |- False =>
       let H' := pretty_ident H' in
       fail "iIntuitionistic:" H' "not fresh"
     | _ => idtac (* subgoal *)
     end].

Ltac _iSpatial H H' :=
  eapply tac_spatial with H H' _ _ _;
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iSpatial:" H "not found"
    |pm_reduce; tc_solve
    |pm_reduce;
     lazymatch goal with
     | |- False =>
       let H' := pretty_ident H' in
       fail "iSpatial:" H' "not fresh"
     | _ => idtac (* subgoal *)
     end].

Tactic Notation "iPure" constr(H) "as" simple_intropattern(pat) :=
  eapply tac_pure with H _ _ _; (* (i:=H1) *)
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iPure:" H "not found"
    |tc_solve ||
     let P := match goal with |- IntoPure ?P _ => P end in
     fail "iPure:" P "not pure"
    |pm_reduce; tc_solve ||
     let P := match goal with |- TCOr (Affine ?P) _ => P end in
     fail "iPure:" P "not affine and the goal not absorbing"
    |pm_reduce; intros pat].

Tactic Notation "iEmpIntro" :=
  iStartProof;
  eapply tac_emp_intro;
    [pm_reduce; tc_solve ||
     fail "iEmpIntro: spatial context contains non-affine hypotheses"].

Tactic Notation "iPureIntro" :=
  iStartProof;
  eapply tac_pure_intro;
    [tc_solve ||
     let P := match goal with |- FromPure _ ?P _ => P end in
     fail "iPureIntro:" P "not pure"
    |pm_reduce; tc_solve ||
     fail "iPureIntro: spatial context contains non-affine hypotheses"
    |].

(** Framing *)
(** Helper tactics are exposed for users that build their own custom framing
logic *)
Ltac iFrameFinish :=
  pm_prettify;
  try match goal with
  | |- envs_entails _ True => by iPureIntro
  | |- envs_entails _ emp => iEmpIntro
  end.

Ltac iFramePure t :=
  iStartProof;
  let φ := type of t in
  eapply (tac_frame_pure _ _ _ _ t);
    [tc_solve || fail "iFrame: cannot frame" φ
    |iFrameFinish].

Ltac iFrameHyp H :=
  iStartProof;
  eapply tac_frame with H _ _ _;
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iFrame:" H "not found"
    |tc_solve ||
     let R := match goal with |- Frame _ ?R _ _ => R end in
     fail "iFrame: cannot frame" R
    |pm_reduce; iFrameFinish].

Ltac iFrameAnyPure :=
  repeat match goal with H : _ |- _ => iFramePure H end.

Ltac iFrameAnyIntuitionistic :=
  iStartProof;
  let rec go Hs :=
    match Hs with [] => idtac | ?H :: ?Hs => repeat iFrameHyp H; go Hs end in
  match goal with
  | |- envs_entails ?Δ _ =>
     (* [lazy] because [Δ] involves user terms *)
     let Hs := eval lazy in (env_dom (env_intuitionistic Δ)) in go Hs
  end.

Ltac iFrameAnySpatial :=
  iStartProof;
  let rec go Hs :=
    match Hs with [] => idtac | ?H :: ?Hs => try iFrameHyp H; go Hs end in
  match goal with
  | |- envs_entails ?Δ _ =>
     (* [lazy] because [Δ] involves user terms *)
     let Hs := eval lazy in (env_dom (env_spatial Δ)) in go Hs
  end.

Local Ltac _iFrame_go Hs :=
  lazymatch Hs with
  | [] => idtac
  | SelPure :: ?Hs => iFrameAnyPure; _iFrame_go Hs
  | SelIntuitionistic :: ?Hs => iFrameAnyIntuitionistic; _iFrame_go Hs
  | SelSpatial :: ?Hs => iFrameAnySpatial; _iFrame_go Hs
  | SelIdent ?H :: ?Hs => iFrameHyp H; _iFrame_go Hs
  end.

Ltac _iFrame0 Hs :=
  let Hs := sel_pat.parse Hs in
  _iFrame_go Hs.
Ltac _iFrame ts Hs :=
  ltac1_list_iter iFramePure ts;
  _iFrame0 Hs.

Tactic Notation "iFrame" := iFrameAnySpatial.
Tactic Notation "iFrame" "(" ne_constr_list(ts) ")" := _iFrame ts "".
Tactic Notation "iFrame" constr(Hs) := _iFrame0 Hs.
Tactic Notation "iFrame" "(" ne_constr_list(ts) ")" constr(Hs) := _iFrame ts Hs.

Tactic Notation "iFrame" "select" open_constr(pat) :=
  iSelect pat ltac:(fun H => iFrameHyp H).

(** * Basic introduction tactics *)
Tactic Notation "_iIntro" "(" simple_intropattern(x) ")" :=
  (* In the case the goal starts with an [let x := _ in _], we do not
     want to unfold x and start the proof mode. Instead, we want to
     use intros. So [iStartProof] has to be called only if [intros]
     fails *)
  (* We use [_ || _] instead of [first [..|..]] so that the error in the second
  branch propagates upwards. *)
  (
    (* introduction at the meta level *)
    intros x
  ) || (
    (* introduction in the logic *)
    iStartProof;
    lazymatch goal with
    | |- envs_entails _ _ =>
      eapply tac_forall_intro;
        [tc_solve ||
         let P := match goal with |- FromForall ?P _ _ => P end in
         fail "iIntro: cannot turn" P "into a universal quantifier"
        |let name := lazymatch goal with
                     | |- let _ := (λ name, _) in _ => name
                     end in
         pm_prettify;
         let y := fresh name in
         intros y; revert y; intros x
         (* subgoal *)]
    end).

Ltac _iIntroSpatial H :=
  iStartProof;
  first
  [(* (?Q → _) *)
    eapply tac_impl_intro with H _ _ _; (* (i:=H) *)
      [tc_solve
      |pm_reduce; tc_solve ||
       let P := lazymatch goal with |- Persistent ?P => P end in
       let H := pretty_ident H in
       fail 1 "iIntro: introducing non-persistent" H ":" P
              "into non-empty spatial context"
      |tc_solve
      |pm_reduce;
       let H := pretty_ident H in
        lazymatch goal with
        | |- False =>
          let H := pretty_ident H in
          fail 1 "iIntro:" H "not fresh"
        | _ => idtac (* subgoal *)
        end]
  |(* (_ -∗ _) *)
    eapply tac_wand_intro with H _ _; (* (i:=H) *)
      [tc_solve
      | pm_reduce;
        lazymatch goal with
        | |- False =>
          let H := pretty_ident H in
          fail 1 "iIntro:" H "not fresh"
        | _ => idtac (* subgoal *)
        end]
  | let H := pretty_ident H in
    fail 1 "iIntro: could not introduce" H ", goal is not a wand or implication" ].

Ltac _iIntroPersistent H :=
  iStartProof;
  first
  [(* (?P → _) *)
   eapply tac_impl_intro_intuitionistic with H _ _ _; (* (i:=H) *)
     [tc_solve
     |tc_solve ||
      let P := match goal with |- IntoPersistent _ ?P _ => P end in
      fail 1 "iIntro:" P "not persistent"
     |pm_reduce;
      lazymatch goal with
      | |- False =>
        let H := pretty_ident H in
        fail 1 "iIntro:" H "not fresh"
      | _ => idtac (* subgoal *)
      end]
  |(* (?P -∗ _) *)
   eapply tac_wand_intro_intuitionistic with H _ _ _; (* (i:=H) *)
     [tc_solve
     |tc_solve ||
      let P := match goal with |- IntoPersistent _ ?P _ => P end in
      fail 1 "iIntro:" P "not intuitionistic"
     |tc_solve ||
      let P := match goal with |- TCOr (Affine ?P) _ => P end in
      fail 1 "iIntro:" P "not affine and the goal not absorbing"
     |pm_reduce;
      lazymatch goal with
      | |- False =>
        let H := pretty_ident H in
        fail 1 "iIntro:" H "not fresh"
      | _ => idtac (* subgoal *)
      end]
  |fail 1 "iIntro: nothing to introduce"].

(* Introduce [H] into persistent (if [p] is true) or spatial (if [p] is false)
context *)
Ltac _iIntroMaybePersistent H p :=
  lazymatch p with
  | true => _iIntroPersistent H
  | _ =>  _iIntroSpatial H
  end.

Ltac _iIntroDrop :=
  iStartProof;
  first
  [(* (?Q → _) *)
   eapply tac_impl_intro_drop;
     [tc_solve
     |(* subgoal *)]
  |(* (_ -∗ _) *)
   eapply tac_wand_intro_drop;
     [tc_solve
     |tc_solve ||
      let P := match goal with |- TCOr (Affine ?P) _ => P end in
      fail 1 "iIntro:" P "not affine and the goal not absorbing"
     |(* subgoal *)]
  |(* (∀ _, _) *)
   _iIntro (_)
   (* subgoal *)
  |fail 1 "iIntro: nothing to introduce"].

Ltac _iIntroForall :=
  lazymatch goal with
  | |- ∀ _, ?P => fail (* actually an →, this is handled by iIntro below *)
  | |- ∀ _, _ => intro
  | |- let _ := _ in _ => intro
  | |- _ =>
    iStartProof;
    lazymatch goal with
    | |- envs_entails _ (∀ x : _, _) => let x' := fresh x in _iIntro (x')
    end
  end.
Ltac _iIntro :=
  lazymatch goal with
  | |- _ → ?P => intro
  | |- _ =>
    iStartProof;
    lazymatch goal with
    | |- envs_entails _ (_ -∗ _) => _iIntro (?) ||
        let H := iFresh in
        _iIntroPersistent H ||
        _iIntroSpatial H
    | |- envs_entails _ (_ → _) => _iIntro (?) ||
         let H := iFresh in
         _iIntroSpatial H ||
         _iIntroSpatial H
    end
  end.

(** * Revert *)
Ltac iForallRevert x :=
  let err x :=
    intros x;
    iMatchHyp (fun H P =>
      lazymatch P with
      | context [x] =>
         let H := pretty_ident H in fail 2 "iRevert:" x "is used in hypothesis" H
      end) in
  iStartProof;
  first [let A := type of x in idtac|fail 1 "iRevert:" x "not in scope"];
  let A := type of x in
  lazymatch type of A with
  | Prop =>
     revert x; first
       [eapply tac_pure_revert;
         [tc_solve (* [MakeAffinely], should never fail *)
         |]
       |err x]
  | _ =>
    revert x; first
      [apply tac_forall_revert;
       (* Ensure the name [x] is preserved, see [test_iRevert_order_and_names]. *)
       lazymatch goal with
       | |- envs_entails ?Δ (bi_forall ?P) =>
         change (envs_entails Δ (∀ x, P x)); lazy beta
       end
      |err x]
  end.

(** The tactic [iRevertHyp H with tac] reverts the hypothesis [H] and calls
[tac] with a Boolean that is [true] iff [H] was in the intuitionistic context. *)
Tactic Notation "iRevertHyp" constr(H) "with" tactic1(tac) :=
  eapply tac_revert with H;
    [lazymatch goal with
     | |- match envs_lookup_delete true ?i ?Δ with _ => _ end =>
        lazymatch eval pm_eval in (envs_lookup_delete true i Δ) with
        | Some (?p,_,_) => pm_reduce; tac p
        | None =>
           let H := pretty_ident H in
           fail "iRevert:" H "not found"
        end
     end].

Tactic Notation "iRevertHyp" constr(H) := iRevertHyp H with (fun _ => idtac).

Ltac _iRevert_go Hs :=
  lazymatch Hs with
  | [] => idtac
  | ESelPure :: ?Hs =>
     repeat match goal with x : _ |- _ => revert x end;
     _iRevert_go Hs
  | ESelIdent _ ?H :: ?Hs => iRevertHyp H; _iRevert_go Hs
  end.

Ltac _iRevert0 Hs :=
  iStartProof;
  let Hs := iElaborateSelPat Hs in
  _iRevert_go Hs.
Ltac _iRevert xs Hs :=
  _iRevert0 Hs;
  ltac1_list_rev_iter iForallRevert xs.

Tactic Notation "iRevert" constr(Hs) := _iRevert0 Hs.
Tactic Notation "iRevert" "(" ne_ident_list(xs) ")" := _iRevert xs "".
Tactic Notation "iRevert" "(" ne_ident_list(xs) ")" constr(Hs) := _iRevert xs Hs.

Tactic Notation "iRevert" "select" open_constr(pat) :=
  iSelect pat ltac:(fun H => iRevertHyp H).

(** * The specialize and pose proof tactics *)
Record iTrm {X As S} :=
  ITrm { itrm : X ; itrm_vars : hlist As ; itrm_hyps : S }.
Global Arguments ITrm {_ _ _} _ _ _.

Notation "( H $! x1 .. xn )" :=
  (ITrm H (hcons x1 .. (hcons xn hnil) ..) "") (at level 0, x1, xn at level 9).
Notation "( H $! x1 .. xn 'with' pat )" :=
  (ITrm H (hcons x1 .. (hcons xn hnil) ..) pat) (at level 0, x1, xn at level 9).
Notation "( H 'with' pat )" := (ITrm H hnil pat) (at level 0).

Tactic Notation "iPoseProofCoreHyp" constr(H) "as" constr(Hnew) :=
  let Δ := iGetCtx in
  notypeclasses refine (tac_pose_proof_hyp _ H Hnew _ _);
    pm_reduce;
    lazymatch goal with
    | |- False =>
      let lookup := pm_eval (envs_lookup_delete false H Δ) in
      lazymatch lookup with
      | None =>
        let H := pretty_ident H in
        fail "iPoseProof:" H "not found"
      | _ =>
        let Hnew := pretty_ident Hnew in
        fail "iPoseProof:" Hnew "not fresh"
      end
    | _ => idtac
    end.

(* The tactic [iIntoEmpValid] tactic "imports a Coq lemma into the proofmode",
i.e., it solves a goal [IntoEmpValid ψ ?Q]. The argument [ψ] must be of the
following shape:

[∀ (x_1 : A_1) .. (x_n : A_n), φ]

for which we have an instance [AsEmpValid DirectionIntoEmpValid φ ?Q].

Examples of such [φ]s are

- [⊢ P], in which case [?Q] is unified with [P].
- [P1 ⊢ P2], in which case [?Q] is unified with [P1 -∗ P2].
- [P1 ⊣⊢ P2], in which case [?Q] is unified with [P1 ↔ P2].

The tactic instantiates each dependent argument [x_i : A_i] with an evar, and
generates a goal [A_i] for each non-dependent argument [x_i : A_i].

For example, if goal is [IntoEmpValid (∀ x, P x → R1 x ⊢ R2 x) ?Q], then the
[iIntoEmpValid] tactic generates an evar [?x], a subgoal [P ?x], and unifies
[?Q] with [R1 ?x -∗ R2 ?x].

The tactic is implemented so as to provide a "fast path" for the arrow, forall
and tforall cases, gated by syntactic ltac pattern matching on the shape of the
goal. This is an optimization: the behavior of the tactic is equivalent to the
code in the last "wildcard" case, but faster on larger goals, where running
(possibly failing) [notypeclasses refine]s can take a significant amount of
time.
*)
Ltac iIntoEmpValid_go :=
  lazymatch goal with
  | |- IntoEmpValid (let _ := _ in _) _ =>
    (* Normalize [let] so we don't need to rely on type class search to do so.
    Letting type class search do so is unreliable, see Iris issue #520, and test
    [test_apply_wand_below_let]. *)
    lazy zeta; iIntoEmpValid_go
  | |- IntoEmpValid (?φ → ?ψ) _ =>
    (* Case [φ → ψ] *)
    (* note: the ltac pattern [_ → _] would not work as it would also match
       [∀ _, _] *)
    notypeclasses refine (into_emp_valid_impl _ _ _ _ _);
      [(*goal for [φ] *)|iIntoEmpValid_go]
  | |- IntoEmpValid (∀ _, _) _ =>
    (* Case [∀ x : A, φ] *)
    notypeclasses refine (into_emp_valid_forall _ _ _ _); iIntoEmpValid_go
  | |- IntoEmpValid (∀.. _, _) _ =>
    (* Case [∀.. x : TT, φ] *)
    notypeclasses refine (into_emp_valid_tforall _ _ _ _); iIntoEmpValid_go
  | |- _ =>
    first
      [(* Case [φ → ψ] *)
       notypeclasses refine (into_emp_valid_impl _ _ _ _ _);
         [(*goal for [φ] *)|iIntoEmpValid_go]
      |(* Case [∀ x : A, φ] *)
       notypeclasses refine (into_emp_valid_forall _ _ _ _); iIntoEmpValid_go
      |(* Case [∀.. x : TT, φ] *)
       notypeclasses refine (into_emp_valid_tforall _ _ _ _); iIntoEmpValid_go
      |(* Case [P ⊢ Q], [P ⊣⊢ Q], [⊢ P] *)
       notypeclasses refine (into_emp_valid_here _ _ _) ]
  end.

Ltac iIntoEmpValid :=
  (* Factor out the base case of the loop to avoid needless backtracking *)
  iIntoEmpValid_go;
    [.. (* goals for premises *)
    |tc_solve ||
     lazymatch goal with |- @AsEmpValid ?PROP _ ?φ _ =>
        fail "iPoseProof:" φ "not a" PROP "assertion" end].

Tactic Notation "iPoseProofCoreLem" open_constr(lem) "as" tactic3(tac) :=
  let Hnew := iFresh in
  notypeclasses refine (tac_pose_proof _ Hnew _ _ (into_emp_valid_proj _ _ _ lem) _);
    [iIntoEmpValid
    |pm_reduce;
     lazymatch goal with
     | |- False =>
       let Hnew := pretty_ident Hnew in
       fail "iPoseProof:" Hnew "not fresh"
     | _ => tac Hnew
     end];
  (* Solve all remaining TC premises generated by [iIntoEmpValid] *)
  try tc_solve.

(** There is some hacky stuff going on here: because of Coq bug #6583, unresolved
type classes in e.g. the arguments [xs] of [iSpecializeArgs_go] are resolved at
arbitrary moments. That is because tactics like [apply], [split] and [eexists]
wrongly trigger type class search. To avoid TC being triggered too eagerly, the
tactics below use [notypeclasses refine] instead of [apply], [split] and
[eexists]. *)
Local Ltac iSpecializeArgs_go H xs :=
  lazymatch xs with
  | hnil => idtac
  | hcons ?x ?xs =>
     notypeclasses refine (tac_forall_specialize _ H _ _ _ _ _ _ _);
       [pm_reflexivity ||
        let H := pretty_ident H in
        fail "iSpecialize:" H "not found"
       |tc_solve ||
        let P := match goal with |- IntoForall ?P _ => P end in
        fail "iSpecialize: cannot instantiate" P "with" x
       |lazymatch goal with (* Force [A] in [ex_intro] to deal with coercions. *)
        | |- ∃ _ : ?A, _ =>
          notypeclasses refine (@ex_intro A _ x _)
        end; [shelve..|pm_reduce; iSpecializeArgs_go H xs]]
  end.
Local Tactic Notation "iSpecializeArgs" constr(H) open_constr(xs) :=
  iSpecializeArgs_go H xs.

Ltac iSpecializePat_go H1 pats :=
  let solve_to_wand H1 :=
    tc_solve ||
    let P := match goal with |- IntoWand _ _ ?P _ _ => P end in
    fail "iSpecialize:" P "not an implication/wand" in
  let solve_done d :=
    lazymatch d with
    | true =>
       first [ done
             | let Q := match goal with |- envs_entails _ ?Q => Q end in
               fail 1 "iSpecialize: cannot solve" Q "using done"
             | let Q := match goal with |- ?Q => Q end in
               fail 1 "iSpecialize: cannot solve" Q "using done" ]
    | false => idtac
    end in
  let Δ := iGetCtx in
  lazymatch pats with
    | [] => idtac
    | SIdent ?H2 [] :: ?pats =>
       (* If we not need to specialize [H2] we can avoid a lot of unncessary
       context manipulation. *)
       notypeclasses refine (tac_specialize false _ H2 _ H1 _ _ _ _ _ _ _ _ _);
         [pm_reflexivity ||
          let H2 := pretty_ident H2 in
          fail "iSpecialize:" H2 "not found"
         |pm_reflexivity ||
          let H1 := pretty_ident H1 in
          fail "iSpecialize:" H1 "not found"
         |tc_solve ||
          let P := match goal with |- IntoWand _ _ ?P ?Q _ => P end in
          let Q := match goal with |- IntoWand _ _ ?P ?Q _ => Q end in
          fail "iSpecialize: cannot instantiate" P "with" Q
         |pm_reduce; iSpecializePat_go H1 pats]
    | SIdent ?H2 ?pats1 :: ?pats =>
       (* If [H2] is in the intuitionistic context, we copy it into a new
       hypothesis [Htmp], so that it can be used multiple times. *)
       let H2tmp := iFresh in
       iPoseProofCoreHyp H2 as H2tmp;
       (* Revert [H1] and re-introduce it later so that it will not be consumsed
       by [pats1]. *)
       iRevertHyp H1 with (fun p =>
         iSpecializePat_go H2tmp pats1;
           [.. (* side-conditions of [iSpecialize] *)
           |_iIntroMaybePersistent H1 p]);
         (* We put the stuff below outside of the closure to get less verbose
         Ltac backtraces (which would otherwise include the whole closure). *)
         [.. (* side-conditions of [iSpecialize] *)
         |(* Use [remove_intuitionistic = true] to remove the copy [Htmp]. *)
          notypeclasses refine (tac_specialize true _ H2tmp _ H1 _ _ _ _ _ _ _ _ _);
            [pm_reflexivity ||
             let H2tmp := pretty_ident H2tmp in
             fail "iSpecialize:" H2tmp "not found"
            |pm_reflexivity ||
             let H1 := pretty_ident H1 in
             fail "iSpecialize:" H1 "not found"
            |tc_solve ||
             let P := match goal with |- IntoWand _ _ ?P ?Q _ => P end in
             let Q := match goal with |- IntoWand _ _ ?P ?Q _ => Q end in
             fail "iSpecialize: cannot instantiate" P "with" Q
            |pm_reduce; iSpecializePat_go H1 pats]]
    | SPureGoal ?d :: ?pats =>
       notypeclasses refine (tac_specialize_assert_pure _ H1 _ _ _ _ _ _ _ _ _ _ _ _);
         [pm_reflexivity ||
          let H1 := pretty_ident H1 in
          fail "iSpecialize:" H1 "not found"
         |solve_to_wand H1
         |tc_solve ||
          let Q := match goal with |- FromPure _ ?Q _ => Q end in
          fail "iSpecialize:" Q "not pure"
         |solve_done d (*goal*)
         |pm_reduce;
          iSpecializePat_go H1 pats]
    | SGoal (SpecGoal GIntuitionistic false ?Hs_frame [] ?d) :: ?pats =>
       notypeclasses refine (tac_specialize_assert_intuitionistic _ H1 _ _ _ _ _ _ _ _ _ _ _ _);
         [pm_reflexivity ||
          let H1 := pretty_ident H1 in
          fail "iSpecialize:" H1 "not found"
         |solve_to_wand H1
         |tc_solve ||
          let Q := match goal with |- Persistent ?Q => Q end in
          fail "iSpecialize:" Q "not persistent"
         |tc_solve
         |pm_reduce; iFrame Hs_frame; solve_done d (*goal*)
         |pm_reduce; iSpecializePat_go H1 pats]
    | SGoal (SpecGoal GIntuitionistic _ _ _ _) :: ?pats =>
       fail "iSpecialize: cannot select hypotheses for intuitionistic premise"
    | SGoal (SpecGoal ?m ?lr ?Hs_frame ?Hs ?d) :: ?pats =>
       let Hs' := eval cbv in (if lr then Hs else Hs_frame ++ Hs) in
       notypeclasses refine (tac_specialize_assert _ H1 _
           (if m is GModal then true else false) lr Hs' _ _ _ _ _ _ _ _ _);
         [pm_reflexivity ||
          let H1 := pretty_ident H1 in
          fail "iSpecialize:" H1 "not found"
         |solve_to_wand H1
         |tc_solve || fail "iSpecialize: goal not a modality"
         |pm_reduce;
          lazymatch goal with
          | |- False =>
            let Hs' := iMissingHypsCore Δ Hs' in
            fail "iSpecialize: hypotheses" Hs' "not found"
          | _ =>
            notypeclasses refine (conj _ _);
              [iFrame Hs_frame; solve_done d (*goal*)
              |iSpecializePat_go H1 pats]
          end]
    | SAutoFrame GIntuitionistic :: ?pats =>
       notypeclasses refine (tac_specialize_assert_intuitionistic _ H1 _ _ _ _ _ _ _ _ _ _ _ _);
         [pm_reflexivity ||
          let H1 := pretty_ident H1 in
          fail "iSpecialize:" H1 "not found"
         |solve_to_wand H1
         |tc_solve ||
          let Q := match goal with |- Persistent ?Q => Q end in
          fail "iSpecialize:" Q "not persistent"
         |tc_solve ||
          fail "iSpecialize: Cannot find IntoAbsorbingly;"
               "this should not happen, please report a bug"
         |pm_reduce; solve [iFrame "∗ #"]
         |pm_reduce; iSpecializePat_go H1 pats]
    | SAutoFrame ?m :: ?pats =>
       notypeclasses refine (tac_specialize_frame _ H1 _
           (if m is GModal then true else false) _ _ _ _ _ _ _ _ _ _ _);
         [pm_reflexivity ||
          let H1 := pretty_ident H1 in
          fail "iSpecialize:" H1 "not found"
         |solve_to_wand H1
         |tc_solve || fail "iSpecialize: goal not a modality"
         |pm_reduce;
          first
            [notypeclasses refine (tac_unlock_emp _ _ _)
            |notypeclasses refine (tac_unlock_True _ _ _)
            |iFrame "∗ #"; notypeclasses refine (tac_unlock _ _ _)
            |let P :=
               match goal with |- envs_entails _ (?P ∗ locked _)%I => P end in
             fail 1 "iSpecialize: premise" P "cannot be solved by framing"]
         |exact eq_refl]; _iIntroSpatial H1; iSpecializePat_go H1 pats
    end.

Local Tactic Notation "iSpecializePat" open_constr(H) constr(pat) :=
  let pats := spec_pat.parse pat in iSpecializePat_go H pats.

(** The tactics [iSpecialize trm as #] and [iSpecializeCore trm as true] allow
one to use the entire spatial context /twice/: the first time for proving the
premises [Q1 .. Qn] of [H : Q1 -* .. -∗ Qn -∗ R], and the second time for
proving the remaining goal. This is possible if all of the following properties
hold:
1. The conclusion [R] of the hypothesis [H] is persistent.
2. The specialization pattern [[> ..]] for wrapping a modality is not used for
   any of the premises [Q1 .. Qn].
3. The BI is either affine, or the hypothesis [H] resides in the intuitionistic
   context.

The copying of the context for proving the premises of [H] and the remaining
goal is implemented using the lemma [tac_specialize_intuitionistic_helper].

Since the tactic [iSpecialize .. as #] is used a helper to implement
[iDestruct .. as "#.."], [iPoseProof .. as "#.."], [iSpecialize .. as "#.."],
and friends, the behavior on violations of these conditions is as follows:

- If condition 1 is violated (i.e. the conclusion [R] of [H] is not persistent),
  the tactic will fail.
- If condition 2 or 3 is violated, the tactic will fall back to consuming the
  hypotheses for proving the premises [Q1 .. Qn]. That is, it will fall back to
  not using [tac_specialize_intuitionistic_helper].

The function [use_tac_specialize_intuitionistic_helper Δ pat] below returns
[true] iff the specialization pattern [pat] consumes any spatial hypotheses,
and does not contain the pattern [[> ..]] (cf. condition 2). If the function
returns [false], then the conclusion can be moved in the intuitionistic context
even if conditions 1 and 3 do not hold. Therefore, in that case, we prefer
putting the conclusion to the intuitionistic context directly and not using
[tac_specialize_intuitionistic_helper], which requires conditions 1 and 3. *)
Fixpoint use_tac_specialize_intuitionistic_helper {M}
    (Δ : envs M) (pats : list spec_pat) : bool :=
  match pats with
  | [] => false
  | SPureGoal _ :: pats =>
     use_tac_specialize_intuitionistic_helper Δ pats
  | SAutoFrame _ :: _ => true
  | SIdent H _ :: pats =>
     match envs_lookup_delete false H Δ with
     | Some (false, _, Δ) => true
     | Some (true, _, Δ) => use_tac_specialize_intuitionistic_helper Δ pats
     | None => false (* dummy case (invalid pattern, will fail in the tactic anyway) *)
     end
  | SGoal (SpecGoal GModal _ _ _ _) :: _ => false
  | SGoal (SpecGoal GIntuitionistic _ _ _ _) :: pats =>
     use_tac_specialize_intuitionistic_helper Δ pats
  | SGoal (SpecGoal GSpatial neg Hs_frame Hs _) :: pats =>
     match envs_split (if neg is true then Right else Left)
                      (if neg then Hs else pm_app Hs_frame Hs) Δ with
     | Some (Δ1,Δ2) => if env_spatial_is_nil Δ1
                       then use_tac_specialize_intuitionistic_helper Δ2 pats
                       else true
     | None => false (* dummy case (invalid pattern, will fail in the tactic anyway) *)
     end
  end.

(** The argument [p] of [iSpecializeCore] can either be a Boolean, or an
introduction pattern that is coerced into [true] when it solely contains [#] or
[%] patterns at the top-level. *)
Tactic Notation "iSpecializeCore" open_constr(H)
    "with" open_constr(xs) open_constr(pat) "as" constr(p) :=
  let p := intro_pat_intuitionistic p in
  let pat := spec_pat.parse pat in
  let H :=
    lazymatch type of H with
    | string => constr:(INamed H)
    | _ => H
    end in
  iSpecializeArgs H xs; [..|
    lazymatch type of H with
    | ident =>
       let pat := spec_pat.parse pat in
       let Δ := iGetCtx in
       (* Check if we should use [tac_specialize_intuitionistic_helper]. Notice
       that [pm_eval] does not unfold [use_tac_specialize_intuitionistic_helper],
       so we should do that first. *)
       (* [lazy] because [Δ] involves user terms *)
       let b := eval lazy [use_tac_specialize_intuitionistic_helper] in
         (if p then use_tac_specialize_intuitionistic_helper Δ pat else false) in
       lazymatch eval pm_eval in b with
       | true =>
          (* Check that the BI is either affine, or the hypothesis [H] resides
          in the intuitionistic context. *)
          lazymatch iTypeOf H with
          | Some (?q, _) =>
             let PROP := iBiOfGoal in
             (* [lazy] because [PROP] involves user terms *)
             lazymatch eval lazy in (q || tc_to_bool (BiAffine PROP)) with
             | true =>
                notypeclasses refine (tac_specialize_intuitionistic_helper _ H _ _ _ _ _ _ _ _ _ _);
                  [pm_reflexivity
                   (* This premise, [envs_lookup j Δ = Some (q,P)],
                   holds because the [iTypeOf] above succeeded *)
                  |pm_reduce; tc_solve
                   (* This premise, [if q then TCTrue else BiAffine PROP], holds
                   because we established that [q || TC_to_bool (BiAffine PROP)]
                   is true *)
                  |iSpecializePat H pat;
                    [..
                    |notypeclasses refine (tac_specialize_intuitionistic_helper_done _ H _ _ _);
                     pm_reflexivity]
                  |tc_solve ||
                   let Q := match goal with |- IntoPersistent _ ?Q _ => Q end in
                   fail "iSpecialize:" Q "not persistent"
                  |pm_reduce (* goal *)]
             | false => iSpecializePat H pat
             end
          | None =>
             let H := pretty_ident H in
             fail "iSpecialize:" H "not found"
          end
       | false => iSpecializePat H pat
       end
    | _ => fail "iSpecialize:" H "should be a hypothesis, use iPoseProof instead"
    end].

Tactic Notation "iSpecializeCore" open_constr(t) "as" constr(p) :=
  lazymatch type of t with
  | string => iSpecializeCore t with hnil "" as p
  | ident => iSpecializeCore t with hnil "" as p
  | _ =>
    lazymatch t with
    | ITrm ?H ?xs ?pat => iSpecializeCore H with xs pat as p
    | _ => fail "iSpecialize:" t "should be a proof mode term"
    end
  end.

Tactic Notation "iSpecialize" open_constr(t) :=
  iSpecializeCore t as false.
Tactic Notation "iSpecialize" open_constr(t) "as" "#" :=
  iSpecializeCore t as true.

(** The tactic [iPoseProofCore lem as p tac] inserts the resource
described by [lem] into the context. The tactic takes a continuation [tac] as
its argument, which is called with a temporary fresh name [H] that refers to
the hypothesis containing [lem].

The argument [p] is like that of [iSpecialize]. It is a Boolean that denotes
whether the conclusion of the specialized term [lem] is persistent. *)
Tactic Notation "iPoseProofCore" open_constr(lem)
    "as" constr(p) tactic3(tac) :=
  iStartProof;
  let t := lazymatch lem with ITrm ?t ?xs ?pat => t | _ => lem end in
  let t := lazymatch type of t with string => constr:(INamed t) | _ => t end in
  let spec_tac Htmp :=
    lazymatch lem with
    | ITrm _ ?xs ?pat => iSpecializeCore (ITrm Htmp xs pat) as p
    | _ => idtac
    end in
  lazymatch type of t with
  | ident =>
     let Htmp := iFresh in
     iPoseProofCoreHyp t as Htmp; spec_tac Htmp; [..|tac Htmp]
  | _ => iPoseProofCoreLem t as (fun Htmp => spec_tac Htmp; [..|tac Htmp])
  end.

(** * The apply tactic *)
(** [iApply lem] takes an argument [lem : P₁ -∗ .. -∗ Pₙ -∗ Q] (after the
specialization patterns in [lem] have been executed), where [Q] should match
the goal, and generates new goals [P1] ... [Pₙ]. Depending on the number of
premises [n], the tactic will have the following behavior:

- If [n = 0], it will immediately solve the goal (i.e. it will not generate any
  subgoals). When working in a general BI, this means that the tactic can fail
  in case there are non-affine spatial hypotheses in the context prior to using
  the [iApply] tactic. Note that if [n = 0], the tactic behaves exactly like
  [iExact lem].
- If [n > 0] it will generate a goals [P₁] ... [Pₙ]. All spatial hypotheses
  will be transferred to the last goal, i.e. [Pₙ]; the other goals will receive
  no spatial hypotheses. If you want to control more precisely how the spatial
  hypotheses are subdivided, you should add additional introduction patterns to
  [lem]. *)

(* The helper [iApplyHypExact] takes care of the [n=0] case. It fails with level
0 if we should proceed to the [n > 0] case, and with level 1 if there is an
actual error. *)
Local Ltac iApplyHypExact H :=
  eapply tac_assumption with H _ _; (* (i:=H) *)
    [pm_reflexivity
    |tc_solve
    |pm_reduce; tc_solve ||
     fail 1 "iApply: remaining hypotheses not affine and the goal not absorbing"].

Local Ltac iApplyHypLoop H :=
  first
    [eapply tac_apply with H _ _ _;
      [pm_reflexivity
      |tc_solve
      |pm_reduce]
    |iSpecializePat H "[]"; last iApplyHypLoop H].

Tactic Notation "iApplyHyp" constr(H) :=
  first
    [iApplyHypExact H
    |iApplyHypLoop H
    |lazymatch iTypeOf H with
     | Some (_,?Q) => fail 1 "iApply: cannot apply" Q
     end].

Tactic Notation "iApply" open_constr(lem) :=
  iPoseProofCore lem as false (fun H => iApplyHyp H);
  pm_prettify. (* reduce redexes created by instantiation; this is done at the
  very end after all type classes have been solved. *)

(** * Disjunction *)
Tactic Notation "iLeft" :=
  iStartProof;
  eapply tac_or_l;
    [tc_solve ||
     let P := match goal with |- FromOr ?P _ _ => P end in
     fail "iLeft:" P "not a disjunction"
    |(* subgoal *)].
Tactic Notation "iRight" :=
  iStartProof;
  eapply tac_or_r;
    [tc_solve ||
     let P := match goal with |- FromOr ?P _ _ => P end in
     fail "iRight:" P "not a disjunction"
    |(* subgoal *)].

Tactic Notation "iOrDestruct" constr(H) "as" constr(H1) constr(H2) :=
  eapply tac_or_destruct with H _ H1 H2 _ _ _; (* (i:=H) (j1:=H1) (j2:=H2) *)
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iOrDestruct:" H "not found"
    |tc_solve ||
     let P := match goal with |- IntoOr ?P _ _ => P end in
     fail "iOrDestruct: cannot destruct" P
    | pm_reduce;
      lazymatch goal with
      | |- False =>
        let H1 := pretty_ident H1 in
        let H2 := pretty_ident H2 in
        fail "iOrDestruct:" H1 "or" H2 "not fresh"
      |  _ => split
      end].

(** * Conjunction and separating conjunction *)
Tactic Notation "iSplit" :=
  iStartProof;
  eapply tac_and_split;
    [tc_solve ||
     let P := match goal with |- FromAnd ?P _ _ => P end in
     fail "iSplit:" P "not a conjunction"
    |(* subgoal 1 *)
    |(* subgoal 2 *)].

Tactic Notation "iSplitL" constr(Hs) :=
  iStartProof;
  let Hs := String.words Hs in
  let Hs := eval vm_compute in (INamed <$> Hs) in
  let Δ := iGetCtx in
  eapply tac_sep_split with Left Hs _ _; (* (js:=Hs) *)
    [tc_solve ||
     let P := match goal with |- FromSep ?P _ _ => P end in
     fail "iSplitL:" P "not a separating conjunction"
    |pm_reduce;
     lazymatch goal with
     | |- False => let Hs := iMissingHypsCore Δ Hs in
                 fail "iSplitL: hypotheses" Hs "not found"
     | _ => split; [(* subgoal 1 *)|(* subgoal 2 *)]
     end].

Tactic Notation "iSplitR" constr(Hs) :=
  iStartProof;
  let Hs := String.words Hs in
  let Hs := eval vm_compute in (INamed <$> Hs) in
  let Δ := iGetCtx in
  eapply tac_sep_split with Right Hs _ _; (* (js:=Hs) *)
    [tc_solve ||
     let P := match goal with |- FromSep ?P _ _ => P end in
     fail "iSplitR:" P "not a separating conjunction"
    |pm_reduce;
     lazymatch goal with
     | |- False => let Hs := iMissingHypsCore Δ Hs in
                 fail "iSplitR: hypotheses" Hs "not found"
     | _ => split; [(* subgoal 1 *)|(* subgoal 2 *)]
     end].

Tactic Notation "iSplitL" := iSplitR "".
Tactic Notation "iSplitR" := iSplitL "".

(* iDestruct H as [H1 H2] *)
Ltac _iAndDestruct H H1 H2 :=
  eapply tac_and_destruct with H _ H1 H2 _ _ _; (* (i:=H) (j1:=H1) (j2:=H2) *)
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iAndDestruct:" H "not found"
    |pm_reduce; tc_solve ||
     let P :=
       lazymatch goal with
       | |- IntoSep ?P _ _ => P
       | |- IntoAnd _ ?P _ _ => P
       end in
     fail "iAndDestruct: cannot destruct" P
    |pm_reduce;
     lazymatch goal with
       | |- False =>
         let H1 := pretty_ident H1 in
         let H2 := pretty_ident H2 in
         fail "iAndDestruct:" H1 "or" H2 "not fresh"
       | _ => idtac (* subgoal *)
     end].

(* iDestruct H as (depending on d) [H _] or [_ H] *)
Ltac _iAndDestructChoice H d H' :=
  eapply tac_and_destruct_choice with H _ d H' _ _ _;
    [pm_reflexivity || fail "iAndDestructChoice:" H "not found"
    |pm_reduce; tc_solve ||
     let P := match goal with |- TCOr (IntoAnd _ ?P _ _) _ => P end in
     fail "iAndDestructChoice: cannot destruct" P
    |pm_reduce;
     lazymatch goal with
     | |- False =>
       let H' := pretty_ident H' in
       fail "iAndDestructChoice:" H' "not fresh"
     | _ => idtac (* subgoal *)
     end].

(** * Existential *)

Ltac _iExists x :=
  iStartProof;
  eapply tac_exist;
    [tc_solve ||
     let P := match goal with |- FromExist ?P _ => P end in
     fail "iExists:" P "not an existential"
    |pm_prettify; eexists x
     (* subgoal *) ].

Tactic Notation "iExists" ne_uconstr_list_sep(xs,",") :=
  ltac1_list_iter _iExists xs.

Ltac _iExistDestructFail P := first
  [ (* Give a special error message if one tries to destruct [▷ ∃ x : A. Q]
    without [A] being inhabited, or some variation thereof (e.g., with other
    modalities in between). *)
    (* Search for [IntoExist] with the assumption that any type is inhabited.
    Here, [T] contains the type class query, [t] will be the instance (failure
    happens if no instance is found, in which case the default error is given by
    backtracking to the second branch of [first].
    We then match on the type of the instance [t] to extract the type for which
    no [Inhabited] instance could be found. *)
    let T := open_constr:((∀ B, Inhabited B) → IntoExist P _ _) in
    let t := constr:(_ : T) in
    lazymatch type of t with
    | _ → IntoExist (A:=?A) _ _ _ => fail 1 "iExistDestruct: cannot destruct" P
        "because no `Inhabited` instance for" A "could be found"
    end
  | fail 1 "iExistDestruct: cannot destruct" P ].
Tactic Notation "_iExistDestruct" constr(H)
    "as" simple_intropattern(x) constr(Hx) :=
  eapply tac_exist_destruct with H _ Hx _ _ _; (* (i:=H) (j:=Hx) *)
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iExistDestruct:" H "not found"
    |tc_solve ||
     let P := match goal with |- IntoExist ?P _ _ => P end in
     _iExistDestructFail P|];
    let name := lazymatch goal with
                | |- let _ := (λ name, _) in _ => name
                end in
    intros _;
    let y := fresh name in
    intros y; pm_reduce;
    lazymatch goal with
    | |- False =>
      let Hx := pretty_ident Hx in
      fail "iExistDestruct:" Hx "not fresh"
    | _ => revert y; intros x (* subgoal *)
    end.

(** * Modality introduction *)
Tactic Notation "iModIntro" uconstr(sel) :=
  iStartProof;
  notypeclasses refine (tac_modal_intro _ _ sel _ _ _ _ _ _ _ _ _ _ _ _ _ _);
    [tc_solve ||
     fail "iModIntro: the goal is not a modality"
    |tc_solve ||
     let s := lazymatch goal with |- IntoModalIntuitionisticEnv _ _ _ ?s => s end in
     lazymatch eval hnf in s with
     | MIEnvForall ?C => fail "iModIntro: intuitionistic context does not satisfy" C
     | MIEnvIsEmpty => fail "iModIntro: intuitionistic context is non-empty"
     end
    |tc_solve ||
     let s := lazymatch goal with |- IntoModalSpatialEnv _ _ _ ?s _ => s end in
     lazymatch eval hnf in s with
     | MIEnvForall ?C => fail "iModIntro: spatial context does not satisfy" C
     | MIEnvIsEmpty => fail "iModIntro: spatial context is non-empty"
     end
    |pm_reduce; tc_solve ||
     fail "iModIntro: cannot filter spatial context when goal is not absorbing"
    |iSolveSideCondition
    |pm_prettify (* reduce redexes created by instantiation *)
     (* subgoal *) ].
Tactic Notation "iModIntro" := iModIntro _.

(** DEPRECATED *)
#[deprecated(note = "Use iModIntro instead")]
Tactic Notation "iAlways" := iModIntro.

(** * Later *)
Tactic Notation "iNext" open_constr(n) := iModIntro (▷^n _)%I.
Tactic Notation "iNext" := iModIntro (▷^_ _)%I.

(** * Update modality *)
Tactic Notation "iModCore" constr(H) "as" constr(H') :=
  eapply tac_modal_elim with H H' _ _ _ _ _ _;
    [pm_reflexivity || fail "iMod:" H "not found"
    |tc_solve ||
     let P := match goal with |- ElimModal _ _ _ ?P _ _ _ => P end in
     let Q := match goal with |- ElimModal _ _ _ _ _ ?Q _ => Q end in
     fail "iMod: cannot eliminate modality" P "in" Q
    |iSolveSideCondition
    |pm_reduce;
     lazymatch goal with
     | |- False =>
       let H' := pretty_ident H' in
       fail "iMod:" H' "not fresh"
     | _ => pm_prettify(* subgoal *)
     end].

(** * Basic destruct tactic *)

(* Two helper tactics to compute an identifier for the hypothesis corresponding
   to the intro-pattern [pat], when trying to avoid extra renamings. These
   mainly look whether the pattern is a name, and use that name in that case.
   Otherwise, [ident_for_pat] generates a fresh name (a safe option), and
   [ident_for_pat_default] uses the [default] name that it was provided if
   it is an anonymous name.
*)
Ltac _ident_for_pat pat :=
  lazymatch pat with
  | IIdent ?x => x
  | _ => let x := iFresh in x
  end.

Ltac _ident_for_pat_default pat default :=
  lazymatch pat with
  | IIdent ?x => x
  | _ =>
    lazymatch default with
    | IAnon _ => default
    | _ => let x := iFresh in x
    end
  end.

(** [pat0] is the unparsed pattern, and is only used in error messages *)
Ltac _iDestructHypGo Hz pat0 pat :=
  lazymatch pat with
  | IFresh =>
     lazymatch Hz with
     | IAnon _ => idtac
     | INamed ?Hz => let Hz' := iFresh in iRename Hz into Hz'
     end
  | IDrop => _iClearHyp Hz
  | IFrame => iFrameHyp Hz
  | IIdent Hz => idtac
  | IIdent ?y => iRename Hz into y
  | IList [[]] => iExFalso; iExact Hz

  (* conjunctive patterns like [H1 H2] *)
  | IList [[?pat1; IDrop]] =>
     let x := _ident_for_pat_default pat1 Hz in
     _iAndDestructChoice Hz Left x;
     _iDestructHypGo x pat0 pat1
  | IList [[IDrop; ?pat2]] =>
     let x := _ident_for_pat_default pat2 Hz in
     _iAndDestructChoice Hz Right x;
     _iDestructHypGo x pat0 pat2
  (* [% ...] is always interpreted as an existential; there are [IntoExist]
  instances in place to handle conjunctions with a pure left-hand side this way
  as well. *)
  | IList [[IPure IGallinaAnon; ?pat2]] =>
     let x := _ident_for_pat_default pat2 Hz in
     _iExistDestruct Hz as ? x; _iDestructHypGo x pat0 pat2
  | IList [[IPure (IGallinaNamed ?s); ?pat2]] =>
     let x := fresh in
     let y := _ident_for_pat_default pat2 Hz in
     _iExistDestruct Hz as x y;
     rename_by_string x s;
     _iDestructHypGo y pat0 pat2
  | IList [[?pat1; ?pat2]] =>
     (* We have to take care of not using the same name for the two hypotheses:
        [_ident_for_pat_default] will thus only reuse [Hz] (which could in principle
        clash with a name from [pat2]) if it is an anonymous name. *)
     let x1 := _ident_for_pat_default pat1 Hz in
     let x2 := _ident_for_pat pat2 in
     _iAndDestruct Hz x1 x2;
     _iDestructHypGo x1 pat0 pat1; _iDestructHypGo x2 pat0 pat2
  | IList [_ :: _ :: _] => fail "iDestruct:" pat0 "has too many conjuncts"
  | IList [[_]] => fail "iDestruct:" pat0 "has just a single conjunct"

  (* disjunctive patterns like [H1|H2] *)
  | IList [[?pat1];[?pat2]] =>
     let x1 := _ident_for_pat_default pat1 Hz in
     let x2 := _ident_for_pat_default pat2 Hz in
     iOrDestruct Hz as x1 x2;
     [_iDestructHypGo x1 pat0 pat1|_iDestructHypGo x2 pat0 pat2]
  (* this matches a list of three or more disjunctions [H1|H2|H3] *)
  | IList (_ :: _ :: _ :: _) => fail "iDestruct:" pat0 "has too many disjuncts"
  (* the above patterns don't match [H1 H2|H3] *)
  | IList [_;_] => fail "iDestruct: in" pat0 "a disjunct has multiple patterns"

  | IPure IGallinaAnon => iPure Hz as ?
  | IPure (IGallinaNamed ?s) =>
     let x := fresh in
     iPure Hz as x;
     rename_by_string x s
  | IRewrite Right => iPure Hz as ->
  | IRewrite Left => iPure Hz as <-
  | IIntuitionistic ?pat =>
    let x := _ident_for_pat_default pat Hz in
    _iIntuitionistic Hz x; _iDestructHypGo x pat0 pat
  | ISpatial ?pat =>
    let x := _ident_for_pat_default pat Hz in
    _iSpatial Hz x; _iDestructHypGo x pat0 pat
  | IModalElim ?pat =>
    let x := _ident_for_pat_default pat Hz in
    iModCore Hz as x; _iDestructHypGo x pat0 pat
  | ICustom ?custom ?arg =>
      first
      [ lazymatch eval vm_compute in (custom_ipat custom arg) with
        | None =>
            fail 1 "iDestruct: invalid arguments for custom intro pattern:" custom
        | Some ?pat =>
            lazymatch eval cbv in (intro_pat.parse pat) with
            | None =>
                fail 1 "iDestruct: invalid intro pattern generated by custom intro pattern:" custom
            | Some [?pat] =>
                _iDestructHypGo Hz pat0 pat
            | Some _ =>
                fail 1 "iDestruct: custom intro pattern" custom "should generate exactly one intro pattern"
            end
        end
      | fail 1 "iDestruct: unrecognized custom intro pattern:" custom
      ]
  | _ => fail "iDestruct:" pat0 "is not supported due to" pat
  end.
Ltac _iDestructHypFindPat Hgo pat found pats :=
  lazymatch pats with
  | [] =>
    lazymatch found with
    | true => pm_prettify (* post-tactic prettification *)
    | false => fail "iDestruct:" pat "should contain exactly one proper introduction pattern"
    end
  | ISimpl :: ?pats => simpl; _iDestructHypFindPat Hgo pat found pats
  | IClear ?H :: ?pats => iClear H; _iDestructHypFindPat Hgo pat found pats
  | IClearFrame ?H :: ?pats => iFrame H; _iDestructHypFindPat Hgo pat found pats
  | ?pat1 :: ?pats =>
     lazymatch found with
     | false => _iDestructHypGo Hgo pat pat1; _iDestructHypFindPat Hgo pat true pats
     | true => fail "iDestruct:" pat "should contain exactly one proper introduction pattern"
     end
  end.

(* This is the core implementation of [iDestruct]. *)
Ltac _iDestructHyp0 H pat :=
  let pats := intro_pat.parse pat in
  _iDestructHypFindPat H pat false pats.
Ltac _iDestructHyp H xs pat :=
  ltac1_list_iter ltac:(fun x => _iExistDestruct H as x H) xs;
  _iDestructHyp0 H pat.

Tactic Notation "iDestructHyp" constr(H) "as" constr(pat) :=
  _iDestructHyp0 H pat.
Tactic Notation "iDestructHyp" constr(H) "as"
  "(" ne_simple_intropattern_list(xs) ")" constr(pat) := _iDestructHyp H xs pat.

(** * Combinining hypotheses *)
Tactic Notation "iCombine" constr(Hs) "as" constr(pat) :=
  let Hs := String.words Hs in
  let Hs := eval vm_compute in (INamed <$> Hs) in
  let H := iFresh in
  let Δ := iGetCtx in
  notypeclasses refine (tac_combine_as _ _ _ Hs _ _ H _ _ _ _ _ _);
    [pm_reflexivity ||
     let Hs := iMissingHypsCore Δ Hs in
     fail "iCombine: hypotheses" Hs "not found"
    |tc_solve
    |pm_reflexivity ||
     let H := pretty_ident H in
     fail "iCombine:" H "not fresh"
     (* should never happen in normal usage, since [H := iFresh]
     FIXME: improve once consistent error messages are added,
     see https://gitlab.mpi-sws.org/iris/iris/-/issues/499 *)
    |iDestructHyp H as pat].

Tactic Notation "iCombine" constr(H1) constr(H2) "as" constr(pat) :=
  iCombine [H1;H2] as pat.

Tactic Notation "iCombineGivesCore" constr(Hs) "gives" tactic3(tac) :=
  let Hs := String.words Hs in
  let Hs := eval vm_compute in (INamed <$> Hs) in
  let H := iFresh in
  let Δ := iGetCtx in
  notypeclasses refine (tac_combine_gives _ _ _ Hs _ _ H _ _ _ _ _ _ _);
    [pm_reflexivity ||
     let Hs := iMissingHypsCore Δ Hs in
     fail "iCombine: hypotheses" Hs "not found"
    |tc_solve || fail "iCombine: cannot find 'gives' clause for hypotheses" Hs
    |pm_reflexivity ||
     let H := pretty_ident H in
     fail "iCombine:" H "not fresh"
     (* should never happen in normal usage, since [H := iFresh]
     FIXME: improve once consistent error messages are added,
     see https://gitlab.mpi-sws.org/iris/iris/-/issues/499 *)
    |tac H].

Tactic Notation "iCombine" constr(Hs) "gives" constr(pat) :=
  iCombineGivesCore Hs gives (fun H => iDestructHyp H as pat).

Tactic Notation "iCombine" constr(H1) constr(H2) "gives" constr(pat) :=
  iCombine [H1;H2] gives pat.

Tactic Notation "iCombine" constr(Hs) "gives" "%" simple_intropattern(pat) :=
  iCombineGivesCore Hs gives (fun H => iPure H as pat).

Tactic Notation "iCombine" constr(H1) constr(H2)
                                      "gives" "%" simple_intropattern(pat) :=
  iCombine [H1;H2] gives %pat.

Tactic Notation "iCombineAsGivesCore" constr(Hs) "as" constr(pat1)
                                      "gives" tactic3(tac) :=
  let Hs := String.words Hs in
  let Hs := eval vm_compute in (INamed <$> Hs) in
  let H1 := iFresh in
  let H2 := iFresh in
  let Δ := iGetCtx in
  notypeclasses refine (tac_combine_as_gives _ _ _ Hs _ _ H1 H2 _ _ _ _ _ _ _);
    [pm_reflexivity ||
     let Hs := iMissingHypsCore Δ Hs in
     fail "iCombine: hypotheses" Hs "not found"
    |tc_solve || fail "iCombine: cannot find 'gives' clause for hypotheses" Hs
    |pm_reflexivity ||
     let H1 := pretty_ident H1 in
     let H2 := pretty_ident H2 in
     fail "iCombine:" H1 "or" H2 "not fresh"
     (* should never happen in normal usage, since [H1] and [H2] are [iFresh]
     FIXME: improve once consistent error messages are added,
     see https://gitlab.mpi-sws.org/iris/iris/-/issues/499 *)
    |iDestructHyp H1 as pat1; tac H2].

Tactic Notation "iCombine" constr(Hs) "as" constr(pat1) "gives" constr(pat2) :=
  iCombineAsGivesCore Hs as pat1 gives (fun H => iDestructHyp H as pat2).

Tactic Notation "iCombine" constr(H1) constr(H2) "as" constr(pat1)
                                      "gives" constr(pat2) :=
  iCombine [H1;H2] as pat1 gives pat2.

Tactic Notation "iCombine" constr(Hs) "as" constr(pat1)
                                      "gives" "%" simple_intropattern(pat2) :=
  iCombineAsGivesCore Hs as pat1 gives (fun H => iPure H as pat2).

Tactic Notation "iCombine" constr(H1) constr(H2) "as" constr(pat1)
                                      "gives" "%" simple_intropattern(pat2) :=
  iCombine [H1;H2] as pat1 gives %pat2.

(** * Introduction tactic *)
Ltac _iIntros_go pats startproof :=
  lazymatch pats with
  | [] =>
    lazymatch startproof with
    | true => iStartProof
    | false => idtac
    end
  (* Optimizations to avoid generating fresh names *)
  | IPure (IGallinaNamed ?s) :: ?pats =>
     let i := fresh in
     _iIntro (i);
     rename_by_string i s;
     _iIntros_go pats startproof
  | IPure IGallinaAnon :: ?pats => _iIntro (?); _iIntros_go pats startproof
  | IIntuitionistic (IIdent ?H) :: ?pats => _iIntroPersistent H; _iIntros_go pats false
  | IDrop :: ?pats => _iIntroDrop; _iIntros_go pats startproof
  | IIdent ?H :: ?pats => _iIntroSpatial H; _iIntros_go pats startproof
  (* Introduction patterns that can only occur at the top-level *)
  | IPureIntro :: ?pats => iPureIntro; _iIntros_go pats false
  | IModalIntro :: ?pats => iModIntro; _iIntros_go pats false
  | IForall :: ?pats => repeat _iIntroForall; _iIntros_go pats startproof
  | IAll :: ?pats => repeat (_iIntroForall || _iIntro); _iIntros_go pats startproof
  (* Clearing and simplifying introduction patterns *)
  | ISimpl :: ?pats => simpl; _iIntros_go pats startproof
  | IClear ?H :: ?pats => iClear H; _iIntros_go pats false
  | IClearFrame ?H :: ?pats => iFrame H; _iIntros_go pats false
  | IDone :: ?pats => try done; _iIntros_go pats startproof
  (* Introduction + destruct *)
  | IIntuitionistic ?pat :: ?pats =>
     let H := iFresh in _iIntroPersistent H; iDestructHyp H as pat; _iIntros_go pats false
  | ICustom ?custom ?arg :: ?pats =>
      first
      [ lazymatch eval vm_compute in (custom_ipat custom arg) with
        | None =>
            fail 1 "iIntros: invalid arguments for custom intro pattern:" custom
        | Some ?pat =>
            lazymatch eval cbv in (intro_pat.parse pat) with
            | None =>
                fail 1 "iIntros: invalid intro pattern generated by custom intro pattern:" custom
            | Some ?pats' =>
                let pats := eval cbv in (pats' ++ pats) in
                _iIntros_go pats startproof
            end
        end
      | fail 1 "iIntros: unrecognized custom intro pattern:" custom
      ]
  | ?pat :: ?pats =>
     let H := iFresh in _iIntroSpatial H; iDestructHyp H as pat; _iIntros_go pats false
  end.

(* This is the core implementation of [iIntros]. *)
Ltac _iIntros0 pat :=
  let pats := intro_pat.parse pat in
  (* HACK to avoid calling [iStartProof] on side-conditions opened by [iIntros (?%lemma)]. *)
  lazymatch pats with
  | [] => idtac
  | _ => _iIntros_go pats true
  end.
Ltac _iIntros xs pat :=
  ltac1_list_iter ltac:(fun x => _iIntro (x)) xs;
  _iIntros0 pat.

Tactic Notation "iIntros" := _iIntros0 [IAll].
Tactic Notation "iIntros" constr(pat) := _iIntros0 pat.
Tactic Notation "iIntros" "(" ne_simple_intropattern_list(xs) ")" :=
  _iIntros xs "".
Tactic Notation "iIntros" "(" ne_simple_intropattern_list(xs) ")" constr(pat) :=
  _iIntros xs pat.
Tactic Notation "iIntros" constr(pat) "(" ne_simple_intropattern_list(xs) ")" :=
  _iIntros0 pat; _iIntros xs "".
Tactic Notation "iIntros" constr(pat1)
    "(" ne_simple_intropattern_list(xs) ")" constr(pat2) :=
  _iIntros0 pat1; _iIntros xs pat2.

(* Used for generalization in [iInduction] and [iLöb] *)
Ltac _iRevertIntros_go Hs tac :=
  lazymatch Hs with
  | [] => tac ()
  | ESelPure :: ?Hs => fail "iRevertIntros: % not supported"
  | ESelIdent ?p ?H :: ?Hs =>
    iRevertHyp H; _iRevertIntros_go Hs tac; _iIntroMaybePersistent H p
  end.

Ltac _iRevertIntros0 Hs tac :=
  try iStartProof;
  let Hs := iElaborateSelPat Hs in
  _iRevertIntros_go Hs tac.
Ltac _iRevertIntros xs Hs tac :=
  _iRevertIntros0 Hs ltac:(fun _ => _iRevert xs ""; tac (); _iIntros xs "").

Tactic Notation "iRevertIntros" constr(Hs) "with" tactic3(tac) :=
  _iRevertIntros0 Hs tac.
Tactic Notation "iRevertIntros" "(" ne_ident_list(xs) ")" constr(Hs) "with" tactic3(tac):=
  _iRevertIntros xs Hs tac.
Tactic Notation "iRevertIntros" "with" tactic3(tac) :=
  _iRevertIntros0 "" tac.
Tactic Notation "iRevertIntros" "(" ne_ident_list(xs) ")" "with" tactic3(tac):=
  _iRevertIntros xs "" tac.

(** * Destruct and PoseProof tactics *)
(** The tactics [iDestruct] and [iPoseProof] are similar, but there are some
subtle differences:

1. The [iDestruct] tactic can be called with a natural number [n] instead of a
   hypothesis/lemma, i.e., [iDestruct n as ...]. This introduces [n] hypotheses,
   and then calls [iDestruct] on the last introduced hypothesis. The
   [iPoseProof] tactic does not support this feature.
2. When the argument [lem] of [iDestruct lem as ...] is a proof mode identifier
   (instead of a proof mode term, i.e., no quantifiers or wands/implications are
   eliminated), then the original hypothesis will always be removed. For
   example, calling [iDestruct "H" as ...] on ["H" : P ∨ Q] will remove ["H"].
   Conversely, [iPoseProof] always tries to keep the hypothesis. For example,
   calling [iPoseProof "H" as ...] on ["H" : P ∨ Q] will keep ["H"] if it
   resides in the intuitionistic context.

These differences are also present in Coq's [destruct] and [pose proof] tactics.
However, Coq's [destruct lem as ...] is more eager on removing the original
hypothesis, it might also remove the original hypothesis if [lem] is not an
identifier, but an applied term. For example, calling [destruct (H HP) as ...]
on [H : P → Q] and [HP : P] will remove [H]. The [iDestruct] does not do this
because it could lead to information loss if [H] resides in the intuitionistic
context and [HP] resides in the spatial context. *)
Tactic Notation "iDestructCore" open_constr(lem) "as" constr(p) tactic3(tac) :=
  let intro_destruct n :=
    let rec go n' :=
      lazymatch n' with
      | 0 => fail "iDestruct: cannot introduce" n "hypotheses"
      | 1 => repeat _iIntroForall; let H := iFresh in _iIntroSpatial H; tac H
      | S ?n' => repeat _iIntroForall; let H := iFresh in _iIntroSpatial H; go n'
      end in
    intros; go n in
  lazymatch type of lem with
  | nat => intro_destruct lem
  | Z =>
     (** This case is used to make the tactic work in [Z_scope]. It would be
     better if we could bind tactic notation arguments to notation scopes, but
     that is not supported by Ltac. *)
     let n := eval cbv in (Z.to_nat lem) in intro_destruct n
  | ident => tac lem
  | string => tac constr:(INamed lem)
  | _ => iPoseProofCore lem as p tac
  end.

Ltac _iDestruct0 lem pat :=
  iDestructCore lem as pat (fun H => iDestructHyp H as pat).
Ltac _iDestruct lem xs pat :=
  iDestructCore lem as pat (fun H => _iDestructHyp H xs pat).

Tactic Notation "iDestruct" open_constr(lem) "as" constr(pat) :=
  _iDestruct0 lem pat.
Tactic Notation "iDestruct" open_constr(lem) "as" "(" ne_simple_intropattern_list(xs) ")"
    constr(pat) :=
  _iDestruct lem xs pat.

Tactic Notation "iDestruct" open_constr(lem) "as" "%" simple_intropattern(pat) :=
  iDestructCore lem as true (fun H => iPure H as pat).

Tactic Notation "iDestruct" "select" open_constr(pat) "as" constr(ipat) :=
  iSelect pat ltac:(fun H => _iDestruct0 H ipat).
Tactic Notation "iDestruct" "select" open_constr(pat) "as" "("
    ne_simple_intropattern_list(xs) ")" constr(ipat) :=
  iSelect pat ltac:(fun H => _iDestruct H xs ipat).
Tactic Notation "iDestruct" "select" open_constr(pat) "as" "%" simple_intropattern(ipat) :=
  iSelect pat ltac:(fun H => iDestruct H as % ipat).

Tactic Notation "iPoseProof" open_constr(lem) "as" constr(pat) :=
  iPoseProofCore lem as pat (fun H => iDestructHyp H as pat).
Tactic Notation "iPoseProof" open_constr(lem) "as" "(" ne_simple_intropattern_list(xs) ")"
    constr(pat) :=
  iPoseProofCore lem as pat (fun H => _iDestructHyp H xs pat).

(** * Induction *)
(* An invocation of [iInduction (x) as pat IH forall (x1...xn) Hs] will
result in the following actions:

- Revert the proofmode hypotheses [Hs]
- Revert all remaining spatial hypotheses and the remaining intuitionistic
  hypotheses containing the induction variable [x]
- Revert the pure hypotheses [x1..xn]

- Actually perform induction

- Introduce the pure hypotheses [x1..xn]
- Introduce the spatial hypotheses and intuitionistic hypotheses involving [x]
- Introduce the proofmode hypotheses [Hs]

The argument [IH] in the tactics below is either [Some "IH"], in which case
the induction hypotheses are named "IH", "IH1", "IH2" (used for the legacy
syntax), or [None], in which case the names from the Coq introduction pattern
are used (they are converted from idents into strings). *)
Tactic Notation "iInductionCore" tactic3(tac) "as" constr(IH) :=
  let rec fix_ihs rev_tac :=
    lazymatch goal with
    | H : context [envs_entails _ _] |- _ =>
       notypeclasses refine (tac_revert_ih _ _ _ H _ _ _);
         [tc_solve ||
          let φ := match goal with |- IntoIH ?φ _ _ => φ end in
          fail "iInduction: cannot import IH" φ
               "into proof mode context (IntoIH instance missing)"
         |pm_reflexivity ||
          fail "iInduction: spatial context not empty, this should not happen"
         |clear H];
       fix_ihs ltac:(fun j =>
         (* Written in CPS style because [ident_to_string_cps] is CPS. *)
         let cont IH' :=
           iIntros [IIntuitionistic (IIdent IH')];
           let j := eval vm_compute in (1 + j)%N in
           rev_tac j in
         match IH with
         | Some ?IH =>
            let IH' := eval vm_compute in
              match j with 0%N => IH | _ => IH +:+ pretty j end in
            cont IH'
         | None =>
            ident_to_string_cps ident:(H) cont
         end)
    | _ => rev_tac 0%N
    end in
  tac ();
  fix_ihs ltac:(fun _ => idtac).

Ltac iHypsContaining x :=
  let rec go Γ x Hs :=
    lazymatch Γ with
    | Enil => constr:(Hs)
    | Esnoc ?Γ ?H ?Q =>
       match Q with
       | context [x] => go Γ x (H :: Hs)
       | _ => go Γ x Hs
       end
     end in
  let Γp := lazymatch goal with |- envs_entails (Envs ?Γp _ _) _ => Γp end in
  let Γs := lazymatch goal with |- envs_entails (Envs _ ?Γs _) _ => Γs end in
  let Hs := go Γp x (@nil ident) in go Γs x Hs.

Ltac _iInduction x xs Hs tac IH :=
  (* FIXME: We should be able to do this in a more sane way, by concatenating
  the spec patterns instead of calling [iRevertIntros] multiple times. *)
  _iRevertIntros0 Hs ltac:(fun _ =>
    _iRevertIntros0 "∗" ltac:(fun _ =>
      let Hsx := iHypsContaining x in
      _iRevertIntros xs Hsx ltac:(fun _ =>
        iInductionCore tac as IH
      )
    )
  ).
Ltac _iInduction0 x Hs tac IH :=
  with_ltac1_nil ltac:(fun xs => _iInduction x xs Hs tac IH).

(* Without induction scheme *)
(* legacy syntax *)
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH) :=
  _iInduction0 x "" ltac:(fun _ => induction x as pat) (Some IH).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ne_ident_list(xs) ")" :=
  _iInduction x xs "" ltac:(fun _ => induction x as pat) (Some IH).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" constr(Hs) :=
  _iInduction0 x Hs ltac:(fun _ => induction x as pat) (Some IH).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "forall" "(" ne_ident_list(xs) ")" constr(Hs) :=
  _iInduction x xs Hs ltac:(fun _ => induction x as pat) (Some IH).

(* new syntax that uses IH names from Coq intro pattern *)
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) :=
  _iInduction0 x "" ltac:(fun _ => induction x as pat) (@None string).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat)
    "forall" "(" ne_ident_list(xs) ")" :=
  _iInduction x xs "" ltac:(fun _ => induction x as pat) (@None string).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat)
    "forall" constr(Hs) :=
  _iInduction0 x Hs ltac:(fun _ => induction x as pat) (@None string).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat)
    "forall" "(" ne_ident_list(xs) ")" constr(Hs) :=
  _iInduction x xs Hs ltac:(fun _ => induction x as pat) (@None string).

(* With induction scheme *)
(* legacy syntax *)
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) :=
  _iInduction0 x "" ltac:(fun _ => induction x as pat using u) (Some IH).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ne_ident_list(xs) ")" :=
  _iInduction x xs "" ltac:(fun _ => induction x as pat using u) (Some IH).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" constr(Hs) :=
  _iInduction0 x Hs ltac:(fun _ => induction x as pat using u) (Some IH).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat) constr(IH)
    "using" uconstr(u) "forall" "(" ne_ident_list(xs) ")" constr(Hs) :=
  _iInduction x xs Hs ltac:(fun _ => induction x as pat using u) (Some IH).

(* new syntax that uses IH names from Coq intro pattern *)
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat)
    "using" uconstr(u) :=
  _iInduction0 x "" ltac:(fun _ => induction x as pat using u) (@None string).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat)
    "using" uconstr(u) "forall" "(" ne_ident_list(xs) ")" :=
  _iInduction x xs "" ltac:(fun _ => induction x as pat using u) (@None string).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat)
    "using" uconstr(u) "forall" constr(Hs) :=
  _iInduction0 x Hs ltac:(fun _ => induction x as pat using u) (@None string).
Tactic Notation "iInduction" constr(x) "as" simple_intropattern(pat)
    "using" uconstr(u) "forall" "(" ne_ident_list(xs) ")" constr(Hs) :=
  _iInduction x xs Hs ltac:(fun _ => induction x as pat using u) (@None string).

(** * Löb Induction *)
Tactic Notation "iLöbCore" "as" constr (IH) :=
  iStartProof;
  (* apply is sometimes confused wrt. canonical structures search.
     refine should use the other unification algorithm, which should
     not have this issue. *)
  notypeclasses refine (tac_löb _ IH _ _ _ _);
    [tc_solve || fail "iLöb: no 'BiLöb' instance found"
    |reflexivity || fail "iLöb: spatial context not empty; this should not happen, please report a bug"
    |pm_reduce;
     lazymatch goal with
     | |- False =>
       let IH := pretty_ident IH in
       fail "iLöb:" IH "not fresh"
     | _ => idtac
     end].

Ltac _iLöb xs Hs IH :=
  (* FIXME: We should be able to do this in a more sane way, by concatenating
  the spec patterns instead of calling [iRevertIntros] multiple times. *)
  _iRevertIntros0 Hs ltac:(fun _ =>
    _iRevertIntros xs "∗" ltac:(fun _ =>
      iLöbCore as IH
    )
  ).
Ltac _iLöb0 Hs IH :=
  with_ltac1_nil ltac:(fun xs => _iLöb xs Hs IH).

Tactic Notation "iLöb" "as" constr (IH) :=
  _iLöb0 "" IH.
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ne_ident_list(xs) ")" :=
  _iLöb xs "" IH.
Tactic Notation "iLöb" "as" constr (IH) "forall" constr(Hs) :=
  _iLöb0 Hs IH.
Tactic Notation "iLöb" "as" constr (IH) "forall" "(" ne_ident_list(xs) ")" constr(Hs) :=
  _iLöb xs Hs IH.

(** * Assert *)
(* The argument [p] denotes whether [Q] is persistent. It can either be a
Boolean or an introduction pattern, which will be coerced into [true] if it
only contains [#] or [%] patterns at the top-level, and [false] otherwise. *)
Tactic Notation "iAssertCore" open_constr(Q)
    "with" constr(Hs) "as" constr(p) tactic3(tac) :=
  iStartProof;
  let pats := spec_pat.parse Hs in
  lazymatch pats with
  | [_] => idtac
  | _ => fail "iAssert: exactly one specialization pattern should be given"
  end;
  let H := iFresh in
  eapply tac_assert with H Q;
  [pm_reduce;
   iSpecializeCore H with hnil pats as p; [..|tac H]].

Tactic Notation "iAssertCore" open_constr(Q) "as" constr(p) tactic3(tac) :=
  let p := intro_pat_intuitionistic p in
  lazymatch p with
  | true => iAssertCore Q with "[#]" as p tac
  | false => iAssertCore Q with "[]" as p tac
  end.

Tactic Notation "iAssert" open_constr(Q) "with" constr(Hs) "as" constr(pat) :=
  iAssertCore Q with Hs as pat (fun H => _iDestructHyp0 H pat).
Tactic Notation "iAssert" open_constr(Q) "with" constr(Hs) "as"
    "(" ne_simple_intropattern_list(xs) ")" constr(pat) :=
  iAssertCore Q with Hs as pat (fun H => _iDestructHyp H xs pat).

Tactic Notation "iAssert" open_constr(Q) "as" constr(pat) :=
  iAssertCore Q as pat (fun H => _iDestructHyp0 H pat).
Tactic Notation "iAssert" open_constr(Q) "as"
    "(" ne_simple_intropattern_list(xs) ")" constr(pat) :=
  iAssertCore Q as pat (fun H => _iDestructHyp H xs pat).

Tactic Notation "iAssert" open_constr(Q) "with" constr(Hs)
    "as" "%" simple_intropattern(pat) :=
  iAssertCore Q with Hs as true (fun H => iPure H as pat).
Tactic Notation "iAssert" open_constr(Q) "as" "%" simple_intropattern(pat) :=
  iAssert Q with "[-]" as %pat.

(** * Rewrite *)
Local Ltac iRewriteFindPred :=
  match goal with
  | |- _ ⊣⊢ ?Φ ?x =>
     generalize x;
     match goal with |- (∀ y, @?Ψ y ⊣⊢ _) => unify Φ Ψ; reflexivity end
  end.

Local Tactic Notation "iRewriteCore" constr(lr) open_constr(lem) :=
  iPoseProofCore lem as true (fun Heq =>
    eapply (tac_rewrite _ Heq _ _ lr);
      [pm_reflexivity ||
       let Heq := pretty_ident Heq in
       fail "iRewrite:" Heq "not found"
      |tc_solve ||
       let P := match goal with |- IntoInternalEq ?P _ _ ⊢ _ => P end in
       fail "iRewrite:" P "not an equality"
      |iRewriteFindPred
      |intros ??? ->; reflexivity|pm_prettify; _iClearHyp Heq]).

Tactic Notation "iRewrite" open_constr(lem) := iRewriteCore Right lem.
Tactic Notation "iRewrite" "-" open_constr(lem) := iRewriteCore Left lem.

Local Tactic Notation "iRewriteCore" constr(lr) open_constr(lem) "in" constr(H) :=
  iPoseProofCore lem as true (fun Heq =>
    eapply (tac_rewrite_in _ Heq _ _ H _ _ lr);
      [pm_reflexivity ||
       let Heq := pretty_ident Heq in
       fail "iRewrite:" Heq "not found"
      |pm_reflexivity ||
       let H := pretty_ident H in
       fail "iRewrite:" H "not found"
      |tc_solve ||
       let P := match goal with |- IntoInternalEq ?P _ _ ⊢ _ => P end in
       fail "iRewrite:" P "not an equality"
      |iRewriteFindPred
      |intros ??? ->; reflexivity
      |pm_reduce; pm_prettify; _iClearHyp Heq]).

Tactic Notation "iRewrite" open_constr(lem) "in" constr(H) :=
  iRewriteCore Right lem in H.
Tactic Notation "iRewrite" "-" open_constr(lem) "in" constr(H) :=
  iRewriteCore Left lem in H.

Ltac iSimplifyEq := repeat (
  iMatchHyp (fun H P => match P with ⌜_ = _⌝%I => iDestruct H as %? end)
  || simplify_eq/=).

(** * Update modality *)
Tactic Notation "iMod" open_constr(lem) :=
  iDestructCore lem as false (fun H => iModCore H as H).
Tactic Notation "iMod" open_constr(lem) "as" constr(pat) :=
  iDestructCore lem as false (fun H => iModCore H as H; last iDestructHyp H as pat).
Tactic Notation "iMod" open_constr(lem) "as" "(" ne_simple_intropattern_list(xs) ")"
    constr(pat) :=
  iDestructCore lem as false (fun H => iModCore H as H; last _iDestructHyp H xs pat).

Tactic Notation "iMod" open_constr(lem) "as" "%" simple_intropattern(pat) :=
  iDestructCore lem as false (fun H => iModCore H as H; iPure H as pat).

(** * Invariant *)

(* Finds a hypothesis in the context that is an invariant with
   namespace [N].  To do so, we check whether for each hypothesis
   ["H":P] we can find an instance of [IntoInv P N] *)
Tactic Notation "iAssumptionInv" constr(N) :=
  let rec find Γ i :=
    lazymatch Γ with
    | Esnoc ?Γ ?j ?P' =>
      first [let H := constr:(_: IntoInv P' N) in unify i j|find Γ i]
    end in
  lazymatch goal with
  | |- envs_lookup ?i (Envs ?Γp ?Γs _) = Some _ =>
     first [find Γp i|find Γs i]; pm_reflexivity
  end.

(* The argument [select] is the namespace [N] or hypothesis name ["H"] of the
invariant. *)
Tactic Notation "iInvCore" constr(select) "with" constr(pats) "as" open_constr(Hclose) "in" tactic3(tac) :=
  iStartProof;
  let pats := spec_pat.parse pats in
  lazymatch pats with
  | [_] => idtac
  | _ => fail "iInv: exactly one specialization pattern should be given"
  end;
  let H := iFresh in
  let Pclose_pat :=
    lazymatch Hclose with
    | Some _ => open_constr:(Some _)
    | None => open_constr:(None)
    end in
  lazymatch type of select with
  | string =>
     notypeclasses refine (tac_inv_elim _ select H _ _ _ _ _ Pclose_pat _ _ _ _ _ _);
     [ (by iAssumptionCore) || fail "iInv: invariant" select "not found" |..]
  | ident  =>
     notypeclasses refine (tac_inv_elim _ select H _ _ _ _ _ Pclose_pat _ _ _ _ _ _);
     [ (by iAssumptionCore) || fail "iInv: invariant" select "not found" |..]
  | namespace =>
     notypeclasses refine (tac_inv_elim _ _ H _ _ _ _ _ Pclose_pat _ _ _ _ _ _);
     [ (by iAssumptionInv select) || fail "iInv: invariant" select "not found" |..]
  | _ => fail "iInv: selector" select "is not of the right type "
  end;
    [tc_solve ||
     let I := match goal with |- ElimInv _ ?I  _ _ _ _ _ => I end in
     fail "iInv: cannot open invariant" I "in the current goal"
       "(the goal should be a fancy update or WP,"
       "or another modality that supports invariant opening)"
    |iSolveSideCondition
    |let R := fresh in intros R; pm_reduce;
     (* Now we are left proving [envs_entails Δ'' R]. *)
     iSpecializePat H pats; last (
       iApplyHyp H; clear R; pm_reduce;
       (* Now the goal is
          [∀ x, Pout x -∗ pm_option_fun Pclose x -∗? Q' x],
          reduced because we can rely on Pclose being a constructor. *)
       let x := fresh in
       iIntros (x);
       _iIntroSpatial H; (* H was spatial, so it's gone due to the apply and we
       can reuse the name *)
       lazymatch Hclose with
       | Some ?Hcl => iIntros Hcl
       | None => idtac
       end;
       tac x H
    )].

(* Without closing view shift *)
Tactic Notation "iInvCore" constr(N) "with" constr(pats) "in" tactic3(tac) :=
  iInvCore N with pats as (@None string) in tac.
(* Without selection pattern *)
Tactic Notation "iInvCore" constr(N) "as" constr(Hclose) "in" tactic3(tac) :=
  iInvCore N with "[$]" as Hclose in tac.
(* Without both *)
Tactic Notation "iInvCore" constr(N) "in" tactic3(tac) :=
  iInvCore N with "[$]" as (@None string) in tac.

Ltac _iDestructAccAndHyp0 pat x H :=
  lazymatch type of x with
  | unit => destruct x as []; _iDestructHyp0 H pat
  | _ => fail "Missing intro pattern for accessor variable"
  end.

(** [_iDestructAccAndHyp xs pat x H] expects [x] to be a variable in the context.
Then it behaves as follows:
- If [x] has type [unit], it destructs [x] and continues as
  [_iDestructHyp H xs pat]. That is, it is basically as if [x] did not exist.
- Otherwise, [xs] must be a non-empty list of patterns, and the first pattern is
  applied to [x]. Then we continue as [_iDestructHyp H (tail xs) pat].
  Basically it is as if "H" (the hypothesis being destructed) actually was
  [∃ x, H], so that the first pattern in the [xs] destructs this existential. *)
Ltac _iDestructAccAndHyp xs pat x H :=
  let go := ltac2:(tac xs |-
    match of_ltac1_list xs with
    | [] =>
      Control.throw_invalid_argument "iDestructAccAndHyp: List should be non-empty"
    | x1 :: xs' =>
      ltac1:(x1 |- intros x1) x1;
      ltac1:(tac xs' |- tac xs') tac (Ltac1.of_list xs')
    end) in
  lazymatch type of x with
  | unit => destruct x as []; _iDestructHyp H xs pat
  | _ => revert x; go ltac:(fun xs' => _iDestructHyp H xs' pat) xs
  end.

(* With everything *)
Tactic Notation "iInv" constr(N) "with" constr(Hs) "as" constr(pat) constr(Hclose) :=
  iInvCore N with Hs as (Some Hclose) in _iDestructAccAndHyp0 pat.
Tactic Notation "iInv" constr(N) "with" constr(Hs) "as"
    "(" ne_simple_intropattern_list(xs) ")" constr(pat) constr(Hclose) :=
  iInvCore N with Hs as (Some Hclose) in _iDestructAccAndHyp xs pat.

(* Without closing view shift *)
Tactic Notation "iInv" constr(N) "with" constr(Hs) "as" constr(pat) :=
  iInvCore N with Hs in _iDestructAccAndHyp0 pat.
Tactic Notation "iInv" constr(N) "with" constr(Hs) "as"
    "(" ne_simple_intropattern_list(xs) ")" constr(pat) :=
  iInvCore N with Hs in _iDestructAccAndHyp xs pat.

(* Without selection pattern *)
Tactic Notation "iInv" constr(N) "as" constr(pat) constr(Hclose) :=
  iInvCore N as (Some Hclose) in _iDestructAccAndHyp0 pat.
Tactic Notation "iInv" constr(N) "as" "(" ne_simple_intropattern_list(xs) ")"
    constr(pat) constr(Hclose) :=
  iInvCore N as (Some Hclose) in _iDestructAccAndHyp xs pat.

(* Without both *)
Tactic Notation "iInv" constr(N) "as" constr(pat) :=
  iInvCore N in _iDestructAccAndHyp0 pat.
Tactic Notation "iInv" constr(N) "as" "(" ne_simple_intropattern_list(xs) ")"
    constr(pat) :=
  iInvCore N in _iDestructAccAndHyp xs pat.

(** Miscellaneous *)
Tactic Notation "iAccu" :=
  iStartProof; eapply tac_accu; [pm_reflexivity || fail "iAccu: not an evar"].

(** Automation *)
Global Hint Extern 0 (_ ⊢ _) => iStartProof : core.
Global Hint Extern 0 (⊢ _) => iStartProof : core.

(* Make sure that [by] and [done] solve trivial things in proof mode.
[iPureIntro] invokes [FromPure], so adding [FromPure] instances can help improve
what [done] can do. *)
Global Hint Extern 0 (envs_entails _ _) => iPureIntro; try done : core.
Global Hint Extern 0 (envs_entails _ ?Q) =>
  first [is_evar Q; fail 1|iAssumption] : core.
Global Hint Extern 0 (envs_entails _ emp) => iEmpIntro : core.

(* TODO: look for a more principled way of adding trivial hints like those
below; see the discussion in !75 for further details. *)
Global Hint Extern 0 (envs_entails _ (_ ≡ _)) =>
  rewrite envs_entails_unseal; apply internal_eq_refl : core.
Global Hint Extern 0 (envs_entails _ (big_opL _ _ _)) =>
  rewrite envs_entails_unseal; apply (big_sepL_nil' _) : core.
Global Hint Extern 0 (envs_entails _ (big_sepL2 _ _ _)) =>
  rewrite envs_entails_unseal; apply (big_sepL2_nil' _) : core.
Global Hint Extern 0 (envs_entails _ (big_opM _ _ _)) =>
  rewrite envs_entails_unseal; apply (big_sepM_empty' _) : core.
Global Hint Extern 0 (envs_entails _ (big_sepM2 _ _ _)) =>
  rewrite envs_entails_unseal; apply (big_sepM2_empty' _) : core.
Global Hint Extern 0 (envs_entails _ (big_opS _ _ _)) =>
  rewrite envs_entails_unseal; apply (big_sepS_empty' _) : core.
Global Hint Extern 0 (envs_entails _ (big_opMS _ _ _)) =>
  rewrite envs_entails_unseal; apply (big_sepMS_empty' _) : core.

(* These introduce as much as possible at once, for better performance. *)
Global Hint Extern 0 (envs_entails _ (∀ _, _)) => iIntros : core.
Global Hint Extern 0 (envs_entails _ (_ → _)) => iIntros : core.
Global Hint Extern 0 (envs_entails _ (_ -∗ _)) => iIntros : core.
(* Multi-intro doesn't work for custom binders. *)
Global Hint Extern 0 (envs_entails _ (∀.. _, _)) => iIntros (?) : core.

Global Hint Extern 1 (envs_entails _ (_ ∧ _)) => iSplit : core.
Global Hint Extern 1 (envs_entails _ (_ ∗ _)) => iSplit : core.
Global Hint Extern 1 (envs_entails _ (_ ↔ _)) => iSplit : core.
Global Hint Extern 1 (envs_entails _ (_ ∗-∗ _)) => iSplit : core.
Global Hint Extern 1 (envs_entails _ (▷ _)) => iNext : core.
Global Hint Extern 1 (envs_entails _ (■ _)) => iModIntro : core.
Global Hint Extern 1 (envs_entails _ (<pers> _)) => iModIntro : core.
Global Hint Extern 1 (envs_entails _ (<affine> _)) => iModIntro : core.
Global Hint Extern 1 (envs_entails _ (□ _)) => iModIntro : core.
Global Hint Extern 1 (envs_entails _ (∃ _, _)) => iExists _ : core.
Global Hint Extern 1 (envs_entails _ (∃.. _, _)) => iExists _ : core.
Global Hint Extern 1 (envs_entails _ (◇ _)) => iModIntro : core.
Global Hint Extern 1 (envs_entails _ (_ ∨ _)) => iLeft : core.
Global Hint Extern 1 (envs_entails _ (_ ∨ _)) => iRight : core.
Global Hint Extern 1 (envs_entails _ (|==> _)) => iModIntro : core.
Global Hint Extern 1 (envs_entails _ (<absorb> _)) => iModIntro : core.
Global Hint Extern 2 (envs_entails _ (|={_}=> _)) => iModIntro : core.

Global Hint Extern 2 (envs_entails _ (_ ∗ _)) => progress iFrame : iFrame.
