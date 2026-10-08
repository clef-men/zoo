Require Ltac2.Ltac2.

Require Import stdpp.coPset.
Require Import stdpp.namespaces.

Require Export iris.bi.bi.
Require Export iris.bi.updates.
Require Import iris.bi.lib.fixpoint_mono.
Require Import iris.proofmode.rocq_tactics.
Require Import iris.proofmode.proofmode.
Require Import iris.proofmode.reduction.
Require Import iris.prelude.options.

(** Conveniently split a conjunction on both assumption and conclusion. *)
Local Tactic Notation "iSplitWith" constr(H) :=
  iApply (bi.and_parallel with H); iSplit; iIntros H.

Section definition.
  Context {PROP : bi} `{!BiFUpd PROP} {TA TB : tele}.
  Implicit Type
    (Eo Ei : coPset) (* outer/inner masks *)
    (α : TA → PROP) (* atomic pre-condition *)
    (P : PROP) (* abortion condition *)
    (β : TA → TB → PROP) (* atomic post-condition *)
    (Φ : TA → TB → PROP) (* post-condition *)
  .

  (** aacc as the "introduction form" of atomic updates: An accessor
      that can be aborted back to [P]. *)
  Definition aacc Eo Ei α P β Φ : PROP :=
    |={Eo, Ei}=> ∃.. x, α x ∗
          ((α x ={Ei, Eo}=∗ P) ∧ (∀.. y, β x y ={Ei, Eo}=∗ Φ x y)).

  Lemma aaccｰwand Eo Ei α P1 P2 β Φ1 Φ2 :
    ((P1 -∗ P2) ∧ (∀.. x y, Φ1 x y -∗ Φ2 x y)) -∗
    (aacc Eo Ei α P1 β Φ1 -∗ aacc Eo Ei α P2 β Φ2).
  Proof.
    iIntros "HP12 AS". iMod "AS" as (x) "[Hα Hclose]".
    iModIntro. iExists x. iFrame "Hα". iSplit.
    - iIntros "Hα". iDestruct "Hclose" as "[Hclose _]".
      iApply "HP12". iApply "Hclose". done.
    - iIntros (y) "Hβ". iDestruct "Hclose" as "[_ Hclose]".
      iApply "HP12". iApply "Hclose". done.
  Qed.

  Lemma aaccｰmask Eo Ed α P β Φ :
    aacc Eo (Eo∖Ed) α P β Φ ⊣⊢ ∀ E, ⌜Eo ⊆ E⌝ → aacc E (E∖Ed) α P β Φ.
  Proof.
    iSplit; last first.
    { iIntros "Hstep". iApply ("Hstep" with "[% //]"). }
    iIntros "Hstep" (E HE).
    iApply (fupd_mask_frame_acc with "Hstep"); first done.
    iIntros "Hstep". iDestruct "Hstep" as (x) "[Hα Hclose]".
    iIntros "!> Hclose'".
    iExists x. iFrame. iSplitWith "Hclose".
    - iIntros "Hα". iApply "Hclose'". iApply "Hclose". done.
    - iIntros (y) "Hβ". iApply "Hclose'". iApply "Hclose". done.
  Qed.

  Lemma aaccｰmaskｰweaken Eo1 Eo2 Ei α P β Φ :
    Eo1 ⊆ Eo2 →
    aacc Eo1 Ei α P β Φ -∗ aacc Eo2 Ei α P β Φ.
  Proof.
    iIntros (HE) "Hstep".
    iMod (fupd_mask_subseteq Eo1) as "Hclose1"; first done.
    iMod "Hstep" as (x) "[Hα Hclose2]". iIntros "!>". iExists x.
    iFrame. iSplitWith "Hclose2".
    - iIntros "Hα". iMod ("Hclose2" with "Hα") as "$". done.
    - iIntros (y) "Hβ". iMod ("Hclose2" with "Hβ") as "$". done.
  Qed.

  (** aupd as a fixed-point of the equation
   AU = aacc α AU β Q
  *)
  Context Eo Ei α β Φ.

  Definition aupd۰pre (Ψ : () → PROP) (_ : ()) : PROP :=
    aacc Eo Ei α (Ψ ()) β Φ.

  Local Instance aupd۰preｰmono : BiMonoPred aupd۰pre.
  Proof.
    constructor.
    - iIntros (P1 P2 ??) "#HP12". iIntros ([]) "AU".
      iApply (aaccｰwand with "[HP12] AU").
      iSplit; last by eauto. iApply "HP12".
    - intros ??. solve_proper.
  Qed.

  Local Definition aupd۰def :=
    bi_greatest_fixpoint aupd۰pre ().

End definition.

(** Seal it *)
Local Definition aupd۰aux : seal (@aupd۰def).
Proof. by eexists. Qed.
Definition aupd := aupd۰aux.(unseal).
Global Arguments aupd {PROP _ TA TB}.
Local Definition aupdｰunseal :
  @aupd = _ := aupd۰aux.(seal_eq).

Global Arguments aacc {PROP _ TA TB} Eo Ei _ _ _ _ : simpl never.
Global Arguments aupd {PROP _ TA TB} Eo Ei _ _ _ : simpl never.

(** Notation: Atomic updates *)
(** We avoid '<<'/'>>' since those can also reasonably be infix operators
(and in fact Autosubst uses the latter). *)
Notation "'AU' '<{' ∃∃ x1 .. xn , α '}>' @ Eo , Ei '<{' ∀∀ y1 .. yn , β , 'COMM' Φ '}>'" :=
(* The way to read the [tele_app foo] here is that they convert the n-ary
function [foo] into a unary function taking a telescope as the argument. *)
  (aupd (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                 (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                 Eo Ei
                 (tele_app $ λ x1, .. (λ xn, α%I) ..)
                 (tele_app $ λ x1, .. (λ xn,
                         tele_app (λ y1, .. (λ yn, β%I) .. )
                        ) .. )
                 (tele_app $ λ x1, .. (λ xn,
                         tele_app (λ y1, .. (λ yn, Φ%I) .. )
                        ) .. )
  )
  (at level 0, Eo, Ei, α, β, Φ at level 200, x1 binder, xn binder, y1 binder, yn binder,
   format "'[hv   ' 'AU'  '<{'  '[' ∃∃  x1  ..  xn ,  '/' α  ']' '}>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<{'  '[' ∀∀  y1  ..  yn ,  '/' β ,  '/' COMM  Φ  ']' '}>' ']'") : bi_scope.

Notation "'AU' '<{' ∃∃ x1 .. xn , α '}>' @ Eo , Ei '<{' β , 'COMM' Φ '}>'" :=
  (aupd (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                 (TB:=TeleO)
                 Eo Ei
                 (tele_app $ λ x1, .. (λ xn, α%I) ..)
                 (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
                 (tele_app $ λ x1, .. (λ xn, tele_app Φ%I) .. )
  )
  (at level 0, Eo, Ei, α, β, Φ at level 200, x1 binder, xn binder,
   format "'[hv   ' 'AU'  '<{'  '[' ∃∃  x1  ..  xn ,  '/' α  ']' '}>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<{'  '[' β ,  '/' COMM  Φ  ']' '}>' ']'") : bi_scope.

Notation "'AU' '<{' α '}>' @ Eo , Ei '<{' ∀∀ y1 .. yn , β , 'COMM' Φ '}>'" :=
  (aupd (TA:=TeleO)
                 (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                 Eo Ei
                 (tele_app α%I)
                 (tele_app $ tele_app (λ y1, .. (λ yn, β%I) ..))
                 (tele_app $ tele_app (λ y1, .. (λ yn, Φ%I) ..))
  )
  (at level 0, Eo, Ei, α, β, Φ at level 200, y1 binder, yn binder,
   format "'[hv   ' 'AU'  '<{'  '[' α  ']' '}>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<{'  '[' ∀∀  y1  ..  yn ,  '/' β ,  '/' COMM  Φ  ']' '}>' ']'") : bi_scope.

Notation "'AU' '<{' α '}>' @ Eo , Ei '<{' β , 'COMM' Φ '}>'" :=
  (aupd (TA:=TeleO) (TB:=TeleO)
                 Eo Ei
                 (tele_app α%I)
                 (tele_app $ tele_app β%I)
                 (tele_app $ tele_app Φ%I)
  )
  (at level 0, Eo, Ei, α, β, Φ at level 200,
   format "'[hv   ' 'AU'  '<{'  '[' α  ']' '}>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<{'  '[' β ,  '/' COMM  Φ  ']' '}>' ']'") : bi_scope.

(** Notation: Atomic accessors *)
Notation "'AACC' '<{' ∃∃ x1 .. xn , α , 'ABORT' P '}>' @ Eo , Ei '<{' ∀∀ y1 .. yn , β , 'COMM' Φ '}>'" :=
  (aacc (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
              (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
              Eo Ei
              (tele_app $ λ x1, .. (λ xn, α%I) ..)
              P%I
              (tele_app $ λ x1, .. (λ xn,
                      tele_app (λ y1, .. (λ yn, β%I) .. )
                     ) .. )
              (tele_app $ λ x1, .. (λ xn,
                      tele_app (λ y1, .. (λ yn, Φ%I) .. )
                     ) .. )
  )
  (at level 0, Eo, Ei, α, P, β, Φ at level 200, x1 binder, xn binder, y1 binder, yn binder,
   format "'[hv     ' 'AACC'  '<{'  '[' ∃∃  x1  ..  xn ,  '/' α ,  '/' ABORT  P  ']' '}>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<{'  '[' ∀∀  y1  ..  yn ,  '/' β ,  '/' COMM  Φ  ']' '}>' ']'") : bi_scope.

Notation "'AACC' '<{' ∃∃ x1 .. xn , α , 'ABORT' P '}>' @ Eo , Ei '<{' β , 'COMM' Φ '}>'" :=
  (aacc (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
              (TB:=TeleO)
              Eo Ei
              (tele_app $ λ x1, .. (λ xn, α%I) ..)
              P%I
              (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
              (tele_app $ λ x1, .. (λ xn, tele_app Φ%I) .. )
  )
  (at level 0, Eo, Ei, α, P, β, Φ at level 200, x1 binder, xn binder,
   format "'[hv     ' 'AACC'  '<{'  '[' ∃∃  x1  ..  xn ,  '/' α ,  '/' ABORT  P  ']' '}>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<{'  '[' β ,  '/' COMM  Φ  ']' '}>' ']'") : bi_scope.

Notation "'AACC' '<{' α , 'ABORT' P '}>' @ Eo , Ei '<{' ∀∀ y1 .. yn , β , 'COMM' Φ '}>'" :=
  (aacc (TA:=TeleO)
              (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
              Eo Ei
              (tele_app α%I)
              P%I
              (tele_app $ tele_app (λ y1, .. (λ yn, β%I) ..))
              (tele_app $ tele_app (λ y1, .. (λ yn, Φ%I) ..))
  )
  (at level 0, Eo, Ei, α, P, β, Φ at level 200, y1 binder, yn binder,
   format "'[hv     ' 'AACC'  '<{'  '[' α ,  '/' ABORT  P  ']' '}>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<{'  '[' ∀∀  y1  ..  yn ,  '/' β ,  '/' COMM  Φ  ']' '}>' ']'") : bi_scope.

Notation "'AACC' '<{' α , 'ABORT' P '}>' @ Eo , Ei '<{' β , 'COMM' Φ '}>'" :=
  (aacc (TA:=TeleO)
              (TB:=TeleO)
              Eo Ei
              (tele_app α%I)
              P%I
              (tele_app $ tele_app β%I)
              (tele_app $ tele_app Φ%I)
  )
  (at level 0, Eo, Ei, α, P, β, Φ at level 200,
   format "'[hv     ' 'AACC'  '<{'  '[' α ,  '/' ABORT  P  ']' '}>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<{'  '[' β ,  '/' COMM  Φ  ']' '}>' ']'") : bi_scope.

(** Lemmas about AU *)
Section lemmas.
  Context `{BiFUpd PROP} {TA TB : tele}.
  Implicit Type (α : TA → PROP) (β Φ : TA → TB → PROP) (P : PROP).

  Local Existing Instance aupd۰preｰmono.

  (* Can't be in the section above as that fixes the parameters *)
  Global Instance aaccｰne Eo Ei n :
    Proper (
        pointwise_relation TA (dist n) ==>
        dist n ==>
        pointwise_relation TA (pointwise_relation TB (dist n)) ==>
        pointwise_relation TA (pointwise_relation TB (dist n)) ==>
        dist n
    ) (aacc (PROP:=PROP) Eo Ei).
  Proof. solve_proper. Qed.

  Global Instance aupdｰne Eo Ei n :
    Proper (
        pointwise_relation TA (dist n) ==>
        pointwise_relation TA (pointwise_relation TB (dist n)) ==>
        pointwise_relation TA (pointwise_relation TB (dist n)) ==>
        dist n
    ) (aupd (PROP:=PROP) Eo Ei).
  Proof.
    rewrite aupdｰunseal /aupd۰def /aupd۰pre. solve_proper.
  Qed.

  Lemma aupdｰmaskｰweaken Eo1 Eo2 Ei α β Φ :
    Eo1 ⊆ Eo2 →
    aupd Eo1 Ei α β Φ -∗ aupd Eo2 Ei α β Φ.
  Proof.
    rewrite aupdｰunseal {2}/aupd۰def /=.
    iIntros (Heo) "HAU".
    iApply (greatest_fixpoint_coiter _ (λ _, aupd۰def Eo1 Ei α β Φ)); last done.
    iIntros "!> *". rewrite {1}/aupd۰def /= greatest_fixpoint_unfold.
    iApply aaccｰmaskｰweaken. done.
  Qed.

  Local Lemma aupdｰunfold Eo Ei α β Φ :
    aupd Eo Ei α β Φ ⊣⊢
    aacc Eo Ei α (aupd Eo Ei α β Φ) β Φ.
  Proof.
    rewrite aupdｰunseal /aupd۰def /=. apply: greatest_fixpoint_unfold.
  Qed.

  (** The elimination form: an atomic accessor *)
  Lemma aupdｰaacc Eo Ei α β Φ :
    aupd Eo Ei α β Φ ⊢
    aacc Eo Ei α (aupd Eo Ei α β Φ) β Φ.
  Proof using Type*. by rewrite {1}aupdｰunfold. Qed.

  (* This lets you eliminate atomic updates with iMod. *)
  Global Instance elim_modｰaupd φ Eo Ei E α β Φ Q Q' :
    (∀ R, ElimModal φ false false (|={E,Ei}=> R) R Q Q') →
    ElimModal (φ ∧ Eo ⊆ E) false false
              (aupd Eo Ei α β Φ)
              (∃.. x, α x ∗
                       (α x ={Ei,E}=∗ aupd Eo Ei α β Φ) ∧
                       (∀.. y, β x y ={Ei,E}=∗ Φ x y))
              Q Q'.
  Proof.
    intros ?. rewrite /ElimModal /= =>-[??]. iIntros "[AU Hcont]".
    iPoseProof (aupdｰaacc with "AU") as "AC".
    iMod (aaccｰmaskｰweaken with "AC"); first done.
    iApply "Hcont". done.
  Qed.

  (** The introduction lemma for aupd. This should usually not be used
  directly; use the [iAuIntro] tactic instead. *)
  Local Lemma aupdｰintro P Q α β Eo Ei Φ :
    Absorbing P → Persistent P →
    (P ∧ Q ⊢ aacc Eo Ei α Q β Φ) →
    P ∧ Q ⊢ aupd Eo Ei α β Φ.
  Proof.
    rewrite aupdｰunseal {1}/aupd۰def /=.
    iIntros (?? HAU) "[#HP HQ]".
    iApply (greatest_fixpoint_coiter _ (λ _, Q)); last done. iIntros "!>" ([]) "HQ".
    iApply HAU. iSplit; by iFrame.
  Qed.

  Lemma aaccｰintro Eo Ei α P β Φ x :
    Ei ⊆ Eo →
    α x -∗
    ( α x ={Eo}=∗ P)
    ∧ (∀.. y : TB, β x y ={Eo}=∗ Φ x y
    ) -∗
    aacc Eo Ei α P β Φ.
  Proof.
    iIntros (?) "Hα Hclose".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose'".
    iExists x. iFrame. iSplitWith "Hclose".
    - iIntros "Hα". iMod "Hclose'" as "_". iApply "Hclose". done.
    - iIntros (y) "Hβ". iMod "Hclose'" as "_". iApply "Hclose". done.
  Qed.

  (* This lets you open invariants etc. when the goal is an atomic accessor. *)
  Global Instance elim_accｰaacc {X} E1 E2 Ei (α' β' : X → PROP) γ' α β Pas Φ :
    ElimAcc (X:=X) True (fupd E1 E2) (fupd E2 E1) α' β' γ'
            (aacc E1 Ei α Pas β Φ)
            (λ x', aacc E2 Ei α (β' x' ∗ (γ' x' -∗? Pas))%I β
                (λ.. x y, β' x' ∗ (γ' x' -∗? Φ x y))
            )%I.
  Proof.
    (* FIXME: Is there any way to prevent maybe_wand from unfolding?
       It gets unfolded by env_cbv in the proofmode, ideally we'd like that
       to happen only if one argument is a constructor. *)
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x') "[Hα' Hclose]".
    iMod ("Hinner" with "Hα'") as (x) "[Hα Hclose']".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose''".
    iExists x. iFrame. iSplitWith "Hclose'".
    - iIntros "Hα". iMod "Hclose''" as "_".
      iMod ("Hclose'" with "Hα") as "[Hβ' HPas]".
      iMod ("Hclose" with "Hβ'") as "Hγ'".
      iModIntro. destruct (γ' x'); iApply "HPas"; done.
    - iIntros (y) "Hβ". iMod "Hclose''" as "_".
      iMod ("Hclose'" with "Hβ") as "Hβ'".
      (* FIXME: Using ssreflect rewrite does not work, see Rocq bug #7773. *)
      rewrite ->!tele_app_bind. iDestruct "Hβ'" as "[Hβ' HΦ]".
      iMod ("Hclose" with "Hβ'") as "Hγ'".
      iModIntro. destruct (γ' x'); iApply "HΦ"; done.
  Qed.

  (* Everything that fancy updates can eliminate without changing, atomic
  accessors can eliminate as well.  This is a forwarding instance needed because
  aacc is becoming opaque. *)
  Global Instance elim_modalｰacc p q φ P P' Eo Ei α Pas β Φ :
    (∀ Q, ElimModal φ p q P P' (|={Eo,Ei}=> Q) (|={Eo,Ei}=> Q)) →
    ElimModal φ p q P P'
              (aacc Eo Ei α Pas β Φ)
              (aacc Eo Ei α Pas β Φ).
  Proof. intros Helim. apply Helim. Qed.

  (** Lemmas for directly proving one atomic accessor in terms of another (or an
      atomic update).  These are only really useful when the atomic accessor you
      are trying to prove exactly corresponds to an atomic update/accessor you
      have as an assumption -- which is not very common. *)
  Lemma aaccｰaacc {TA' TB' : tele} E1 E1' E2 E3
        α P β Φ
        (α' : TA' → PROP) P' (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 →
    aacc E1' E2 α P β Φ -∗
    (∀.. x, α x -∗ aacc E2 E3 α' (α x ∗ (P ={E1}=∗ P')) β'
            (λ.. x' y', (α x ∗ (P ={E1}=∗ Φ' x' y'))
                    ∨ ∃.. y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y'))) -∗
    aacc E1 E3 α' P' β' Φ'.
  Proof.
    iIntros (?) "Hupd Hstep".
    iMod (aaccｰmaskｰweaken with "Hupd") as (x) "[Hα Hclose]"; first done.
    iMod ("Hstep" with "Hα") as (x') "[Hα' Hclose']".
    iModIntro. iExists x'. iFrame "Hα'". iSplit.
    - iIntros "Hα'". iDestruct "Hclose'" as "[Hclose' _]".
      iMod ("Hclose'" with "Hα'") as "[Hα Hupd]".
      iDestruct "Hclose" as "[Hclose _]".
      iMod ("Hclose" with "Hα"). iApply "Hupd". auto.
    - iIntros (y') "Hβ'". iDestruct "Hclose'" as "[_ Hclose']".
      iMod ("Hclose'" with "Hβ'") as "Hres".
      (* FIXME: Using ssreflect rewrite does not work, see Rocq bug #7773. *)
      rewrite ->!tele_app_bind. iDestruct "Hres" as "[[Hα HΦ']|Hcont]".
      + (* Abort the step we are eliminating *)
        iDestruct "Hclose" as "[Hclose _]".
        iMod ("Hclose" with "Hα") as "HP".
        iApply "HΦ'". done.
      + (* Complete the step we are eliminating *)
        iDestruct "Hclose" as "[_ Hclose]".
        iDestruct "Hcont" as (y) "[Hβ HΦ']".
        iMod ("Hclose" with "Hβ") as "HΦ".
        iApply "HΦ'". done.
  Qed.

  Lemma aaccｰaupd {TA' TB' : tele} E1 E1' E2 E3
        α β Φ
        (α' : TA' → PROP) P' (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 →
    aupd E1' E2 α β Φ -∗
    (∀.. x, α x -∗ aacc E2 E3 α' (α x ∗ (aupd E1' E2 α β Φ ={E1}=∗ P')) β'
            (λ.. x' y', (α x ∗ (aupd E1' E2 α β Φ ={E1}=∗ Φ' x' y'))
                    ∨ ∃.. y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y'))) -∗
    aacc E1 E3 α' P' β' Φ'.
  Proof.
    iIntros (?) "Hupd Hstep". iApply (aaccｰaacc with "[Hupd] Hstep"); first done.
    iApply aupdｰaacc; done.
  Qed.

  Lemma aaccｰaupdｰcommit {TA' TB' : tele} E1 E1' E2 E3
        α β Φ
        (α' : TA' → PROP) P' (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 →
    aupd E1' E2 α β Φ -∗
    (∀.. x, α x -∗ aacc E2 E3 α' (α x ∗ (aupd E1' E2 α β Φ ={E1}=∗ P')) β'
            (λ.. x' y', ∃.. y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y'))) -∗
    aacc E1 E3 α' P' β' Φ'.
  Proof.
    iIntros (?) "Hupd Hstep". iApply (aaccｰaupd with "Hupd"); first done.
    iIntros (x) "Hα". iApply aaccｰwand; last first.
    { iApply "Hstep". done. }
    (* FIXME: Using ssreflect rewrite does not work, see Rocq bug #7773. *)
    iSplit; first by eauto. iIntros (??) "?". rewrite ->!tele_app_bind. by iRight.
  Qed.

  Lemma aaccｰaupdｰabort {TA' TB' : tele} E1 E1' E2 E3
        α β Φ
        (α' : TA' → PROP) P' (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 →
    aupd E1' E2 α β Φ -∗
    (∀.. x, α x -∗ aacc E2 E3 α' (α x ∗ (aupd E1' E2 α β Φ ={E1}=∗ P')) β'
            (λ.. x' y', α x ∗ (aupd E1' E2 α β Φ ={E1}=∗ Φ' x' y'))) -∗
    aacc E1 E3 α' P' β' Φ'.
  Proof.
    iIntros (?) "Hupd Hstep". iApply (aaccｰaupd with "Hupd"); first done.
    iIntros (x) "Hα". iApply aaccｰwand; last first.
    { iApply "Hstep". done. }
    (* FIXME: Using ssreflect rewrite does not work, see Rocq bug #7773. *)
    iSplit; first by eauto. iIntros (??) "?". rewrite ->!tele_app_bind. by iLeft.
  Qed.

End lemmas.

(** ProofMode support for atomic updates. *)
Section proof_mode.
  Context `{BiFUpd PROP} {TA TB : tele}.
  Implicit Type (α : TA → PROP) (β Φ : TA → TB → PROP) (P : PROP).

  Lemma tacｰaupdｰintro Γp Γs n α β Eo Ei Φ P :
    P = env_to_prop Γs →
    envs_entails (Envs Γp Γs n) (aacc Eo Ei α P β Φ) →
    envs_entails (Envs Γp Γs n) (aupd Eo Ei α β Φ).
  Proof.
    intros ->. rewrite envs_entails_unseal of_envs_eq /aacc /=.
    setoid_rewrite env_to_prop_sound =>HAU.
    rewrite assoc. apply: aupdｰintro. by rewrite -assoc.
  Qed.
End proof_mode.

(** * Now the Rocq-level tactics *)

Tactic Notation "iAuIntro" :=
  match goal with
  | |- envs_entails (Envs ?Γp ?Γs _) (aupd _ _ _ _ ?Φ) =>
      notypeclasses refine (tacｰaupdｰintro Γp Γs _ _ _ _ _ Φ _ _ _); [
        (* P = ...: make the P pretty *) pm_reflexivity
      | (* the new proof mode goal *) ]
  end.

Module iAaccIntro.
  Import Ltac2.

  Ltac2 Type error :=
    [ Invalid_telescope
    | Too_many_witnesses
    ].

  Ltac2 error_to_string err :=
    match err with
    | Invalid_telescope =>
        "invalid telescope"
    | Too_many_witnesses =>
        "too many witnesses"
    end.
  Ltac2 error err :=
    let err := error_to_string err in
    let err := String.app "iAaccIntro: " err in
    Control.throw_invalid_argument err.

  Ltac2 rec extra_witnesses xs tele :=
    lazy_match! tele with
    | TeleO =>
        'TargO
    | TeleS ?tele =>
        match Constr.Unsafe.kind tele with
        | Constr.Unsafe.Lambda bdr tele =>
            let ty := Constr.Binder.type bdr in
            let ty := Constr.Unsafe.substnl xs 0 ty in
            let x := '?[?witness] in
            let xs := extra_witnesses (x :: xs) tele in
            Constr.Unsafe.make (Constr.Unsafe.App '@TeleArgCons [|ty; '_; x; xs|])
        | _ =>
            '?[?witnesses]
        end
    | _ =>
        '?[?witnesses]
    end.

  Ltac2 rec witnesses' xs1 tele xs2 :=
    match xs2 with
    | [] =>
        extra_witnesses xs1 tele
    | x :: xs2 =>
        lazy_match! tele with
        | TeleO =>
            error Too_many_witnesses
        | TeleS ?tele =>
            match Constr.Unsafe.kind tele with
            | Constr.Unsafe.Lambda bdr tele =>
                let ty := Constr.Binder.type bdr in
                let ty := Constr.Unsafe.substnl xs1 0 ty in
                let x :=
                  Constr.Pretype.pretype
                    Constr.Pretype.Flags.open_constr_flags_with_tc
                    Constr.Pretype.expected_without_type_constraint
                    preterm:($preterm:x : $ty)
                in
                let xs2 := witnesses' (x :: xs1) tele xs2 in
                Constr.Unsafe.make (Constr.Unsafe.App '@TeleArgCons [|ty; '_; x; xs2|])
            | _ =>
                error Invalid_telescope
            end
        | _ =>
            error Invalid_telescope
        end
    end.
  Ltac2 witnesses tele xs :=
    witnesses' [] tele xs.
End iAaccIntro.

Tactic Notation "iAaccIntro" uconstr_list_sep(xs, ",") "with" constr(H) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (@aacc _ _ ?tele _ ?Eo ?Ei ?α ?P ?β ?Φ) =>
      let go := ltac2val:(tele xs |-
        let tele := Option.get (Ltac1.to_constr tele) in
        let xs := Option.get (Ltac1.to_list xs) in
        let xs := List.map (fun x => Option.get (Ltac1.to_preterm x)) xs in
        let xs := iAaccIntro.witnesses tele xs in
        Ltac1.of_constr xs
      ) in
      let xs := go tele xs in
      iApply (aaccｰintro Eo Ei α P β Φ xs with H);
        first try solve_ndisj;
        last iSplit
  | _ =>
      fail "iAaccIntro: goal is not an atomic accessor"
  end.

(* From here on, prevent TC search from implicitly unfolding these. *)
Global Typeclasses Opaque aacc aupd.
