Require Import zoo.prelude.
Require Import zoo.iris.diaframe.
Require Import zoo.language.tactics.
Require Import zoo.language.notations.
Require Export zoo.language.typeclasses.
Require Export zoo.program_logic.bwp.
Require Import zoo.options.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  #[local] Definition wp۰def e tid E Φ :=
    match tid with
    | None =>
        ∀ tid, BWP e ∶ tid @ E {{ Φ }}
    | Some tid =>
        BWP e ∶ tid @ E {{ Φ }}
    end%I.
  #[global] Arguments wp۰def _ _%_E _ _%_I : assert.
End zoo۰G.

#[local] Definition wp۰aux : seal (@wp۰def).
  Proof. by eexists. Qed.
Definition wp :=
  wp۰aux.(unseal).
#[global] Arguments wp {_ _} _ _%_E _ _%_I : assert.
#[local] Lemma wpｰunseal `{zoo۰G : !ZooG Σ} :
  wp = wp۰def.
Proof.
  rewrite -wp۰aux.(seal_eq) //.
Qed.

#[local] Ltac wpｰunseal :=
  rewrite wpｰunseal /wp۰def;
  select (option thread_id) (fun tid => destruct tid).

Declare Custom Entry wp۰thread_id.
Notation "" := (
  None
)(in custom wp۰thread_id
).
Notation "∶ tid" := (
  Some tid
)(in custom wp۰thread_id at level 200,
  tid constr,
  format "'/  ' ∶  tid "
).
Notation "∷ tid" :=
  tid
( in custom wp۰thread_id at level 200,
  tid constr,
  format "'/  ' ∷  tid "
).

Notation "'WP' e tid E {{ Φ } }" := (
  wp e%E tid E Φ%I
)(at level 0,
  e at level 200,
  tid custom wp۰thread_id at level 200,
  E custom wp۰mask at level 200,
  Φ at level 200,
  format "'[hv' WP  '/  ' '[' e ']'  tid E '/' {{  '[' Φ ']'  '/' } } ']'"
) : bi_scope.
Notation "'WP' e tid E {{ v , Q } }" := (
  wp e%E tid E (λ v, Q%I)
)(at level 0,
  e at level 200,
  tid custom wp۰thread_id at level 200,
  E custom wp۰mask at level 200,
  v at level 200 as pattern,
  Q at level 200,
  format "'[hv' WP  '/  ' '[' e ']'  tid E '/' {{  '[' v ,  '/' Q ']'  '/' } } ']'"
) : bi_scope.

Notation "'{{{' P } } } e tid E {{{ x1 .. xn , 'RET' v ; Q } } }" :=
  ( □ ∀ Φ,
      P -∗
      ▷ (∀ x1, .. (∀ xn, Q -∗ Φ (v : val)) ..) -∗
      wp e%E tid E Φ
  )%I
( at level 20,
  P at level 200,
  e at level 200,
  tid custom wp۰thread_id at level 200,
  E custom wp۰mask at level 200,
  x1 closed binder,
  xn closed binder,
  Q at level 200,
  format "'[hv' {{{  '/  ' '[' P ']'  '/' } } }  '/  ' '[' e ']'  tid E '/' {{{  x1  ..  xn ,  '/  ' RET  v ;  '/  ' '[' Q ']'  '/' } } } ']'"
) : bi_scope.
Notation "'{{{' P } } } e tid E {{{ 'RET' v ; Q } } }" :=
  ( □ ∀ Φ,
      P -∗
      ▷ (Q -∗ Φ (v : val)) -∗
      wp e%E tid E Φ
  )%I
( at level 20,
  P at level 200,
  e at level 200,
  tid custom wp۰thread_id at level 200,
  E custom wp۰mask at level 200,
  Q at level 200,
  format "'[hv' {{{  '/  ' '[' P ']'  '/' } } }  '/  ' '[' e ']'  tid E '/' {{{  '/  ' RET  v ;  '/  ' '[' Q ']'  '/' } } } ']'"
) : bi_scope.

Notation "'{{{' P } } } e tid E {{{ x1 .. xn , 'RET' v ; Q } } }" := (
  ∀ Φ,
  P%I -∗
  ▷ (∀ x1, .. (∀ xn, Q%I -∗ Φ (v : val)) ..) -∗
  wp e%E tid E Φ%I
) : stdpp_scope.
Notation "'{{{' P } } } e tid E {{{ 'RET' v ; Q } } }" := (
  ∀ Φ,
  P%I -∗
  ▷ (Q%I -∗ Φ (v : val)) -∗
  wp e%E tid E Φ%I
) : stdpp_scope.

Implicit Type b : bool.
Implicit Type l : location.
Implicit Type pid : prophet_id.
Implicit Type e : expr.
Implicit Type es : list expr.
Implicit Type v w : val.
Implicit Type σ : state.
Implicit Type κ κs : list observation.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Implicit Type P R : iProp Σ.
  Implicit Type Φ : val → iProp Σ.

  #[global] Instance wpｰne e tid E n :
    Proper (pointwise_relation _ (≡{n}≡) ==> (≡{n}≡)) (wp e tid E).
  Proof.
    rewrite wpｰunseal. solve_proper.
  Qed.
  #[global] Instance wpｰproper e tid E :
    Proper (pointwise_relation _ (≡) ==> (≡)) (wp e tid E).
  Proof.
    rewrite wpｰunseal. solve_proper.
  Qed.
  #[global] Instance wpｰcontractive e tid E n :
    TCEq (to_val e) None →
    Proper (pointwise_relation _ (dist_later n) ==> (≡{n}≡)) (wp e tid E).
  Proof.
    wpｰunseal.
    - apply bwpｰcontractive.
    - intros He Φ1 Φ2 HΦ.
      f_equiv => tid.
      apply bwpｰcontractive; done.
  Qed.

  Lemma wpｰthread_id_mono e tid E Φ :
    WP e @ E {{ Φ }} ⊢
    WP e ∷ tid @ E {{ Φ }}.
  Proof.
    wpｰunseal.
    all: iSteps.
  Qed.

  Lemma wpｰbwp e tid E Φ :
    WP e ∶ tid @ E {{ Φ }} ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    rewrite wpｰunseal. iSteps.
  Qed.

  Lemma bwpｰwp e tid E Φ :
    BWP e ∶ tid @ E {{ Φ }} ⊢
    WP e ∶ tid @ E {{ Φ }}.
  Proof.
    rewrite wpｰunseal //.
  Qed.
  Lemma bwpｰwpｰweak e tid E Φ :
    (∀ tid, BWP e ∶ tid @ E {{ Φ }}) ⊢
    WP e ∷ tid @ E {{ Φ }}.
  Proof.
    rewrite -wpｰthread_id_mono wpｰunseal //.
  Qed.

  Lemma wpｰstate_interp e tid E Φ :
    ( ∀ ns nt σ κs,
      state_interp ns nt σ κs ={E}=∗
        state_interp ns nt σ κs ∗
        WP e ∷ tid @ E {{ Φ }}
    ) ⊢
    WP e ∷ tid @ E {{ Φ }}.
  Proof.
    wpｰunseal.
    - apply bwpｰstate_interp.
    - iIntros "H %tid".
      iApply bwpｰstate_interp. iIntros "%ns %nt %σ %κs Hinterp".
      iMod ("H" with "Hinterp") as "($ & H)".
      iSteps.
  Qed.

  Lemma wpｰvalueｰfupd' v tid E Φ :
    (|={E}=> Φ v) ⊢
    WP of_val v ∷ tid @ E {{ Φ }}.
  Proof.
    wpｰunseal.
    - apply bwpｰvalueｰfupd'.
    - iIntros "H %tid".
      iApply (bwpｰvalueｰfupd' with "H").
  Qed.
  Lemma wpｰvalueｰfupd e v tid E Φ :
    AsVal e v →
    (|={E}=> Φ v) ⊢
    WP e ∷ tid @ E {{ Φ }}.
  Proof.
    rewrite wpｰvalueｰfupd' => <- //.
  Qed.
  Lemma wpｰvalue' v tid E Φ :
    Φ v ⊢
    WP of_val v ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply (wpｰvalueｰfupd' with "HΦ").
  Qed.
  Lemma wpｰvalue e v tid E Φ :
    AsVal e v →
    Φ v ⊢
    WP e ∷ tid @ E {{ Φ }}.
  Proof.
    rewrite wpｰvalue' => <- //.
  Qed.

  Lemma wpｰvalueｰmono v tid E Φ1 Φ2 :
    WP of_val v ∷ tid @ E {{ Φ1 }} -∗
    (Φ1 v ={E}=∗ Φ2 v) -∗
    WP of_val v ∷ tid @ E {{ Φ2 }}.
  Proof.
    wpｰunseal.
    - apply bwpｰvalueｰmono.
    - iIntros "H HΦ %tid".
      iApply (bwpｰvalueｰmono with "H HΦ").
  Qed.

  Lemma wpｰstrongｰmono e tid E1 Φ1 E2 Φ2 :
    E1 ⊆ E2 →
    WP e ∷ tid @ E1 {{ Φ1 }} -∗
    (∀ v, Φ1 v ={E2}=∗ Φ2 v) -∗
    WP e ∷ tid @ E2 {{ Φ2 }}.
  Proof.
    wpｰunseal.
    - apply bwpｰstrongｰmono.
    - iIntros "%HE H HΦ %tid".
      iApply (bwpｰstrongｰmono with "H HΦ"); first done.
  Qed.
  Lemma wpｰmono e tid E Φ1 Φ2 :
    (∀ v, Φ1 v ⊢ Φ2 v) →
    WP e ∷ tid @ E {{ Φ1 }} ⊢
    WP e ∷ tid @ E {{ Φ2 }}.
  Proof.
    iIntros "%HΦ H".
    iApply (wpｰstrongｰmono with "H"); first done. iIntros "%v HΦ".
    iApply (HΦ with "HΦ").
  Qed.
  #[global] Instance wpｰmono' e tid E :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp e tid E).
  Proof.
    intros Φ1 Φ2 HΦ.
    apply wpｰmono. done.
  Qed.
  #[global] Instance wpｰflipｰmono' e tid E :
    Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp e tid E).
  Proof.
    solve_proper.
  Qed.

  Lemma fupdｰwp e tid E Φ :
    (|={E}=> WP e ∷ tid @ E {{ Φ }}) ⊢
    WP e ∷ tid @ E {{ Φ }}.
  Proof.
    wpｰunseal.
    - apply fupdｰbwp.
    - iIntros "H %tid".
      iSpecialize ("H" $! tid).
      iApply (fupdｰbwp with "H").
  Qed.
  Lemma wpｰfupd e tid E Φ :
    WP e ∷ tid @ E {{ v, |={E}=> Φ v }} ⊢
    WP e ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (wpｰstrongｰmono with "H"); first done.
    iSteps.
  Qed.

  Lemma wpｰframeｰl e tid E Φ R :
    R ∗ WP e ∷ tid @ E {{ Φ }} ⊢
    WP e ∷ tid @ E {{ v, R ∗ Φ v }}.
  Proof.
    iIntros "(HR & H)".
    iApply (wpｰstrongｰmono with "H"); first done.
    iSteps.
  Qed.
  Lemma wpｰframeｰr e tid E Φ R :
    WP e ∷ tid @ E {{ Φ }} ∗ R ⊢
    WP e ∷ tid @ E {{ v, Φ v ∗ R }}.
  Proof.
    iIntros "(H & HR)".
    iApply (wpｰstrongｰmono with "H"); first done.
    iSteps.
  Qed.

  Lemma wpｰwand {e tid E} Φ1 Φ2 :
    WP e ∷ tid @ E {{ Φ1 }} -∗
    (∀ v, Φ1 v -∗ Φ2 v) -∗
    WP e ∷ tid @ E {{ Φ2 }}.
  Proof.
    iIntros "H HΦ".
    iApply (wpｰstrongｰmono with "H"); first done.
    iSteps.
  Qed.
  Lemma wpｰframeｰwand e tid E Φ R :
    R -∗
    WP e ∷ tid @ E {{ v, R -∗ Φ v }} -∗
    WP e ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros "HR H".
    iApply (wpｰwand with "H").
    iSteps.
  Qed.

  Lemma wpｰatomic e `{!Atomic e} tid E1 E2 Φ :
    (|={E1,E2}=> WP e ∷ tid @ E2 {{ v, |={E2,E1}=> Φ v }}) ⊢
    WP e ∷ tid @ E1 {{ Φ }}.
  Proof.
    wpｰunseal.
    - apply bwpｰatomic; first done.
    - iIntros "H %tid".
      iSpecialize ("H" $! tid).
      iApply (bwpｰatomic with "H").
  Qed.

  Lemma wpｰbind K `{!Context K} e tid1 tid2 E Φ :
    ( if tid2 is Some tid2 then
        if tid1 is Some tid1 then
          tid1 = tid2
        else
          False
      else
        True
    ) →
    WP e ∷ tid2 @ E {{ v, WP K (of_val v) ∷ tid1 @ E {{ Φ }} }} ⊢
    WP K e ∷ tid1 @ E {{ Φ }}.
  Proof.
    wpｰunseal; destruct tid1 as [tid1 |].
    - intros ->.
      apply bwpｰbind; first done.
    - done.
    - iIntros "_ H".
      iApply (bwpｰbind with "H").
    - iIntros "_ H %tid".
      iApply bwpｰbind.
      iApply (bwpｰwand with "H").
      iSteps.
  Qed.
  Lemma wpｰbind' K `{!Context K} e tid E Φ :
    WP e ∷ tid @ E {{ v, WP K (of_val v) ∷ tid @ E {{ Φ }} }} ⊢
    WP K e ∷ tid @ E {{ Φ }}.
  Proof.
    apply: wpｰbind.
    destruct tid; done.
  Qed.

  #[global] Instance frameｰwp p e tid E R Φ1 Φ2 :
    (∀ v, Frame p R (Φ1 v) (Φ2 v)) →
    Frame
      p
      R
      (WP e ∷ tid @ E {{ Φ1 }})
      (WP e ∷ tid @ E {{ Φ2 }})
  | 2.
  Proof.
    rewrite /Frame wpｰframeｰl => HR.
    apply wpｰmono, HR.
  Qed.

  #[global] Instance is_except_0ｰwp e tid E Φ :
    IsExcept0 (WP e ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite /IsExcept0 -{2}fupdｰwp -except_0_fupd -fupd_intro //.
  Qed.

  #[global] Instance elim_modalｰbupdｰwp p e tid E P Φ :
    ElimModal
      True
      p
      false
      (|==> P)
      P
      (WP e ∷ tid @ E {{ Φ }})
      (WP e ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupdｰwp //.
  Qed.

  #[global] Instance elim_modalｰfupdｰwp p e tid E P Φ :
    ElimModal
      True
      p
      false
      (|={E}=> P)
      P
      (WP e ∷ tid @ E {{ Φ }})
      (WP e ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim fupd_frame_r bi.wand_elim_r fupdｰwp //.
  Qed.
  #[global] Instance elim_modalｰfupdｰwpｰwrong_mask p e tid E1 E2 P Φ :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iApply fupdｰwp; iMod (fupd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
      p
      false
      (|={E2}=> P)
      False
      (WP e ∷ tid @ E1 {{ Φ }})
      False
  | 100.
  Proof.
    intros [].
  Qed.

  #[global] Instance elim_modalｰfupdｰwpｰatomic p e tid E1 E2 P Φ :
    ElimModal
      (Atomic e)
      p
      false
      (|={E1,E2}=> P)
      P
      (WP e ∷ tid @ E1 {{ Φ }})
      (WP e ∷ tid @ E2 {{ v, |={E2,E1}=> Φ v }})%I
  | 100.
  Proof.
    intros He.
    rewrite bi.intuitionistically_if_elim fupd_frame_r bi.wand_elim_r wpｰatomic //.
  Qed.
  #[global] Instance elim_modalｰfupdｰwpｰatomicｰwrong_mask p e tid E1 E2 E2' P Φ :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iMod (fupd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
      p
      false
      (|={E2,E2'}=> P)
      False
      (WP e ∷ tid @ E1 {{ Φ }})
      False
  | 200.
  Proof.
    intros [].
  Qed.

  #[global] Instance add_modalｰfupdｰwp e tid E P Φ :
    AddModal
      (|={E}=> P)
      P
      (WP e ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite /AddModal fupd_frame_r bi.wand_elim_r fupdｰwp //.
  Qed.

  #[global] Instance elim_accｰwpｰatomic {X} e tid E1 E2 α β γ Φ :
    ElimAcc (X := X)
      (Atomic e)
      (fupd E1 E2)
      (fupd E2 E1)
      α
      β
      γ
      (WP e ∷ tid @ E1 {{ Φ }})
      (λ x, WP e ∷ tid @ E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I
  | 100.
  Proof.
    iIntros "%He Hinner >Hacc".
    iDestruct "Hacc" as "(%x & Hα & Hclose)".
    iApply (wpｰwand with "(Hinner Hα)"). iIntros "%v >(Hβ & HΦ)".
    iApply ("HΦ" with "(Hclose Hβ)").
  Qed.

  #[global] Instance elim_accｰwpｰnonatomic {X} e tid E α β γ Φ :
    ElimAcc (X := X)
      True
      (fupd E E)
      (fupd E E)
      α
      β
      γ
      (WP e ∷ tid @ E {{ Φ }})
      (λ x, WP e ∷ tid @ E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc".
    iDestruct "Hacc" as "(%x & Hα & Hclose)".
    iApply wpｰfupd.
    iApply (wpｰwand with "(Hinner Hα)"). iIntros "%v >(Hβ & HΦ)".
    iApply ("HΦ" with "(Hclose Hβ)").
  Qed.
End zoo۰G.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Implicit Type Φ : val → iProp Σ.

  Lemma wpｰpure_stepｰstrong ϕ n e1 e2 ns tid E Φ :
    PureExec ϕ n e1 e2 →
    ϕ →
    ⧖ ns -∗
    ▷^n (
      ⧖ (ns + n) -∗
      £ (later۰sum ns n) -∗
      WP e2 ∷ tid @ E {{ Φ }}
    ) -∗
    WP e1 ∷ tid @ E {{ Φ }}.
  Proof.
    wpｰunseal.
    - apply bwpｰpureｰstep.
    - iIntros "%Hexec %Hϕ H⧖ H %tid".
      iApply (bwpｰpureｰstep with "H⧖"); first done.
      iSteps.
  Qed.
  Lemma wpｰpure_step ϕ n e1 e2 tid E Φ :
    PureExec ϕ n e1 e2 →
    ϕ →
    ▷^n (
      £ (n * later_constant) -∗
      WP e2 ∷ tid @ E {{ Φ }}
    ) ⊢
    WP e1 ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros "%Hexec %Hϕ H".
    iMod steps۰lbｰ0 as "H⧖".
    iApply (wpｰpure_stepｰstrong with "H⧖"); first done.
    iSteps as "_ H£".
    iApply (lc_weaken with "H£").
    { apply later۰sumｰlb. }
  Qed.
End zoo۰G.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Lemma wpｰequalｰnobranch v1 v2 tid E Φ :
    ▷ (
      ∀ b,
      ⌜(if b then (≈) else (≉)) v1 v2⌝ -∗
      Φ #b
    ) ⊢
    WP v1 == v2 ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply bwpｰwpｰweak. iIntros.
    iApply bwpｰliftｰatomicｰbaseｰstepｰnofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp !>".
    iSplit. { iPureIntro. apply base_reducibleｰequal. }
    iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !> !>".
    invert_base_step; iSteps.
  Qed.
  Lemma wpｰequal v1 v2 tid E Φ :
    ▷ (
      ( ⌜v1 ≉ v2⌝ -∗
        Φ false%V
      ) ∧ (
        ⌜v1 ≈ v2⌝ -∗
        Φ true%V
      )
    ) ⊢
    WP v1 == v2 ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply wpｰequalｰnobranch. iIntros "!>" ([]).
    1: iDestruct "HΦ" as "(_ & HΦ)".
    2: iDestruct "HΦ" as "(HΦ & _)".
    all: iSteps.
  Qed.

  Lemma wpｰalloc (tag : Z) n tid E :
    (0 ≤ tag)%Z →
    (0 ≤ n)%Z →
    {{{
      True
    }}}
      Alloc #tag #n ∷ tid @ E
    {{{
      l
    , RET #l;
      l ↦ₕ Header ₊tag ₊n ∗
      meta_token l ⊤ ∗
      l ↦∗ replicate ₊n ()%V
    }}}.
  Proof.
    iIntros "%Htag %Hn %Φ _ HΦ".
    Z_to_nat tag. rewrite Nat2Z.id.
    iApply bwpｰwpｰweak. iIntros.
    iApply bwpｰliftｰatomicｰbaseｰstepｰnofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp !>".
    iSplit; first auto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step.
    select (state۰alloc_condition _ _ _) ltac:(fun H =>
      destruct H
    ).
    iMod (state_interpｰalloc _ _ (replicate ₊n ()%V) with "Hinterp") as "(Hinterp & Hheader & Hmeta & Hl)". all: simp_length. 1: naive_solver.
    iFrameSteps.
  Qed.

  Lemma wpｰblockｰmutable {es tag} vs tid E :
    0 < length es →
    to_vals es = Some vs →
    {{{
      True
    }}}
      Block Mutable tag es ∷ tid @ E
    {{{
      l
    , RET #l;
      l ↦ₕ Header tag (length es) ∗
      meta_token l ⊤ ∗
      l ↦∗ vs
    }}}.
  Proof.
    iIntros (Hlen <-%of_valsｰto_vals) "%Φ _ HΦ".
    iApply bwpｰwpｰweak. iIntros.
    iApply bwpｰliftｰatomicｰbaseｰstepｰnofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp !>".
    iSplit; first auto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step.
    select (state۰alloc_condition _ _ _) ltac:(fun H =>
      destruct H
    ).
    iMod (state_interpｰalloc with "Hinterp") as "(Hinterp & Hheader & Hmeta & Hl)". all: simp_length in *. 1: naive_solver.
    iFrameSteps.
  Qed.

  Lemma wpｰblockｰgenerative {es tag} vs tid E :
    to_vals es = Some vs →
    {{{
      True
    }}}
      Block ImmutableGenerativeStrong tag es ∷ tid @ E
    {{{
      bid
    , RET ValBlock (Generative (Some bid)) tag vs;
      True
    }}}.
  Proof.
    iIntros (<-%of_valsｰto_vals) "%Φ _ HΦ".
    iApply bwpｰwpｰweak. iIntros.
    iApply bwpｰliftｰatomicｰbaseｰstepｰnofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp !>".
    iSplit; first auto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step.
    iFrameSteps.
  Qed.

  Lemma wpｰmatch l hdr x_fb e_fb brs e tid E Φ :
    eval_match hdr.(header۰tag) hdr.(header۰size) (SubjectLoc l) x_fb e_fb brs = Some e →
    ▷ l ↦ₕ hdr -∗
    ▷ WP e ∷ tid @ E {{ Φ }} -∗
    WP Match #l x_fb e_fb brs ∷ tid @ E {{ Φ }}.
  Proof.
    wpｰunseal.
    - apply bwpｰmatch.
    - iIntros "%He >#Hl H %tid".
      iSpecialize ("H" $! tid).
      iApply (bwpｰmatch with "Hl H"); first done.
  Qed.
  Lemma wpｰmatchｰcontext K `{!Context K} l hdr x_fb e_fb brs e tid E Φ :
    eval_match hdr.(header۰tag) hdr.(header۰size) (SubjectLoc l) x_fb e_fb brs = Some e →
    ▷ l ↦ₕ hdr -∗
    ▷ WP K e ∷ tid @ E {{ Φ }} -∗
    WP K (Match #l x_fb e_fb brs) ∷ tid @ E {{ Φ }}.
  Proof.
    wpｰunseal.
    - apply: bwpｰmatchｰcontext.
    - iIntros "%He >#Hl H %tid".
      iSpecialize ("H" $! tid).
      iApply (bwpｰmatchｰcontext with "Hl H"); first done.
  Qed.

  Lemma wpｰtag l hdr tid E Φ :
    ▷ l ↦ₕ hdr -∗
    ▷ Φ #(encode_tag hdr.(header۰tag)) -∗
    WP GetTag #l ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros ">Hheader HΦ".
    iApply bwpｰwpｰweak. iIntros.
    iApply bwpｰliftｰatomicｰbaseｰstepｰnofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iDestruct (state_interpｰheaders۰atｰvalid with "Hinterp Hheader") as %Hheaders_lookup.
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e %σ2 %es -> %Hstep _ !>".
    invert_base_step.
    iFrameSteps.
  Qed.

  Lemma wpｰsize l hdr tid E Φ :
    ▷ l ↦ₕ hdr -∗
    ▷ Φ #hdr.(header۰size) -∗
    WP GetSize #l ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros ">Hheader HΦ".
    iApply bwpｰwpｰweak. iIntros.
    iApply bwpｰliftｰatomicｰbaseｰstepｰnofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iDestruct (state_interpｰheaders۰atｰvalid with "Hinterp Hheader") as %Hheaders_lookup.
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e %σ2 %es -> %Hstep _ !>".
    invert_base_step.
    iFrameSteps.
  Qed.

  Lemma wpｰload l fld dq v tid E :
    {{{
      ▷ (l +ₗ fld) ↦{dq} v
    }}}
      Load #l #fld ∷ tid @ E
    {{{
      RET v;
      (l +ₗ fld) ↦{dq} v
    }}}.
  Proof.
    iIntros "%Φ >Hl HΦ".
    iApply bwpｰwpｰweak. iIntros.
    iApply bwpｰliftｰatomicｰbaseｰstepｰnofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp !>".
    iDestruct (state_interpｰpointstoｰvalid with "Hinterp Hl") as %Hlookup.
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !> !>".
    invert_base_step.
    iFrameSteps.
  Qed.

  Lemma wpｰstore l fld w v tid E :
    {{{
      ▷ (l +ₗ fld) ↦ w
    }}}
      Store #l #fld v ∷ tid @ E
    {{{
      RET ();
      (l +ₗ fld) ↦ v
    }}}.
  Proof.
    iIntros "%Φ >Hl HΦ".
    iApply bwpｰwpｰweak. iIntros.
    iApply bwpｰliftｰatomicｰbaseｰstepｰnofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp !>".
    iDestruct (state_interpｰpointstoｰvalid with "Hinterp Hl") as %Hlookup.
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step.
    iMod (state_interpｰpointstoｰupdate with "Hinterp Hl") as "($ & Hl)".
    iSteps.
  Qed.

  Lemma wpｰxchg l fld w v tid E :
    {{{
      ▷ (l +ₗ fld) ↦ w
    }}}
      Xchg (#l, #fld)%V v ∷ tid @ E
    {{{
      RET w;
      (l +ₗ fld) ↦ v
    }}}.
  Proof.
    iIntros "%Φ >Hl HΦ".
    iApply bwpｰwpｰweak. iIntros.
    iApply bwpｰliftｰatomicｰbaseｰstepｰnofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp !>".
    iDestruct (state_interpｰpointstoｰvalid with "Hinterp Hl") as %Hlookup.
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step.
    iMod (state_interpｰpointstoｰupdate with "Hinterp Hl") as "($ & Hl)".
    iSteps.
  Qed.

  Lemma wpｰcasｰnobranch l fld dq v v1 v2 tid E Φ :
    ▷ (l +ₗ fld) ↦{dq} v -∗
    ▷ (
      ∀ b,
      ⌜(if b then (≈) else (≉)) v v1⌝ -∗
      (l +ₗ fld) ↦{dq} v -∗
        ⌜if b then dq = DfracOwn 1 else True⌝ ∗
        (l +ₗ fld) ↦{dq} v ∗
        ( (l +ₗ fld) ↦{dq} (if b then v2 else v) -∗
          Φ #b
        )
    ) -∗
    WP CAS (#l, #fld)%V v1 v2 ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros ">Hl HΦ".
    iApply bwpｰwpｰweak. iIntros.
    iApply bwpｰliftｰatomicｰbaseｰstepｰnofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp !>".
    iDestruct (state_interpｰpointstoｰvalid with "Hinterp Hl") as %Hlookup.
    iSplit. { iPureIntro. eapply base_reducibleｰcas. done. }
    iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step; first iSteps.
    iDestruct ("HΦ" $! true with "[//] Hl") as "(-> & Hl & HΦ)".
    iMod (state_interpｰpointstoｰupdate with "Hinterp Hl") as "($ & Hl)".
    iSteps.
  Qed.
  Lemma wpｰcasｰnobranch' l fld v v1 v2 tid E Φ :
    ▷ (l +ₗ fld) ↦ v -∗
    ▷ (
      ∀ b,
      ⌜(if b then (≈) else (≉)) v v1⌝ -∗
      (l +ₗ fld) ↦ (if b then v2 else v) -∗
      Φ #b
    ) -∗
    WP CAS (#l, #fld)%V v1 v2 ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros "Hl HΦ".
    iApply (wpｰcasｰnobranch with "Hl"). iIntros "!> %b".
    destruct b; iSteps.
  Qed.
  Lemma wpｰcas l fld dq v v1 v2 tid E Φ :
    ▷ (l +ₗ fld) ↦{dq} v -∗
    ▷ (
      ( ⌜v ≉ v1⌝ -∗
        (l +ₗ fld) ↦{dq} v -∗
        Φ false%V
      ) ∧ (
        ⌜v ≈ v1⌝ -∗
        (l +ₗ fld) ↦{dq} v -∗
          ⌜dq = DfracOwn 1⌝ ∗
          (l +ₗ fld) ↦{dq} v ∗
          ( (l +ₗ fld) ↦ v2 -∗
            Φ true%V
          )
      )
    ) -∗
    WP CAS (#l, #fld)%V v1 v2 ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros "Hl HΦ".
    iApply (wpｰcasｰnobranch with "Hl"). iIntros "!>" ([] ?) "Hl".
    1: iDestruct ("HΦ" with "[//] Hl") as "(-> & Hl & HΦ)".
    2: iDestruct "HΦ" as "(HΦ & _)".
    all: iSteps.
  Qed.
  Lemma wpｰcas' l fld v v1 v2 tid E Φ :
    ▷ (l +ₗ fld) ↦ v -∗
    ▷ (
      ( ⌜v ≉ v1⌝ -∗
        (l +ₗ fld) ↦ v -∗
        Φ false%V
      ) ∧ (
        ⌜v ≈ v1⌝ -∗
        (l +ₗ fld) ↦ v2 -∗
        Φ true%V
      )
    ) -∗
    WP CAS (#l, #fld)%V v1 v2 ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros "Hl HΦ".
    iApply (wpｰcas with "Hl").
    iSplit.
    1: iDestruct "HΦ" as "(HΦ & _)".
    2: iDestruct "HΦ" as "(_ & HΦ)".
    all: iFrameSteps.
  Qed.

  Lemma wpｰfaa l fld (i1 i2 : Z) tid E :
    {{{
      ▷ (l +ₗ fld) ↦ #i1
    }}}
      FAA (#l, #fld)%V #i2 ∷ tid @ E
    {{{
      RET #i1;
      (l +ₗ fld) ↦ #(i1 + i2)
    }}}.
  Proof.
    iIntros "%Φ >Hl HΦ".
    iApply bwpｰwpｰweak. iIntros.
    iApply bwpｰliftｰatomicｰbaseｰstepｰnofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp !>".
    iDestruct (state_interpｰpointstoｰvalid with "Hinterp Hl") as %Hlookup.
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step.
    iMod (state_interpｰpointstoｰupdate with "Hinterp Hl") as "($ & Hl)";
    iFrameSteps.
  Qed.

  Lemma wpｰfork e tid E Φ :
    ▷ (
      ∀ tid v,
      tid ↦ₗ v -∗
      WP e ∶ tid {{ λ _, True }}
    ) -∗
    ▷ Φ ()%V -∗
    WP Fork e ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros "H HΦ".
    iApply bwpｰwpｰweak. iIntros.
    iApply bwpｰliftｰatomicｰbaseｰstep; first done. iIntros "%ns %nt %σ1 %κs Hinterp !>".
    iSplit; first auto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step.
    iMod (state_interpｰfork with "Hinterp") as "(Hinterp & Htid)".
    iFrameStep.
    rewrite right_id Nat.add_0_r.
    iApply (wpｰbwp with "(H Htid)").
  Qed.

  Lemma wpｰget_local tid dq v E :
    {{{
      ▷ tid ↦ₗ{dq} v
    }}}
      GetLocal ∶ tid @ E
    {{{
      RET v;
      tid ↦ₗ{dq} v
    }}}.
  Proof.
    iIntros "%Φ >Htid HΦ".
    iApply bwpｰwp.
    iApply bwpｰliftｰatomicｰbaseｰstepｰnofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp !>".
    iDestruct (state_interpｰlocal_pointstoｰvalid with "Hinterp Htid") as %Hlookup.
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step.
    iFrameSteps.
  Qed.

  Lemma wpｰset_local tid w v E :
    {{{
      ▷ tid ↦ₗ w
    }}}
      SetLocal v ∶ tid @ E
    {{{
      RET ();
      tid ↦ₗ v
    }}}.
  Proof.
    iIntros "%Φ >Htid HΦ".
    iApply bwpｰwp.
    iApply bwpｰliftｰatomicｰbaseｰstepｰnofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp !>".
    iDestruct (state_interpｰlocal_pointstoｰvalid with "Hinterp Htid") as %Hlookup.
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step.
    iMod (state_interpｰlocal_pointstoｰupdate with "Hinterp Htid") as "($ & Htid)".
    iSteps.
  Qed.

  Lemma wpｰproph tid E :
    {{{
      True
    }}}
      Proph ∷ tid @ E
    {{{
      prophs pid
    , RET #pid;
      prophet۰model pid prophs
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    iApply bwpｰwpｰweak. iIntros.
    iApply bwpｰliftｰatomicｰbaseｰstepｰnofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp !>".
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step.
    iMod (state_interpｰprophetｰnew with "Hinterp") as "(%prophs & Hinterp & Hpid)"; first done.
    iFrameSteps.
  Qed.

  Lemma wpｰresolve e pid v prophs tid E Φ :
    Atomic e →
    to_val e = None →
    prophet۰model pid prophs -∗
    WP e ∷ tid @ E {{ res,
      ∀ prophs',
      ⌜prophs = (res, v) :: prophs'⌝ -∗
      prophet۰model pid prophs' -∗
      Φ res
    }} -∗
    WP Resolve e #pid v ∷ tid @ E {{ Φ }}.
  Proof.
    wpｰunseal.
    - apply bwpｰresolve.
    - iIntros "%Hatomic %He Hpid H %tid".
      iSpecialize ("H" $! tid).
      iApply (bwpｰresolve with "Hpid H"); first done.
  Qed.
End zoo۰G.
