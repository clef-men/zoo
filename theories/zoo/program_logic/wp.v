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
#[local] Lemma wp𑁒unseal `{zoo۰G : !ZooG Σ} :
  wp = wp۰def.
Proof.
  rewrite -wp۰aux.(seal_eq) //.
Qed.

#[local] Ltac wp𑁒unseal :=
  rewrite wp𑁒unseal /wp۰def;
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

Implicit Types b : bool.
Implicit Types l : location.
Implicit Types pid : prophet_id.
Implicit Types e : expr.
Implicit Types es : list expr.
Implicit Types v w : val.
Implicit Types σ : state.
Implicit Types κ κs : list observation.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Implicit Types P R : iProp Σ.
  Implicit Types Φ : val → iProp Σ.

  #[global] Instance wp𑁒ne e tid E n :
    Proper (pointwise_relation _ (≡{n}≡) ==> (≡{n}≡)) (wp e tid E).
  Proof.
    rewrite wp𑁒unseal. solve_proper.
  Qed.
  #[global] Instance wp𑁒proper e tid E :
    Proper (pointwise_relation _ (≡) ==> (≡)) (wp e tid E).
  Proof.
    rewrite wp𑁒unseal. solve_proper.
  Qed.
  #[global] Instance wp𑁒contractive e tid E n :
    TCEq (to_val e) None →
    Proper (pointwise_relation _ (dist_later n) ==> (≡{n}≡)) (wp e tid E).
  Proof.
    wp𑁒unseal.
    - apply bwp𑁒contractive.
    - intros He Φ1 Φ2 HΦ.
      f_equiv => tid.
      apply bwp𑁒contractive; done.
  Qed.

  Lemma wp𑁒thread_id_mono e tid E Φ :
    WP e @ E {{ Φ }} ⊢
    WP e ∷ tid @ E {{ Φ }}.
  Proof.
    wp𑁒unseal.
    all: iSteps.
  Qed.

  Lemma wp𑁒bwp e tid E Φ :
    WP e ∶ tid @ E {{ Φ }} ⊢
    BWP e ∶ tid @ E {{ Φ }}.
  Proof.
    rewrite wp𑁒unseal. iSteps.
  Qed.

  Lemma bwp𑁒wp e tid E Φ :
    BWP e ∶ tid @ E {{ Φ }} ⊢
    WP e ∶ tid @ E {{ Φ }}.
  Proof.
    rewrite wp𑁒unseal //.
  Qed.
  Lemma bwp𑁒wp𑁒weak e tid E Φ :
    (∀ tid, BWP e ∶ tid @ E {{ Φ }}) ⊢
    WP e ∷ tid @ E {{ Φ }}.
  Proof.
    rewrite -wp𑁒thread_id_mono wp𑁒unseal //.
  Qed.

  Lemma wp𑁒state_interp e tid E Φ :
    ( ∀ ns nt σ κs,
      state_interp ns nt σ κs ={E}=∗
        state_interp ns nt σ κs ∗
        WP e ∷ tid @ E {{ Φ }}
    ) ⊢
    WP e ∷ tid @ E {{ Φ }}.
  Proof.
    wp𑁒unseal.
    - apply bwp𑁒state_interp.
    - iIntros "H %tid".
      iApply bwp𑁒state_interp. iIntros "%ns %nt %σ %κs Hinterp".
      iMod ("H" with "Hinterp") as "($ & H)".
      iSteps.
  Qed.

  Lemma wp𑁒value𑁒fupd' v tid E Φ :
    (|={E}=> Φ v) ⊢
    WP of_val v ∷ tid @ E {{ Φ }}.
  Proof.
    wp𑁒unseal.
    - apply bwp𑁒value𑁒fupd'.
    - iIntros "H %tid".
      iApply (bwp𑁒value𑁒fupd' with "H").
  Qed.
  Lemma wp𑁒value𑁒fupd e v tid E Φ :
    AsVal e v →
    (|={E}=> Φ v) ⊢
    WP e ∷ tid @ E {{ Φ }}.
  Proof.
    rewrite wp𑁒value𑁒fupd' => <- //.
  Qed.
  Lemma wp𑁒value' v tid E Φ :
    Φ v ⊢
    WP of_val v ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply (wp𑁒value𑁒fupd' with "HΦ").
  Qed.
  Lemma wp𑁒value e v tid E Φ :
    AsVal e v →
    Φ v ⊢
    WP e ∷ tid @ E {{ Φ }}.
  Proof.
    rewrite wp𑁒value' => <- //.
  Qed.

  Lemma wp𑁒value𑁒mono v tid E Φ1 Φ2 :
    WP of_val v ∷ tid @ E {{ Φ1 }} -∗
    (Φ1 v ={E}=∗ Φ2 v) -∗
    WP of_val v ∷ tid @ E {{ Φ2 }}.
  Proof.
    wp𑁒unseal.
    - apply bwp𑁒value𑁒mono.
    - iIntros "H HΦ %tid".
      iApply (bwp𑁒value𑁒mono with "H HΦ").
  Qed.

  Lemma wp𑁒strong𑁒mono e tid E1 Φ1 E2 Φ2 :
    E1 ⊆ E2 →
    WP e ∷ tid @ E1 {{ Φ1 }} -∗
    (∀ v, Φ1 v ={E2}=∗ Φ2 v) -∗
    WP e ∷ tid @ E2 {{ Φ2 }}.
  Proof.
    wp𑁒unseal.
    - apply bwp𑁒strong𑁒mono.
    - iIntros "%HE H HΦ %tid".
      iApply (bwp𑁒strong𑁒mono with "H HΦ"); first done.
  Qed.
  Lemma wp𑁒mono e tid E Φ1 Φ2 :
    (∀ v, Φ1 v ⊢ Φ2 v) →
    WP e ∷ tid @ E {{ Φ1 }} ⊢
    WP e ∷ tid @ E {{ Φ2 }}.
  Proof.
    iIntros "%HΦ H".
    iApply (wp𑁒strong𑁒mono with "H"); first done. iIntros "%v HΦ".
    iApply (HΦ with "HΦ").
  Qed.
  #[global] Instance wp𑁒mono' e tid E :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp e tid E).
  Proof.
    intros Φ1 Φ2 HΦ.
    apply wp𑁒mono. done.
  Qed.
  #[global] Instance wp𑁒flip𑁒mono' e tid E :
    Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp e tid E).
  Proof.
    solve_proper.
  Qed.

  Lemma fupd𑁒wp e tid E Φ :
    (|={E}=> WP e ∷ tid @ E {{ Φ }}) ⊢
    WP e ∷ tid @ E {{ Φ }}.
  Proof.
    wp𑁒unseal.
    - apply fupd𑁒bwp.
    - iIntros "H %tid".
      iSpecialize ("H" $! tid).
      iApply (fupd𑁒bwp with "H").
  Qed.
  Lemma wp𑁒fupd e tid E Φ :
    WP e ∷ tid @ E {{ v, |={E}=> Φ v }} ⊢
    WP e ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (wp𑁒strong𑁒mono with "H"); first done.
    iSteps.
  Qed.

  Lemma wp𑁒frame𑁒l e tid E Φ R :
    R ∗ WP e ∷ tid @ E {{ Φ }} ⊢
    WP e ∷ tid @ E {{ v, R ∗ Φ v }}.
  Proof.
    iIntros "(HR & H)".
    iApply (wp𑁒strong𑁒mono with "H"); first done.
    iSteps.
  Qed.
  Lemma wp𑁒frame𑁒r e tid E Φ R :
    WP e ∷ tid @ E {{ Φ }} ∗ R ⊢
    WP e ∷ tid @ E {{ v, Φ v ∗ R }}.
  Proof.
    iIntros "(H & HR)".
    iApply (wp𑁒strong𑁒mono with "H"); first done.
    iSteps.
  Qed.

  Lemma wp𑁒wand {e tid E} Φ1 Φ2 :
    WP e ∷ tid @ E {{ Φ1 }} -∗
    (∀ v, Φ1 v -∗ Φ2 v) -∗
    WP e ∷ tid @ E {{ Φ2 }}.
  Proof.
    iIntros "H HΦ".
    iApply (wp𑁒strong𑁒mono with "H"); first done.
    iSteps.
  Qed.
  Lemma wp𑁒frame𑁒wand e tid E Φ R :
    R -∗
    WP e ∷ tid @ E {{ v, R -∗ Φ v }} -∗
    WP e ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros "HR H".
    iApply (wp𑁒wand with "H").
    iSteps.
  Qed.

  Lemma wp𑁒atomic e `{!Atomic e} tid E1 E2 Φ :
    (|={E1,E2}=> WP e ∷ tid @ E2 {{ v, |={E2,E1}=> Φ v }}) ⊢
    WP e ∷ tid @ E1 {{ Φ }}.
  Proof.
    wp𑁒unseal.
    - apply bwp𑁒atomic; first done.
    - iIntros "H %tid".
      iSpecialize ("H" $! tid).
      iApply (bwp𑁒atomic with "H").
  Qed.

  Lemma wp𑁒bind K `{!Context K} e tid1 tid2 E Φ :
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
    wp𑁒unseal; destruct tid1 as [tid1 |].
    - intros ->.
      apply bwp𑁒bind; first done.
    - done.
    - iIntros "_ H".
      iApply (bwp𑁒bind with "H").
    - iIntros "_ H %tid".
      iApply bwp𑁒bind.
      iApply (bwp𑁒wand with "H").
      iSteps.
  Qed.
  Lemma wp𑁒bind' K `{!Context K} e tid E Φ :
    WP e ∷ tid @ E {{ v, WP K (of_val v) ∷ tid @ E {{ Φ }} }} ⊢
    WP K e ∷ tid @ E {{ Φ }}.
  Proof.
    apply: wp𑁒bind.
    destruct tid; done.
  Qed.

  #[global] Instance frame𑁒wp p e tid E R Φ1 Φ2 :
    (∀ v, Frame p R (Φ1 v) (Φ2 v)) →
    Frame
      p
      R
      (WP e ∷ tid @ E {{ Φ1 }})
      (WP e ∷ tid @ E {{ Φ2 }})
  | 2.
  Proof.
    rewrite /Frame wp𑁒frame𑁒l => HR.
    apply wp𑁒mono, HR.
  Qed.

  #[global] Instance is_except_0𑁒wp e tid E Φ :
    IsExcept0 (WP e ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite /IsExcept0 -{2}fupd𑁒wp -except_0_fupd -fupd_intro //.
  Qed.

  #[global] Instance elim_modal𑁒bupd𑁒wp p e tid E P Φ :
    ElimModal
      True
      p
      false
      (|==> P)
      P
      (WP e ∷ tid @ E {{ Φ }})
      (WP e ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd𑁒wp //.
  Qed.

  #[global] Instance elim_modal𑁒fupd𑁒wp p e tid E P Φ :
    ElimModal
      True
      p
      false
      (|={E}=> P)
      P
      (WP e ∷ tid @ E {{ Φ }})
      (WP e ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim fupd_frame_r bi.wand_elim_r fupd𑁒wp //.
  Qed.
  #[global] Instance elim_modal𑁒fupd𑁒wp𑁒wrong_mask p e tid E1 E2 P Φ :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iApply fupd𑁒wp; iMod (fupd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
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

  #[global] Instance elim_modal𑁒fupd𑁒wp𑁒atomic p e tid E1 E2 P Φ :
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
    rewrite bi.intuitionistically_if_elim fupd_frame_r bi.wand_elim_r wp𑁒atomic //.
  Qed.
  #[global] Instance elim_modal𑁒fupd𑁒wp𑁒atomic𑁒wrong_mask p e tid E1 E2 E2' P Φ :
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

  #[global] Instance add_modal𑁒fupd𑁒wp e tid E P Φ :
    AddModal
      (|={E}=> P)
      P
      (WP e ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd𑁒wp //.
  Qed.

  #[global] Instance elim_acc𑁒wp𑁒atomic {X} e tid E1 E2 α β γ Φ :
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
    iApply (wp𑁒wand with "(Hinner Hα)"). iIntros "%v >(Hβ & HΦ)".
    iApply ("HΦ" with "(Hclose Hβ)").
  Qed.

  #[global] Instance elim_acc𑁒wp𑁒nonatomic {X} e tid E α β γ Φ :
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
    iApply wp𑁒fupd.
    iApply (wp𑁒wand with "(Hinner Hα)"). iIntros "%v >(Hβ & HΦ)".
    iApply ("HΦ" with "(Hclose Hβ)").
  Qed.
End zoo۰G.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Implicit Types Φ : val → iProp Σ.

  Lemma wp𑁒pure_step𑁒strong ϕ n e1 e2 ns tid E Φ :
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
    wp𑁒unseal.
    - apply bwp𑁒pure𑁒step.
    - iIntros "%Hexec %Hϕ H⧖ H %tid".
      iApply (bwp𑁒pure𑁒step with "H⧖"); first done.
      iSteps.
  Qed.
  Lemma wp𑁒pure_step ϕ n e1 e2 tid E Φ :
    PureExec ϕ n e1 e2 →
    ϕ →
    ▷^n (
      £ (n * later_constant) -∗
      WP e2 ∷ tid @ E {{ Φ }}
    ) ⊢
    WP e1 ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros "%Hexec %Hϕ H".
    iMod steps۰lb𑁒0 as "H⧖".
    iApply (wp𑁒pure_step𑁒strong with "H⧖"); first done.
    iSteps as "_ H£".
    iApply (lc_weaken with "H£").
    { apply later۰sum𑁒lb. }
  Qed.
End zoo۰G.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Lemma wp𑁒equal𑁒nobranch v1 v2 tid E Φ :
    ▷ (
      ∀ b,
      ⌜(if b then (≈) else (≉)) v1 v2⌝ -∗
      Φ #b
    ) ⊢
    WP v1 == v2 ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply bwp𑁒wp𑁒weak. iIntros.
    iApply bwp𑁒lift𑁒atomic𑁒base𑁒step𑁒nofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp !>".
    iSplit. { iPureIntro. apply base_reducible𑁒equal. }
    iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !> !>".
    invert_base_step; iSteps.
  Qed.
  Lemma wp𑁒equal v1 v2 tid E Φ :
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
    iApply wp𑁒equal𑁒nobranch. iIntros "!>" ([]).
    1: iDestruct "HΦ" as "(_ & HΦ)".
    2: iDestruct "HΦ" as "(HΦ & _)".
    all: iSteps.
  Qed.

  Lemma wp𑁒alloc (tag : Z) n tid E :
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
    iApply bwp𑁒wp𑁒weak. iIntros.
    iApply bwp𑁒lift𑁒atomic𑁒base𑁒step𑁒nofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp !>".
    iSplit; first auto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step.
    select (state۰alloc_condition _ _ _) ltac:(fun H =>
      destruct H
    ).
    iMod (state_interp𑁒alloc _ _ (replicate ₊n ()%V) with "Hinterp") as "(Hinterp & Hheader & Hmeta & Hl)". all: simpl_length. 1: naive_solver.
    iFrameSteps.
  Qed.

  Lemma wp𑁒block𑁒mutable {es tag} vs tid E :
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
    iIntros (Hlen <-%of_vals𑁒to_vals) "%Φ _ HΦ".
    iApply bwp𑁒wp𑁒weak. iIntros.
    iApply bwp𑁒lift𑁒atomic𑁒base𑁒step𑁒nofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp !>".
    iSplit; first auto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step.
    select (state۰alloc_condition _ _ _) ltac:(fun H =>
      destruct H
    ).
    iMod (state_interp𑁒alloc with "Hinterp") as "(Hinterp & Hheader & Hmeta & Hl)". all: simpl_length in *. 1: naive_solver.
    iFrameSteps.
  Qed.

  Lemma wp𑁒block𑁒generative {es tag} vs tid E :
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
    iIntros (<-%of_vals𑁒to_vals) "%Φ _ HΦ".
    iApply bwp𑁒wp𑁒weak. iIntros.
    iApply bwp𑁒lift𑁒atomic𑁒base𑁒step𑁒nofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp !>".
    iSplit; first auto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step.
    iFrameSteps.
  Qed.

  Lemma wp𑁒match l hdr x_fb e_fb brs e tid E Φ :
    eval_match hdr.(header۰tag) hdr.(header۰size) (SubjectLoc l) x_fb e_fb brs = Some e →
    ▷ l ↦ₕ hdr -∗
    ▷ WP e ∷ tid @ E {{ Φ }} -∗
    WP Match #l x_fb e_fb brs ∷ tid @ E {{ Φ }}.
  Proof.
    wp𑁒unseal.
    - apply bwp𑁒match.
    - iIntros "%He >#Hl H %tid".
      iSpecialize ("H" $! tid).
      iApply (bwp𑁒match with "Hl H"); first done.
  Qed.
  Lemma wp𑁒match𑁒context K `{!Context K} l hdr x_fb e_fb brs e tid E Φ :
    eval_match hdr.(header۰tag) hdr.(header۰size) (SubjectLoc l) x_fb e_fb brs = Some e →
    ▷ l ↦ₕ hdr -∗
    ▷ WP K e ∷ tid @ E {{ Φ }} -∗
    WP K (Match #l x_fb e_fb brs) ∷ tid @ E {{ Φ }}.
  Proof.
    wp𑁒unseal.
    - apply: bwp𑁒match𑁒context.
    - iIntros "%He >#Hl H %tid".
      iSpecialize ("H" $! tid).
      iApply (bwp𑁒match𑁒context with "Hl H"); first done.
  Qed.

  Lemma wp𑁒tag l hdr tid E Φ :
    ▷ l ↦ₕ hdr -∗
    ▷ Φ #(encode_tag hdr.(header۰tag)) -∗
    WP GetTag #l ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros ">Hheader HΦ".
    iApply bwp𑁒wp𑁒weak. iIntros.
    iApply bwp𑁒lift𑁒atomic𑁒base𑁒step𑁒nofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iDestruct (state_interp𑁒headers۰at𑁒valid with "Hinterp Hheader") as %Hheaders_lookup.
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e %σ2 %es -> %Hstep _ !>".
    invert_base_step.
    iFrameSteps.
  Qed.

  Lemma wp𑁒size l hdr tid E Φ :
    ▷ l ↦ₕ hdr -∗
    ▷ Φ #hdr.(header۰size) -∗
    WP GetSize #l ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros ">Hheader HΦ".
    iApply bwp𑁒wp𑁒weak. iIntros.
    iApply bwp𑁒lift𑁒atomic𑁒base𑁒step𑁒nofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iDestruct (state_interp𑁒headers۰at𑁒valid with "Hinterp Hheader") as %Hheaders_lookup.
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e %σ2 %es -> %Hstep _ !>".
    invert_base_step.
    iFrameSteps.
  Qed.

  Lemma wp𑁒load l fld dq v tid E :
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
    iApply bwp𑁒wp𑁒weak. iIntros.
    iApply bwp𑁒lift𑁒atomic𑁒base𑁒step𑁒nofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp !>".
    iDestruct (state_interp𑁒pointsto𑁒valid with "Hinterp Hl") as %Hlookup.
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !> !>".
    invert_base_step.
    iFrameSteps.
  Qed.

  Lemma wp𑁒store l fld w v tid E :
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
    iApply bwp𑁒wp𑁒weak. iIntros.
    iApply bwp𑁒lift𑁒atomic𑁒base𑁒step𑁒nofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp !>".
    iDestruct (state_interp𑁒pointsto𑁒valid with "Hinterp Hl") as %Hlookup.
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step.
    iMod (state_interp𑁒pointsto𑁒update with "Hinterp Hl") as "($ & Hl)".
    iSteps.
  Qed.

  Lemma wp𑁒xchg l fld w v tid E :
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
    iApply bwp𑁒wp𑁒weak. iIntros.
    iApply bwp𑁒lift𑁒atomic𑁒base𑁒step𑁒nofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp !>".
    iDestruct (state_interp𑁒pointsto𑁒valid with "Hinterp Hl") as %Hlookup.
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step.
    iMod (state_interp𑁒pointsto𑁒update with "Hinterp Hl") as "($ & Hl)".
    iSteps.
  Qed.

  Lemma wp𑁒cas𑁒nobranch l fld dq v v1 v2 tid E Φ :
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
    iApply bwp𑁒wp𑁒weak. iIntros.
    iApply bwp𑁒lift𑁒atomic𑁒base𑁒step𑁒nofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp !>".
    iDestruct (state_interp𑁒pointsto𑁒valid with "Hinterp Hl") as %Hlookup.
    iSplit. { iPureIntro. eapply base_reducible𑁒cas. done. }
    iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step; first iSteps.
    iDestruct ("HΦ" $! true with "[//] Hl") as "(-> & Hl & HΦ)".
    iMod (state_interp𑁒pointsto𑁒update with "Hinterp Hl") as "($ & Hl)".
    iSteps.
  Qed.
  Lemma wp𑁒cas𑁒nobranch' l fld v v1 v2 tid E Φ :
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
    iApply (wp𑁒cas𑁒nobranch with "Hl"). iIntros "!> %b".
    destruct b; iSteps.
  Qed.
  Lemma wp𑁒cas l fld dq v v1 v2 tid E Φ :
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
    iApply (wp𑁒cas𑁒nobranch with "Hl"). iIntros "!>" ([] ?) "Hl".
    1: iDestruct ("HΦ" with "[//] Hl") as "(-> & Hl & HΦ)".
    2: iDestruct "HΦ" as "(HΦ & _)".
    all: iSteps.
  Qed.
  Lemma wp𑁒cas' l fld v v1 v2 tid E Φ :
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
    iApply (wp𑁒cas with "Hl").
    iSplit.
    1: iDestruct "HΦ" as "(HΦ & _)".
    2: iDestruct "HΦ" as "(_ & HΦ)".
    all: iFrameSteps.
  Qed.

  Lemma wp𑁒faa l fld (i1 i2 : Z) tid E :
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
    iApply bwp𑁒wp𑁒weak. iIntros.
    iApply bwp𑁒lift𑁒atomic𑁒base𑁒step𑁒nofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp !>".
    iDestruct (state_interp𑁒pointsto𑁒valid with "Hinterp Hl") as %Hlookup.
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step.
    iMod (state_interp𑁒pointsto𑁒update with "Hinterp Hl") as "($ & Hl)";
    iFrameSteps.
  Qed.

  Lemma wp𑁒fork e tid E Φ :
    ▷ (
      ∀ tid v,
      tid ↦ₗ v -∗
      WP e ∶ tid {{ λ _, True }}
    ) -∗
    ▷ Φ ()%V -∗
    WP Fork e ∷ tid @ E {{ Φ }}.
  Proof.
    iIntros "H HΦ".
    iApply bwp𑁒wp𑁒weak. iIntros.
    iApply bwp𑁒lift𑁒atomic𑁒base𑁒step; first done. iIntros "%ns %nt %σ1 %κs Hinterp !>".
    iSplit; first auto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step.
    iMod (state_interp𑁒fork with "Hinterp") as "(Hinterp & Htid)".
    iFrameStep.
    rewrite right_id Nat.add_0_r.
    iApply (wp𑁒bwp with "(H Htid)").
  Qed.

  Lemma wp𑁒get_local tid dq v E :
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
    iApply bwp𑁒wp.
    iApply bwp𑁒lift𑁒atomic𑁒base𑁒step𑁒nofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp !>".
    iDestruct (state_interp𑁒local_pointsto𑁒valid with "Hinterp Htid") as %Hlookup.
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step.
    iFrameSteps.
  Qed.

  Lemma wp𑁒set_local tid w v E :
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
    iApply bwp𑁒wp.
    iApply bwp𑁒lift𑁒atomic𑁒base𑁒step𑁒nofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp !>".
    iDestruct (state_interp𑁒local_pointsto𑁒valid with "Hinterp Htid") as %Hlookup.
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step.
    iMod (state_interp𑁒local_pointsto𑁒update with "Hinterp Htid") as "($ & Htid)".
    iSteps.
  Qed.

  Lemma wp𑁒proph tid E :
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
    iApply bwp𑁒wp𑁒weak. iIntros.
    iApply bwp𑁒lift𑁒atomic𑁒base𑁒step𑁒nofork; first done. iIntros "%ns %nt %σ1 %κs Hinterp !>".
    iSplit; first eauto with zoo. iIntros "%κ %κs' %e2 %σ2 %es -> %Hstep _ !> !>".
    invert_base_step.
    iMod (state_interp𑁒prophet𑁒new with "Hinterp") as "(%prophs & Hinterp & Hpid)"; first done.
    iFrameSteps.
  Qed.

  Lemma wp𑁒resolve e pid v prophs tid E Φ :
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
    wp𑁒unseal.
    - apply bwp𑁒resolve.
    - iIntros "%Hatomic %He Hpid H %tid".
      iSpecialize ("H" $! tid).
      iApply (bwp𑁒resolve with "Hpid H"); first done.
  Qed.
End zoo۰G.
