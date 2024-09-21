From iris.proofmode Require Export
  proofmode.
From iris.proofmode Require Import
  coq_tactics
  reduction
  spec_patterns.

From zoo Require Import
  prelude.
From zoo.iris Require Import
  diaframe.
From zoo.iris.program_logic Require Export
  atomic.
From zoo.language Require Export
  tactics
  wp.
From zoo.language Require Import
  notations.
From zoo Require Import
  options.

Implicit Types l : location.
Implicit Types lit : literal.
Implicit Types e : expr.
Implicit Types v : val.
Implicit Types K : ectx.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Implicit Types Φ : val → iProp Σ.

  Lemma tac_wp_expr_eval Δ e e' E Φ :
    (∀ (e'' := e'), e = e'') →
    envs_entails Δ (WP e' @ E {{ Φ }}) →
    envs_entails Δ (WP e @ E {{ Φ }}).
  Proof.
    intros ->. done.
  Qed.

  Lemma tac_wp_pure Δ Δ' K e1 e2 ϕ n E Φ :
    PureExec ϕ n e1 e2 →
    ϕ →
    MaybeIntoLaterNEnvs n Δ Δ' →
    envs_entails Δ' (WP (fill K e2) @ E {{ Φ }}) →
    envs_entails Δ (WP (fill K e1) @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hexec Hϕ HΔ HΔ'.
    pose proof @pure_exec_fill. rewrite -wp_lifting.wp_pure_step_later //.
    rewrite into_laterN_env_sound HΔ'.
    iSteps.
  Qed.
  Lemma tac_wp_pure_credit Δ Δ' id K e1 e2 ϕ E Φ :
    PureExec ϕ 1 e1 e2 →
    ϕ →
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    match
      envs_app false (Esnoc Enil
        id (£ 1))
        Δ'
    with
    | Some Δ'' =>
        envs_entails Δ'' (WP fill K e2 @ E {{ Φ }})
    | None =>
        False
    end →
    envs_entails Δ (WP (fill K e1) @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hexec Hϕ HΔ HΔ''.
    destruct (envs_app _ _ _) as [Δ'' |] eqn:HΔ'; last done.
    pose proof @pure_exec_fill. rewrite -wp_lifting.wp_pure_step_later //=.
    rewrite into_laterN_env_sound envs_app_sound //= HΔ''.
    iSteps.
  Qed.

  Lemma tac_wp_value_nofupd Δ v E Φ :
    envs_entails Δ (Φ v) →
    envs_entails Δ (WP (Val v) @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => ->.
    apply: wp_value.
  Qed.
  Lemma tac_wp_value Δ v E Φ :
    envs_entails Δ (|={E}=> Φ v) →
    envs_entails Δ (WP (Val v) @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => ->.
    rewrite wp_value_fupd //.
  Qed.

  Lemma tac_wp_bind Δ K e (f : expr → expr) E Φ :
    f = (λ e, fill K e) →
    envs_entails Δ (WP e @ E {{ v, WP f (Val v) @ E {{ Φ }} }})%I →
    envs_entails Δ (WP fill K e @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => -> ->.
    apply: wp_bind.
  Qed.

  Lemma tac_wp_equal Δ Δ' K v1 v2 E Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    ValPhysical v1 →
    ValPhysical v2 →
    ( val_neq v1 v2 →
      envs_entails Δ' (WP fill K #false @ E {{ Φ }})
    ) →
    ( val_eq v1 v2 →
      envs_entails Δ' (WP fill K #true @ E {{ Φ }})
    ) →
    envs_entails Δ (WP fill K (v1 = v2) @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => HΔ Hv1 Hv2 Hfail Hsuc.
    rewrite into_laterN_env_sound -wp_bind -wp_equal //.
    apply bi.later_mono, bi.and_intro.
    all: repeat (rewrite bi.pure_wand_forall; apply bi.forall_intro => ?).
    all: naive_solver.
  Qed.

  Lemma tac_wp_alloc Δ Δ' id1 id2 id3 K tag n E Φ :
    (0 ≤ tag)%Z →
    (0 ≤ n)%Z →
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    ( ∀ l,
      match
        envs_app false (Esnoc (Esnoc (Esnoc Enil
          id1 (l ↦ₕ Header (Z.to_nat tag) (Z.to_nat n)))
          id2 (meta_token l ⊤))
          id3 (l ↦∗ replicate (Z.to_nat n) ()%V))
          Δ'
      with
      | Some Δ'' =>
          envs_entails Δ'' (WP fill K #l @ E {{ Φ }})
      | None =>
          False
      end
    ) →
    envs_entails Δ (WP fill K (Alloc #tag #n) @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Htag Hn HΔ HΔ''.
    rewrite into_laterN_env_sound -wp_bind.
    iIntros "HΔ'".
    iApply (wp_alloc with "[//]"); [done.. |]. iIntros "!> %l (Hhdr & Hmeta & Hl)".
    specialize (HΔ'' l). destruct (envs_app _ _ _) as [Δ'' |] eqn:HΔ'; last done.
    rewrite -HΔ'' envs_app_sound //= right_id.
    iApply ("HΔ'" with "[$Hhdr $Hl $Hmeta]").
  Qed.

  Lemma tac_wp_block Δ Δ' id1 id2 id3 K tag es vs E Φ :
    0 < length es →
    to_vals es = Some vs →
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    ( ∀ l,
      match
        envs_app false (Esnoc (Esnoc (Esnoc Enil
          id1 (l ↦ₕ Header tag (length es)))
          id2 (meta_token l ⊤))
          id3 (l ↦∗ vs))
          Δ'
      with
      | Some Δ'' =>
          envs_entails Δ'' (WP fill K #l @ E {{ Φ }})
      | None =>
          False
      end
    ) →
    envs_entails Δ (WP fill K (Block Concrete tag es) @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hlen Hes HΔ HΔ''.
    rewrite into_laterN_env_sound -wp_bind.
    iIntros "HΔ'".
    iApply (wp_block with "[//]"); [done.. |]. iIntros "!> %l (Hhdr & Hmeta & Hl)".
    specialize (HΔ'' l). destruct (envs_app _ _ _) as [Δ'' |] eqn:HΔ'; last done.
    rewrite -HΔ'' envs_app_sound //= right_id.
    iApply ("HΔ'" with "[$Hhdr $Hl $Hmeta]").
  Qed.

  Lemma tac_wp_ref Δ Δ' id1 id2 id3 K v E Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    ( ∀ l,
      match
        envs_app false (Esnoc (Esnoc (Esnoc Enil
          id1 (l ↦ₕ Header 0 1))
          id2 (meta_token l ⊤))
          id3 (l ↦ᵣ v))
          Δ'
      with
      | Some Δ'' =>
          envs_entails Δ'' (WP fill K #l @ E {{ Φ }})
      | None =>
          False
      end
    ) →
    envs_entails Δ (WP fill K (ref v) @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => HΔ HΔ''.
    rewrite into_laterN_env_sound -wp_bind.
    iIntros "HΔ'".
    iApply (wp_block with "[//]"); [simpl; lia | done |]. iIntros "!> %l (Hhdr & Hmeta & Hl)".
    specialize (HΔ'' l). destruct (envs_app _ _ _) as [Δ'' |] eqn:HΔ'; last done.
    rewrite -HΔ'' envs_app_sound //= !right_id.
    iApply ("HΔ'" with "[$Hhdr $Hl $Hmeta]").
  Qed.

  Lemma tac_wp_reveal Δ Δ' K tag vs E Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    ( ∀ bid,
      envs_entails Δ' (WP fill K (ValBlock (Some bid) tag vs) @ E {{ Φ }})
    ) →
    envs_entails Δ (WP fill K (Reveal $ ValBlock None tag vs) @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => HΔ HΔ'.
    rewrite into_laterN_env_sound -wp_bind -wp_reveal.
    apply bi.forall_intro => bid.
    rewrite (HΔ' bid) //.
  Qed.

  Lemma tac_wp_match Δ Δ' id p K l hdr vs x e brs e' E Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup id Δ' = Some (p, l ↦ₕ hdr)%I →
    envs_entails Δ' (l ↦∗□ vs) →
    length vs = hdr.(header_size) →
    eval_match (Some l) None hdr.(header_tag) vs x e brs = Some e' →
    envs_entails Δ' (WP fill K e' @ E {{ Φ }}) →
    envs_entails Δ (WP fill K (Match #l x e brs) @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => HΔ Hlookup1 Hlookup2 Hvs He' HΔ'.
    rewrite into_laterN_env_sound -wp_bind /=.
    iIntros "HΔ'".
    iAssert (▷ l ↦ₕ hdr)%I as "#Hhdr".
    { iDestruct (envs_lookup_split with "HΔ'") as "(Hhdr & _)"; first done.
      destruct p; iSteps.
    }
    iDestruct (Hlookup2 with "HΔ'") as "#Hl".
    iApply (wp_match with "Hhdr Hl"); [done.. |]. iIntros "!> _".
    rewrite -wp_bind_inv HΔ'. iSteps.
  Qed.

  Lemma tac_wp_get_tag Δ Δ' id p K l hdr E Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup id Δ' = Some (p, l ↦ₕ hdr)%I →
    envs_entails Δ' (WP fill K #hdr.(header_tag) @ E {{ Φ }}) →
    envs_entails Δ (WP fill K (GetTag #l) @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => HΔ Hlookup HΔ'.
    rewrite into_laterN_env_sound -wp_bind envs_lookup_split //= HΔ'.
    iIntros "(Hhdr & H)".
    iAssert (▷ l ↦ₕ hdr)%I with "[Hhdr]" as "#Hhdr_".
    { destruct p; iSteps. }
    iApply (wp_get_tag with "Hhdr_").
    iSteps.
  Qed.

  Lemma tac_wp_get_size Δ Δ' id p K l hdr E Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup id Δ' = Some (p, l ↦ₕ hdr)%I →
    envs_entails Δ' (WP fill K #hdr.(header_size) @ E {{ Φ }}) →
    envs_entails Δ (WP fill K (GetSize #l) @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => HΔ Hlookup HΔ'.
    rewrite into_laterN_env_sound -wp_bind envs_lookup_split //= HΔ'.
    iIntros "(Hhdr & H)".
    iAssert (▷ l ↦ₕ hdr)%I with "[Hhdr]" as "#Hhdr_".
    { destruct p; iSteps. }
    iApply (wp_get_size with "Hhdr_").
    iSteps.
  Qed.

  Lemma tac_wp_load Δ Δ' id p K l fld dq v E Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup id Δ' = Some (p, (l +ₗ fld) ↦{dq} v)%I →
    envs_entails Δ' (WP fill K v @ E {{ Φ }}) →
    envs_entails Δ (WP fill K (Load #l #fld) @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => HΔ Hlookup HΔ'.
    rewrite into_laterN_env_sound -wp_bind envs_lookup_split //= HΔ'.
    iIntros "(Hl & H)".
    iAssert (▷ (□ (if p then (l +ₗ fld) ↦{dq} v else True) ∗ (l +ₗ fld) ↦{dq} v))%I with "[Hl]" as "(#Hl_ & Hl)".
    { destruct p; iSteps. }
    iApply (wp_load with "Hl").
    iSteps. destruct p; iSteps.
  Qed.

  Lemma tac_wp_store Δ Δ' id K l fld v w E Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup id Δ' = Some (false, (l +ₗ fld) ↦ w)%I →
    match
      envs_simple_replace id false (Esnoc Enil
      id ((l +ₗ fld) ↦ v)
      ) Δ'
    with
    | Some Δ'' =>
        envs_entails Δ'' (WP fill K () @ E {{ Φ }})
    | None =>
        False
    end →
    envs_entails Δ (WP fill K (Store #l #fld v) @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => HΔ Hlookup HΔ'.
    destruct (envs_simple_replace _ _ _ _) as [Δ'' |] eqn:HΔ''; last done.
    rewrite into_laterN_env_sound -wp_bind envs_simple_replace_sound //= HΔ'.
    iIntros "(Hl & H)".
    iApply (wp_store with "Hl").
    iSteps.
  Qed.

  Lemma tac_wp_xchg Δ Δ' id K l fld v w E Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup id Δ' = Some (false, (l +ₗ fld) ↦ w)%I →
    match
      envs_simple_replace id false (Esnoc Enil
        id ((l +ₗ fld) ↦ v)
      ) Δ'
    with
    | Some Δ'' =>
        envs_entails Δ'' (WP fill K w @ E {{ Φ }})
    | None =>
        False
    end →
    envs_entails Δ (WP fill K (Xchg (#l, #fld)%V v) @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => HΔ Hlookup HΔ'.
    destruct (envs_simple_replace _ _ _ _) as [Δ'' |] eqn:HΔ''; last done.
    rewrite into_laterN_env_sound -wp_bind envs_simple_replace_sound //= HΔ'.
    iIntros "(Hl & H)".
    iApply (wp_xchg with "Hl").
    iSteps.
  Qed.

  Lemma tac_wp_cas Δ Δ' Δ'' id p K l fld dq v v1 v2 E Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup_delete true id Δ' = Some (p, (l +ₗ fld) ↦{dq} v, Δ'')%I →
    ValPhysical v →
    ValPhysical v1 →
    ( val_neq v v1 →
      envs_entails Δ' (WP fill K #false @ E {{ Φ }})
    ) →
    ( val_eq v v1 →
      envs_entails Δ' ⌜dq = DfracOwn 1⌝
    ) →
    match
      envs_app false (Esnoc Enil
        id ((l +ₗ fld) ↦ v2))
        Δ''
    with
    | Some Δ''' =>
        val_eq v v1 →
        envs_entails Δ''' (WP fill K #true @ E {{ Φ }})
    | None =>
        False
    end →
    envs_entails Δ (WP fill K (CAS (#l, #fld)%V v1 v2) @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal. intros HΔ (Hlookup & ->)%envs_lookup_delete_Some Hv Hv1 Hfail Hsuc1 Hsuc2.
    destruct (envs_app _ _ _) as [Δ''' |] eqn:HΔ'''; last done.
    rewrite into_laterN_env_sound -wp_bind //=.
    iIntros "HΔ'".
    iAssert (▷ ⌜envs_wf Δ'⌝)%I as "#>%Hwf".
    { iDestruct (of_envs_alt with "HΔ'") as "($ & _)". }
    iDestruct (envs_lookup_sound with "HΔ'") as "(Hl & HΔ'')"; first done.
    iAssert (▷ (□ (if p then (l +ₗ fld) ↦{dq} v else True) ∗ (l +ₗ fld) ↦{dq} v))%I with "[Hl]" as "(#Hl_ & Hl)".
    { destruct p; iSteps. }
    iApply (wp_cas with "Hl"); [done.. |].
    iSplit.
    - iIntros "!> %Hneq Hl".
      iDestruct (envs_lookup_sound_2 with "[Hl HΔ'']") as "HΔ'"; [done.. | |].
      { iFrame. destruct p; iSteps. }
      iApply (Hfail with "HΔ'"); first done.
    - iIntros "!> %Heq Hl".
      iDestruct (envs_lookup_sound_2 with "[Hl HΔ'']") as "HΔ'"; [done.. | |].
      { iFrame. destruct p; iSteps. }
      iDestruct (Hsuc1 with "HΔ'") as %->; [done.. |].
      iDestruct (envs_lookup_sound with "HΔ'") as "(Hl & HΔ'')"; first done.
      rewrite envs_app_sound //= Hsuc2 // bi.intuitionistically_if_elim. iSteps.
  Qed.
  Lemma tac_wp_cas_suc Δ Δ' id K l fld lit lit1 v2 E Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup id Δ' = Some (false, (l +ₗ fld) ↦ #lit)%I →
    literal_physical lit →
    lit = lit1 →
    match
      envs_simple_replace id false (Esnoc Enil
        id ((l +ₗ fld) ↦ v2)
      ) Δ'
    with
    | Some Δ'' =>
        envs_entails Δ'' (WP fill K #true @ E {{ Φ }})
    | None =>
        False
    end →
    envs_entails Δ (WP fill K (CAS (#l, #fld)%V #lit1 v2) @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal. intros HΔ Hlookup Hlit -> HΔ'.
    destruct (envs_simple_replace _ _ _ _) as [Δ'' |] eqn:HΔ''; last done.
    rewrite into_laterN_env_sound -wp_bind envs_simple_replace_sound //= HΔ'.
    iIntros "(Hl & H)".
    iApply (wp_cas_suc with "Hl"); [done.. |].
    iSteps.
  Qed.

  Lemma tac_wp_faa Δ Δ' id K l fld (i1 i2 : Z) E Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup id Δ' = Some (false, (l +ₗ fld) ↦ #i1)%I →
    match
      envs_simple_replace id false (Esnoc Enil
        id ((l +ₗ fld) ↦ #(i1 + i2))
      ) Δ'
    with
    | Some Δ'' =>
        envs_entails Δ'' (WP fill K #i1 @ E {{ Φ }})
    | None =>
        False
    end →
    envs_entails Δ (WP fill K (FAA (#l, #fld)%V #i2) @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => HΔ Hlookup HΔ''.
    destruct (envs_simple_replace _ _ _) as [Δ'' |] eqn:HΔ'; last done.
    rewrite into_laterN_env_sound -wp_bind envs_simple_replace_sound //= HΔ''.
    iIntros "(Hl & H)".
    iApply (wp_faa with "Hl").
    iSteps.
  Qed.
End zoo_G.

#[local] Ltac wp_start tac :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?e _ _) =>
      tac e
  | _ =>
      fail "not a 'wp'"
  end.

Tactic Notation "wp_expr_eval" tactic3(tac) :=
  wp_start ltac:(fun e =>
    notypeclasses refine (tac_wp_expr_eval _ e _ _ _ _ _);
    [ let x := fresh in
      intros x;
      tac;
      unfold x;
      notypeclasses refine eq_refl
    | idtac
    ]
  ).
Ltac wp_expr_simpl :=
  wp_expr_eval simpl.

#[local] Ltac wp_value_head :=
  lazymatch goal with
  | |- envs_entails _ (wp (Val _) _ (λ _, fupd _ _ _)) =>
      eapply tac_wp_value_nofupd
  | |- envs_entails _ (wp (Val _) _ (λ _, wp _ _ _ _)) =>
      eapply tac_wp_value_nofupd
  | |- envs_entails _ (wp (Val _) _ _) =>
      eapply tac_wp_value
  end.
#[local] Ltac wp_finish :=
  wp_expr_simpl;
  try wp_value_head;
  pm_prettify.

Tactic Notation "wp_pure" open_constr(e_foc) :=
  wp_start ltac:(fun e =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' e_foc;
      eapply (tac_wp_pure _ _ K e');
      [ tc_solve
      | split_and?; fast_done
      | tc_solve
      | wp_finish
      ]
    )
    || fail "wp_pure: cannot find" e_foc "in" e "or" e_foc "is not a redex"
  ).
Tactic Notation "wp_pure" :=
  wp_pure _.
Tactic Notation "wp_pure" open_constr(e_foc) "credit:" constr(H) :=
  wp_start ltac:(fun e =>
    let Htmp := iFresh in
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' e_foc;
      eapply (tac_wp_pure_credit _ _ Htmp K e');
      [ tc_solve
      | split_and?; fast_done
      | tc_solve
      | pm_reduce;
        first
        [ iDestructHyp Htmp as H
        | fail 2 "wp_pure:" H "is not fresh"
        ];
        wp_finish
      ]
    )
    || fail "wp_pure: cannot find" e_foc "in" e "or" e_foc "is not a redex"
  ).
Tactic Notation "wp_pure" "credit:" constr(H) :=
  wp_pure _ credit: H.
Tactic Notation "wp_pures" :=
  first
  [ progress repeat (wp_pure _; [])
  | wp_finish
  ].
Tactic Notation "wp_pures" "credit:" constr(H) :=
  wp_pure credit:H;
  wp_pures.

Tactic Notation "wp_rec" :=
  let H := fresh in
  assert (H := ValRec_as_ValRec);
  wp_pure (App _ _);
  clear H.
Tactic Notation "wp_rec" "credit:" constr(Hcredit) :=
  let H := fresh in
  assert (H := ValRec_as_ValRec);
  wp_pure (App _ _) credit:Hcredit;
  clear H.

Tactic Notation "wp_for" :=
  let H := fresh in
  assert (H := pure_for);
  wp_pure (For _ _ _);
  clear H.
Tactic Notation "wp_for" "credit:" constr(Hcredit) :=
  let H := fresh in
  assert (H := pure_for);
  wp_pure (For _ _ _) credit:Hcredit;
  clear H.

Ltac wp_bind_core K :=
  lazymatch eval hnf in K with
  | [] =>
      idtac
  | _ =>
      eapply (tac_wp_bind _ K);
      [ simpl; reflexivity
      | pm_prettify
      ]
  end.
Tactic Notation "wp_bind" open_constr(e_foc) :=
  wp_start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        unify e' e_foc;
        wp_bind_core K
      )
    | fail 1 "wp_bind: cannot find" e_foc "in" e
    ]
  ).

#[local] Ltac solve_val_physical :=
  try (fast_done || tc_solve).

Tactic Notation "wp_equal" "as" simple_intropattern(Hfail) "|" simple_intropattern(Hsuc) :=
  wp_pures;
  wp_start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tac_wp_equal _ _ K)
      )
    | fail 1 "wp_equal: cannot find 'Equal' in" e
    ];
    [ tc_solve
    | solve_val_physical
    | solve_val_physical
    | intros Hfail;
      wp_finish
    | intros Hsuc;
      wp_finish
    ]
  ).

Tactic Notation "wp_alloc" ident(l) "as" constr(Hhdr) constr(Hmeta) constr(Hl) :=
  let Hhdr' := Hhdr in
  let Hmeta' := iFresh in
  let Hl' := iFresh in
  wp_pures;
  wp_start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tac_wp_alloc _ _ Hhdr' Hmeta' Hl' K)
      )
    | fail 1 "wp_alloc: cannot find 'Alloc' in" e
    ];
    [ idtac
    | idtac
    | tc_solve
    | first
      [ intros l
      | fail 1 "wp_alloc:" l "not fresh"
      ];
      pm_reduce;
      first
      [ iDestructHyp Hhdr' as Hhdr
      | fail 1 "wp_alloc:" Hhdr "is not fresh"
      ];
      first
      [ iDestructHyp Hmeta' as Hmeta
      | fail 1 "wp_alloc:" Hmeta "is not fresh"
      ];
      first
      [ iDestructHyp Hl' as Hl
      | fail 1 "wp_alloc:" Hl "is not fresh"
      ];
      wp_finish
    ]
  ).
Tactic Notation "wp_alloc" ident(l) "as" constr(Hmeta) constr(Hl) :=
  wp_alloc l as "_" Hmeta Hl.
Tactic Notation "wp_alloc" ident(l) "as" constr(Hl) :=
  wp_alloc l as "_" Hl.
Tactic Notation "wp_alloc" ident(l) :=
  wp_alloc l as "?".

Tactic Notation "wp_block" ident(l) "as" constr(Hhdr) constr(Hmeta) constr(Hl) :=
  let Hhdr' := iFresh in
  let Hmeta' := iFresh in
  let Hl' := iFresh in
  wp_pures;
  wp_start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tac_wp_block _ _ Hhdr' Hmeta' Hl' K);
        [ simpl; lia
        | fast_done
        | idtac..
        ]
      )
    | fail 1 "wp_block: cannot find 'Block Concrete' in" e
    ];
    [ tc_solve
    | first
      [ intros l
      | fail 1 "wp_block:" l "not fresh"
      ];
      pm_reduce;
      first
      [ iDestructHyp Hhdr' as Hhdr
      | fail 1 "wp_block:" Hhdr "is not fresh"
      ];
      first
      [ iDestructHyp Hmeta' as Hmeta
      | fail 1 "wp_block:" Hmeta "is not fresh"
      ];
      first
      [ iDestructHyp Hl' as Hl
      | fail 1 "wp_block:" Hl "is not fresh"
      ];
      wp_finish
    ]
  ).
Tactic Notation "wp_block" ident(l) "as" constr(Hmeta) constr(Hl) :=
  wp_block l as "_" Hmeta Hl.
Tactic Notation "wp_block" ident(l) "as" constr(Hl) :=
  wp_block l as "_" Hl.
Tactic Notation "wp_block" ident(l) :=
  wp_block l as "?".

Tactic Notation "wp_ref" ident(l) "as" constr(Hhdr) constr(Hmeta) constr(Hl) :=
  let Hhdr' := Hhdr in
  let Hmeta' := iFresh in
  let Hl' := iFresh in
  wp_pures;
  wp_start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tac_wp_ref _ _ Hhdr' Hmeta' Hl' K)
      )
    | fail 1 "wp_ref: cannot find 'ref' in" e
    ];
    [ tc_solve
    | first
      [ intros l
      | fail 1 "wp_ref:" l "not fresh"
      ];
      pm_reduce;
      first
      [ iDestructHyp Hhdr' as Hhdr
      | fail 1 "wp_ref:" Hhdr "is not fresh"
      ];
      first
      [ iDestructHyp Hmeta' as Hmeta
      | fail 1 "wp_ref:" Hmeta "is not fresh"
      ];
      first
      [ iDestructHyp Hl' as Hl
      | fail 1 "wp_ref:" Hl "is not fresh"
      ];
      wp_finish
    ]
  ).
Tactic Notation "wp_ref" ident(l) "as" constr(Hmeta) constr(Hl) :=
  wp_ref l as "_" Hmeta Hl.
Tactic Notation "wp_ref" ident(l) "as" constr(Hl) :=
  wp_ref l as "_" Hl.
Tactic Notation "wp_ref" ident(l) :=
  wp_ref l as "?".

Tactic Notation "wp_reveal" simple_intropattern(bid) :=
  wp_pures;
  wp_start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tac_wp_reveal _ _ K)
      )
    | fail 1 "wp_reveal: cannot find 'Reveal' in" e
    ];
    [ tc_solve
    | intros bid;
      wp_finish
    ]
  ).

Tactic Notation "wp_match" open_constr(vs) :=
  wp_pures;
  wp_start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tac_wp_match _ _ _ _ K _ _ vs)
      )
    | fail 1 "wp_match: cannot find 'Match' on location in" e
    ];
    [ tc_solve
    | let l := match goal with |- _ = Some (_, (has_header ?l _)) => l end in
      first
      [ iAssumptionCore
      | fail 1 "wp_match: cannot find" l "↦ₕ ?"
      ]
    | try iFrame
    | try fast_done
    | try fast_done
    | wp_finish
    ]
  ).

Ltac wp_get_tag :=
  wp_pures;
  wp_start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tac_wp_get_tag _ _ _ _ K)
      )
    | fail 1 "wp_get_tag: cannot find 'GetTag' in" e
    ];
    [ tc_solve
    | let l := match goal with |- _ = Some (_, (has_header ?l _)) => l end in
      first
      [ iAssumptionCore
      | fail 1 "wp_get_tag: cannot find" l "↦ₕ ?"
      ]
    | wp_finish
    ]
  ).

Ltac wp_get_size :=
  wp_pures;
  wp_start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tac_wp_get_size _ _ _ _ K)
      )
    | fail 1 "wp_get_size: cannot find 'GetSize' in" e
    ];
    [ tc_solve
    | let l := match goal with |- _ = Some (_, (has_header ?l _)) => l end in
      first
      [ iAssumptionCore
      | fail 1 "wp_get_size: cannot find" l "↦ₕ ?"
      ]
    | wp_finish
    ]
  ).

Ltac wp_load :=
  wp_pures;
  wp_start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tac_wp_load _ _ _ _ K)
      )
    | fail 1 "wp_load: cannot find 'Load' in" e
    ];
    [ tc_solve
    | let l := match goal with |- _ = Some (_, (pointsto ?l _ _)) => l end in
      first
      [ iAssumptionCore
      | fail 1 "wp_load: cannot find" l "↦ ?"
      ]
    | wp_finish
    ]
  ).

Ltac wp_store :=
  wp_pures;
  wp_start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tac_wp_store _ _ _ K)
      )
    | fail 1 "wp_store: cannot find 'Store' in" e
    ];
    [ tc_solve
    | let l := match goal with |- _ = Some (_, (pointsto ?l _ _)) => l end in
      first
      [ iAssumptionCore
      | fail 1 "wp_store: cannot find" l "↦ ?"
      ]
    | pm_reduce;
      wp_finish
    ]
  ).

Ltac wp_xchg :=
  wp_pures;
  wp_start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tac_wp_xchg _ _ _ K)
      )
    | fail 1 "wp_xchg: cannot find 'Xchg in" e
    ];
    [ tc_solve
    | let l := match goal with |- _ = Some (_, (pointsto ?l _ _)) => l end in
      first
      [ iAssumptionCore
      | fail 1 "wp_xchg: cannot find" l "↦ ?"
      ]
    | pm_reduce;
      wp_finish
    ]
  ).

Tactic Notation "wp_cas" "as" simple_intropattern(Hfail) "|" simple_intropattern(Hsuc) :=
  wp_pures;
  wp_start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tac_wp_cas _ _ _ _ _ K)
      )
    | fail 1 "wp_cas: cannot find 'CAS' with literal arguments in" e
    ];
    [ tc_solve
    | let l := match goal with |- _ = Some (_, (pointsto ?l _ _), _) => l end in
      first
      [ iAssumptionCore
      | fail 1 "wp_cas: cannot find" l "↦ ?"
      ]
    | solve_val_physical
    | solve_val_physical
    | intros Hfail;
      wp_finish
    | intros Hsuc;
      try (iPureIntro; fast_done)
    | pm_reduce;
      intros Hsuc;
      wp_finish
    ]
  ).
Ltac wp_cas_suc :=
  wp_pures;
  wp_start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tac_wp_cas_suc _ _ _ K)
      )
    | fail 1 "wp_cas_suc: cannot find 'CAS' with literal arguments in" e
    ];
    [ tc_solve
    | let l := match goal with |- _ = Some (_, (pointsto ?l _ _)) => l end in
      first
      [ iAssumptionCore
      | fail 1 "wp_cas_suc: cannot find" l "↦ ?"
      ]
    | try fast_done
    | try (simpl; congruence)
    | pm_reduce;
      wp_finish
    ]
  ).

Ltac wp_faa :=
  wp_pures;
  wp_start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tac_wp_faa _ _ _ K)
      )
    | fail 1 "wp_faa: cannot find 'FAA' in" e
    ];
    [ tc_solve
    | let l := match goal with |- _ = Some (_, (pointsto ?l _ _)) => l end in
      first
      [ iAssumptionCore
      | fail "wp_faa: cannot find" l "↦ ?"
      ]
    | pm_reduce;
      wp_finish
    ]
  ).

#[local] Ltac wp_apply_core lemma tac_suc tac_fail :=
  first
  [ iPoseProofCore lemma as false (fun H =>
      wp_start ltac:(fun e =>
       reshape_expr e ltac:(fun K e' =>
         wp_bind_core K;
         tac_suc H
       )
      )
    )
  | tac_fail ltac:(fun _ =>
      wp_apply_core lemma tac_suc tac_fail
    )
  | let P := type of lemma in
    fail "wp_apply: cannot apply" lemma ":" P
  ].

Tactic Notation "wp_apply" open_constr(lemma) :=
  wp_apply_core lemma
    ltac:(fun H => iApplyHyp H; try iNext; try wp_expr_simpl)
    ltac:(fun _ => fail).
Tactic Notation "wp_apply" open_constr(lemma) "as"
  constr(pat)
:=
  wp_apply lemma; last iIntros pat.
Tactic Notation "wp_apply" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
  ")"
  constr(pat)
:=
  wp_apply lemma; last iIntros ( x1 ) pat.
Tactic Notation "wp_apply" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
      simple_intropattern(x2)
  ")"
  constr(pat)
:=
  wp_apply lemma; last iIntros ( x1 x2 ) pat.
Tactic Notation "wp_apply" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
      simple_intropattern(x2)
      simple_intropattern(x3)
  ")"
  constr(pat)
:=
  wp_apply lemma; last iIntros ( x1 x2 x3 ) pat.
Tactic Notation "wp_apply" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
      simple_intropattern(x2)
      simple_intropattern(x3)
      simple_intropattern(x4)
  ")"
  constr(pat)
:=
  wp_apply lemma; last iIntros ( x1 x2 x3 x4 ) pat.
Tactic Notation "wp_apply" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
      simple_intropattern(x2)
      simple_intropattern(x3)
      simple_intropattern(x4)
      simple_intropattern(x5)
  ")"
  constr(pat)
:=
  wp_apply lemma; last iIntros ( x1 x2 x3 x4 x5 ) pat.
Tactic Notation "wp_apply" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
      simple_intropattern(x2)
      simple_intropattern(x3)
      simple_intropattern(x4)
      simple_intropattern(x5)
      simple_intropattern(x6)
  ")"
  constr(pat)
:=
  wp_apply lemma; last iIntros ( x1 x2 x3 x4 x5 x6 ) pat.
Tactic Notation "wp_apply" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
      simple_intropattern(x2)
      simple_intropattern(x3)
      simple_intropattern(x4)
      simple_intropattern(x5)
      simple_intropattern(x6)
      simple_intropattern(x7)
  ")"
  constr(pat)
:=
  wp_apply lemma; last iIntros ( x1 x2 x3 x4 x5 x6 x7 ) pat.
Tactic Notation "wp_apply" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
      simple_intropattern(x2)
      simple_intropattern(x3)
      simple_intropattern(x4)
      simple_intropattern(x5)
      simple_intropattern(x6)
      simple_intropattern(x7)
      simple_intropattern(x8)
  ")"
  constr(pat)
:=
  wp_apply lemma; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat.
Tactic Notation "wp_apply" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
      simple_intropattern(x2)
      simple_intropattern(x3)
      simple_intropattern(x4)
      simple_intropattern(x5)
      simple_intropattern(x6)
      simple_intropattern(x7)
      simple_intropattern(x8)
      simple_intropattern(x9)
  ")"
  constr(pat)
:=
  wp_apply lemma; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ) pat.
Tactic Notation "wp_apply" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
      simple_intropattern(x2)
      simple_intropattern(x3)
      simple_intropattern(x4)
      simple_intropattern(x5)
      simple_intropattern(x6)
      simple_intropattern(x7)
      simple_intropattern(x8)
      simple_intropattern(x9)
      simple_intropattern(x10)
  ")"
  constr(pat)
:=
  wp_apply lemma; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) pat.

Tactic Notation "wp_smart_apply" open_constr(lemma) :=
  wp_apply_core lemma
    ltac:(fun H =>
      iApplyHyp H;
      try iNext;
      try wp_expr_simpl
    )
    ltac:(fun retry =>
      wp_pure _; [];
      retry ()
    ).
Tactic Notation "wp_smart_apply" open_constr(lemma) "as"
  constr(pat)
:=
  wp_smart_apply lemma; last iIntros pat.
Tactic Notation "wp_smart_apply" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
  ")"
  constr(pat)
:=
  wp_smart_apply lemma; last iIntros ( x1 ) pat.
Tactic Notation "wp_smart_apply" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
      simple_intropattern(x2)
  ")"
  constr(pat)
:=
  wp_smart_apply lemma; last iIntros ( x1 x2 ) pat.
Tactic Notation "wp_smart_apply" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
      simple_intropattern(x2)
      simple_intropattern(x3)
  ")"
  constr(pat)
:=
  wp_smart_apply lemma; last iIntros ( x1 x2 x3 ) pat.
Tactic Notation "wp_smart_apply" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
      simple_intropattern(x2)
      simple_intropattern(x3)
      simple_intropattern(x4)
  ")"
  constr(pat)
:=
  wp_smart_apply lemma; last iIntros ( x1 x2 x3 x4 ) pat.
Tactic Notation "wp_smart_apply" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
      simple_intropattern(x2)
      simple_intropattern(x3)
      simple_intropattern(x4)
      simple_intropattern(x5)
  ")"
  constr(pat)
:=
  wp_smart_apply lemma; last iIntros ( x1 x2 x3 x4 x5 ) pat.
Tactic Notation "wp_smart_apply" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
      simple_intropattern(x2)
      simple_intropattern(x3)
      simple_intropattern(x4)
      simple_intropattern(x5)
      simple_intropattern(x6)
  ")"
  constr(pat)
:=
  wp_smart_apply lemma; last iIntros ( x1 x2 x3 x4 x5 x6 ) pat.
Tactic Notation "wp_smart_apply" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
      simple_intropattern(x2)
      simple_intropattern(x3)
      simple_intropattern(x4)
      simple_intropattern(x5)
      simple_intropattern(x6)
      simple_intropattern(x7)
  ")"
  constr(pat)
:=
  wp_smart_apply lemma; last iIntros ( x1 x2 x3 x4 x5 x6 x7 ) pat.
Tactic Notation "wp_smart_apply" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
      simple_intropattern(x2)
      simple_intropattern(x3)
      simple_intropattern(x4)
      simple_intropattern(x5)
      simple_intropattern(x6)
      simple_intropattern(x7)
      simple_intropattern(x8)
  ")"
  constr(pat)
:=
  wp_smart_apply lemma; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat.
Tactic Notation "wp_smart_apply" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
      simple_intropattern(x2)
      simple_intropattern(x3)
      simple_intropattern(x4)
      simple_intropattern(x5)
      simple_intropattern(x6)
      simple_intropattern(x7)
      simple_intropattern(x8)
      simple_intropattern(x9)
  ")"
  constr(pat)
:=
  wp_smart_apply lemma; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ) pat.
Tactic Notation "wp_smart_apply" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
      simple_intropattern(x2)
      simple_intropattern(x3)
      simple_intropattern(x4)
      simple_intropattern(x5)
      simple_intropattern(x6)
      simple_intropattern(x7)
      simple_intropattern(x8)
      simple_intropattern(x9)
      simple_intropattern(x10)
  ")"
  constr(pat)
:=
  wp_smart_apply lemma; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) pat.

Tactic Notation "awp_apply" open_constr(lemma) :=
  wp_apply_core lemma
    ltac:(fun H => iApplyHyp H; pm_prettify)
    ltac:(fun _ => fail);
  last iAuIntro.
Tactic Notation "awp_apply" open_constr(lemma) "without" constr(Hs) :=
  let Hs := String.words Hs in
  let Hs := eval vm_compute in (INamed <$> Hs) in
  wp_apply_core lemma
    ltac:(fun H =>
      iApply (wp_frame_wand with [SGoal $ SpecGoal GSpatial false [] Hs false]);
      [ iAccu
      | iApplyHyp H;
        pm_prettify
      ]
    )
    ltac:(fun _ =>
      fail
    );
  last iAuIntro.

Tactic Notation "awp_smart_apply" open_constr(lemma) :=
  wp_apply_core lemma
    ltac:(fun H =>
      iApplyHyp H
    )
    ltac:(fun retry =>
      wp_pure _; [];
      retry ()
    );
  last iAuIntro.
Tactic Notation "awp_smart_apply" open_constr(lemma) "without" constr(Hs) :=
  let Hs := String.words Hs in
  let Hs := eval vm_compute in (INamed <$> Hs) in
  wp_apply_core lemma
    ltac:(fun H =>
      iApply (wp_frame_wand with [SGoal $ SpecGoal GSpatial false [] Hs false]);
      [ iAccu
      | iApplyHyp H;
        pm_prettify
      ]
    )
    ltac:(fun retry =>
      wp_pure _; [];
      retry ()
    );
  last iAuIntro.
