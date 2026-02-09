From iris.proofmode Require Import
  coq_tactics
  reduction
  spec_patterns.

From zoo Require Import
  prelude.
From zoo.iris Require Export
  proofmode.
From zoo.iris Require Import
  diaframe.
From zoo.language Require Import
  notations.
From zoo.language Require Export
  tactics.
From zoo.program_logic Require Export
  atomic.
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

  Lemma tac_wp_expr_eval Δ e e' tid E Φ :
    (∀ (e'' := e'), e = e'') →
    envs_entails Δ (WP e' ∷ tid @ E {{ Φ }}) →
    envs_entails Δ (WP e ∷ tid @ E {{ Φ }}).
  Proof.
    intros ->. done.
  Qed.

  Lemma tac_wp_pure Δ Δ' K e1 e2 ϕ n tid E Φ :
    PureExec ϕ n e1 e2 →
    ϕ →
    MaybeIntoLaterNEnvs n Δ Δ' →
    envs_entails Δ' (WP (fill K e2) ∷ tid @ E {{ Φ }}) →
    envs_entails Δ (WP (fill K e1) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hexec Hϕ HΔ HΔ'.
    pose proof @pure_exec_fill. rewrite -wp_pure_step_later //.
    rewrite into_laterN_env_sound HΔ'.
    iSteps.
  Qed.
  #[local] Lemma tac_wp_pure_credits' n Δ Δ' id K e1 e2 ϕ tid E Φ :
    n ≤ later_constant →
    PureExec ϕ 1 e1 e2 →
    ϕ →
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    match
      envs_app false (Esnoc Enil
        id (£ n))
        Δ'
    with
    | Some Δ'' =>
        envs_entails Δ'' (WP fill K e2 ∷ tid @ E {{ Φ }})
    | None =>
        False
    end →
    envs_entails Δ (WP (fill K e1) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hn Hexec Hϕ HΔ HΔ''.
    destruct (envs_app _ _ _) as [Δ'' |] eqn:HΔ'; last done.
    pose proof @pure_exec_fill. rewrite -wp_pure_step_later //= Nat.add_0_r.
    rewrite (bi.wand_entails _ _ (lc_weaken n _)) //.
    rewrite into_laterN_env_sound envs_app_sound //= HΔ''.
    iSteps.
  Qed.
  Lemma tac_wp_pure_credits Δ Δ' id K e1 e2 ϕ tid E Φ :
    PureExec ϕ 1 e1 e2 →
    ϕ →
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    match
      envs_app false (Esnoc Enil
        id (£ later_constant))
        Δ'
    with
    | Some Δ'' =>
        envs_entails Δ'' (WP fill K e2 ∷ tid @ E {{ Φ }})
    | None =>
        False
    end →
    envs_entails Δ (WP (fill K e1) ∷ tid @ E {{ Φ }}).
  Proof.
    apply tac_wp_pure_credits'. done.
  Qed.
  Lemma tac_wp_pure_credit Δ Δ' id K e1 e2 ϕ tid E Φ :
    PureExec ϕ 1 e1 e2 →
    ϕ →
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    match
      envs_app false (Esnoc Enil
        id (£ 1))
        Δ'
    with
    | Some Δ'' =>
        envs_entails Δ'' (WP fill K e2 ∷ tid @ E {{ Φ }})
    | None =>
        False
    end →
    envs_entails Δ (WP (fill K e1) ∷ tid @ E {{ Φ }}).
  Proof.
    apply tac_wp_pure_credits'.
    pose proof later_constant_lb. lia.
  Qed.

  Lemma tac_wp_value_nofupd Δ v tid E Φ :
    envs_entails Δ (Φ v) →
    envs_entails Δ (WP (Val v) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => ->.
    apply wp_value'.
  Qed.
  Lemma tac_wp_value Δ v tid E Φ :
    envs_entails Δ (|={E}=> Φ v) →
    envs_entails Δ (WP (Val v) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => ->.
    apply wp_value_fupd'.
  Qed.

  Lemma tac_wp_bind Δ K e (f : expr → expr) tid E Φ :
    f = (λ e, fill K e) →
    envs_entails Δ (WP e ∷ tid @ E {{ v, WP f (Val v) ∷ tid @ E {{ Φ }} }})%I →
    envs_entails Δ (WP fill K e ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => -> ->.
    apply: wp_bind'.
  Qed.

  Lemma tac_wp_equal Δ Δ' K v1 v2 tid E Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    ( v1 ≉ v2 →
      envs_entails Δ' (WP fill K false%V ∷ tid @ E {{ Φ }})
    ) →
    ( v1 ≈ v2 →
      envs_entails Δ' (WP fill K true%V ∷ tid @ E {{ Φ }})
    ) →
    envs_entails Δ (WP fill K (v1 == v2) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => HΔ Hfail Hsuc.
    rewrite into_laterN_env_sound -wp_bind' -wp_equal //.
    apply bi.later_mono, bi.and_intro.
    all: repeat (rewrite bi.pure_wand_forall; apply bi.forall_intro => ?).
    all: naive_solver.
  Qed.

  Lemma tac_wp_alloc Δ Δ' id1 id2 id3 K tag n tid E Φ :
    (0 ≤ tag)%Z →
    (0 ≤ n)%Z →
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    ( ∀ l,
      match
        envs_app false (Esnoc (Esnoc (Esnoc Enil
          id1 (l ↦ₕ Header ₊tag ₊n))
          id2 (meta_token l ⊤))
          id3 (l ↦∗ replicate ₊n ()%V))
          Δ'
      with
      | Some Δ'' =>
          envs_entails Δ'' (WP fill K #l ∷ tid @ E {{ Φ }})
      | None =>
          False
      end
    ) →
    envs_entails Δ (WP fill K (Alloc #tag #n) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Htag Hn HΔ HΔ''.
    rewrite into_laterN_env_sound -wp_bind'.
    iIntros "HΔ'".
    iApply (wp_alloc with "[//]"); [done.. |]. iIntros "!> %l (Hheader & Hmeta & Hl)".
    specialize (HΔ'' l). destruct (envs_app _ _ _) as [Δ'' |] eqn:HΔ'; last done.
    rewrite -HΔ'' envs_app_sound //= right_id.
    iApply ("HΔ'" with "[$Hheader $Hl $Hmeta]").
  Qed.

  Lemma tac_wp_block_mutable Δ Δ' id1 id2 id3 K tag es vs tid E Φ :
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
          envs_entails Δ'' (WP fill K #l ∷ tid @ E {{ Φ }})
      | None =>
          False
      end
    ) →
    envs_entails Δ (WP fill K (Block Mutable tag es) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hlen Hes HΔ HΔ''.
    rewrite into_laterN_env_sound -wp_bind'.
    iIntros "HΔ'".
    iApply (wp_block_mutable with "[//]"); [done.. |]. iIntros "!> %l (Hheader & Hmeta & Hl)".
    specialize (HΔ'' l). destruct (envs_app _ _ _) as [Δ'' |] eqn:HΔ'; last done.
    rewrite -HΔ'' envs_app_sound //= right_id.
    iApply ("HΔ'" with "[$Hheader $Hl $Hmeta]").
  Qed.

  Lemma tac_wp_ref Δ Δ' id1 id2 id3 K v tid E Φ :
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
          envs_entails Δ'' (WP fill K #l ∷ tid @ E {{ Φ }})
      | None =>
          False
      end
    ) →
    envs_entails Δ (WP fill K (ref v) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => HΔ HΔ''.
    rewrite into_laterN_env_sound -wp_bind'.
    iIntros "HΔ'".
    iApply (wp_block_mutable with "[//]"); [simpl; lia | done |]. iIntros "!> %l (Hheader & Hmeta & Hl)".
    specialize (HΔ'' l). destruct (envs_app _ _ _) as [Δ'' |] eqn:HΔ'; last done.
    rewrite -HΔ'' envs_app_sound //= !right_id.
    iApply ("HΔ'" with "[$Hheader $Hl $Hmeta]").
  Qed.

  Lemma tac_wp_block_generative Δ Δ' K tag es vs tid E Φ :
    to_vals es = Some vs →
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    ( ∀ bid,
      envs_entails Δ' (WP fill K (ValBlock (Generative (Some bid)) tag vs) ∷ tid @ E {{ Φ }})
    ) →
    envs_entails Δ (WP fill K (Block ImmutableGenerativeStrong tag es) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hes HΔ HΔ'.
    rewrite into_laterN_env_sound -wp_bind'.
    iIntros "HΔ'".
    iApply (wp_block_generative with "[//]"); first done. iIntros "!> %bid _".
    iApply (HΔ' with "HΔ'").
  Qed.

  Lemma tac_wp_match Δ Δ' id p K l hdr x_fb e_fb brs e tid E Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup id Δ' = Some (p, l ↦ₕ hdr)%I →
    eval_match hdr.(header_tag) hdr.(header_size) (SubjectLoc l) x_fb e_fb brs = Some e →
    envs_entails Δ' (WP fill K e ∷ tid @ E {{ Φ }}) →
    envs_entails Δ (WP fill K (Match #l x_fb e_fb brs) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => HΔ Hlookup He HΔ'.
    rewrite into_laterN_env_sound /=.
    iIntros "HΔ'".
    iAssert (▷ l ↦ₕ hdr)%I as "#Hl".
    { iDestruct (envs_lookup_split with "HΔ'") as "(Hl & _)"; first done.
      destruct p; iSteps.
    }
    iApply (wp_match_context with "Hl"); first done.
    rewrite HΔ'. iSteps.
  Qed.

  Lemma tac_wp_tag Δ Δ' id p K l hdr tid E Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup id Δ' = Some (p, l ↦ₕ hdr)%I →
    envs_entails Δ' (WP fill K #(encode_tag hdr.(header_tag)) ∷ tid @ E {{ Φ }}) →
    envs_entails Δ (WP fill K (GetTag #l) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => HΔ Hlookup HΔ'.
    rewrite into_laterN_env_sound -wp_bind' envs_lookup_split //= HΔ'.
    iIntros "(Hheader & H)".
    iAssert (▷ l ↦ₕ hdr)%I with "[Hheader]" as "#Hheader_".
    { destruct p; iSteps. }
    iApply (wp_tag with "Hheader_").
    iSteps.
  Qed.

  Lemma tac_wp_size Δ Δ' id p K l hdr tid E Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup id Δ' = Some (p, l ↦ₕ hdr)%I →
    envs_entails Δ' (WP fill K #hdr.(header_size) ∷ tid @ E {{ Φ }}) →
    envs_entails Δ (WP fill K (GetSize #l) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => HΔ Hlookup HΔ'.
    rewrite into_laterN_env_sound -wp_bind' envs_lookup_split //= HΔ'.
    iIntros "(Hheader & H)".
    iAssert (▷ l ↦ₕ hdr)%I with "[Hheader]" as "#Hheader_".
    { destruct p; iSteps. }
    iApply (wp_size with "Hheader_").
    iSteps.
  Qed.

  Lemma tac_wp_load Δ Δ' id p K l fld dq v tid E Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup id Δ' = Some (p, (l +ₗ fld) ↦{dq} v)%I →
    envs_entails Δ' (WP fill K v ∷ tid @ E {{ Φ }}) →
    envs_entails Δ (WP fill K (Load #l #fld) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => HΔ Hlookup HΔ'.
    rewrite into_laterN_env_sound -wp_bind' envs_lookup_split //= HΔ'.
    iIntros "(Hl & H)".
    iAssert (▷ (□ (if p then (l +ₗ fld) ↦{dq} v else True) ∗ (l +ₗ fld) ↦{dq} v))%I with "[Hl]" as "(#Hl_ & Hl)".
    { destruct p; iSteps. }
    iApply (wp_load with "Hl").
    iSteps. destruct p; iSteps.
  Qed.

  Lemma tac_wp_store Δ Δ' id K l fld v w tid E Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup id Δ' = Some (false, (l +ₗ fld) ↦ w)%I →
    match
      envs_simple_replace id false (Esnoc Enil
      id ((l +ₗ fld) ↦ v)
      ) Δ'
    with
    | Some Δ'' =>
        envs_entails Δ'' (WP fill K () ∷ tid @ E {{ Φ }})
    | None =>
        False
    end →
    envs_entails Δ (WP fill K (Store #l #fld v) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => HΔ Hlookup HΔ'.
    destruct (envs_simple_replace _ _ _ _) as [Δ'' |] eqn:HΔ''; last done.
    rewrite into_laterN_env_sound -wp_bind' envs_simple_replace_sound //= HΔ'.
    iIntros "(Hl & H)".
    iApply (wp_store with "Hl").
    iSteps.
  Qed.

  Lemma tac_wp_xchg Δ Δ' id K l fld v w tid E Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup id Δ' = Some (false, (l +ₗ fld) ↦ w)%I →
    match
      envs_simple_replace id false (Esnoc Enil
        id ((l +ₗ fld) ↦ v)
      ) Δ'
    with
    | Some Δ'' =>
        envs_entails Δ'' (WP fill K w ∷ tid @ E {{ Φ }})
    | None =>
        False
    end →
    envs_entails Δ (WP fill K (Xchg (#l, #fld)%V v) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => HΔ Hlookup HΔ'.
    destruct (envs_simple_replace _ _ _ _) as [Δ'' |] eqn:HΔ''; last done.
    rewrite into_laterN_env_sound -wp_bind' envs_simple_replace_sound //= HΔ'.
    iIntros "(Hl & H)".
    iApply (wp_xchg with "Hl").
    iSteps.
  Qed.

  Lemma tac_wp_cas Δ Δ' Δ'' id p K l fld dq v v1 v2 tid E Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup_delete true id Δ' = Some (p, (l +ₗ fld) ↦{dq} v, Δ'')%I →
    ( v ≉ v1 →
      envs_entails Δ' (WP fill K false%V ∷ tid @ E {{ Φ }})
    ) →
    ( v ≈ v1 →
      envs_entails Δ' ⌜dq = DfracOwn 1⌝
    ) →
    match
      envs_app false (Esnoc Enil
        id ((l +ₗ fld) ↦ v2))
        Δ''
    with
    | Some Δ''' =>
        v ≈ v1 →
        envs_entails Δ''' (WP fill K true%V ∷ tid @ E {{ Φ }})
    | None =>
        False
    end →
    envs_entails Δ (WP fill K (CAS (#l, #fld)%V v1 v2) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal. intros HΔ (Hlookup & ->)%envs_lookup_delete_Some Hfail Hsuc1 Hsuc2.
    destruct (envs_app _ _ _) as [Δ''' |] eqn:HΔ'''; last done.
    rewrite into_laterN_env_sound -wp_bind' //=.
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

  Lemma tac_wp_faa Δ Δ' id K l fld (i1 i2 : Z) tid E Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup id Δ' = Some (false, (l +ₗ fld) ↦ #i1)%I →
    match
      envs_simple_replace id false (Esnoc Enil
        id ((l +ₗ fld) ↦ #(i1 + i2))
      ) Δ'
    with
    | Some Δ'' =>
        envs_entails Δ'' (WP fill K #i1 ∷ tid @ E {{ Φ }})
    | None =>
        False
    end →
    envs_entails Δ (WP fill K (FAA (#l, #fld)%V #i2) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => HΔ Hlookup HΔ''.
    destruct (envs_simple_replace _ _ _) as [Δ'' |] eqn:HΔ'; last done.
    rewrite into_laterN_env_sound -wp_bind' envs_simple_replace_sound //= HΔ''.
    iIntros "(Hl & H)".
    iApply (wp_faa with "Hl").
    iSteps.
  Qed.
End zoo_G.

#[local] Ltac wp_start tac :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?e _ _ _) =>
      tac e
  | _ =>
      fail "not a 'wp'"
  end.

Tactic Notation "wp_expr_eval" tactic3(tac) :=
  wp_start ltac:(fun e =>
    notypeclasses refine (tac_wp_expr_eval _ e _ _ _ _ _ _);
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
  | |- envs_entails _ (wp (Val _) _ _ (λ _, fupd _ _ _)) =>
      eapply tac_wp_value_nofupd
  | |- envs_entails _ (wp (Val _) _ _ (λ _, wp _ _ _ _)) =>
      eapply tac_wp_value_nofupd
  | |- envs_entails _ (wp (Val _) _ _ _) =>
      eapply tac_wp_value
  end.
#[local] Ltac wp_finish :=
  wp_expr_simpl;
  try wp_value_head;
  pm_prettify.

#[local] Ltac solve_pure_exec_obligation :=
  simpl; split_and?; done || lia.
Tactic Notation "wp_pure" open_constr(e_foc) :=
  wp_start ltac:(fun e =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' e_foc;
      eapply (tac_wp_pure _ _ K e');
      [ tc_solve
      | solve_pure_exec_obligation
      | tc_solve
      | wp_finish
      ]
    )
    || fail "wp_pure: cannot find" e_foc "in" e "or" e_foc "is not a redex"
  ).
Tactic Notation "wp_pure" :=
  wp_pure _.
Tactic Notation "wp_pures" :=
  first
  [ progress repeat (wp_pure _; [])
  | wp_finish
  ].
Tactic Notation "wp_pure" open_constr(e_foc) "credits:" constr(Hcredit) :=
  wp_start ltac:(fun e =>
    let Htmp := iFresh in
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' e_foc;
      eapply (tac_wp_pure_credits _ _ Htmp K e');
      [ tc_solve
      | solve_pure_exec_obligation
      | tc_solve
      | pm_reduce;
        first
        [ iDestructHyp Htmp as Hcredit
        | fail 2 "wp_pure:" Hcredit "is not fresh"
        ];
        wp_finish
      ]
    )
    || fail "wp_pure: cannot find" e_foc "in" e "or" e_foc "is not a redex"
  ).
Tactic Notation "wp_pure" "credits:" constr(Hcredit) :=
  wp_pure _ credits:Hcredit.
Tactic Notation "wp_pures" "credits:" constr(Hcredit) :=
  wp_pure credits:Hcredit;
  wp_pures.
Tactic Notation "wp_pure" open_constr(e_foc) "credit:" constr(Hcredit) :=
  wp_start ltac:(fun e =>
    let Htmp := iFresh in
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' e_foc;
      eapply (tac_wp_pure_credit _ _ Htmp K e');
      [ tc_solve
      | solve_pure_exec_obligation
      | tc_solve
      | pm_reduce;
        first
        [ iDestructHyp Htmp as Hcredit
        | fail 2 "wp_pure:" Hcredit "is not fresh"
        ];
        wp_finish
      ]
    )
    || fail "wp_pure: cannot find" e_foc "in" e "or" e_foc "is not a redex"
  ).
Tactic Notation "wp_pure" "credit:" constr(Hcredit) :=
  wp_pure _ credit:Hcredit.
Tactic Notation "wp_pures" "credit:" constr(Hcredit) :=
  wp_pure credit:Hcredit;
  wp_pures.

#[local] Ltac wp_rec_aux tac :=
  let H1 := fresh in
  assert (H1 := ValRec_as_ValRec);
  let H2 := fresh in
  assert (H2 := as_ValRecs'_as_ValRecs);
  tac ();
  clear H1 H2.
Tactic Notation "wp_rec" :=
  wp_rec_aux ltac:(fun _ =>
    wp_pure (App _ _)
  ).
Tactic Notation "wp_rec" "credits:" constr(Hcredit) :=
  wp_rec_aux ltac:(fun _ =>
    wp_pure (App _ _) credits:Hcredit
  ).
Tactic Notation "wp_rec" "credit:" constr(Hcredit) :=
  wp_rec_aux ltac:(fun _ =>
    wp_pure (App _ _) credit:Hcredit
  ).

Tactic Notation "wp_for" :=
  let H := fresh in
  assert (H := pure_for);
  wp_pure (For _ _ _);
  clear H.
Tactic Notation "wp_for" "credits:" constr(Hcredit) :=
  let H := fresh in
  assert (H := pure_for);
  wp_pure (For _ _ _) credits:Hcredit;
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
    | intros Hfail;
      wp_finish
    | intros Hsuc;
      wp_finish
    ]
  ).
Tactic Notation "wp_equal" "as" simple_intropattern(H) :=
  wp_equal as H | H.
Tactic Notation "wp_equal" :=
  wp_equal as ?.

Tactic Notation "wp_alloc" ident(l) "as" constr(Hheader) constr(Hmeta) constr(Hl) :=
  let Hheader' := Hheader in
  let Hmeta' := iFresh in
  let Hl' := iFresh in
  wp_pures;
  wp_start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tac_wp_alloc _ _ Hheader' Hmeta' Hl' K)
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
      [ iDestructHyp Hheader' as Hheader
      | fail 1 "wp_alloc:" Hheader "is not fresh"
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

Tactic Notation "wp_block" ident(l) "as" constr(Hheader) constr(Hmeta) constr(Hl) :=
  let Hheader' := iFresh in
  let Hmeta' := iFresh in
  let Hl' := iFresh in
  wp_pures;
  wp_start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tac_wp_block_mutable _ _ Hheader' Hmeta' Hl' K);
        [ simpl; lia
        | fast_done
        | idtac..
        ]
      )
    | fail 1 "wp_block: cannot find 'Block Mutable in" e
    ];
    [ tc_solve
    | first
      [ intros l
      | fail 1 "wp_block:" l "not fresh"
      ];
      pm_reduce;
      first
      [ iDestructHyp Hheader' as Hheader
      | fail 1 "wp_block:" Hheader "is not fresh"
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

Tactic Notation "wp_ref" ident(l) "as" constr(Hheader) constr(Hmeta) constr(Hl) :=
  let Hheader' := Hheader in
  let Hmeta' := iFresh in
  let Hl' := iFresh in
  wp_pures;
  wp_start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tac_wp_ref _ _ Hheader' Hmeta' Hl' K)
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
      [ iDestructHyp Hheader' as Hheader
      | fail 1 "wp_ref:" Hheader "is not fresh"
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

Tactic Notation "wp_block_generative" simple_intropattern(bid) :=
  wp_pures;
  wp_start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tac_wp_block_generative _ _ K);
        [ fast_done
        | idtac..
        ]
      )
    | fail 1 "wp_block_generative: cannot find 'Block ImmutableGenerativeStrong' in" e
    ];
    [ tc_solve
    | intros bid;
      wp_finish
    ]
  ).
Tactic Notation "wp_block_generative" :=
  wp_block_generative ?.

Tactic Notation "wp_match" :=
  wp_pures;
  wp_start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tac_wp_match _ _ _ _ K)
      )
    | fail 1 "wp_match: cannot find 'Match' on location in" e
    ];
    [ tc_solve
    | let l := match goal with |- _ = Some (_, (has_header ?l _)) => l end in
      first
      [ iAssumptionCore
      | fail 1 "wp_match: cannot find" l "↦ₕ ?"
      ]
    | try fast_done
    | wp_finish
    ]
  ).

Ltac wp_tag :=
  wp_pures;
  wp_start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tac_wp_tag _ _ _ _ K)
      )
    | fail 1 "wp_tag: cannot find 'GetTag' in" e
    ];
    [ tc_solve
    | let l := match goal with |- _ = Some (_, (has_header ?l _)) => l end in
      first
      [ iAssumptionCore
      | fail 1 "wp_tag: cannot find" l "↦ₕ ?"
      ]
    | wp_finish
    ]
  ).

Ltac wp_size :=
  wp_pures;
  wp_start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tac_wp_size _ _ _ _ K)
      )
    | fail 1 "wp_size: cannot find 'GetSize' in" e
    ];
    [ tc_solve
    | let l := match goal with |- _ = Some (_, (has_header ?l _)) => l end in
      first
      [ iAssumptionCore
      | fail 1 "wp_size: cannot find" l "↦ₕ ?"
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
    | intros Hfail;
      wp_finish
    | intros Hsuc;
      try (iPureIntro; fast_done)
    | pm_reduce;
      intros Hsuc;
      wp_finish
    ]
  ).
Tactic Notation "wp_cas" "as" simple_intropattern(H) :=
  wp_cas as H | H.
Tactic Notation "wp_cas" :=
  wp_cas as ?.

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
