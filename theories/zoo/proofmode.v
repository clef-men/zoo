Require Import iris.proofmode.coq_tactics.
Require Import iris.proofmode.reduction.
Require Import iris.proofmode.spec_patterns.

Require Import zoo.prelude.
Require Export zoo.iris.proofmode.
Require Import zoo.iris.diaframe.
Require Import zoo.language.notations.
Require Export zoo.language.tactics.
Require Export zoo.program_logic.atomic.
Require Import zoo.options.

Implicit Type l : location.
Implicit Type lit : literal.
Implicit Type e : expr.
Implicit Type v : val.
Implicit Type K : ectx.

#[global] Instance bi_intuitionistically_ifｰtimeless {PROP : bi} (P : PROP) p :
  Timeless (emp : PROP) →
  Timeless P →
  Timeless (□?p P).
Proof.
  destruct p => /= HP; apply _.
Qed.

#[local] Notation "'let*' Δ2 := Δ1 'in' cont" := (
  match Δ1 with
  | Some Δ2 =>
      cont
  | None =>
      False
  end
)(at level 200,
  Δ1 at level 200,
  Δ2 ident,
  cont at level 200,
  format "'[v' '[hv' 'let*'  Δ2  :=  '/  ' '[' Δ1 ']'  '/' 'in'  ']' '/' cont ']'"
).

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Implicit Type Φ : val → iProp Σ.

  Lemma tacｰwpｰexprｰeval Δ e e' tid E Φ :
    (∀ (e'' := e'), e = e'') →
    envs_entails Δ (WP e' ∷ tid @ E {{ Φ }}) →
    envs_entails Δ (WP e ∷ tid @ E {{ Φ }}).
  Proof.
    intros ->. done.
  Qed.

  Lemma tacｰwpｰpure Δ1 Δ2 K e1 e2 ϕ n tid E Φ :
    PureExec ϕ n e1 e2 →
    ϕ →
    MaybeIntoLaterNEnvs n Δ1 Δ2 →
    envs_entails Δ2 (WP (fill K e2) ∷ tid @ E {{ Φ }}) →
    envs_entails Δ1 (WP (fill K e1) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hexec Hϕ HΔ1 HΔ2.
    rewrite into_laterN_env_sound HΔ2.
    pose proof pure_execｰfill.
    rewrite -wpｰpure_step //.
    iSteps.
  Qed.
  #[local] Lemma tacｰwpｰpureｰcredits' n Δ1 Δ2 id K e1 e2 ϕ tid E Φ :
    n ≤ later_constant →
    PureExec ϕ 1 e1 e2 →
    ϕ →
    MaybeIntoLaterNEnvs 1 Δ1 Δ2 →
    ( let* Δ3 :=
        envs_app false (Esnoc Enil
          id (£ n))
          Δ2
      in
      envs_entails Δ3 (WP fill K e2 ∷ tid @ E {{ Φ }})
    ) →
    envs_entails Δ1 (WP (fill K e1) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hn Hexec Hϕ HΔ1 HΔ3.
    destruct (envs_app _ _ _) as [Δ3 |] eqn:HΔ2; last done.
    rewrite into_laterN_env_sound envs_app_sound //= HΔ3.
    pose proof pure_execｰfill.
    rewrite -wpｰpure_step //.
    iStep 4 as "H£".
    iDestruct (lc_weaken with "H£") as "$"; first lia.
  Qed.
  Lemma tacｰwpｰpureｰcredits Δ1 Δ2 id K e1 e2 ϕ tid E Φ :
    PureExec ϕ 1 e1 e2 →
    ϕ →
    MaybeIntoLaterNEnvs 1 Δ1 Δ2 →
    ( let* Δ3 :=
        envs_app false (Esnoc Enil
          id (£ later_constant))
          Δ2
      in
      envs_entails Δ3 (WP fill K e2 ∷ tid @ E {{ Φ }})
    ) →
    envs_entails Δ1 (WP (fill K e1) ∷ tid @ E {{ Φ }}).
  Proof.
    apply tacｰwpｰpureｰcredits'. done.
  Qed.
  Lemma tacｰwpｰpureｰcredit Δ1 Δ2 id K e1 e2 ϕ tid E Φ :
    PureExec ϕ 1 e1 e2 →
    ϕ →
    MaybeIntoLaterNEnvs 1 Δ1 Δ2 →
    ( let* Δ3 :=
        envs_app false (Esnoc Enil
          id (£ 1))
          Δ2
      in
      envs_entails Δ3 (WP fill K e2 ∷ tid @ E {{ Φ }})
    ) →
    envs_entails Δ1 (WP (fill K e1) ∷ tid @ E {{ Φ }}).
  Proof.
    apply tacｰwpｰpureｰcredits'.
    pose proof later۰constant_lb. lia.
  Qed.
  Lemma tacｰwpｰpureｰsteps۰lb Δ1 Δ2 id p ns K e1 e2 ϕ tid E Φ :
    PureExec ϕ 1 e1 e2 →
    ϕ →
    MaybeIntoLaterNEnvs 1 Δ1 Δ2 →
    envs_lookup id Δ2 = Some (p, ⧖ ns)%I →
    ( let* Δ3 :=
        envs_simple_replace id p (Esnoc Enil
          id (⧖ ˖ns)
        ) Δ2
      in
      envs_entails Δ3 (WP fill K e2 ∷ tid @ E {{ Φ }})
    ) →
    envs_entails Δ1 (WP (fill K e1) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hexec Hϕ HΔ1 Hlookup HΔ2.
    destruct (envs_simple_replace _ _ _ _) as [Δ3 |] eqn:HΔ3; last done.
    rewrite into_laterN_env_sound envs_simple_replace_sound //= HΔ2.
    rewrite bi.intuitionistically_if_elim.
    iIntros "(>H⧖ & H)".
    pose proof pure_execｰfill.
    iApply (wpｰpure_stepｰstrong with "H⧖"); first done.
    rewrite Nat.add_1_r. iSteps.
    destruct p; iFrame "#∗".
  Qed.
  #[local] Lemma tacｰwpｰpureｰsteps۰lbｰcredits' n Δ1 Δ2 id1 p ns id2 K e1 e2 ϕ tid E Φ :
    n ≤ later۰function ns →
    PureExec ϕ 1 e1 e2 →
    ϕ →
    MaybeIntoLaterNEnvs 1 Δ1 Δ2 →
    envs_lookup id1 Δ2 = Some (p, ⧖ ns)%I →
    ( let* Δ3 :=
        envs_simple_replace id1 p (Esnoc Enil
          id1 (⧖ ˖ns)
        ) Δ2
      in
      let* Δ4 :=
        envs_app false (Esnoc Enil
          id2 (£ n))
          Δ3
      in
      envs_entails Δ4 (WP fill K e2 ∷ tid @ E {{ Φ }})
    ) →
    envs_entails Δ1 (WP (fill K e1) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hn Hexec Hϕ HΔ1 Hlookup HΔ2.
    destruct (envs_simple_replace _ _ _ _) as [Δ3 |] eqn:HΔ3; last done.
    rewrite into_laterN_env_sound envs_simple_replace_sound //=.
    destruct (envs_app _ _ _) as [Δ4 |] eqn:HΔ4; last done.
    rewrite envs_app_sound //= HΔ2.
    rewrite bi.intuitionistically_if_elim.
    iIntros "(>H⧖ & H)".
    pose proof pure_execｰfill.
    iApply (wpｰpure_stepｰstrong with "H⧖"); first done.
    rewrite /= Nat.add_1_r Nat.add_0_r. iStep 4 as "H⧖ H£".
    iDestruct (lc_weaken with "H£") as "$"; first done.
    destruct p; iFrame "#∗".
  Qed.
  Lemma tacｰwpｰpureｰsteps۰lbｰcredits Δ1 Δ2 id1 p ns id2 K e1 e2 ϕ tid E Φ :
    PureExec ϕ 1 e1 e2 →
    ϕ →
    MaybeIntoLaterNEnvs 1 Δ1 Δ2 →
    envs_lookup id1 Δ2 = Some (p, ⧖ ns)%I →
    ( let* Δ3 :=
        envs_simple_replace id1 p (Esnoc Enil
          id1 (⧖ ˖ns)
        ) Δ2
      in
      let* Δ4 :=
        envs_app false (Esnoc Enil
          id2 (£ (later۰function ns)))
          Δ3
      in
      envs_entails Δ4 (WP fill K e2 ∷ tid @ E {{ Φ }})
    ) →
    envs_entails Δ1 (WP (fill K e1) ∷ tid @ E {{ Φ }}).
  Proof.
    apply tacｰwpｰpureｰsteps۰lbｰcredits'. done.
  Qed.
  Lemma tacｰwpｰpureｰsteps۰lbｰcredit Δ1 Δ2 id1 p ns id2 K e1 e2 ϕ tid E Φ :
    PureExec ϕ 1 e1 e2 →
    ϕ →
    MaybeIntoLaterNEnvs 1 Δ1 Δ2 →
    envs_lookup id1 Δ2 = Some (p, ⧖ ns)%I →
    ( let* Δ3 :=
        envs_simple_replace id1 p (Esnoc Enil
          id1 (⧖ ˖ns)
        ) Δ2
      in
      let* Δ4 :=
        envs_app false (Esnoc Enil
          id2 (£ 1))
          Δ3
      in
      envs_entails Δ4 (WP fill K e2 ∷ tid @ E {{ Φ }})
    ) →
    envs_entails Δ1 (WP (fill K e1) ∷ tid @ E {{ Φ }}).
  Proof.
    apply tacｰwpｰpureｰsteps۰lbｰcredits'.
    pose proof (later۰functionｰlb ns).
    pose proof later۰constant_lb.
    lia.
  Qed.

  Lemma tacｰwpｰvalueｰnofupd Δ v tid E Φ :
    envs_entails Δ (Φ v) →
    envs_entails Δ (WP (Val v) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => ->.
    apply wpｰvalue'.
  Qed.
  Lemma tacｰwpｰvalue Δ v tid E Φ :
    envs_entails Δ (|={E}=> Φ v) →
    envs_entails Δ (WP (Val v) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => ->.
    apply wpｰvalueｰfupd'.
  Qed.

  Lemma tacｰwpｰbind Δ K e (f : expr → expr) tid E Φ :
    f = (λ e, fill K e) →
    envs_entails Δ (WP e ∷ tid @ E {{ v, WP f (Val v) ∷ tid @ E {{ Φ }} }})%I →
    envs_entails Δ (WP fill K e ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => -> ->.
    apply: wpｰbind'.
  Qed.

  Lemma tacｰwpｰequal Δ1 Δ2 K v1 v2 tid E Φ :
    MaybeIntoLaterNEnvs 1 Δ1 Δ2 →
    ( v1 ≉ v2 →
      envs_entails Δ2 (WP fill K false%V ∷ tid @ E {{ Φ }})
    ) →
    ( v1 ≈ v2 →
      envs_entails Δ2 (WP fill K true%V ∷ tid @ E {{ Φ }})
    ) →
    envs_entails Δ1 (WP fill K (v1 == v2) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => HΔ1 Hfail Hsuc.
    rewrite into_laterN_env_sound -wpｰbind' -wpｰequal //.
    apply bi.later_mono, bi.and_intro.
    all: repeat (rewrite bi.pure_wand_forall; apply bi.forall_intro => ?).
    all: naive_solver.
  Qed.

  Lemma tacｰwpｰalloc Δ1 Δ2 id1 id2 id3 K tag n tid E Φ :
    (0 ≤ tag)%Z →
    (0 ≤ n)%Z →
    MaybeIntoLaterNEnvs 1 Δ1 Δ2 →
    ( ∀ l,
      let* Δ3 :=
        envs_app false (Esnoc (Esnoc (Esnoc Enil
          id1 (l ↦ₕ Header ₊tag ₊n))
          id2 (meta_token l ⊤))
          id3 (l ↦∗ replicate ₊n ()%V))
          Δ2
      in
      envs_entails Δ3 (WP fill K #l ∷ tid @ E {{ Φ }})
    ) →
    envs_entails Δ1 (WP fill K (Alloc #tag #n) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Htag Hn HΔ1 HΔ3.
    rewrite into_laterN_env_sound -wpｰbind'.
    iIntros "HΔ2".
    iApply (wpｰalloc with "[//]"); [done.. |]. iIntros "!> %l (Hheader & Hmeta & Hl)".
    specialize (HΔ3 l). destruct (envs_app _ _ _) as [Δ3 |] eqn:HΔ2; last done.
    rewrite -HΔ3 envs_app_sound //= right_id.
    iApply ("HΔ2" with "[$Hheader $Hl $Hmeta]").
  Qed.

  Lemma tacｰwpｰblockｰmutable Δ1 Δ2 id1 id2 id3 K tag es vs tid E Φ :
    0 < length es →
    to_vals es = Some vs →
    MaybeIntoLaterNEnvs 1 Δ1 Δ2 →
    ( ∀ l,
      let* Δ3 :=
        envs_app false (Esnoc (Esnoc (Esnoc Enil
          id1 (l ↦ₕ Header tag (length es)))
          id2 (meta_token l ⊤))
          id3 (l ↦∗ vs))
          Δ2
      in
      envs_entails Δ3 (WP fill K #l ∷ tid @ E {{ Φ }})
    ) →
    envs_entails Δ1 (WP fill K (Block Mutable tag es) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hlen Hes HΔ1 HΔ3.
    rewrite into_laterN_env_sound -wpｰbind'.
    iIntros "HΔ2".
    iApply (wpｰblockｰmutable with "[//]"); [done.. |]. iIntros "!> %l (Hheader & Hmeta & Hl)".
    specialize (HΔ3 l). destruct (envs_app _ _ _) as [Δ3 |] eqn:HΔ2; last done.
    rewrite -HΔ3 envs_app_sound //= right_id.
    iApply ("HΔ2" with "[$Hheader $Hl $Hmeta]").
  Qed.

  Lemma tacｰwpｰref Δ1 Δ2 id1 id2 id3 K v tid E Φ :
    MaybeIntoLaterNEnvs 1 Δ1 Δ2 →
    ( ∀ l,
      let* Δ3 :=
        envs_app false (Esnoc (Esnoc (Esnoc Enil
          id1 (l ↦ₕ Header 0 1))
          id2 (meta_token l ⊤))
          id3 (l ↦ᵣ v))
          Δ2
      in
      envs_entails Δ3 (WP fill K #l ∷ tid @ E {{ Φ }})
    ) →
    envs_entails Δ1 (WP fill K (𝗿𝗲𝗳 v) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => HΔ1 HΔ3.
    rewrite into_laterN_env_sound -wpｰbind'.
    iIntros "HΔ2".
    iApply (wpｰblockｰmutable with "[//]"); [simpl; lia | done |]. iIntros "!> %l (Hheader & Hmeta & Hl)".
    specialize (HΔ3 l). destruct (envs_app _ _ _) as [Δ3 |] eqn:HΔ2; last done.
    rewrite -HΔ3 envs_app_sound //= !right_id.
    iApply ("HΔ2" with "[$Hheader $Hl $Hmeta]").
  Qed.

  Lemma tacｰwpｰblockｰgenerative Δ1 Δ2 K tag es vs tid E Φ :
    to_vals es = Some vs →
    MaybeIntoLaterNEnvs 1 Δ1 Δ2 →
    ( ∀ bid,
      envs_entails Δ2 (WP fill K (ValBlock (Generative (Some bid)) tag vs) ∷ tid @ E {{ Φ }})
    ) →
    envs_entails Δ1 (WP fill K (Block ImmutableGenerativeStrong tag es) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hes HΔ1 HΔ2.
    rewrite into_laterN_env_sound -wpｰbind'.
    iIntros "HΔ2".
    iApply (wpｰblockｰgenerative with "[//]"); first done. iIntros "!> %bid _".
    iApply (HΔ2 with "HΔ2").
  Qed.

  Lemma tacｰwpｰmatch Δ1 Δ2 id p K l hdr x_fb e_fb brs e tid E Φ :
    MaybeIntoLaterNEnvs 1 Δ1 Δ2 →
    envs_lookup id Δ2 = Some (p, l ↦ₕ hdr)%I →
    eval_match hdr.(header۰tag) hdr.(header۰size) (SubjectLoc l) x_fb e_fb brs = Some e →
    envs_entails Δ2 (WP fill K e ∷ tid @ E {{ Φ }}) →
    envs_entails Δ1 (WP fill K (Match #l x_fb e_fb brs) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => HΔ1 Hlookup He HΔ2.
    rewrite into_laterN_env_sound /=.
    iIntros "HΔ2".
    iAssert (▷ l ↦ₕ hdr)%I as "#Hl".
    { iDestruct (envs_lookup_split with "HΔ2") as "(Hl & _)"; first done.
      destruct p; iSteps.
    }
    iApply (wpｰmatchｰcontext with "Hl"); first done.
    rewrite HΔ2. iSteps.
  Qed.

  Lemma tacｰwpｰtag Δ1 Δ2 id p K l hdr tid E Φ :
    MaybeIntoLaterNEnvs 1 Δ1 Δ2 →
    envs_lookup id Δ2 = Some (p, l ↦ₕ hdr)%I →
    envs_entails Δ2 (WP fill K #(encode_tag hdr.(header۰tag)) ∷ tid @ E {{ Φ }}) →
    envs_entails Δ1 (WP fill K (GetTag #l) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => HΔ1 Hlookup HΔ2.
    rewrite into_laterN_env_sound -wpｰbind' envs_lookup_split //= HΔ2.
    iIntros "(Hheader & H)".
    iAssert (▷ l ↦ₕ hdr)%I with "[Hheader]" as "#Hheader_".
    { destruct p; iSteps. }
    iApply (wpｰtag with "Hheader_").
    iSteps.
  Qed.

  Lemma tacｰwpｰsize Δ1 Δ2 id p K l hdr tid E Φ :
    MaybeIntoLaterNEnvs 1 Δ1 Δ2 →
    envs_lookup id Δ2 = Some (p, l ↦ₕ hdr)%I →
    envs_entails Δ2 (WP fill K #hdr.(header۰size) ∷ tid @ E {{ Φ }}) →
    envs_entails Δ1 (WP fill K (GetSize #l) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => HΔ1 Hlookup HΔ2.
    rewrite into_laterN_env_sound -wpｰbind' envs_lookup_split //= HΔ2.
    iIntros "(Hheader & H)".
    iAssert (▷ l ↦ₕ hdr)%I with "[Hheader]" as "#Hheader_".
    { destruct p; iSteps. }
    iApply (wpｰsize with "Hheader_").
    iSteps.
  Qed.

  Lemma tacｰwpｰload Δ1 Δ2 id p K l fld dq v tid E Φ :
    MaybeIntoLaterNEnvs 1 Δ1 Δ2 →
    envs_lookup id Δ2 = Some (p, (l +ₗ fld) ↦{dq} v)%I →
    envs_entails Δ2 (WP fill K v ∷ tid @ E {{ Φ }}) →
    envs_entails Δ1 (WP fill K (Load #l #fld) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => HΔ1 Hlookup HΔ2.
    rewrite into_laterN_env_sound -wpｰbind' envs_lookup_split //= HΔ2.
    iIntros "(Hl & H)".
    iAssert (▷ (□ (if p then (l +ₗ fld) ↦{dq} v else True) ∗ (l +ₗ fld) ↦{dq} v))%I with "[Hl]" as "(#Hl_ & Hl)".
    { destruct p; iSteps. }
    iApply (wpｰload with "Hl").
    iSteps. destruct p; iSteps.
  Qed.

  Lemma tacｰwpｰstore Δ1 Δ2 id K l fld v w tid E Φ :
    MaybeIntoLaterNEnvs 1 Δ1 Δ2 →
    envs_lookup id Δ2 = Some (false, (l +ₗ fld) ↦ w)%I →
    ( let* Δ3 :=
        envs_simple_replace id false (Esnoc Enil
          id ((l +ₗ fld) ↦ v))
          Δ2
      in
      envs_entails Δ3 (WP fill K () ∷ tid @ E {{ Φ }})
    ) →
    envs_entails Δ1 (WP fill K (Store #l #fld v) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => HΔ1 Hlookup HΔ2.
    destruct (envs_simple_replace _ _ _ _) as [Δ3 |] eqn:HΔ3; last done.
    rewrite into_laterN_env_sound -wpｰbind' envs_simple_replace_sound //= HΔ2.
    iIntros "(Hl & H)".
    iApply (wpｰstore with "Hl").
    iSteps.
  Qed.

  Lemma tacｰwpｰxchg Δ1 Δ2 id K l fld v w tid E Φ :
    MaybeIntoLaterNEnvs 1 Δ1 Δ2 →
    envs_lookup id Δ2 = Some (false, (l +ₗ fld) ↦ w)%I →
    ( let* Δ3 :=
        envs_simple_replace id false (Esnoc Enil
          id ((l +ₗ fld) ↦ v)
        ) Δ2
      in
      envs_entails Δ3 (WP fill K w ∷ tid @ E {{ Φ }})
    ) →
    envs_entails Δ1 (WP fill K (Xchg (#l, #fld)%V v) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => HΔ1 Hlookup HΔ2.
    destruct (envs_simple_replace _ _ _ _) as [Δ3 |] eqn:HΔ3; last done.
    rewrite into_laterN_env_sound -wpｰbind' envs_simple_replace_sound //= HΔ2.
    iIntros "(Hl & H)".
    iApply (wpｰxchg with "Hl").
    iSteps.
  Qed.

  Lemma tacｰwpｰcas Δ1 Δ2 Δ3 id p K l fld dq v v1 v2 tid E Φ :
    MaybeIntoLaterNEnvs 1 Δ1 Δ2 →
    envs_lookup_delete true id Δ2 = Some (p, (l +ₗ fld) ↦{dq} v, Δ3)%I →
    ( v ≉ v1 →
      envs_entails Δ2 (WP fill K false%V ∷ tid @ E {{ Φ }})
    ) →
    ( v ≈ v1 →
      envs_entails Δ2 ⌜dq = DfracOwn 1⌝
    ) →
    ( let* Δ4 :=
        envs_app false (Esnoc Enil
          id ((l +ₗ fld) ↦ v2))
          Δ3
      in
      v ≈ v1 →
      envs_entails Δ4 (WP fill K true%V ∷ tid @ E {{ Φ }})
    ) →
    envs_entails Δ1 (WP fill K (CAS (#l, #fld)%V v1 v2) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal. intros HΔ1 (Hlookup & ->)%envs_lookup_delete_Some Hfail Hsuc1 Hsuc2.
    destruct (envs_app _ _ _) as [Δ4 |] eqn:HΔ4; last done.
    rewrite into_laterN_env_sound -wpｰbind' //=.
    iIntros "HΔ2".
    iAssert (▷ ⌜envs_wf Δ2⌝)%I as "#>%Hwf".
    { iDestruct (of_envs_alt with "HΔ2") as "($ & _)". }
    iDestruct (envs_lookup_sound with "HΔ2") as "(Hl & HΔ3)"; first done.
    iAssert (▷ (□ (if p then (l +ₗ fld) ↦{dq} v else True) ∗ (l +ₗ fld) ↦{dq} v))%I with "[Hl]" as "(#Hl_ & Hl)".
    { destruct p; iSteps. }
    iApply (wpｰcas with "Hl"); [done.. |].
    iSplit.
    - iIntros "!> %Hneq Hl".
      iDestruct (envs_lookup_sound_2 with "[Hl HΔ3]") as "HΔ2"; [done.. | |].
      { iFrame. destruct p; iSteps. }
      iApply (Hfail with "HΔ2"); first done.
    - iIntros "!> %Heq Hl".
      iDestruct (envs_lookup_sound_2 with "[Hl HΔ3]") as "HΔ2"; [done.. | |].
      { iFrame. destruct p; iSteps. }
      iDestruct (Hsuc1 with "HΔ2") as %->; [done.. |].
      iDestruct (envs_lookup_sound with "HΔ2") as "(Hl & HΔ3)"; first done.
      rewrite envs_app_sound //= Hsuc2 // bi.intuitionistically_if_elim. iSteps.
  Qed.

  Lemma tacｰwpｰfaa Δ1 Δ2 id K l fld (i1 i2 : Z) tid E Φ :
    MaybeIntoLaterNEnvs 1 Δ1 Δ2 →
    envs_lookup id Δ2 = Some (false, (l +ₗ fld) ↦ #i1)%I →
    ( let* Δ3 :=
        envs_simple_replace id false (Esnoc Enil
          id ((l +ₗ fld) ↦ #(i1 + i2))
        ) Δ2
      in
      envs_entails Δ3 (WP fill K #i1 ∷ tid @ E {{ Φ }})
    ) →
    envs_entails Δ1 (WP fill K (FAA (#l, #fld)%V #i2) ∷ tid @ E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => HΔ1 Hlookup HΔ3.
    destruct (envs_simple_replace _ _ _) as [Δ3 |] eqn:HΔ2; last done.
    rewrite into_laterN_env_sound -wpｰbind' envs_simple_replace_sound //= HΔ3.
    iIntros "(Hl & H)".
    iApply (wpｰfaa with "Hl").
    iSteps.
  Qed.
End zoo۰G.

#[local] Ltac wp۰start tac :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?e _ _ _) =>
      tac e
  | _ =>
      fail "not a 'wp'"
  end.

Tactic Notation "wp۰expr۰eval" tactic3(tac) :=
  wp۰start ltac:(fun e =>
    notypeclasses refine (tacｰwpｰexprｰeval _ e _ _ _ _ _ _);
    [ let x := fresh in
      intros x;
      tac;
      unfold x;
      notypeclasses refine eq_refl
    | idtac
    ]
  ).
Ltac wp۰expr۰simpl :=
  wp۰expr۰eval simpl.

#[local] Ltac wp۰value۰head :=
  lazymatch goal with
  | |- envs_entails _ (wp (Val _) _ _ (λ _, fupd _ _ _)) =>
      eapply tacｰwpｰvalueｰnofupd
  | |- envs_entails _ (wp (Val _) _ _ (λ _, wp _ _ _ _)) =>
      eapply tacｰwpｰvalueｰnofupd
  | |- envs_entails _ (wp (Val _) _ _ _) =>
      eapply tacｰwpｰvalue
  end.
#[local] Ltac wp۰finish :=
  try wp۰expr۰simpl;
  try wp۰value۰head;
  pm_prettify.

#[local] Ltac solve_pure_exec_obligation :=
  simpl; split_and?; done || lia.
Tactic Notation "wp۰pure" open_constr(e_foc) :=
  wp۰start ltac:(fun e =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' e_foc;
      eapply (tacｰwpｰpure _ _ K e');
      [ tc_solve
      | solve_pure_exec_obligation
      | tc_solve
      | wp۰finish
      ]
    )
    || fail "wp۰pure: cannot find" e_foc "in" e "or" e_foc "is not a redex"
  ).
Tactic Notation "wp۰pure" :=
  wp۰pure _.
Tactic Notation "wp۰pures" :=
  first
  [ progress repeat (wp۰pure _; [])
  | wp۰finish
  ].

Tactic Notation "wp۰pure" open_constr(e_foc) "credits:" constr(Hcredits) :=
  wp۰start ltac:(fun e =>
    let Htmp := iFresh in
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' e_foc;
      eapply (tacｰwpｰpureｰcredits _ _ Htmp K e');
      [ tc_solve
      | solve_pure_exec_obligation
      | tc_solve
      | pm_reduce;
        first
        [ iDestructHyp Htmp as Hcredits
        | fail 2 "wp۰pure:" Hcredits "is not fresh"
        ];
        wp۰finish
      ]
    )
    || fail "wp۰pure: cannot find" e_foc "in" e "or" e_foc "is not a redex"
  ).
Tactic Notation "wp۰pure" "credits:" constr(Hcredits) :=
  wp۰pure _ credits:Hcredits.
Tactic Notation "wp۰pures" "credits:" constr(Hcredits) :=
  wp۰pure credits:Hcredits;
  wp۰pures.

Tactic Notation "wp۰pure" open_constr(e_foc) "credit:" constr(Hcredit) :=
  wp۰start ltac:(fun e =>
    let Htmp := iFresh in
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' e_foc;
      eapply (tacｰwpｰpureｰcredit _ _ Htmp K e');
      [ tc_solve
      | solve_pure_exec_obligation
      | tc_solve
      | pm_reduce;
        first
        [ iDestructHyp Htmp as Hcredit
        | fail 2 "wp۰pure:" Hcredit "is not fresh"
        ];
        wp۰finish
      ]
    )
    || fail "wp۰pure: cannot find" e_foc "in" e "or" e_foc "is not a redex"
  ).
Tactic Notation "wp۰pure" "credit:" constr(Hcredit) :=
  wp۰pure _ credit:Hcredit.
Tactic Notation "wp۰pures" "credit:" constr(Hcredit) :=
  wp۰pure credit:Hcredit;
  wp۰pures.

Tactic Notation "wp۰pure" open_constr(e_foc) "steps:" constr(Hsteps_lb) :=
  wp۰start ltac:(fun e =>
    let e := eval simpl in e in
    first
    [ reshape_expr e ltac:(fun K e' =>
        unify e' e_foc;
        eapply (tacｰwpｰpureｰsteps۰lb _ _ (INamed Hsteps_lb) _ _ K e');
        [ tc_solve
        | solve_pure_exec_obligation
        | tc_solve
        | first
          [ iAssumptionCore
          | fail 3 "wp۰pure:" Hsteps_lb "must provide time receipts (⧖ _)"
          ]
        | pm_reduce;
          wp۰finish
        ]
      )
    | fail 1 "wp۰pure: cannot find" e_foc "in" e "or" e_foc "is not a redex"
    ]
  ).
Tactic Notation "wp۰pure" "steps:" constr(Hsteps_lb) :=
  wp۰pure _ steps:Hsteps_lb.
Tactic Notation "wp۰pures" "steps:" constr(Hsteps_lb) :=
  wp۰pure steps:Hsteps_lb;
  wp۰pures.

Tactic Notation "wp۰pure" open_constr(e_foc) "steps:" constr(Hsteps_lb) "credits:" constr(Hcredits) :=
  wp۰start ltac:(fun e =>
    let Htmp := iFresh in
    let e := eval simpl in e in
    first
    [ reshape_expr e ltac:(fun K e' =>
        unify e' e_foc;
        eapply (tacｰwpｰpureｰsteps۰lbｰcredits _ _ (INamed Hsteps_lb) _ _ Htmp K e');
        [ tc_solve
        | solve_pure_exec_obligation
        | tc_solve
        | first
          [ iAssumptionCore
          | fail 3 "wp۰pure:" Hsteps_lb "must provide time receipts (⧖ _)"
          ]
        | pm_reduce;
          first
          [ iDestructHyp Htmp as Hcredits
          | fail 3 "wp۰pure:" Hcredits "is not fresh"
          ];
          wp۰finish
        ]
      )
    | fail 1 "wp۰pure: cannot find" e_foc "in" e "or" e_foc "is not a redex"
    ]
  ).
Tactic Notation "wp۰pure" "steps:" constr(Hsteps_lb) "credits:" constr(Hcredits) :=
  wp۰pure _ steps:Hsteps_lb credits:Hcredits.
Tactic Notation "wp۰pures" "steps:" constr(Hsteps_lb) "credits:" constr(Hcredits) :=
  wp۰pure steps:Hsteps_lb credits:Hcredits;
  wp۰pures.

Tactic Notation "wp۰pure" open_constr(e_foc) "steps:" constr(Hsteps_lb) "credit:" constr(Hcredit) :=
  wp۰start ltac:(fun e =>
    let Htmp := iFresh in
    let e := eval simpl in e in
    first
    [ reshape_expr e ltac:(fun K e' =>
        unify e' e_foc;
        eapply (tacｰwpｰpureｰsteps۰lbｰcredit _ _ (INamed Hsteps_lb) _ _ Htmp K e');
        [ tc_solve
        | solve_pure_exec_obligation
        | tc_solve
        | first
          [ iAssumptionCore
          | fail 3 "wp۰pure:" Hsteps_lb "must provide time receipts (⧖ _)"
          ]
        | pm_reduce;
          first
          [ iDestructHyp Htmp as Hcredit
          | fail 3 "wp۰pure:" Hcredit "is not fresh"
          ];
          wp۰finish
        ]
      )
    | fail 1 "wp۰pure: cannot find" e_foc "in" e "or" e_foc "is not a redex"
    ]
  ).
Tactic Notation "wp۰pure" "steps:" constr(Hsteps_lb) "credit:" constr(Hcredit) :=
  wp۰pure _ steps:Hsteps_lb credit:Hcredit.
Tactic Notation "wp۰pures" "steps:" constr(Hsteps_lb) "credit:" constr(Hcredit) :=
  wp۰pure steps:Hsteps_lb credit:Hcredit;
  wp۰pures.

#[local] Ltac wp۰rec۰aux tac :=
  let H1 := fresh in
  assert (H1 := ValRecｰas_ValRec);
  let H2 := fresh in
  assert (H2 := as_ValRecs'ｰas_ValRecs);
  tac ();
  clear H1 H2.
Tactic Notation "wp۰rec" :=
  wp۰rec۰aux ltac:(fun _ =>
    wp۰pure (App _ _)
  ).
Tactic Notation "wp۰rec" "credits:" constr(Hcredits) :=
  wp۰rec۰aux ltac:(fun _ =>
    wp۰pure (App _ _) credits:Hcredits
  ).
Tactic Notation "wp۰rec" "credit:" constr(Hcredit) :=
  wp۰rec۰aux ltac:(fun _ =>
    wp۰pure (App _ _) credit:Hcredit
  ).
Tactic Notation "wp۰rec" "steps:" constr(Hsteps_lb) :=
  wp۰rec۰aux ltac:(fun _ =>
    wp۰pure (App _ _) steps:Hsteps_lb
  ).
Tactic Notation "wp۰rec" "steps:" constr(Hsteps_lb) "credits:" constr(Hcredits) :=
  wp۰rec۰aux ltac:(fun _ =>
    wp۰pure (App _ _) steps:Hsteps_lb credits:Hcredits
  ).
Tactic Notation "wp۰rec" "steps:" constr(Hsteps_lb) "credit:" constr(Hcredit) :=
  wp۰rec۰aux ltac:(fun _ =>
    wp۰pure (App _ _) steps:Hsteps_lb credit:Hcredit
  ).

Tactic Notation "wp۰for" :=
  let H := fresh in
  assert (H := pureｰfor);
  wp۰pure (For _ _ _);
  clear H.
Tactic Notation "wp۰for" "credits:" constr(Hcredit) :=
  let H := fresh in
  assert (H := pureｰfor);
  wp۰pure (For _ _ _) credits:Hcredit;
  clear H.
Tactic Notation "wp۰for" "credit:" constr(Hcredit) :=
  let H := fresh in
  assert (H := pureｰfor);
  wp۰pure (For _ _ _) credit:Hcredit;
  clear H.

Ltac wp۰bind۰core K :=
  lazymatch eval hnf in K with
  | [] =>
      idtac
  | _ =>
      eapply (tacｰwpｰbind _ K);
      [ simpl; reflexivity
      | pm_prettify
      ]
  end.
Tactic Notation "wp۰bind" open_constr(e_foc) :=
  wp۰start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        unify e' e_foc;
        wp۰bind۰core K
      )
    | fail 1 "wp۰bind: cannot find" e_foc "in" e
    ]
  ).

Tactic Notation "wp۰equal" "as" simple_intropattern(Hfail) "|" simple_intropattern(Hsuc) :=
  wp۰pures;
  wp۰start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tacｰwpｰequal _ _ K)
      )
    | fail 1 "wp۰equal: cannot find 'Equal' in" e
    ];
    [ tc_solve
    | intros Hfail;
      wp۰finish
    | intros Hsuc;
      wp۰finish
    ]
  ).
Tactic Notation "wp۰equal" "as" simple_intropattern(H) :=
  wp۰equal as H | H.
Tactic Notation "wp۰equal" :=
  wp۰equal as ?.

Tactic Notation "wp۰alloc" ident(l) "as" constr(Hheader) constr(Hmeta) constr(Hl) :=
  let Hheader' := Hheader in
  let Hmeta' := iFresh in
  let Hl' := iFresh in
  wp۰pures;
  wp۰start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tacｰwpｰalloc _ _ Hheader' Hmeta' Hl' K)
      )
    | fail 1 "wp۰alloc: cannot find 'Alloc' in" e
    ];
    [ idtac
    | idtac
    | tc_solve
    | first
      [ intros l
      | fail 1 "wp۰alloc:" l "not fresh"
      ];
      pm_reduce;
      first
      [ iDestructHyp Hheader' as Hheader
      | fail 1 "wp۰alloc:" Hheader "is not fresh"
      ];
      first
      [ iDestructHyp Hmeta' as Hmeta
      | fail 1 "wp۰alloc:" Hmeta "is not fresh"
      ];
      first
      [ iDestructHyp Hl' as Hl
      | fail 1 "wp۰alloc:" Hl "is not fresh"
      ];
      wp۰finish
    ]
  ).
Tactic Notation "wp۰alloc" ident(l) "as" constr(Hmeta) constr(Hl) :=
  wp۰alloc l as "_" Hmeta Hl.
Tactic Notation "wp۰alloc" ident(l) "as" constr(Hl) :=
  wp۰alloc l as "_" Hl.
Tactic Notation "wp۰alloc" ident(l) :=
  wp۰alloc l as "?".

Tactic Notation "wp۰block" ident(l) "as" constr(Hheader) constr(Hmeta) constr(Hl) :=
  let Hheader' := iFresh in
  let Hmeta' := iFresh in
  let Hl' := iFresh in
  wp۰pures;
  wp۰start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tacｰwpｰblockｰmutable _ _ Hheader' Hmeta' Hl' K);
        [ simpl; lia
        | fast_done
        | idtac..
        ]
      )
    | fail 1 "wp۰block: cannot find 'Block Mutable in" e
    ];
    [ tc_solve
    | first
      [ intros l
      | fail 1 "wp۰block:" l "not fresh"
      ];
      pm_reduce;
      first
      [ iDestructHyp Hheader' as Hheader
      | fail 1 "wp۰block:" Hheader "is not fresh"
      ];
      first
      [ iDestructHyp Hmeta' as Hmeta
      | fail 1 "wp۰block:" Hmeta "is not fresh"
      ];
      first
      [ iDestructHyp Hl' as Hl
      | fail 1 "wp۰block:" Hl "is not fresh"
      ];
      wp۰finish
    ]
  ).
Tactic Notation "wp۰block" ident(l) "as" constr(Hmeta) constr(Hl) :=
  wp۰block l as "_" Hmeta Hl.
Tactic Notation "wp۰block" ident(l) "as" constr(Hl) :=
  wp۰block l as "_" Hl.
Tactic Notation "wp۰block" ident(l) :=
  wp۰block l as "?".

Tactic Notation "wp۰ref" ident(l) "as" constr(Hheader) constr(Hmeta) constr(Hl) :=
  let Hheader' := Hheader in
  let Hmeta' := iFresh in
  let Hl' := iFresh in
  wp۰pures;
  wp۰start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tacｰwpｰref _ _ Hheader' Hmeta' Hl' K)
      )
    | fail 1 "wp۰ref: cannot find '𝗿𝗲𝗳' in" e
    ];
    [ tc_solve
    | first
      [ intros l
      | fail 1 "wp۰ref:" l "not fresh"
      ];
      pm_reduce;
      first
      [ iDestructHyp Hheader' as Hheader
      | fail 1 "wp۰ref:" Hheader "is not fresh"
      ];
      first
      [ iDestructHyp Hmeta' as Hmeta
      | fail 1 "wp۰ref:" Hmeta "is not fresh"
      ];
      first
      [ iDestructHyp Hl' as Hl
      | fail 1 "wp۰ref:" Hl "is not fresh"
      ];
      wp۰finish
    ]
  ).
Tactic Notation "wp۰ref" ident(l) "as" constr(Hmeta) constr(Hl) :=
  wp۰ref l as "_" Hmeta Hl.
Tactic Notation "wp۰ref" ident(l) "as" constr(Hl) :=
  wp۰ref l as "_" Hl.
Tactic Notation "wp۰ref" ident(l) :=
  wp۰ref l as "?".

Tactic Notation "wp۰block۰generative" simple_intropattern(bid) :=
  wp۰pures;
  wp۰start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tacｰwpｰblockｰgenerative _ _ K);
        [ fast_done
        | idtac..
        ]
      )
    | fail 1 "wp۰block۰generative: cannot find 'Block ImmutableGenerativeStrong' in" e
    ];
    [ tc_solve
    | intros bid;
      wp۰finish
    ]
  ).
Tactic Notation "wp۰block۰generative" :=
  wp۰block۰generative ?.

Tactic Notation "wp۰match" :=
  wp۰pures;
  wp۰start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tacｰwpｰmatch _ _ _ _ K)
      )
    | fail 1 "wp۰match: cannot find 'Match' on location in" e
    ];
    [ tc_solve
    | let l := match goal with |- _ = Some (_, ?l ↦ₕ _)%I => l end in
      first
      [ iAssumptionCore
      | fail 1 "wp۰match: cannot find" l "↦ₕ ?"
      ]
    | try fast_done
    | wp۰finish
    ]
  ).

Ltac wp۰tag :=
  wp۰pures;
  wp۰start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tacｰwpｰtag _ _ _ _ K)
      )
    | fail 1 "wp۰tag: cannot find 'GetTag' in" e
    ];
    [ tc_solve
    | let l := match goal with |- _ = Some (_, ?l ↦ₕ _)%I => l end in
      first
      [ iAssumptionCore
      | fail 1 "wp۰tag: cannot find" l "↦ₕ ?"
      ]
    | wp۰finish
    ]
  ).

Ltac wp۰size :=
  wp۰pures;
  wp۰start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tacｰwpｰsize _ _ _ _ K)
      )
    | fail 1 "wp۰size: cannot find 'GetSize' in" e
    ];
    [ tc_solve
    | let l := match goal with |- _ = Some (_, ?l ↦ₕ _)%I => l end in
      first
      [ iAssumptionCore
      | fail 1 "wp۰size: cannot find" l "↦ₕ ?"
      ]
    | wp۰finish
    ]
  ).

Ltac wp۰load :=
  wp۰pures;
  wp۰start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tacｰwpｰload _ _ _ _ K)
      )
    | fail 1 "wp۰load: cannot find 'Load' in" e
    ];
    [ tc_solve
    | let l := match goal with |- _ = Some (_, (pointsto ?l _ _)) => l end in
      first
      [ iAssumptionCore
      | fail 1 "wp۰load: cannot find" l "↦ ?"
      ]
    | wp۰finish
    ]
  ).

Ltac wp۰store :=
  wp۰pures;
  wp۰start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tacｰwpｰstore _ _ _ K)
      )
    | fail 1 "wp۰store: cannot find 'Store' in" e
    ];
    [ tc_solve
    | let l := match goal with |- _ = Some (_, (pointsto ?l _ _)) => l end in
      first
      [ iAssumptionCore
      | fail 1 "wp۰store: cannot find" l "↦ ?"
      ]
    | pm_reduce;
      wp۰finish
    ]
  ).

Ltac wp۰xchg :=
  wp۰pures;
  wp۰start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tacｰwpｰxchg _ _ _ K)
      )
    | fail 1 "wp۰xchg: cannot find 'Xchg in" e
    ];
    [ tc_solve
    | let l := match goal with |- _ = Some (_, (pointsto ?l _ _)) => l end in
      first
      [ iAssumptionCore
      | fail 1 "wp۰xchg: cannot find" l "↦ ?"
      ]
    | pm_reduce;
      wp۰finish
    ]
  ).

Tactic Notation "wp۰cas" "as" simple_intropattern(Hfail) "|" simple_intropattern(Hsuc) :=
  wp۰pures;
  wp۰start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tacｰwpｰcas _ _ _ _ _ K)
      )
    | fail 1 "wp۰cas: cannot find 'CAS' with literal arguments in" e
    ];
    [ tc_solve
    | let l := match goal with |- _ = Some (_, (pointsto ?l _ _), _) => l end in
      first
      [ iAssumptionCore
      | fail 1 "wp۰cas: cannot find" l "↦ ?"
      ]
    | intros Hfail;
      wp۰finish
    | intros Hsuc;
      try (iPureIntro; fast_done)
    | pm_reduce;
      intros Hsuc;
      wp۰finish
    ]
  ).
Tactic Notation "wp۰cas" "as" simple_intropattern(H) :=
  wp۰cas as H | H.
Tactic Notation "wp۰cas" :=
  wp۰cas as ?.

Ltac wp۰faa :=
  wp۰pures;
  wp۰start ltac:(fun e =>
    first
    [ reshape_expr e ltac:(fun K e' =>
        eapply (tacｰwpｰfaa _ _ _ K)
      )
    | fail 1 "wp۰faa: cannot find 'FAA' in" e
    ];
    [ tc_solve
    | let l := match goal with |- _ = Some (_, (pointsto ?l _ _)) => l end in
      first
      [ iAssumptionCore
      | fail "wp۰faa: cannot find" l "↦ ?"
      ]
    | pm_reduce;
      wp۰finish
    ]
  ).

#[local] Ltac wp۰apply۰core lemma tac_suc tac_fail :=
  first
  [ iPoseProofCore lemma as false (fun H =>
      wp۰start ltac:(fun e =>
       reshape_expr e ltac:(fun K e' =>
         wp۰bind۰core K;
         tac_suc H
       )
      )
    )
  | tac_fail ltac:(fun _ =>
      wp۰apply۰core lemma tac_suc tac_fail
    )
  | let P := type of lemma in
    fail "wp۰apply: cannot apply" lemma ":" P
  ].

Tactic Notation "wp۰apply" open_constr(lemma) :=
  wp۰apply۰core lemma
    ltac:(fun H => iApplyHyp H; try iNext; try wp۰expr۰simpl)
    ltac:(fun _ => fail).
Tactic Notation "wp۰apply" open_constr(lemma) "as"
  constr(pat)
:=
  wp۰apply lemma; last iIntros pat.
Tactic Notation "wp۰apply" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
  ")"
  constr(pat)
:=
  wp۰apply lemma; last iIntros ( x1 ) pat.
Tactic Notation "wp۰apply" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
      simple_intropattern(x2)
  ")"
  constr(pat)
:=
  wp۰apply lemma; last iIntros ( x1 x2 ) pat.
Tactic Notation "wp۰apply" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
      simple_intropattern(x2)
      simple_intropattern(x3)
  ")"
  constr(pat)
:=
  wp۰apply lemma; last iIntros ( x1 x2 x3 ) pat.
Tactic Notation "wp۰apply" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
      simple_intropattern(x2)
      simple_intropattern(x3)
      simple_intropattern(x4)
  ")"
  constr(pat)
:=
  wp۰apply lemma; last iIntros ( x1 x2 x3 x4 ) pat.
Tactic Notation "wp۰apply" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
      simple_intropattern(x2)
      simple_intropattern(x3)
      simple_intropattern(x4)
      simple_intropattern(x5)
  ")"
  constr(pat)
:=
  wp۰apply lemma; last iIntros ( x1 x2 x3 x4 x5 ) pat.
Tactic Notation "wp۰apply" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
      simple_intropattern(x2)
      simple_intropattern(x3)
      simple_intropattern(x4)
      simple_intropattern(x5)
      simple_intropattern(x6)
  ")"
  constr(pat)
:=
  wp۰apply lemma; last iIntros ( x1 x2 x3 x4 x5 x6 ) pat.
Tactic Notation "wp۰apply" open_constr(lemma) "as"
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
  wp۰apply lemma; last iIntros ( x1 x2 x3 x4 x5 x6 x7 ) pat.
Tactic Notation "wp۰apply" open_constr(lemma) "as"
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
  wp۰apply lemma; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat.
Tactic Notation "wp۰apply" open_constr(lemma) "as"
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
  wp۰apply lemma; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ) pat.
Tactic Notation "wp۰apply" open_constr(lemma) "as"
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
  wp۰apply lemma; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) pat.

Tactic Notation "wp۰apply+" open_constr(lemma) :=
  wp۰apply۰core lemma
    ltac:(fun H =>
      iApplyHyp H;
      try iNext;
      try wp۰expr۰simpl
    )
    ltac:(fun retry =>
      wp۰pure _; [];
      retry ()
    ).
Tactic Notation "wp۰apply+" open_constr(lemma) "as"
  constr(pat)
:=
  wp۰apply+ lemma; last iIntros pat.
Tactic Notation "wp۰apply+" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
  ")"
  constr(pat)
:=
  wp۰apply+ lemma; last iIntros ( x1 ) pat.
Tactic Notation "wp۰apply+" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
      simple_intropattern(x2)
  ")"
  constr(pat)
:=
  wp۰apply+ lemma; last iIntros ( x1 x2 ) pat.
Tactic Notation "wp۰apply+" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
      simple_intropattern(x2)
      simple_intropattern(x3)
  ")"
  constr(pat)
:=
  wp۰apply+ lemma; last iIntros ( x1 x2 x3 ) pat.
Tactic Notation "wp۰apply+" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
      simple_intropattern(x2)
      simple_intropattern(x3)
      simple_intropattern(x4)
  ")"
  constr(pat)
:=
  wp۰apply+ lemma; last iIntros ( x1 x2 x3 x4 ) pat.
Tactic Notation "wp۰apply+" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
      simple_intropattern(x2)
      simple_intropattern(x3)
      simple_intropattern(x4)
      simple_intropattern(x5)
  ")"
  constr(pat)
:=
  wp۰apply+ lemma; last iIntros ( x1 x2 x3 x4 x5 ) pat.
Tactic Notation "wp۰apply+" open_constr(lemma) "as"
  "(" simple_intropattern(x1)
      simple_intropattern(x2)
      simple_intropattern(x3)
      simple_intropattern(x4)
      simple_intropattern(x5)
      simple_intropattern(x6)
  ")"
  constr(pat)
:=
  wp۰apply+ lemma; last iIntros ( x1 x2 x3 x4 x5 x6 ) pat.
Tactic Notation "wp۰apply+" open_constr(lemma) "as"
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
  wp۰apply+ lemma; last iIntros ( x1 x2 x3 x4 x5 x6 x7 ) pat.
Tactic Notation "wp۰apply+" open_constr(lemma) "as"
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
  wp۰apply+ lemma; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat.
Tactic Notation "wp۰apply+" open_constr(lemma) "as"
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
  wp۰apply+ lemma; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ) pat.
Tactic Notation "wp۰apply+" open_constr(lemma) "as"
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
  wp۰apply+ lemma; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) pat.

Tactic Notation "awp۰apply" open_constr(lemma) :=
  wp۰apply۰core lemma
    ltac:(fun H => iApplyHyp H; pm_prettify)
    ltac:(fun _ => fail);
  last iAuIntro.
Tactic Notation "awp۰apply" open_constr(lemma) "without" constr(Hs) :=
  let Hs := String.words Hs in
  let Hs := eval vm_compute in (INamed <$> Hs) in
  wp۰apply۰core lemma
    ltac:(fun H =>
      iApply (wpｰframeｰwand with [SGoal $ SpecGoal GSpatial false [] Hs false]);
      [ iAccu
      | iApplyHyp H;
        pm_prettify
      ]
    )
    ltac:(fun _ =>
      fail
    );
  last iAuIntro.

Tactic Notation "awp۰apply+" open_constr(lemma) :=
  wp۰apply۰core lemma
    ltac:(fun H =>
      iApplyHyp H
    )
    ltac:(fun retry =>
      wp۰pure _; [];
      retry ()
    );
  last iAuIntro.
Tactic Notation "awp۰apply+" open_constr(lemma) "without" constr(Hs) :=
  let Hs := String.words Hs in
  let Hs := eval vm_compute in (INamed <$> Hs) in
  wp۰apply۰core lemma
    ltac:(fun H =>
      iApply (wpｰframeｰwand with [SGoal $ SpecGoal GSpatial false [] Hs false]);
      [ iAccu
      | iApplyHyp H;
        pm_prettify
      ]
    )
    ltac:(fun retry =>
      wp۰pure _; [];
      retry ()
    );
  last iAuIntro.
