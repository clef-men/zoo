Require Import Stdlib.Logic.FunctionalExtensionality.

Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.common.function.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Export zoo_std.inf_array__code.
Require Import zoo_std.array.
Require Import zoo_std.inf_array__types.
Require Import zoo_std.int.
Require Import zoo_std.mutex.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type l : location.
Implicit Type pid : prophet_id.
Implicit Type v v_resolve t fn : val.
Implicit Type us : list val.
Implicit Type vs : nat → val.

Class InfArrayG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] inf_array۰G۰mutex۰G :: MutexG Σ
  ; #[local] inf_array۰G۰model۰G :: TwinsG Σ (nat -d> val_O)
  }.

Definition inf_array۰Σ :=
  #[mutex۰Σ
  ; twins۰Σ (nat -d> val_O)
  ].
#[global] Instance subG𑁒inf_array۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG inf_array۰Σ Σ →
  InfArrayG Σ .
Proof.
  solve_inG.
Qed.

Section inf_array۰G.
  Context `{inf_array۰G : InfArrayG Σ}.

  Record metadata :=
    { metadata۰default : val
    ; metadata۰model : gname
    }.
  Implicit Type γ : metadata.

  #[local] Instance metadata𑁒eq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[local] Instance metadata𑁒countable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition model₁' γ_model vs :=
    twins۰twin₁ γ_model (DfracOwn 1) vs.
  #[local] Definition model₁ γ vs :=
    model₁' γ.(metadata۰model) vs.
  #[local] Definition model₂' γ_model vs :=
    twins۰twin₂ γ_model vs.
  #[local] Definition model₂ γ vs :=
    model₂' γ.(metadata۰model) vs.

  #[local] Definition inv₂ l γ us : iProp Σ :=
    ∃ data vs,
    l.[data] ↦ data ∗
    array۰model data (DfracOwn 1) us ∗
    model₂ γ vs ∗
    ⌜vs = λ i, if decide (i < length us) then us !!! i else γ.(metadata۰default)⌝.
  #[local] Instance : CustomIpat "inv₂" :=
    " ( %data
      & %vs
      & Hl_data
      & Hdata
      & Hmodel₂
      & %Hvs
      )
    ".
  #[local] Definition inv₁ l γ : iProp Σ :=
    ∃ us,
    inv₂ l γ us.
  #[local] Instance : CustomIpat "inv₁" :=
    " ( %us{}
      & {{lazy}Hinv;(:inv₂)}
      )
    ".
  Definition inf_array۰inv t : iProp Σ :=
    ∃ l γ mtx,
    ⌜t = #l⌝ ∗
    l ↪ γ ∗
    l.[default] ↦□ γ.(metadata۰default) ∗
    l.[mutex] ↦□ mtx ∗
    mutex۰inv mtx (inv₁ l γ).
  #[local] Instance : CustomIpat "inv" :=
    " ( %l
      & %γ
      & %mtx
      & ->
      & #Hmeta
      & #Hl_mtx
      & #Hl_default
      & #Hmtx_inv
      )
    ".

  Definition inf_array۰model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    l ↪ γ ∗
    model₁ γ vs.
  #[local] Instance : CustomIpat "model" :=
    " ( %l_
      & %γ_
      & %Heq
      & #Hmeta_
      & Hmodel₁
      )
    ".
  Definition inf_array۰model' t vsₗ vsᵣ :=
    inf_array۰model t (
      λ i,
        if decide (i < length vsₗ) then vsₗ !!! i else vsᵣ (i - length vsₗ)
    ).

  #[global] Instance inf_array۰inv𑁒persistent t :
    Persistent (inf_array۰inv t).
  Proof.
    apply _.
  Qed.

  #[global] Instance inf_array۰model𑁒ne t n :
    Proper (pointwise_relation nat (=) ==> (≡{n}≡)) (inf_array۰model t).
  Proof.
    intros vs1 vs2 ->%functional_extensionality. done.
  Qed.
  #[global] Instance inf_array۰model𑁒proper t :
    Proper (pointwise_relation nat (=) ==> (≡)) (inf_array۰model t).
  Proof.
    intros vs1 vs2 Hvs. rewrite equiv_dist. solve_proper.
  Qed.

  #[global] Instance inf_array۰model𑁒timeless t vs :
    Timeless (inf_array۰model t vs).
  Proof.
    apply _.
  Qed.

  #[global] Instance inf_array۰model'𑁒ne t n :
    Proper ((=) ==> pointwise_relation nat (=) ==> (≡{n}≡)) (inf_array۰model' t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance inf_array۰model'𑁒proper t :
    Proper ((=) ==> pointwise_relation nat (=) ==> (≡)) (inf_array۰model' t).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance inf_array۰model'𑁒timeless t vsₗ vsᵣ :
    Timeless (inf_array۰model' t vsₗ vsᵣ).
  Proof.
    apply _.
  Qed.

  #[local] Lemma model𑁒alloc default :
    ⊢ |==>
      ∃ γ_model,
      model₁' γ_model (λ _, default) ∗
      model₂' γ_model (λ _, default).
  Proof.
    apply twins𑁒alloc'.
  Qed.
  #[local] Lemma model𑁒agree γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₂ γ vs2 -∗
    ⌜vs1 = vs2⌝.
  Proof.
    iIntros "Hmodel₁ Hmodel₂".
    iDestruct (twins𑁒agree𑁒discrete with "Hmodel₁ Hmodel₂") as %->%functional_extensionality.
    iSteps.
  Qed.
  #[local] Lemma model𑁒update {γ vs1 vs2} vs :
    model₁ γ vs1 -∗
    model₂ γ vs2 ==∗
      model₁ γ vs ∗
      model₂ γ vs.
  Proof.
    apply twins𑁒update.
  Qed.

  Lemma inf_array۰model𑁒to𑁒model' {t vs} vsₗ :
    (∀ i v, vsₗ !! i = Some v → vs i = v) →
    inf_array۰model t vs ⊢
    inf_array۰model' t vsₗ (λ i, vs (length vsₗ + i)).
  Proof.
    intros Hvs.
    rewrite /inf_array۰model' inf_array۰model𑁒proper; last done.
    intros i. case_decide.
    - apply Hvs, list_lookup_lookup_total_lt. done.
    - rewrite -Nat.le_add_sub //; first lia.
  Qed.
  Lemma inf_array۰model𑁒to𑁒model'𑁒replicate {t vs} n v :
    (∀ i, i < n → vs i = v) →
    inf_array۰model t vs ⊢
    inf_array۰model' t (replicate n v) (λ i, vs (n + i)).
  Proof.
    intros Hvs.
    rewrite -{2}(length_replicate n v).
    apply inf_array۰model𑁒to𑁒model'. intros i v_ (-> & Hi)%lookup_replicate.
    auto.
  Qed.
  Lemma inf_array۰model𑁒to𑁒model'𑁒constant {t v} n :
    inf_array۰model t (λ _, v) ⊢
    inf_array۰model' t (replicate n v) (λ _, v).
  Proof.
    apply: inf_array۰model𑁒to𑁒model'𑁒replicate. done.
  Qed.

  Lemma inf_array۰model'𑁒shift t vsₗ v vsᵣ :
    inf_array۰model' t (vsₗ ++ [v]) vsᵣ ⊣⊢
    inf_array۰model' t vsₗ (v .: vsᵣ).
  Proof.
    rewrite /inf_array۰model' inf_array۰model𑁒proper; last done.
    intros j. simpl_length/=.
    destruct (Nat.lt_total j (length vsₗ)) as [| [-> |]].
    - rewrite !decide_True; try lia.
      rewrite lookup_total_app_l //.
    - rewrite decide_True; first lia.
      rewrite decide_False; first lia.
      rewrite lookup_total_app_r //.
      rewrite Nat.sub_diag //.
    - rewrite !decide_False; try lia.
      rewrite /scons. case_match; [lia | f_equal; lia].
  Qed.
  Lemma inf_array۰model'𑁒shift𑁒r t vsₗ v vsᵣ :
    inf_array۰model' t (vsₗ ++ [v]) vsᵣ ⊢
    inf_array۰model' t vsₗ (v .: vsᵣ).
  Proof.
    rewrite inf_array۰model'𑁒shift. iSteps.
  Qed.
  Lemma inf_array۰model'𑁒shift𑁒l t vsₗ vsᵣ v vsᵣ' :
    vsᵣ ≡ᶠ v .: vsᵣ' →
    inf_array۰model' t vsₗ vsᵣ ⊢
    inf_array۰model' t (vsₗ ++ [v]) vsᵣ'.
  Proof.
    intros.
    rewrite inf_array۰model'𑁒shift inf_array۰model'𑁒proper //.
  Qed.
  Lemma inf_array۰model'𑁒shift𑁒l' t vsₗ vsᵣ :
    inf_array۰model' t vsₗ vsᵣ ⊢
    inf_array۰model' t (vsₗ ++ [vsᵣ 0]) (vsᵣ ∘ S).
  Proof.
    rewrite inf_array۰model'𑁒shift𑁒l //.
    intros []; done.
  Qed.

  Lemma inf_array٠create𑁒spec default :
    {{{
      True
    }}}
      inf_array٠create default
    {{{
      t
    , RET t;
      inf_array۰inv t ∗
      inf_array۰model t (λ _, default)
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.
    wp۰apply (array٠create𑁒spec with "[//]") as "%data Hdata".
    wp۰apply+ (mutex٠create𑁒spec𑁒init with "[//]") as (mtx) "Hmtx_init".
    wp۰block l as "Hmeta" "(Hl_data & Hl_default & Hl_mtx & _)".
    iMod (pointsto𑁒persist with "Hl_default") as "#Hl_default".

    iMod (model𑁒alloc default) as "(%γ_model & Hmodel₁ & Hmodel₂)".

    pose γ :=
      {|metadata۰default := default
      ; metadata۰model := γ_model
      |}.
    iMod (meta𑁒set γ with "Hmeta") as "#Hmeta"; first done.

    iMod (mutex۰init𑁒to𑁒inv (inv₁ l γ) with "Hmtx_init [Hl_data Hdata Hmodel₂]") as "#Hmtx_inv".
    { rewrite /inv₁. iSteps. }
    iSteps.
  Qed.

  #[local] Lemma inf_array٠next_capacity𑁒spec n :
    (0 ≤ n)%Z →
    {{{
      True
    }}}
      inf_array٠next_capacity #n
    {{{
      m
    , RET #m;
      ⌜n ≤ m⌝%Z
    }}}.
  Proof.
    iSteps.
  Qed.
  #[local] Lemma inf_array٠reserve𑁒spec l γ us n :
    (0 ≤ n)%Z →
    {{{
      l.[default] ↦□ γ.(metadata۰default) ∗
      inv₂ l γ us
    }}}
      inf_array٠reserve #l #n
    {{{
      us
    , RET ();
      inv₂ l γ us ∗
      ⌜₊n ≤ length us⌝
    }}}.
  Proof.
    iIntros "%Hn %Φ (#Hl_default & (:inv₂)) HΦ".

    wp۰rec. wp۰load.
    wp۰apply+ (array٠size𑁒spec with "Hdata") as "Hdata".
    wp۰pures. case_bool_decide; last iSteps.
    wp۰apply+ (inf_array٠next_capacity𑁒spec with "[//]") as (?) "%"; first lia.
    wp۰apply int٠max𑁒spec.
    wp۰load.
    wp۰apply+ (array٠unsafe_grow𑁒spec with "Hdata") as (data') "(Hdata & Hdata')"; first lia.
    wp۰store.

    iSteps; iPureIntro; simpl_length; last lia.
    apply functional_extensionality => i. rewrite Hvs.
    case_decide; last case_decide.
    - rewrite decide_True; first lia.
      rewrite lookup_total_app_l //.
    - rewrite lookup_total_app_r; first lia.
      rewrite lookup_total_replicate_2 //; first lia.
    - done.
  Qed.

  Lemma inf_array٠get𑁒spec t i :
    (0 ≤ i)%Z →
    <<<
      inf_array۰inv t
    | ∀∀ vs,
      inf_array۰model t vs
    >>>
      inf_array٠get t #i
    <<<
      inf_array۰model t vs
    | RET vs ₊i;
      £ 1
    >>>.
  Proof.
    iIntros "% %Φ (:inv) HΦ".

    wp۰rec credit:"H£". wp۰load.
    wp۰apply (mutex٠protect𑁒spec Φ with "[$Hmtx_inv H£ HΦ]"); last iSteps. iIntros "$ (:inv₁)".
    wp۰load.
    wp۰apply+ (array٠size𑁒spec with "Hdata") as "Hdata".
    wp۰pures. case_decide.

    - rewrite bool_decide_eq_true_2; first lia.
      iApply wp𑁒fupd.
      wp۰apply+ (array٠unsafe_get𑁒spec with "Hdata"); [done | | done |].
      { rewrite list_lookup_lookup_total_lt //. lia. }

      iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.

      rewrite /inv₁. iSteps.
      rewrite Hvs decide_True; first lia. iSteps.

    - rewrite bool_decide_eq_false_2; first lia. wp۰load.

      iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[$Hmodel₁] H£") as "HΦ"; first iSteps.

      rewrite /inv₁. iSteps.
      rewrite Hvs decide_False; first lia. iSteps.
  Qed.
  Lemma inf_array٠get𑁒spec' t i :
    (0 ≤ i)%Z →
    <<<
      inf_array۰inv t
    | ∀∀ vsₗ vsᵣ,
      inf_array۰model' t vsₗ vsᵣ
    >>>
      inf_array٠get t #i
    <<<
      inf_array۰model' t vsₗ vsᵣ
    | RET
        if decide (₊i < length vsₗ) then
          vsₗ !!! ₊i
        else
          vsᵣ (₊i - length vsₗ);
      £ 1
    >>>.
  Proof.
    iIntros "% %Φ Hinv HΦ".
    awp۰apply (inf_array٠get𑁒spec with "Hinv"); first done.
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vsₗ %vsᵣ Hmodel".
    iAaccIntro with "Hmodel"; iSteps.
  Qed.

  Lemma inf_array٠update𑁒spec Ψ1 Ψ2 t i fn :
    (0 ≤ i)%Z →
    <<<
      inf_array۰inv t ∗
      (∀ v, Ψ1 v -∗ WP fn v {{ Ψ2 v }})
    | ∀∀ vs,
      inf_array۰model t vs ∗
      □ Ψ1 (vs ₊i)
    >>>
      inf_array٠update t #i fn
    <<<
      ∃∃ v,
      inf_array۰model t (<[₊i := v]> vs) ∗
      Ψ2 (vs ₊i) v
    | RET vs ₊i;
      £ 1
    >>>.
  Proof.
    iIntros "% %Φ ((:inv) & Hfn) HΦ".

    wp۰rec credit:"H£". wp۰load.
    wp۰apply (mutex٠protect𑁒spec Φ with "[$Hmtx_inv Hfn H£ HΦ]"); last iSteps. iIntros "$ (:inv₁ =1 lazy=)".
    wp۰apply+ (inf_array٠reserve𑁒spec with "[$]") as "%us2 ((:inv₂) & %)"; first lia.
    wp۰load.

    destruct (lookup_lt_is_Some_2 us2 ₊i) as (v & Hlookup); first lia.
    iApply fupd𑁒wp.
    iMod "HΦ" as "(%vs_ & ((:model) & #Hv) & HΦ & _)". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
    assert (vs ₊i = v) as Hv.
    { rewrite Hvs decide_True; first lia.
      apply list_lookup_total_correct. done.
    }
    rewrite Hv.
    iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
    iModIntro.

    wp۰apply (array٠unsafe_get𑁒spec with "Hdata") as "Hdata"; [lia | done.. |].
    wp۰apply+ (wp𑁒wand with "(Hfn Hv)") as (w) "Hw".
    wp۰load.
    wp۰apply+ (array٠unsafe_set𑁒spec with "Hdata") as "Hdata"; first lia.
    wp۰pures.

    iMod "HΦ" as "(%vs_ & ((:model) & _) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
    iMod (model𑁒update (<[₊i := w]> vs) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[$Hmodel₁ Hw] H£") as "HΦ"; first naive_solver.

    iFrame. rewrite Hv. iSplitR "HΦ"; last iSteps. iPureIntro.
    rewrite length_insert Hvs.
    apply functional_extensionality => j.
    destruct_decide (j = ₊i) as -> | ?.
    - rewrite fn_lookup_insert decide_True; first lia.
      rewrite list_lookup_total_insert_eq //. lia.
    - rewrite fn_lookup_insert_ne //. case_decide; last done.
      rewrite list_lookup_total_insert_ne //.
  Qed.

  Lemma inf_array٠xchg𑁒spec t i v :
    (0 ≤ i)%Z →
    <<<
      inf_array۰inv t
    | ∀∀ vs,
      inf_array۰model t vs
    >>>
      inf_array٠xchg t #i v
    <<<
      inf_array۰model t (<[₊i := v]> vs)
    | RET vs ₊i;
      £ 1
    >>>.
  Proof.
    iIntros "% %Φ Hinv HΦ".

    wp۰rec.
    awp۰apply+ (inf_array٠update𑁒spec (λ _, True)%I (λ _ w, ⌜w = v⌝)%I with "[$Hinv]"); [done | iSteps |].
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs Hmodel".
    iAaccIntro with "[$Hmodel]"; iSteps.
  Qed.

  Lemma inf_array٠xchg_resolve𑁒spec t i v pid v_resolve Φ E :
    (0 ≤ i)%Z →
    inf_array۰inv t -∗
    ( |={⊤,E}=>
      ∃ vs,
      inf_array۰model t vs ∗
      ( ∀ e,
        ⌜PureExec True 1 e ()⌝ -∗
        ⌜to_val e = None⌝ -∗
        inf_array۰model t (<[₊i := v]> vs) -∗
        WP Resolve e #pid v_resolve @ E {{ _,
          |={E,⊤}=>
          Φ (vs ₊i)
        }}
      )
    ) -∗
    WP inf_array٠xchg_resolve t #i v #pid v_resolve {{ Φ }}.
  Proof.
    iIntros "% (:inv) HΦ".

    wp۰rec. wp۰load.
    wp۰apply (mutex٠protect𑁒spec Φ with "[$Hmtx_inv HΦ]"); last iSteps. iIntros "$ (:inv₁ =1 lazy=)".
    wp۰apply+ (inf_array٠reserve𑁒spec with "[$]") as "%us2 ((:inv₂) & %)"; first lia.
    wp۰load.

    destruct (lookup_lt_is_Some_2 us2 ₊i) as (w & Hlookup); first lia.
    assert (vs ₊i = w) as Hw.
    { rewrite Hvs decide_True; first lia.
      apply list_lookup_total_correct. done.
    }

    wp۰apply (array٠unsafe_get𑁒spec with "Hdata") as "Hdata"; [lia | done.. |].
    wp۰load.
    wp۰apply+ (array٠unsafe_set𑁒spec with "Hdata") as "Hdata"; first lia.
    wp۰pures.

    set vs' := <[₊i := v]> vs.
    wp۰bind (Resolve _ _ _).
    wp۰apply (wp𑁒wand (λ _,
      model₂ γ vs' ∗
      Φ w
    )%I with "[Hmodel₂ HΦ]") as (?) "(Hmodel₂ & HΦ)".
    { iMod "HΦ" as "(%vs_ & (:model) & HΦ)". injection Heq as <-.
      iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
      iMod (model𑁒update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & $)".
      rewrite Hw.
      wp۰apply (wp𑁒wand with "(HΦ [%] [%] [Hmodel₁])") as (?) "$".
      { done. }
      { iSteps. }
    }

    wp۰pures.
    iFrame. iPureIntro.
    rewrite /vs' length_insert Hvs.
    apply functional_extensionality => j.
    destruct_decide (j = ₊i) as -> | ?.
    - rewrite fn_lookup_insert decide_True; first lia.
      rewrite list_lookup_total_insert_eq //. lia.
    - rewrite fn_lookup_insert_ne //. case_decide; last done.
      rewrite list_lookup_total_insert_ne //.
  Qed.

  Lemma inf_array٠set𑁒spec t i v :
    (0 ≤ i)%Z →
    <<<
      inf_array۰inv t
    | ∀∀ vs,
      inf_array۰model t vs
    >>>
      inf_array٠set t #i v
    <<<
      inf_array۰model t (<[₊i := v]> vs)
    | RET ();
      £ 1
    >>>.
  Proof.
    iIntros "% %Φ Hinv HΦ".

    wp۰rec.
    wp۰apply+ (inf_array٠xchg𑁒spec with "Hinv"); first done.
    iApply (atomic_update𑁒wand with "HΦ").
    iSteps.
  Qed.
  Lemma inf_array٠set𑁒spec' t i v :
    (0 ≤ i)%Z →
    <<<
      inf_array۰inv t
    | ∀∀ vsₗ vsᵣ,
      inf_array۰model' t vsₗ vsᵣ
    >>>
      inf_array٠set t #i v
    <<<
      if decide (₊i < length vsₗ) then
        inf_array۰model' t (<[₊i := v]> vsₗ) vsᵣ
      else
        inf_array۰model' t vsₗ (<[₊i - length vsₗ := v]> vsᵣ)
    | RET ();
      £ 1
    >>>.
  Proof.
    iIntros "% %Φ Hinv HΦ".
    awp۰apply (inf_array٠set𑁒spec with "Hinv"); first done.
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vsₗ %vsᵣ Hmodel".
    iAaccIntro with "Hmodel"; first iSteps. iIntros "Hmodel !>".
    iSplitL "Hmodel"; last iSteps.
    Z_to_nat i. rewrite Nat2Z.id. case_decide.
    all: iApply (inf_array۰model𑁒proper with "Hmodel"); intros j.
    - simpl_length. case_decide.
      + destruct_decide (j = i) as -> | ?.
        * rewrite list_lookup_total_insert_eq // fn_lookup_insert //.
        * rewrite list_lookup_total_insert_ne // fn_lookup_insert_ne // decide_True //.
      + rewrite fn_lookup_insert_ne; first lia.
        rewrite decide_False //.
    - case_decide.
      + rewrite fn_lookup_insert_ne; first lia.
        rewrite decide_True //.
      + destruct_decide (j = i) as -> | ?.
        * rewrite !fn_lookup_insert //.
        * rewrite !fn_lookup_insert_ne; try lia.
          rewrite decide_False //.
  Qed.

  Lemma inf_array٠cas𑁒spec t i v1 v2 :
    (0 ≤ i)%Z →
    <<<
      inf_array۰inv t
    | ∀∀ vs,
      inf_array۰model t vs
    >>>
      inf_array٠cas t #i v1 v2
    <<<
      ∃∃ b,
      ⌜(if b then (≈) else (≉)) (vs ₊i) v1⌝ ∗
      inf_array۰model t (if b then <[₊i := v2]> vs else vs)
    | RET #b;
      £ 1
    >>>.
  Proof.
    iIntros "% %Φ (:inv) HΦ".

    wp۰rec credit:"H£". wp۰load.
    wp۰apply (mutex٠protect𑁒spec Φ with "[$Hmtx_inv H£ HΦ]"); last iSteps. iIntros "$ (:inv₁ =1 lazy=)".
    wp۰apply+ (inf_array٠reserve𑁒spec with "[$]") as "%us2 ((:inv₂) & %)"; first lia.
    wp۰load.

    destruct (lookup_lt_is_Some_2 us2 ₊i) as (v & Hlookup); first lia.
    assert (vs ₊i = v) as Hv.
    { rewrite Hvs decide_True; first lia.
      apply list_lookup_total_correct. done.
    }

    wp۰apply (array٠unsafe_get𑁒spec with "Hdata") as "Hdata"; [lia | done.. |].
    wp۰apply wp𑁒equal𑁒nobranch as (b) "%".
    wp۰pures.

    wp۰bind (if: _ then _ else _)%E.
    wp۰apply (wp𑁒wand (λ res,
      l.[data] ↦ data ∗
      array۰model data (DfracOwn 1) (if b then <[₊i := v2]> us2 else us2)
    )%I with "[Hl_data Hdata]") as (res) "(Hl_data & Hdata)".
    { destruct b; last iSteps.
      wp۰load.
      wp۰apply (array٠unsafe_set𑁒spec with "Hdata") as "Hdata"; first lia.
      iSteps.
    }

    wp۰pures.

    iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
    set vs' := if b then <[₊i := v2]> vs else vs.
    iMod (model𑁒update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" $! b with "[Hmodel₁] H£") as "$".
    { rewrite Hv. iSteps. }

    iFrame. iPureIntro.
    destruct b; last done.
    rewrite /vs' length_insert Hvs.
    apply functional_extensionality => j.
    destruct_decide (j = ₊i) as -> | ?.
    - rewrite fn_lookup_insert decide_True; first lia.
      rewrite list_lookup_total_insert_eq //. lia.
    - rewrite fn_lookup_insert_ne //. case_decide; last done.
      rewrite list_lookup_total_insert_ne //.
  Qed.

  Lemma inf_array٠cas_resolve𑁒spec t i v1 v2 pid v_resolve Φ E :
    (0 ≤ i)%Z →
    inf_array۰inv t -∗
    ( |={⊤,E}=>
      ∃ vs,
      inf_array۰model t vs ∗
      ( ∀ e b,
        ⌜PureExec True 1 e ()⌝ -∗
        ⌜to_val e = None⌝ -∗
        ⌜(if b then (≈) else (≉)) (vs ₊i) v1⌝ -∗
        inf_array۰model t (if b then <[₊i := v2]> vs else vs) -∗
        WP Resolve e #pid v_resolve @ E {{ _,
          |={E,⊤}=>
          Φ #b
        }}
      )
    ) -∗
    WP inf_array٠cas_resolve t #i v1 v2 #pid v_resolve {{ Φ }}.
  Proof.
    iIntros "% (:inv) HΦ".

    wp۰rec. wp۰load.
    wp۰apply (mutex٠protect𑁒spec Φ with "[$Hmtx_inv HΦ]"); last iSteps. iIntros "$ (:inv₁ =1 lazy=)".
    wp۰apply+ (inf_array٠reserve𑁒spec with "[$]") as "%us2 ((:inv₂) & %)"; first lia.
    wp۰load.

    destruct (lookup_lt_is_Some_2 us2 ₊i) as (v & Hlookup); first lia.
    assert (vs ₊i = v) as Hv.
    { rewrite Hvs decide_True; first lia.
      apply list_lookup_total_correct. done.
    }

    wp۰apply (array٠unsafe_get𑁒spec with "Hdata") as "Hdata"; [lia | done.. |].
    wp۰apply wp𑁒equal𑁒nobranch as (b) "%".
    wp۰pures.

    wp۰bind (if: _ then _ else _)%E.
    wp۰apply (wp𑁒wand (λ res,
      l.[data] ↦ data ∗
      array۰model data (DfracOwn 1) (if b then <[₊i := v2]> us2 else us2)
    )%I with "[Hl_data Hdata]") as (res) "(Hl_data & Hdata)".
    { destruct b; last iSteps.
      wp۰load.
      wp۰apply (array٠unsafe_set𑁒spec with "Hdata") as "Hdata"; first lia.
      iSteps.
    }

    wp۰pures.

    set vs' := if b then <[₊i := v2]> vs else vs.
    wp۰bind (Resolve _ _ _).
    wp۰apply (wp𑁒wand (λ _,
      model₂ γ vs' ∗
      Φ #b
    )%I with "[Hmodel₂ HΦ]") as (?) "(Hmodel₂ & HΦ)".
    { iMod "HΦ" as "(%vs_ & (:model) & HΦ)". injection Heq as <-.
      iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
      iMod (model𑁒update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & $)".
      wp۰apply (wp𑁒wand with "(HΦ [%] [%] [%] [Hmodel₁])") as (?) "$".
      { done. }
      { rewrite Hv //. }
      { iSteps. }
    }

    wp۰pures.
    iFrame. iPureIntro.
    destruct b; last done.
    rewrite /vs' length_insert Hvs.
    apply functional_extensionality => j.
    destruct_decide (j = ₊i) as -> | ?.
    - rewrite fn_lookup_insert decide_True; first lia.
      rewrite list_lookup_total_insert_eq //. lia.
    - rewrite fn_lookup_insert_ne //. case_decide; last done.
      rewrite list_lookup_total_insert_ne //.
  Qed.

  Lemma inf_array٠faa𑁒spec t i (incr : Z) :
    (0 ≤ i)%Z →
    <<<
      inf_array۰inv t
    | ∀∀ vs (n : Z),
      ⌜vs ₊i = #n⌝ ∗
      inf_array۰model t vs
    >>>
      inf_array٠faa t #i #incr
    <<<
      inf_array۰model t (<[₊i := #(n + incr)]> vs)
    | RET vs ₊i;
      £ 1
    >>>.
  Proof.
    iIntros "% %Φ Hinv HΦ".

    wp۰rec.
    awp۰apply+ (inf_array٠update𑁒spec (λ v, ∃ n : Z, ⌜v = #n⌝)%I (λ v w, ∃ n : Z, ⌜v = #n ∧ w = #(n + incr)⌝)%I with "[$Hinv]"); [done | iSteps |].
    iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs %n (%Hn & Hmodel)".
    iAaccIntro with "[$Hmodel]". 1,2: iSteps. iSteps as (l γ n_ Hn_) / --silent.
    rewrite Hn_ in Hn. injection Hn as ->. iSteps.
  Qed.
End inf_array۰G.

Require zoo_std.inf_array__opaque.

#[global] Opaque inf_array۰inv.
#[global] Opaque inf_array۰model.
#[global] Opaque inf_array۰model'.
