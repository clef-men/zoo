Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.common.relations.
Require Import zoo.common.list.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.iris.base_logic.lib.auth_twins.
Require Import zoo.iris.base_logic.lib.auth_nat_max.
Require Import zoo.iris.base_logic.lib.mono_list.
Require Import zoo.base.
Require Import zoo_std.option.
Require Import zoo_std.array.
Require Export zoo_saturn.spsc_bqueue__code.
Require Import zoo_saturn.spsc_bqueue__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type i front front_cache back back_cache : nat.
Implicit Type l : location.
Implicit Type v w t : val.
Implicit Type vs ws hist : list val.

Variant stability :=
  | Stable
  | Unstable.
Implicit Type stable : stability.

#[local] Instance stability𑁒inhabited : Inhabited stability :=
  populate Stable.

Class SpscBqueueG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] spsc_bqueue۰G۰model۰G :: AuthTwinsG Σ (leibnizO (list val)) suffix
  ; #[local] spsc_bqueue۰G۰history۰G :: MonoListG Σ val
  ; #[local] spsc_bqueue۰G۰stability۰G :: TwinsG Σ (leibnizO stability)
  ; #[local] spsc_bqueue۰G۰mono_nat۰G :: AuthNatMaxG Σ
  }.

Definition spsc_bqueue۰Σ :=
  #[auth_twins۰Σ (leibnizO (list val)) suffix
  ; mono_list۰Σ val
  ; twins۰Σ (leibnizO stability)
  ; auth_nat_max۰Σ
  ].
#[global] Instance subG𑁒spsc_bqueue۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG spsc_bqueue۰Σ Σ →
  SpscBqueueG Σ.
Proof.
  solve_inG.
Qed.

Section spsc_bqueue۰G.
  Context `{spsc_bqueue۰G : SpscBqueueG Σ}.

  Record metadata :=
    { metadata۰capacity : nat
    ; metadata۰data : val
    ; metadata۰inv : namespace
    ; metadata۰model : auth_twins۰name
    ; metadata۰history : gname
    ; metadata۰producer : gname
    ; metadata۰back : gname
    ; metadata۰consumer : gname
    ; metadata۰front : gname
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
    auth_twins۰twin₁ (auth_twins۰G := spsc_bqueue۰G۰model۰G) _ γ_model vs.
  #[local] Definition model₁ γ :=
    model₁' γ.(metadata۰model).
  #[local] Definition model₂' γ_model vs :=
    auth_twins۰twin₂ (auth_twins۰G := spsc_bqueue۰G۰model۰G) _ γ_model vs.
  #[local] Definition model₂ γ :=
    model₂' γ.(metadata۰model).

  #[local] Definition history۰auth' γ_history :=
    mono_list۰auth γ_history (DfracOwn 1).
  #[local] Definition history۰auth γ :=
    history۰auth' γ.(metadata۰history).
  #[local] Definition history۰at γ :=
    mono_list۰at γ.(metadata۰history).

  #[local] Definition producer₁' γ_producer γ_back γ_model stable back ws : iProp Σ :=
    twins۰twin₁ γ_producer (DfracOwn 1) stable ∗
    auth_nat_max۰auth γ_back (DfracOwn (1/2)) back ∗
    auth_twins۰auth _ (auth_twins۰G := spsc_bqueue۰G۰model۰G) γ_model ws.
  #[local] Definition producer₁ γ :=
    producer₁' γ.(metadata۰producer) γ.(metadata۰back) γ.(metadata۰model).
  #[local] Instance : CustomIpat "producer₁" :=
    " ( Hproducer₁
      & Hback_auth₁
      & Hmodel_auth
      )
    ".
  #[local] Definition producer₂' γ_producer γ_back stable back : iProp Σ :=
    twins۰twin₂ γ_producer stable ∗
    auth_nat_max۰auth γ_back (DfracOwn (1/2)) back.
  #[local] Definition producer₂ γ :=
    producer₂' γ.(metadata۰producer) γ.(metadata۰back).
  #[local] Instance : CustomIpat "producer₂" :=
    " ( Hproducer₂
      & Hback_auth₂
      )
    ".
  #[local] Definition back۰lb γ :=
    auth_nat_max۰lb γ.(metadata۰back).

  #[local] Definition consumer₁' γ_consumer γ_front stable front : iProp Σ :=
    twins۰twin₁ γ_consumer (DfracOwn 1) stable ∗
    auth_nat_max۰auth γ_front (DfracOwn (1/2)) front.
  #[local] Definition consumer₁ γ :=
    consumer₁' γ.(metadata۰consumer) γ.(metadata۰front).
  #[local] Instance : CustomIpat "consumer₁" :=
    " ( Hconsumer₁
      & Hfront_auth₁
      )
    ".
  #[local] Definition consumer₂' γ_consumer γ_front stable front : iProp Σ :=
    twins۰twin₂ γ_consumer stable ∗
    auth_nat_max۰auth γ_front (DfracOwn (1/2)) front.
  #[local] Definition consumer₂ γ :=
    consumer₂' γ.(metadata۰consumer) γ.(metadata۰front).
  #[local] Instance : CustomIpat "consumer₂" :=
    " ( Hconsumer₂
      & Hfront_auth₂
      )
    ".
  #[local] Definition front۰lb γ :=
    auth_nat_max۰lb γ.(metadata۰front).

  #[local] Definition inv۰inner l γ : iProp Σ :=
    ∃ cstable front pstable back vs hist,
    ⌜back = (front + length vs)%nat⌝ ∗
    ⌜back ≤ front + γ.(metadata۰capacity)⌝ ∗
    ⌜length hist = back⌝ ∗
    ⌜vs = drop front hist⌝ ∗
    l.[front] ↦ #front ∗
    consumer₂ γ cstable front ∗
    l.[back] ↦ #back ∗
    producer₂ γ pstable back ∗
    model₂ γ vs ∗
    history۰auth γ hist ∗
    ( if cstable then
        array۰cslice γ.(metadata۰data) γ.(metadata۰capacity) front (DfracOwn 1) ((λ v, ‘Some( v )%V) <$> take 1 vs)
      else
        True
    ) ∗
    array۰cslice γ.(metadata۰data) γ.(metadata۰capacity) ˖front (DfracOwn 1) ((λ v, ‘Some( v )%V) <$> drop 1 vs) ∗
    ( if pstable then
        array۰cslice γ.(metadata۰data) γ.(metadata۰capacity) back (DfracOwn 1) (if decide (back = front + γ.(metadata۰capacity)) then [] else [§None%V])
      else
        True
    ) ∗
    array۰cslice γ.(metadata۰data) γ.(metadata۰capacity) ˖back (DfracOwn 1) (replicate (γ.(metadata۰capacity) - (back - front) - 1) §None%V).
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %cstable{}
      & %front{}
      & %pstable{}
      & %back{}
      & %vs{}
      & %hist{}
      & >%Hback{}
      & >%Hback{}_le
      & >%Hhist{}_len
      & >%Hvs{}
      & >Hl_front
      & >Hconsumer₂
      & >Hl_back
      & >Hproducer₂
      & >Hmodel₂
      & >Hhistory_auth
      & >Hfront
      & >Hvs
      & >Hback
      & >Hextra
      )
    ".
  #[local] Definition inv' l γ : iProp Σ :=
    l ↪ γ ∗
    l.[data] ↦□ γ.(metadata۰data) ∗
    array۰inv γ.(metadata۰data) γ.(metadata۰capacity) ∗
    inv γ.(metadata۰inv) (inv۰inner l γ).
  #[local] Instance : CustomIpat "inv'" :=
    " ( #Hmeta{_{}}
      & #Hl_data
      & #Hdata_inv
      & #Hinv
      )
    ".
  Definition spsc_bqueue۰inv t ι cap : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    ⌜ι = γ.(metadata۰inv)⌝ ∗
    ⌜cap = γ.(metadata۰capacity)⌝ ∗
    inv' l γ.
  #[local] Instance : CustomIpat "inv" :=
    " ( %l{}
      & %γ{}
      & {%Heq{};->}
      & ->
      & ->
      & (:inv')
      )
    ".

  Definition spsc_bqueue۰model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    l ↪ γ ∗
    model₁ γ vs ∗
    ⌜length vs ≤ γ.(metadata۰capacity)⌝.
  #[local] Instance : CustomIpat "model" :=
    " ( %l{;_}
      & %γ{;_}
      & %Heq{}
      & #Hmeta_{}
      & Hmodel₁{_{}}
      & %Hvs{}
      )
    ".

  Definition spsc_bqueue۰producer t ws : iProp Σ :=
    ∃ l γ front_cache back,
    ⌜t = #l⌝ ∗
    l ↪ γ ∗
    l.[front_cache] ↦ #front_cache ∗
    producer₁ γ Stable back ws ∗
    front۰lb γ front_cache.
  #[local] Instance : CustomIpat "producer" :=
    " ( %l{;_}
      & %γ{;_}
      & %front_cache
      & %back
      & %Heq{}
      & #Hmeta_{}
      & Hl_front_cache
      & Hproducer₁
      & #Hfront_lb
      )
    ".

  Definition spsc_bqueue۰consumer t : iProp Σ :=
    ∃ l γ front back_cache,
    ⌜t = #l⌝ ∗
    l ↪ γ ∗
    l.[back_cache] ↦ #back_cache ∗
    consumer₁ γ Stable front ∗
    back۰lb γ back_cache.
  #[local] Instance : CustomIpat "consumer" :=
    " ( %l{;_}
      & %γ{;_}
      & %front
      & %back_cache
      & %Heq{}
      & #Hmeta_{}
      & Hl_back_cache
      & Hconsumer₁
      & #Hback_lb
      )
    ".

  #[global] Instance spsc_bqueue۰inv𑁒persistent t ι cap :
    Persistent (spsc_bqueue۰inv t ι cap).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_bqueue۰model𑁒timeless t vs :
    Timeless (spsc_bqueue۰model t vs).
  Proof.
    apply _.
  Qed.
  #[local] Instance producer₂𑁒timeless γ stable back :
    Timeless (producer₂ γ stable back).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_bqueue۰producer𑁒timeless t ws :
    Timeless (spsc_bqueue۰producer t ws).
  Proof.
    apply _.
  Qed.
  #[local] Instance consumer₂𑁒timeless γ stable front :
    Timeless (consumer₂ γ stable front).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_bqueue۰consumer𑁒timeless t :
    Timeless (spsc_bqueue۰consumer t).
  Proof.
    apply _.
  Qed.

  #[local] Lemma model𑁒producer𑁒alloc :
    ⊢ |==>
      ∃ γ_model γ_producer γ_back,
      model₁' γ_model [] ∗
      model₂' γ_model [] ∗
      producer₁' γ_producer γ_back γ_model Stable 0 [] ∗
      producer₂' γ_producer γ_back Stable 0.
  Proof.
    iMod (auth_twins𑁒alloc (auth_twins۰G := spsc_bqueue۰G۰model۰G) _ []) as "(%γ_model & Hmodel_auth & Hmodel₁ & Hmodel₂)".
    iMod twins𑁒alloc' as "(%γ_producer & Hproducer₁ & Hproducer₂)".
    iMod auth_nat_max𑁒alloc as "(%γ_back & Hback_auth₁ & Hback_auth₂)".
    iSteps.
  Qed.
  #[local] Lemma model𑁒valid γ stable back ws vs :
    producer₁ γ stable back ws -∗
    model₁ γ vs -∗
    ⌜vs `suffix_of` ws⌝.
  Proof.
    iIntros "(:producer₁) Hmodel₁".
    iDestruct (auth_twins𑁒valid₁ with "Hmodel_auth Hmodel₁") as %H.
    rewrite preorder𑁒rtc in H. iSteps.
  Qed.
  #[local] Lemma model₁𑁒exclusive γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₁ γ vs2 -∗
    False.
  Proof.
    apply auth_twins۰twin₁𑁒exclusive.
  Qed.
  #[local] Lemma model𑁒agree γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₂ γ vs2 -∗
    ⌜vs1 = vs2⌝.
  Proof.
    iIntros "Hmodel₁ Hmodel₂".
    iDestruct (auth_twins𑁒agree𑁒L with "Hmodel₁ Hmodel₂") as %->.
    iSteps.
  Qed.
  #[local] Lemma model𑁒push {γ stable back ws vs1 vs2} v :
    producer₁ γ stable back ws -∗
    model₁ γ vs1 -∗
    model₂ γ vs2 ==∗
      producer₁ γ stable back (vs1 ++ [v]) ∗
      model₁ γ (vs1 ++ [v]) ∗
      model₂ γ (vs1 ++ [v]).
  Proof.
    iIntros "(:producer₁) Hmodel₁ Hmodel₂".
    iMod (auth_twins𑁒update𑁒auth with "Hmodel_auth Hmodel₁ Hmodel₂") as "(Hmodel_auth & Hmodel₁ & Hmodel₂)".
    iSteps.
  Qed.
  #[local] Lemma model𑁒pop γ v vs1 vs2 :
    model₁ γ (v :: vs1) -∗
    model₂ γ vs2 ==∗
      model₁ γ vs1 ∗
      model₂ γ vs1.
  Proof.
    apply: auth_twins𑁒update𑁒twins𑁒L.
    rewrite preorder𑁒rtc. solve_suffix.
  Qed.

  #[local] Lemma history𑁒alloc :
    ⊢ |==>
      ∃ γ_history,
      history۰auth' γ_history [].
  Proof.
    apply mono_list𑁒alloc.
  Qed.
  #[local] Lemma history۰at𑁒get {γ hist} i v :
    hist !! i = Some v →
    history۰auth γ hist ⊢
    history۰at γ i v.
  Proof.
    apply mono_list۰at𑁒get.
  Qed.
  #[local] Lemma history𑁒agree γ hist i v :
    history۰auth γ hist -∗
    history۰at γ i v -∗
    ⌜hist !! i = Some v⌝.
  Proof.
    apply mono_list۰at𑁒valid.
  Qed.
  #[local] Lemma history𑁒update {γ hist} v :
    history۰auth γ hist ⊢ |==>
    history۰auth γ (hist ++ [v]).
  Proof.
    apply mono_list𑁒update𑁒snoc.
  Qed.

  #[local] Lemma producer𑁒agree γ stable1 back1 ws stable2 back2 :
    producer₁ γ stable1 back1 ws -∗
    producer₂ γ stable2 back2 -∗
      ⌜stable1 = stable2⌝ ∗
      ⌜back1 = back2⌝.
  Proof.
    iIntros "(:producer₁) (:producer₂)".
    iDestruct (twins𑁒agree𑁒L with "Hproducer₁ Hproducer₂") as %<-.
    iDestruct (auth_nat_max۰auth𑁒agree with "Hback_auth₁ Hback_auth₂") as %<-.
    iSteps.
  Qed.
  #[local] Lemma producer𑁒update𑁒stability {γ stable1 back1 ws stable2 back2} stable :
    producer₁ γ stable1 back1 ws -∗
    producer₂ γ stable2 back2 ==∗
      producer₁ γ stable back1 ws ∗
      producer₂ γ stable back2.
  Proof.
    iIntros "(:producer₁) (:producer₂)".
    iMod (twins𑁒update with "Hproducer₁ Hproducer₂") as "(Hproducer₁ & Hproducer₂)".
    iSteps.
  Qed.
  #[local] Lemma producer𑁒update𑁒back {γ stable1 back1 ws stable2 back2} back :
    back1 ≤ back →
    producer₁ γ stable1 back1 ws -∗
    producer₂ γ stable2 back2 ==∗
      producer₁ γ stable1 back ws ∗
      producer₂ γ stable2 back.
  Proof.
    iIntros "% (:producer₁) (:producer₂)".
    iDestruct (auth_nat_max۰auth𑁒agree with "Hback_auth₁ Hback_auth₂") as %->.
    iCombine "Hback_auth₁ Hback_auth₂" as "Hback_auth".
    iMod (auth_nat_max𑁒update with "Hback_auth") as "(Hback_auth₁ & Hback_auth₂)"; first done.
    iSteps.
  Qed.
  #[local] Lemma back۰lb𑁒get γ stable back :
    producer₂ γ stable back ⊢
    back۰lb γ back.
  Proof.
    iIntros "(:producer₂)".
    iApply (auth_nat_max۰lb𑁒get with "Hback_auth₂").
  Qed.
  #[local] Lemma back۰lb𑁒valid γ stable back1 back2 :
    producer₂ γ stable back1 -∗
    back۰lb γ back2 -∗
    ⌜back2 ≤ back1⌝.
  Proof.
    iIntros "(:producer₂) Hback_lb".
    iApply (auth_nat_max۰lb𑁒valid with "Hback_auth₂ Hback_lb").
  Qed.

  #[local] Lemma consumer𑁒alloc :
    ⊢ |==>
      ∃ γ_consumer γ_front,
      consumer₁' γ_consumer γ_front Stable 0 ∗
      consumer₂' γ_consumer γ_front Stable 0.
  Proof.
    iMod twins𑁒alloc' as "(%γ_consumer & Hconsumer₁ & Hconsumer₂)".
    iMod auth_nat_max𑁒alloc as "(%γ_front & Hfront_auth₁ & Hfront_auth₂)".
    iSteps.
  Qed.
  #[local] Lemma consumer𑁒agree γ stable1 front1 stable2 front2 :
    consumer₁ γ stable1 front1 -∗
    consumer₂ γ stable2 front2 -∗
      ⌜stable1 = stable2⌝ ∗
      ⌜front1 = front2⌝.
  Proof.
    iIntros "(:consumer₁) (:consumer₂)".
    iDestruct (twins𑁒agree𑁒L with "Hconsumer₁ Hconsumer₂") as %<-.
    iDestruct (auth_nat_max۰auth𑁒agree with "Hfront_auth₁ Hfront_auth₂") as %<-.
    iSteps.
  Qed.
  #[local] Lemma consumer𑁒update𑁒front {γ stable1 front1 stable2 front2} front :
    front1 ≤ front →
    consumer₁ γ stable1 front1 -∗
    consumer₂ γ stable2 front2 ==∗
      consumer₁ γ stable1 front ∗
      consumer₂ γ stable2 front.
  Proof.
    iIntros "% (:consumer₁) (:consumer₂)".
    iDestruct (auth_nat_max۰auth𑁒agree with "Hfront_auth₁ Hfront_auth₂") as %->.
    iCombine "Hfront_auth₁ Hfront_auth₂" as "Hfront_auth".
    iMod (auth_nat_max𑁒update with "Hfront_auth") as "(Hauth_auth₁ & Hfront_auth₂)"; first done.
    iSteps.
  Qed.
  #[local] Lemma consumer𑁒update𑁒stability {γ stable1 front1 stable2 front2} stable :
    consumer₁ γ stable1 front1 -∗
    consumer₂ γ stable2 front2 ==∗
      consumer₁ γ stable front1 ∗
      consumer₂ γ stable front2.
  Proof.
    iIntros "(:consumer₁) (:consumer₂)".
    iMod (twins𑁒update with "Hconsumer₁ Hconsumer₂") as "(Hconsumer₁ & Hconsumer₂)".
    iSteps.
  Qed.
  #[local] Lemma front۰lb𑁒get γ stable front :
    consumer₂ γ stable front ⊢
    front۰lb γ front.
  Proof.
    iIntros "(:consumer₂)".
    iApply (auth_nat_max۰lb𑁒get with "Hfront_auth₂").
  Qed.
  #[local] Lemma front۰lb𑁒valid γ stable front1 front2 :
    consumer₂ γ stable front1 -∗
    front۰lb γ front2 -∗
    ⌜front2 ≤ front1⌝.
  Proof.
    iIntros "(:consumer₂) Hfront_lb".
    iApply (auth_nat_max۰lb𑁒valid with "Hfront_auth₂ Hfront_lb").
  Qed.

  Opaque producer₁'.
  Opaque producer₂'.
  Opaque consumer₁'.
  Opaque consumer₂'.

  Lemma spsc_bqueue۰model𑁒valid t ι cap vs :
    spsc_bqueue۰inv t ι cap -∗
    spsc_bqueue۰model t vs -∗
    ⌜length vs ≤ cap⌝.
  Proof.
    iIntros "(:inv =1) (:model =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %<-.
    iSteps.
  Qed.
  Lemma spsc_bqueue۰model𑁒exclusive t vs1 vs2 :
    spsc_bqueue۰model t vs1 -∗
    spsc_bqueue۰model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (model₁𑁒exclusive with "Hmodel₁_1 Hmodel₁_2").
  Qed.

  Lemma spsc_bqueue۰producer𑁒exclusive t ws :
    spsc_bqueue۰producer t ws -∗
    spsc_bqueue۰producer t ws -∗
    False.
  Proof.
    iSteps.
  Qed.
  Lemma spsc_bqueue𑁒producer𑁒model t ws vs :
    spsc_bqueue۰producer t ws -∗
    spsc_bqueue۰model t vs -∗
    ⌜vs `suffix_of` ws⌝.
  Proof.
    iIntros "(:producer =1) (:model =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (model𑁒valid with "Hproducer₁ Hmodel₁_2").
  Qed.

  Lemma spsc_bqueue۰consumer𑁒exclusive t :
    spsc_bqueue۰consumer t -∗
    spsc_bqueue۰consumer t -∗
    False.
  Proof.
    iSteps.
  Qed.

  #[local] Instance hint𑁒array۰cslice𑁒nil t cap i dq :
    HINT ε₁ ✱ [- ;
      array۰inv t cap
    ] ⊫ [id];
      array۰cslice t cap i dq []
    ✱ [
      emp
    ].
  Proof.
    iSteps. rewrite array۰cslice𑁒nil. iSteps.
  Qed.

  Lemma spsc_bqueue٠create𑁒spec ι cap :
    (0 ≤ cap)%Z →
    {{{
      True
    }}}
      spsc_bqueue٠create #cap
    {{{
      t
    , RET t;
      spsc_bqueue۰inv t ι ₊cap ∗
      spsc_bqueue۰model t [] ∗
      spsc_bqueue۰producer t [] ∗
      spsc_bqueue۰consumer t
    }}}.
  Proof.
    iIntros "%Hcap %Φ _ HΦ".

    wp۰rec.
    iApply wp𑁒fupd.
    wp۰apply (array٠unsafe_make𑁒spec with "[//]") as "%data Hdata_model"; first done.
    iDestruct (array۰model𑁒to𑁒inv with "Hdata_model") as "#Hdata_inv". simpl_length.
    wp۰block l as "Hmeta" "(Hl_data & Hl_front & Hl_front_cache & Hl_back & Hl_back_cache & _)".
    iMod (pointsto𑁒persist with "Hl_data") as "#Hl_data".

    iMod model𑁒producer𑁒alloc as "(%γ_model & %γ_producer & %γ_back & Hmodel₁ & Hmodel₂ & Hproducer₁ & Hproducer₂)".
    iMod history𑁒alloc as "(%γ_history & Hhistory_auth)".
    iMod consumer𑁒alloc as "(%γ_consumer & %γ_front & Hconsumer₁ & Hconsumer₂)".

    pose γ :=
      {|metadata۰capacity := ₊cap
      ; metadata۰data := data
      ; metadata۰inv := ι
      ; metadata۰model := γ_model
      ; metadata۰history := γ_history
      ; metadata۰producer := γ_producer
      ; metadata۰back := γ_back
      ; metadata۰consumer := γ_consumer
      ; metadata۰front := γ_front
      |}.
    iMod (meta𑁒set γ with "Hmeta") as "#Hmeta"; first done.

    iDestruct (back۰lb𑁒get γ with "Hproducer₂") as "#Hback_lb".
    iDestruct (front۰lb𑁒get γ with "Hconsumer₂") as "#Hfront_lb".

    iApply "HΦ".
    iSplitL "Hdata_model Hl_front Hl_back Hmodel₂ Hhistory_auth Hproducer₂ Hconsumer₂"; last iSteps.
    iExists l, γ. iStep 6.
    iApply inv_alloc. iExists Stable, 0, Stable, 0, [], []. iStep 11.
    Z_to_nat cap. rewrite Nat2Z.id. destruct cap as [| cap]; first iSteps.
    iDestruct (array۰model𑁒to𑁒cslice with "Hdata_model") as "Hdata_cslice".
    rewrite length_replicate -(take_drop 1 (replicate _ _)).
    iDestruct (array۰cslice𑁒app with "Hdata_cslice") as "(Hback & Hextra)".
    rewrite Nat.add_0_l take_replicate_add. iStep.
    rewrite Nat.sub_0_r. iSteps.
  Qed.

  Lemma spsc_bqueue٠capacity𑁒spec t ι cap :
    {{{
      spsc_bqueue۰inv t ι cap
    }}}
      spsc_bqueue٠capacity t
    {{{
      RET #cap;
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec. wp۰load.
    wp۰apply (array٠size𑁒spec𑁒inv with "Hdata_inv").
    iSteps.
  Qed.

  #[local] Lemma front𑁒spec l γ stable front :
    {{{
      inv' l γ ∗
      consumer₁ γ stable front
    }}}
      (#l).{front}
    {{{
      RET #front;
      consumer₁ γ stable front
    }}}.
  Proof.
    iIntros "%Φ ((:inv') & Hconsumer₁) HΦ".

    iInv "Hinv" as "(:inv۰inner =')".
    wp۰load.
    iDestruct (consumer𑁒agree with "Hconsumer₁ Hconsumer₂") as %(<- & <-).
    iSplitR "Hconsumer₁ HΦ". { iFrameSteps. }
    iSteps.
  Qed.

  #[local] Lemma back𑁒spec l γ stable back ws :
    {{{
      inv' l γ ∗
      producer₁ γ stable back ws
    }}}
      (#l).{back}
    {{{
      RET #back;
      producer₁ γ stable back ws
    }}}.
  Proof.
    iIntros "%Φ ((:inv') & Hproducer₁) HΦ".

    iInv "Hinv" as "(:inv۰inner =')".
    wp۰load.
    iDestruct (producer𑁒agree with "Hproducer₁ Hproducer₂") as %(<- & <-).
    iSplitR "Hproducer₁ HΦ". { iFrameSteps. }
    iSteps.
  Qed.

  Lemma spsc_bqueue٠size𑁒spec𑁒producer t ι cap ws :
    <<<
      spsc_bqueue۰inv t ι cap ∗
      spsc_bqueue۰producer t ws
    | ∀∀ vs,
      spsc_bqueue۰model t vs
    >>>
      spsc_bqueue٠size t @ ↑ι
    <<<
      spsc_bqueue۰model t vs
    | RET #(length vs);
      spsc_bqueue۰producer t ws
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:producer)) HΦ". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec.

    wp۰apply (back𑁒spec with "[$]") as "Hproducer₁".
    wp۰pures.

    wp۰bind (_.{front})%E.
    iInv "Hinv" as "(:inv۰inner =2)".
    wp۰load.
    iDestruct (producer𑁒agree with "Hproducer₁ Hproducer₂") as %(<- & <-).

    iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %<-.
    iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.

    iSplitR "Hl_front_cache Hproducer₁ HΦ". { iFrameSteps. }
    assert (⁺back - ⁺front2 = length vs)%Z as Hlen by lia.
    iIntros "!> {%- Hlen}".

    iSteps. rewrite Hlen. iSteps.
  Qed.
  Lemma spsc_bqueue٠size𑁒spec𑁒consumer t ι cap :
    <<<
      spsc_bqueue۰inv t ι cap ∗
      spsc_bqueue۰consumer t
    | ∀∀ vs,
      spsc_bqueue۰model t vs
    >>>
      spsc_bqueue٠size t @ ↑ι
    <<<
      spsc_bqueue۰model t vs
    | RET #(length vs);
      spsc_bqueue۰consumer t
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:consumer)) HΦ". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec.

    wp۰bind (_.{back})%E.
    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰load.
    iDestruct (consumer𑁒agree with "Hconsumer₁ Hconsumer₂") as %(<- & <-).

    iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %<-.
    iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.

    iSplitR "Hl_back_cache Hconsumer₁ HΦ". { iFrameSteps. }
    assert (⁺back1 - ⁺front = length vs)%Z as Hlen by lia.
    iIntros "!> {%- Hlen}".

    wp۰apply+ (front𑁒spec with "[$]") as "Hconsumer₁".
    iSteps. rewrite Hlen. iSteps.
  Qed.

  Lemma spsc_bqueue٠is_empty𑁒spec𑁒producer t ι cap ws :
    <<<
      spsc_bqueue۰inv t ι cap ∗
      spsc_bqueue۰producer t ws
    | ∀∀ vs,
      spsc_bqueue۰model t vs
    >>>
      spsc_bqueue٠is_empty t @ ↑ι
    <<<
      spsc_bqueue۰model t vs
    | RET #(bool_decide (vs = []%list));
      spsc_bqueue۰producer t ws
    >>>.
  Proof.
    iIntros "%Φ (#Hinv & Hproducer) HΦ".

    wp۰rec.

    wp۰apply (spsc_bqueue٠size𑁒spec𑁒producer with "[$Hinv $Hproducer]").
    iApply (atomic_update𑁒wand with "HΦ"). iIntros "%vs HΦ Hproducer".

    wp۰pures.
    setoid_rewrite (bool_decide_ext _ (vs = [])) at 2; last first.
    { rewrite -length_zero_iff_nil. lia. }
    iApply ("HΦ" with "Hproducer").
  Qed.
  Lemma spsc_bqueue٠is_empty𑁒spec𑁒consumer t ι cap :
    <<<
      spsc_bqueue۰inv t ι cap ∗
      spsc_bqueue۰consumer t
    | ∀∀ vs,
      spsc_bqueue۰model t vs
    >>>
      spsc_bqueue٠is_empty t @ ↑ι
    <<<
      spsc_bqueue۰model t vs
    | RET #(bool_decide (vs = []%list));
      spsc_bqueue۰consumer t
    >>>.
  Proof.
    iIntros "%Φ (#Hinv & Hconsumer) HΦ".

    wp۰rec.

    wp۰apply (spsc_bqueue٠size𑁒spec𑁒consumer with "[$Hinv $Hconsumer]").
    iApply (atomic_update𑁒wand with "HΦ"). iIntros "%vs HΦ Hconsumer".

    wp۰pures.
    setoid_rewrite (bool_decide_ext _ (vs = [])) at 2; last first.
    { rewrite -length_zero_iff_nil. lia. }
    iApply ("HΦ" with "Hconsumer").
  Qed.

  #[local] Definition push۰au l γ v Ψ : iProp Σ :=
    AU <{
      ∃∃ vs,
      spsc_bqueue۰model #l vs
    }> @ ⊤ ∖ ↑γ.(metadata۰inv), ∅ <{
      ∀∀ b,
      ⌜b = bool_decide (length vs = γ.(metadata۰capacity))⌝ ∗
      spsc_bqueue۰model #l (if b then vs else vs ++ [v]),
    COMM
      Ψ vs b
    }>.
  #[local] Lemma spsc_bqueue٠push₀𑁒spec l γ front_cache stable back ws v Ψ :
    {{{
      inv' l γ ∗
      l.[front_cache] ↦ #front_cache ∗
      producer₁ γ stable back ws ∗
      front۰lb γ front_cache ∗
      push۰au l γ v Ψ
    }}}
      spsc_bqueue٠push₀ #l γ.(metadata۰data) #back
    {{{
      b front_cache
    , RET #b;
      ⌜b = bool_decide (back < front_cache + γ.(metadata۰capacity))⌝ ∗
      l.[front_cache] ↦ #front_cache ∗
      producer₁ γ stable back ws ∗
      front۰lb γ front_cache ∗
      if b then
        push۰au l γ v Ψ
      else
        ∃ vs,
        ⌜length vs = γ.(metadata۰capacity)⌝ ∗
        Ψ vs true
    }}}.
  Proof.
    iIntros "%Φ ((:inv') & Hl_front_cache & Hproducer₁ & #Hfront_lb & HΨ) HΦ".

    wp۰rec.
    wp۰apply+ (array٠size𑁒spec𑁒inv with "Hdata_inv") as "_".
    wp۰load. wp۰pures.
    case_bool_decide as Hbranch1; wp۰pures.

    - iSpecialize ("HΦ" $! true front_cache). rewrite bool_decide_eq_true_2; first lia.
      iSteps.

    - wp۰bind (_.{front})%E.
      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰load.
      iDestruct (producer𑁒agree with "Hproducer₁ Hproducer₂") as %(<- & <-).
      iClear "Hfront_lb". iDestruct (front۰lb𑁒get with "Hconsumer₂") as "#Hfront_lb".
      destruct_decide (back < front1 + γ.(metadata۰capacity)) as Hbranch2.

      + iSplitR "Hl_front_cache Hproducer₁ HΨ HΦ". { iFrameSteps. }
        iIntros "!> {%- Hbranch2}".

        wp۰store. wp۰pures.
        iApply ("HΦ" $! _ front1).
        rewrite !bool_decide_eq_true_2; [lia.. |]. iSteps.

      + assert (length vs1 = γ.(metadata۰capacity)) as Hvs1_len by lia.

        iMod "HΨ" as "(%vs & (:model) & _ & HΨ)". injection Heq as <-.
        iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
        iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
        rewrite bool_decide_eq_true_2 //.
        iMod ("HΨ" with "[Hmodel₁]") as "HΨ"; first iSteps.

        iSplitR "Hl_front_cache Hproducer₁ HΨ HΦ". { iFrameSteps. }
        iIntros "!> {%- Hbranch2 Hvs1_len}".

        wp۰store. wp۰pures.
        iApply ("HΦ" $! _ front1).
        rewrite !bool_decide_eq_false_2; [lia.. |]. iSteps.
  Qed.
  Lemma spsc_bqueue٠push𑁒spec t ι cap ws v :
    <<<
      spsc_bqueue۰inv t ι cap ∗
      spsc_bqueue۰producer t ws
    | ∀∀ vs,
      spsc_bqueue۰model t vs
    >>>
      spsc_bqueue٠push t v @ ↑ι
    <<<
      ∃∃ b,
      ⌜b = bool_decide (length vs = cap)⌝ ∗
      spsc_bqueue۰model t (if b then vs else vs ++ [v])
    | RET #b;
      spsc_bqueue۰producer t (if b then ws else vs ++ [v])
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:producer)) HΦ". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰load.
    wp۰apply+ (back𑁒spec with "[$]") as "Hproducer₁".
    iDestruct "Hfront_lb" as "-#Hfront_lb". wp۰apply+ (spsc_bqueue٠push₀𑁒spec with "[$]") as (? front_cache') "(-> & Hl_front_cache & Hproducer₁ & #Hfront_lb & HΦ)".
    case_bool_decide as Hbranch; last iSteps.

    iApply fupd𑁒wp.
    iInv "Hinv" as "(:inv۰inner =2)".
    iDestruct (producer𑁒agree with "Hproducer₁ Hproducer₂") as %(<- & <-).
    iDestruct (front۰lb𑁒valid with "Hconsumer₂ Hfront_lb") as %Hfront2.
    rewrite decide_False; first lia.
    iMod (producer𑁒update𑁒stability Unstable with "Hproducer₁ Hproducer₂") as "(Hproducer₁ & Hproducer₂)".
    iSplitR "Hl_front_cache Hproducer₁ Hback HΦ". { iFrameSteps. }
    iIntros "!> {%- Hbranch} !>".

    wp۰apply+ (array٠unsafe_cset𑁒spec𑁒cell with "Hback") as "Hback_"; first done.
    wp۰pures.

    wp۰bind (_ <-{back} _)%E.
    iInv "Hinv" as "(:inv۰inner =3)".
    wp۰store.
    iDestruct (producer𑁒agree with "Hproducer₁ Hproducer₂") as %(<- & <-).
    iDestruct (front۰lb𑁒valid with "Hconsumer₂ Hfront_lb") as %Hfront3_ge.
    iMod (producer𑁒update𑁒stability Stable with "Hproducer₁ Hproducer₂") as "(Hproducer₁ & Hproducer₂)".
    iMod (producer𑁒update𑁒back ˖back with "Hproducer₁ Hproducer₂") as "(Hproducer₁ & Hproducer₂)"; first lia.
    iMod (history𑁒update v with "Hhistory_auth") as "Hhistory_auth".

    iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
    iMod (model𑁒push v with "Hproducer₁ Hmodel₁ Hmodel₂") as "(Hproducer₁ & Hmodel₁ & Hmodel₂)".
    rewrite bool_decide_eq_false_2; first lia.
    iMod ("HΦ" with "[Hmodel₁]") as "HΦ".
    { iSteps. iPureIntro. simpl_length/=. lia. }

    iSplitR "Hl_front_cache Hproducer₁ HΦ".
    { do 2 iModIntro. iExists _, front3, _, ˖back, (vs3 ++ [v]), (hist3 ++ [v]). iFrame.
      simpl_length. iStep 3.
      iSplit. { rewrite Hvs3 drop_app_le //; first lia. }
      iStep.
      rewrite assoc. iSplitL "Hfront Hvs Hback_".
      - destruct vs3 as [| v' vs3]; iFrame.
        + assert (front3 = back) as -> by naive_solver lia.
          destruct cstable3; iSteps.
        + rewrite /= !drop_0 fmap_app.
          iApply (array۰cslice𑁒app₁ with "Hvs Hback_").
          simpl_length. naive_solver lia.
      - case_decide.
        + assert (γ.(metadata۰capacity) - (˖back - front3) - 1 = 0) as -> by lia.
          iSteps.
        + iDestruct (array۰cslice𑁒app₂ [§None%V] (replicate (γ.(metadata۰capacity) - (˖back - front3) - 1) §None%V) with "Hextra") as "($ & Hextra)".
          { rewrite /= -replicate_S. f_equal. lia. }
          rewrite Nat.add_1_r //.
    }
    iSteps.
  Qed.

  #[local] Definition pop۰au l γ Ψ : iProp Σ :=
    AU <{
      ∃∃ vs,
      spsc_bqueue۰model #l vs
    }> @ ⊤ ∖ ↑γ.(metadata۰inv), ∅ <{
      spsc_bqueue۰model #l (tail vs),
    COMM
      spsc_bqueue۰consumer #l -∗
      Ψ (head vs : val)
    }>.
  #[local] Lemma spsc_bqueue٠pop₀𑁒spec l γ back_cache stable front Ψ :
    {{{
      inv' l γ ∗
      l.[back_cache] ↦ #back_cache ∗
      consumer₁ γ stable front ∗
      back۰lb γ back_cache ∗
      pop۰au l γ Ψ
    }}}
      spsc_bqueue٠pop₀ #l #front
    {{{
      b back_cache
    , RET #b;
      ⌜b = bool_decide (front < back_cache)⌝ ∗
      l.[back_cache] ↦ #back_cache ∗
      consumer₁ γ stable front ∗
      back۰lb γ back_cache ∗
      if b then
        pop۰au l γ Ψ
      else
        spsc_bqueue۰consumer #l -∗
        Ψ None
    }}}.
  Proof.
    iIntros "%Φ ((:inv') & Hl_back_cache & Hconsumer₁ & #Hback_lb & HΨ) HΦ".

    wp۰rec.
    wp۰load. wp۰pures.
    case_bool_decide as Hbranch1; wp۰pures.

    - iSpecialize ("HΦ" $! true back_cache). rewrite bool_decide_eq_true_2; first lia.
      iSteps.

    - wp۰bind (_.{back})%E.
      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰load.
      iDestruct (consumer𑁒agree with "Hconsumer₁ Hconsumer₂") as %(<- & <-).
      iClear "Hback_lb". iDestruct (back۰lb𑁒get with "Hproducer₂") as "#Hback_lb".
      destruct_decide (front < back1) as Hbranch2.

      + iSplitR "Hl_back_cache Hconsumer₁ HΨ HΦ". { iFrameSteps. }
        iIntros "!> {%- Hbranch2}".

        wp۰store. wp۰pures.
        iApply ("HΦ" $! _ back1).
        rewrite !bool_decide_eq_true_2; [lia.. |]. iSteps.

      + assert (front = back1) as <- by lia.

        iMod "HΨ" as "(%vs & (:model) & _ & HΨ)". injection Heq as <-.
        iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
        iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
        assert (length vs1 = 0) as ->%nil_length_inv by lia.
        iMod ("HΨ" with "[$Hmodel₁]") as "HΨ"; first iSteps.

        iSplitR "Hl_back_cache Hconsumer₁ HΨ HΦ". { iFrameSteps. }
        iIntros "!> {%- Hbranch2}".

        wp۰store. wp۰pures.
        iApply ("HΦ" $! _ front).
        rewrite !bool_decide_eq_false_2; [lia.. |]. iSteps.
  Qed.
  Lemma spsc_bqueue٠pop𑁒spec t ι cap :
    <<<
      spsc_bqueue۰inv t ι cap ∗
      spsc_bqueue۰consumer t
    | ∀∀ vs,
      spsc_bqueue۰model t vs
    >>>
      spsc_bqueue٠pop t @ ↑ι
    <<<
      spsc_bqueue۰model t (tail vs)
    | RET head vs;
      spsc_bqueue۰consumer t
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:consumer)) HΦ". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec.
    wp۰apply+ (front𑁒spec with "[$]") as "Hconsumer₁".
    iDestruct "Hback_lb" as "-#Hback_lb". wp۰apply+ (spsc_bqueue٠pop₀𑁒spec with "[$]") as (? back_cache') "(-> & Hl_back_cache & Hconsumer₁ & #Hback_lb & HΦ)".
    case_bool_decide as Hbranch; last iSteps.

    iApply fupd𑁒wp.
    iInv "Hinv" as "(:inv۰inner =1)".
    iDestruct (consumer𑁒agree with "Hconsumer₁ Hconsumer₂") as %(<- & <-).
    iDestruct (back۰lb𑁒valid with "Hproducer₂ Hback_lb") as %Hback1_ge.
    destruct vs1 as [| v vs1]; first naive_solver lia.
    iDestruct (history۰at𑁒get front v with "Hhistory_auth") as "#Hhistory_at".
    { rewrite -(take_drop front hist1) -Hvs1 lookup_app_r length_take; first lia.
      rewrite Nat.min_l; first lia.
      rewrite Nat.sub_diag //.
    }
    iMod (consumer𑁒update𑁒stability Unstable with "Hconsumer₁ Hconsumer₂") as "(Hconsumer₁ & Hconsumer₂)".
    iSplitR "Hl_back_cache Hconsumer₁ Hfront HΦ". { iFrameSteps. }
    iIntros "!> {%- Hbranch} !>".

    wp۰load.
    wp۰apply+ (array٠unsafe_cget𑁒spec𑁒cell with "Hfront") as "Hfront"; first done.
    wp۰apply+ (array٠unsafe_cset𑁒spec𑁒cell with "Hfront") as "Hfront_"; first done.
    wp۰pures.

    wp۰bind (_ <-{front} _)%E.
    iInv "Hinv" as "(:inv۰inner =2)".
    wp۰store.
    iDestruct (consumer𑁒agree with "Hconsumer₁ Hconsumer₂") as %(<- & <-).
    iDestruct (back۰lb𑁒valid with "Hproducer₂ Hback_lb") as %?.
    destruct vs2 as [| _v vs2]; first naive_solver lia.
    iDestruct (history𑁒agree with "Hhistory_auth Hhistory_at") as %Hhist2_lookup.
    assert (_v = v) as ->.
    { move: Hhist2_lookup.
      rewrite -(take_drop front hist2) -Hvs2 lookup_app_r length_take; first lia.
      rewrite Nat.min_l; first lia.
      rewrite Nat.sub_diag. naive_solver.
    }
    rewrite /= drop_0.
    iMod (consumer𑁒update𑁒stability Stable with "Hconsumer₁ Hconsumer₂") as "(Hconsumer₁ & Hconsumer₂)".
    iMod (consumer𑁒update𑁒front ˖front with "Hconsumer₁ Hconsumer₂") as "(Hconsumer₁ & Hconsumer₂)"; first lia.

    iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
    iMod (model𑁒pop with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[$Hmodel₁]") as "HΦ".
    { simpl in Hvs. iSteps. }

    iSplitR "Hl_back_cache Hconsumer₁ HΦ".
    { do 2 iModIntro. iExists _, ˖front, _, back2, vs2, hist2. iFrame. simpl in *.
      iStep 3.
      iSplit. { erewrite drop_S in Hvs2 => //. naive_solver. }
      iStep.
      rewrite assoc. iSplitL "Hvs".
      - rewrite -{1}(take_drop 1 vs2) fmap_app -array۰cslice𑁒app. simpl_length.
        destruct vs2.
        2: rewrite Nat.add_1_r.
        all: destruct pstable2; iSteps.
      - iApply array۰cslice𑁒shift in "Hfront_".
        case_decide as Hcase.
        + rewrite -Hcase decide_False; first lia.
          assert (γ.(metadata۰capacity) - (back2 - ˖front) - 1 = 0) as -> by lia.
          destruct pstable2; iSteps.
        + rewrite decide_False; first lia. iFrame.
          iDestruct (array۰cslice𑁒app₁ with "Hextra Hfront_") as "Hextra".
          { simpl_length. lia. }
          rewrite -replicate_S_end.
          assert (˖(γ.(metadata۰capacity) - (back2 - front) - 1) = γ.(metadata۰capacity) - (back2 - ˖front) - 1) as -> by lia.
          iSteps.
    }
    iSteps.
  Qed.
End spsc_bqueue۰G.

Require zoo_saturn.spsc_bqueue__opaque.

#[global] Opaque spsc_bqueue۰inv.
#[global] Opaque spsc_bqueue۰model.
#[global] Opaque spsc_bqueue۰producer.
#[global] Opaque spsc_bqueue۰consumer.
