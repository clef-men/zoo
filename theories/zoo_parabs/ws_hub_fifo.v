Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.iris.bi.big_op.
Require Import zoo.iris.base_logic.lib.excl.
Require Import zoo.iris.base_logic.lib.ghost_list.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_parabs.base.
Require Export zoo_parabs.ws_hub_fifo__code.
Require Import zoo_parabs.ws_hub_fifo__types.
Require Import zoo.options.

Implicit Type b closed : bool.
Implicit Type num_active : Z.
Implicit Type 𝑡 : location.
Implicit Type v t notification notify pred : val.
Implicit Type ws : list val.
Implicit Type vs : gmultiset val.
Implicit Type status : status.
Implicit Type empty : emptiness.
Implicit Type emptys : list emptiness.

Class WsHubFifoG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] ws_hub_fifo۰G۰queue۰G :: QueueMpmc1G Σ
  ; #[local] ws_hub_fifo۰G۰waiters۰G :: WaitersG Σ
  ; #[local] ws_hub_fifo۰G۰owner۰G :: ExclG Σ unitO
  ; #[local] ws_hub_fifo۰G۰emptiness۰G :: GhostListG Σ emptiness
  }.

Definition ws_hub_fifo۰Σ :=
  #[queue_mpmc_1۰Σ
  ; waiters۰Σ
  ; excl۰Σ unitO
  ; ghost_list۰Σ emptiness
  ].
#[global] Instance subGｰws_hub_fifo۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG ws_hub_fifo۰Σ Σ →
  WsHubFifoG Σ.
Proof.
  solve_inG.
Qed.

Section consistent.
  #[local] Definition consistent vs ws :=
    vs = list_to_set_disj ws.

  #[local] Lemma consistentｰnilｰinv vs :
    consistent vs [] →
    vs = ∅.
  Proof.
    done.
  Qed.

  #[local] Lemma consistentｰpush {vs ws} v :
    consistent vs ws →
    consistent ({[+v+]} ⊎ vs) (ws ++ [v]).
  Proof.
    intros ->.
    rewrite /consistent.
    rewrite list_to_set_disj_app list_to_set_disj_cons right_id (comm (⊎)) //.
  Qed.
  #[local] Lemma consistentｰpop vs v ws :
    consistent vs (v :: ws) →
      ∃ vs',
      vs = {[+v+]} ⊎ vs' ∧
      consistent vs' ws.
  Proof.
    naive_solver.
  Qed.
End consistent.

Opaque consistent.

Section ws_hub_fifo۰G.
  Context `{ws_hub_fifo۰G : WsHubFifoG Σ}.

  Implicit Type P P_notification P_pred Q Q_pred : iProp Σ.

  Record metadata :=
    { metadata۰size : nat
    ; metadata۰queue : val
    ; metadata۰waiters : val
    ; metadata۰owners : list gname
    ; metadata۰emptiness : gname
    }.
  Implicit Type γ : metadata.
  Implicit Type γ_owners : list gname.

  #[local] Instance metadataｰeq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[local] Instance metadataｰcountable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition owner' γ_owners sz i : iProp Σ :=
    ∃ γ_owner,
    ⌜γ_owners !! i = Some γ_owner⌝ ∗
    ⌜length γ_owners = sz⌝ ∗
    excl γ_owner ().
  #[local] Definition owner γ i :=
    owner' γ.(metadata۰owners) γ.(metadata۰size) i.
  #[local] Instance : CustomIpat "owner_" :=
    " ( %γ_owner{}
      & %Hlookup{}
      & %Hlength{_{}}
      & Howner{}
      )
    ".

  #[local] Definition emptiness۰auth' γ_emptiness sz vs : iProp Σ :=
    ∃ emptys,
    ghost_list۰auth γ_emptiness emptys ∗
    ⌜length emptys = sz⌝ ∗
    ⌜ vs = ∅
    ∨ ∃ i,
      emptys !! i = Some Nonempty
    ⌝.
  #[local] Definition emptiness۰auth γ :=
    emptiness۰auth' γ.(metadata۰emptiness) γ.(metadata۰size).
  #[local] Instance : CustomIpat "emptiness۰auth" :=
    " ( %emptys
      & Hauth
      & %Hemptys
      & %Hemptiness
      )
    ".
  #[local] Definition emptiness۰at' γ_emptiness i :=
    ghost_list۰at γ_emptiness i (DfracOwn 1).
  #[local] Definition emptiness۰at γ :=
    emptiness۰at' γ.(metadata۰emptiness).

  #[local] Definition inv۰inner 𝑡 : iProp Σ :=
    ∃ num_active,
    𝑡.[num_active] ↦ #num_active.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %num_active
      & H𝑡_num_active
      )
    ".
  Definition ws_hub_fifo۰inv t ι (sz : nat) : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    ⌜sz = γ.(metadata۰size)⌝ ∗
    𝑡 ↪ γ ∗
    𝑡.[size] ↦□ #γ.(metadata۰size) ∗
    𝑡.[queue] ↦□ γ.(metadata۰queue) ∗
    𝑡.[waiters] ↦□ γ.(metadata۰waiters) ∗
    queue_mpmc_1۰inv γ.(metadata۰queue) ι ∗
    waiters۰inv γ.(metadata۰waiters) sz ∗
    inv nroot (inv۰inner 𝑡).
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & ->
      & #Hmeta{}
      & #H𝑡{}_size
      & #H𝑡{}_queue
      & #H𝑡{}_waiters
      & #Hqueue{}_inv
      & #Hwaiters{}_inv
      & #Hinv{}
      )
    ".

  Definition ws_hub_fifo۰model t vs : iProp Σ :=
    ∃ 𝑡 γ ws,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    queue_mpmc_1۰model γ.(metadata۰queue) ws ∗
    ⌜consistent vs ws⌝ ∗
    emptiness۰auth γ vs.
  #[local] Instance : CustomIpat "model" :=
    " ( %l_
      & %γ_
      & %ws
      & %Heq
      & Hmeta_
      & Hqueue_model
      & %Hconsistent
      & Hemptiness_auth
      )
    ".

  Definition ws_hub_fifo۰owner t i status empty : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    owner γ i ∗
    emptiness۰at γ i empty.
  #[local] Instance : CustomIpat "owner" :=
    " ( %𝑡{;_}
      & %γ{;_}
      & %Heq{}
      & #Hmeta_{}
      & Howner{_{}}
      & Hemptiness_at{_{}}
      )
    ".

  #[global] Instance ws_hub_fifo۰modelｰtimeless t vs :
    Timeless (ws_hub_fifo۰model t vs).
  Proof.
    apply _.
  Qed.

  #[global] Instance ws_hub_fifo۰invｰpersistent t ι sz :
    Persistent (ws_hub_fifo۰inv t ι sz).
  Proof.
    apply _.
  Qed.

  #[local] Lemma ownerｰalloc sz :
    ⊢ |==>
      ∃ γ_owners,
      [∗ list] i ∈ seq 0 sz,
        owner' γ_owners sz i.
  Proof.
    iAssert (
      [∗ list] _ ∈ seq 0 sz,
        |==>
        ∃ γ_owner,
        excl (excl۰G := ws_hub_fifo۰G۰owner۰G) γ_owner ()
    )%I as "-#H".
    { iApply big_sepL_intro. iIntros "!> % % _".
      iApply exclｰalloc.
    }
    iMod (big_sepL_bupd with "H") as "H".
    iDestruct (big_sepLｰexists with "H") as "(%γ_owners & %Hlength & H)".
    iDestruct (big_sepL2_intro (λ _ _ _, ⌜length γ_owners = sz⌝)%I (seq 0 sz) γ_owners with "[%]") as "Hlength". 1: done.
    { simp_length in Hlength. naive_solver. }
    iDestruct (big_sepL2_sep_2 with "Hlength H") as "H".
    iDestruct (big_sepL2ｰretractｰr with "H") as "(_ & H)".
    iDestruct (big_sepLｰseqｰindex₂ with "H") as "H".
    { simp_length. }
    iSteps.
  Qed.
  #[local] Lemma ownerｰvalid γ i :
    owner γ i ⊢
    ⌜i < γ.(metadata۰size)⌝.
  Proof.
    iIntros "(:owner_)". iPureIntro.
    rewrite -Hlength. eapply lookup_lt_Some => //.
  Qed.
  #[local] Lemma ownerｰexclusive γ i :
    owner γ i -∗
    owner γ i -∗
    False.
  Proof.
    iIntros "(:owner_ =1) (:owner_ =2)". simp.
    iApply (exclｰexclusive with "Howner1 Howner2").
  Qed.

  Opaque owner'.

  #[local] Lemma emptinessｰalloc sz :
    ⊢ |==>
      ∃ γ_emptiness,
      emptiness۰auth' γ_emptiness sz ∅ ∗
      [∗ list] i ∈ seq 0 sz,
        emptiness۰at' γ_emptiness i Empty.
  Proof.
    iMod ghost_listｰalloc as "(%γ_emptiness & $ & Hats)".
    iDestruct (big_sepLｰreplicate₁ with "Hats") as "$".
    iSteps. iPureIntro. simp_length.
  Qed.
  #[local] Lemma emptiness۰atｰvalid γ vs i empty :
    emptiness۰auth γ vs -∗
    emptiness۰at γ i empty -∗
    ⌜i < γ.(metadata۰size)⌝.
  Proof.
    iIntros "(:emptiness۰auth) Hat".
    iDestruct (ghost_listｰlookup with "Hauth Hat") as %Hi%lookup_lt_Some.
    iSteps.
  Qed.
  #[local] Lemma emptinessｰempty γ vs :
    emptiness۰auth γ vs -∗
    ( [∗ list] i ∈ seq 0 γ.(metadata۰size),
      emptiness۰at γ i Empty
    ) -∗
    ⌜vs = ∅⌝.
  Proof.
    iIntros "(:emptiness۰auth) Hats".
    destruct Hemptiness as [-> | (i & Hlookup)]. 1: iSteps.
    iDestruct (big_sepL_lookup with "Hats") as "Hat".
    { apply lookup_lt_Some in Hlookup.
      rewrite lookup_seq -Hemptys /=. eauto.
    }
    iDestruct (ghost_listｰlookup with "Hauth Hat") as %?. congruence.
  Qed.
  #[local] Lemma emptinessｰupdateｰauth γ v vs :
    emptiness۰auth γ ({[+v+]} ⊎ vs) ⊢
    emptiness۰auth γ vs.
  Proof.
    iIntros "(:emptiness۰auth)".
    destruct Hemptiness as [? | (i & Hlookup)]. 2: iSteps.
    exfalso. multiset_solver.
  Qed.
  #[local] Lemma emptinessｰupdateｰNonempty {γ vs i empty} vs' :
    emptiness۰auth γ vs -∗
    emptiness۰at γ i empty ==∗
      emptiness۰auth γ vs' ∗
      emptiness۰at γ i Nonempty.
  Proof.
    iIntros "(:emptiness۰auth) Hat".
    iDestruct (ghost_listｰlookup with "Hauth Hat") as %Hi%lookup_lt_Some.
    iMod (ghost_listｰupdateｰat Nonempty with "Hauth Hat") as "($ & $)".
    iPureIntro. split.
    - simp_length.
    - right. exists i. apply list_lookup_insert_eq => //.
  Qed.
  #[local] Lemma emptinessｰupdateｰEmpty γ i empty :
    emptiness۰auth γ ∅ -∗
    emptiness۰at γ i empty ==∗
      emptiness۰auth γ ∅ ∗
      emptiness۰at γ i Empty.
  Proof.
    iIntros "(:emptiness۰auth) Hat".
    iMod (ghost_listｰupdateｰat Empty with "Hauth Hat") as "($ & $)".
    iSteps. simp_length.
  Qed.

  Opaque emptiness۰auth'.

  Lemma ws_hub_fifo۰invｰagree t ι sz1 sz2 :
    ws_hub_fifo۰inv t ι sz1 -∗
    ws_hub_fifo۰inv t ι sz2 -∗
    ⌜sz1 = sz2⌝.
  Proof.
    iIntros "(:inv =1) (:inv =2)". simp.
    iDestruct (pointstoｰagree with "H𝑡1_size H𝑡2_size") as %[=].
    iSteps.
  Qed.

  Lemma ws_hub_fifo۰ownerｰexclusive t i status1 empty1 status2 empty2 :
    ws_hub_fifo۰owner t i status1 empty1 -∗
    ws_hub_fifo۰owner t i status2 empty2 -∗
    False.
  Proof.
    iIntros "(:owner =1) (:owner =2)". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iApply (ownerｰexclusive with "Howner_1 Howner_2").
  Qed.

  Lemma ws_hub_fifoｰinvｰowner t ι sz i status empty :
    ws_hub_fifo۰inv t ι sz -∗
    ws_hub_fifo۰owner t i status empty -∗
    ⌜i < sz⌝.
  Proof.
    iIntros "(:inv) (:owner)". simp.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-.
    iApply (ownerｰvalid with "Howner").
  Qed.

  Lemma ws_hub_fifo۰modelｰempty t ι sz vs :
    ws_hub_fifo۰inv t ι sz -∗
    ws_hub_fifo۰model t vs -∗
    ( [∗ list] i ∈ seq 0 sz,
      ∃ status,
      ws_hub_fifo۰owner t i status Empty
    ) -∗
    ⌜vs = ∅⌝.
  Proof.
    iIntros "(:inv) (:model) Howners". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iApply (emptinessｰempty with "Hemptiness_auth").
    iApply (big_sepLｰseqｰimpl with "Howners"). iIntros "!> %i %Hi (%status & (:owner)) /=". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iSteps.
  Qed.

  Lemma ws_hub_fifo٠createｰspec ι sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      ws_hub_fifo٠create #sz
    {{{
      t
    , RET t;
      ws_hub_fifo۰inv t ι ₊sz ∗
      ws_hub_fifo۰model t ∅ ∗
      [∗ list] i ∈ seq 0 ₊sz,
        ws_hub_fifo۰owner t i Nonblocked Empty
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".

    wp۰rec.
    wp۰apply+ (waiters٠createｰspec with "[//]") as (waiters) "#Hwaiters_inv". 1: done.
    wp۰apply (queue_mpmc_1٠createｰspec with "[//]") as (queue) "(#Hqueue_inv & Hqueue_model)".
    wp۰block 𝑡 as "Hmeta" "#H𝑡_size #H𝑡_queue #H𝑡_waiters H𝑡_num_active".

    iMod ownerｰalloc as "(%γ_owners & Howners)".
    iMod (emptinessｰalloc ₊sz) as "(%γ_emptiness & Hemptiness_auth & Hemptiness_ats)".

    pose γ :=
      {|metadata۰size := ₊sz
      ; metadata۰queue := queue
      ; metadata۰waiters := waiters
      ; metadata۰owners := γ_owners
      ; metadata۰emptiness := γ_emptiness
      |}.

    iMod (metaｰset γ with "Hmeta") as "#Hmeta". 1: done.

    iApply "HΦ".
    iSplitL "H𝑡_num_active".
    { iExists 𝑡, γ. iSteps. }
    iSplitL "Hqueue_model Hemptiness_auth".
    { iSteps. }
    iDestruct (big_sepL_sep_2 with "Howners Hemptiness_ats") as "Howners".
    iApply (big_sepLｰseqｰimpl with "Howners").
    iSteps.
  Qed.

  Lemma ws_hub_fifo٠sizeｰspec t ι sz :
    {{{
      ws_hub_fifo۰inv t ι sz
    }}}
      ws_hub_fifo٠size t
    {{{
      RET #sz;
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma ws_hub_fifo٠begin_inactiveｰspec t ι sz :
    {{{
      ws_hub_fifo۰inv t ι sz
    }}}
      ws_hub_fifo٠begin_inactive t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma ws_hub_fifo٠end_inactiveｰspec t ι sz :
    {{{
      ws_hub_fifo۰inv t ι sz
    }}}
      ws_hub_fifo٠end_inactive t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma ws_hub_fifo٠blockｰspec t ι sz i i_ empty :
    i = ⁺i_ →
    {{{
      ws_hub_fifo۰inv t ι sz ∗
      ws_hub_fifo۰owner t i_ Nonblocked empty
    }}}
      ws_hub_fifo٠block t #i
    {{{
      RET ();
      ws_hub_fifo۰owner t i_ Blocked empty
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hinv & Howner) HΦ".

    wp۰rec.
    wp۰apply+ (ws_hub_fifo٠begin_inactiveｰspec with "Hinv") as "_".
    iApply ("HΦ" with "Howner").
  Qed.

  Lemma ws_hub_fifo٠unblockｰspec t ι sz i i_ empty :
    i = ⁺i_ →
    {{{
      ws_hub_fifo۰inv t ι sz ∗
      ws_hub_fifo۰owner t i_ Blocked empty
    }}}
      ws_hub_fifo٠unblock t #i
    {{{
      RET ();
      ws_hub_fifo۰owner t i_ Nonblocked empty
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hinv & Howner) HΦ".

    wp۰rec.
    wp۰apply+ (ws_hub_fifo٠end_inactiveｰspec with "Hinv") as "_".
    iApply ("HΦ" with "Howner").
  Qed.

  Lemma ws_hub_fifo٠closedｰspec t ι sz :
    {{{
      ws_hub_fifo۰inv t ι sz
    }}}
      ws_hub_fifo٠closed t
    {{{
      closed
    , RET #closed;
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma ws_hub_fifo٠notifyｰspec t ι sz :
    {{{
      ws_hub_fifo۰inv t ι sz
    }}}
      ws_hub_fifo٠notify t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec. wp۰load.
    wp۰apply (waiters٠notify_oneｰspec with "Hwaiters_inv HΦ").
  Qed.

  #[local] Lemma ws_hub_fifo٠notify_allｰspec t ι sz :
    {{{
      ws_hub_fifo۰inv t ι sz
    }}}
      ws_hub_fifo٠notify_all t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec. wp۰load.
    wp۰apply (waiters٠notify_allｰspec with "Hwaiters_inv HΦ").
  Qed.

  Lemma ws_hub_fifo٠pushｰspec t ι sz i i_ empty v :
    i = ⁺i_ →
    <<<
      ws_hub_fifo۰inv t ι sz ∗
      ws_hub_fifo۰owner t i_ Nonblocked empty
    | ∀∀ vs,
      ws_hub_fifo۰model t vs
    >>>
      ws_hub_fifo٠push t #i v @ ↑ι
    <<<
      ws_hub_fifo۰model t ({[+v+]} ⊎ vs)
    | RET ();
      ws_hub_fifo۰owner t i_ Nonblocked Nonempty
    >>>.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    iApply (wpｰframeｰwand with "Howner").

    wp۰rec. wp۰load.

    awp۰apply (queue_mpmc_1٠pushｰspec with "Hqueue_inv").
    iApply (aaccｰaupdｰcommit with "HΦ"). 1: solve_ndisj. iIntros "%vs (:model)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iAaccIntro with "Hqueue_model". 1: iSteps. iIntros "Hqueue_model".
    iMod (emptinessｰupdateｰNonempty ({[+v+]} ⊎ vs) with "Hemptiness_auth Hemptiness_at") as "(Hemptiness_auth & Hemptiness_at)".
    iSplitR "Hemptiness_at".
    { iFrameSteps. iPureIntro. apply consistentｰpush => //. }
    iIntros "!> HΦ !> _ {%}".

    wp۰apply+ ws_hub_fifo٠notifyｰspec as "_". 1: iSteps.
    iSteps.
  Qed.

  #[local] Lemma ws_hub_fifo٠pop'ｰspecｰaux (owner : option (nat * emptiness)) t ι sz :
    <<<
      ws_hub_fifo۰inv t ι sz ∗
      match owner with
      | None =>
          True
      | Some (i, empty) =>
          ws_hub_fifo۰owner t i Nonblocked empty
      end
    | ∀∀ vs,
      ws_hub_fifo۰model t vs
    >>>
      ws_hub_fifo٠pop' t @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_fifo۰model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_fifo۰model t vs'
      end
    | RET o;
      match owner with
      | None =>
          True
      | Some (i, empty) =>
          ws_hub_fifo۰owner t i Nonblocked (if o then empty else Empty)
      end
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & Howner) HΦ".

    wp۰rec. wp۰load.

    awp۰apply+ (queue_mpmc_1٠popｰspec with "Hqueue_inv").
    iApply (aaccｰaupdｰcommit with "HΦ"). 1: solve_ndisj. iIntros "%vs (:model)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iAaccIntro with "Hqueue_model". 1: iSteps. iIntros "Hqueue_model".
    iExists (head ws).
    destruct ws as [| v ws] => /=.

    - apply consistentｰnilｰinv in Hconsistent as ->.

      iAssert (
        emptiness۰auth γ ∅ ∗
        match owner with
        | None =>
            True
        | Some (i, empty) =>
            ws_hub_fifo۰owner #𝑡 i Nonblocked Empty
        end
      )%I with "[> Hemptiness_auth Howner]" as "(Hemptiness_auth & Howner)".
      { destruct owner as [(i, empty) |]. 2: iSteps.
        iDestruct "Howner" as "(:owner)". injection Heq as <-.
        iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-.
        iMod (emptinessｰupdateｰEmpty with "Hemptiness_auth Hemptiness_at") as "($ & $)".
        iFrameSteps.
      }

      iSteps.

    - apply consistentｰpop in Hconsistent as (vs' & -> & Hconsistent).
      iDestruct (emptinessｰupdateｰauth with "Hemptiness_auth") as "Hemptiness_auth".
      iSteps.
  Qed.
  #[local] Lemma ws_hub_fifo٠pop'ｰspec t ι sz :
    <<<
      ws_hub_fifo۰inv t ι sz
    | ∀∀ vs,
      ws_hub_fifo۰model t vs
    >>>
      ws_hub_fifo٠pop' t @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_fifo۰model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_fifo۰model t vs'
      end
    | RET o;
      True
    >>>.
  Proof.
    iIntros "%Φ Hinv HΦ".

    wp۰apply (ws_hub_fifo٠pop'ｰspecｰaux None with "[$Hinv] HΦ").
  Qed.
  #[local] Lemma ws_hub_fifo٠pop'ｰspecｰowner t ι sz i empty :
    <<<
      ws_hub_fifo۰inv t ι sz ∗
      ws_hub_fifo۰owner t i Nonblocked empty
    | ∀∀ vs,
      ws_hub_fifo۰model t vs
    >>>
      ws_hub_fifo٠pop' t @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_fifo۰model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_fifo۰model t vs'
      end
    | RET o;
      ws_hub_fifo۰owner t i Nonblocked (if o then empty else Empty)
    >>>.
  Proof.
    iIntros "%Φ (#Hinv & Howner) HΦ".

    wp۰apply (ws_hub_fifo٠pop'ｰspecｰaux (Some (i, empty)) with "[$Hinv $Howner] HΦ").
  Qed.

  Lemma ws_hub_fifo٠popｰspec t ι sz i i_ empty :
    i = ⁺i_ →
    <<<
      ws_hub_fifo۰inv t ι sz ∗
      ws_hub_fifo۰owner t i_ Nonblocked empty
    | ∀∀ vs,
      ws_hub_fifo۰model t vs
    >>>
      ws_hub_fifo٠pop t #i @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_fifo۰model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_fifo۰model t vs'
      end
    | RET o;
      ws_hub_fifo۰owner t i_ Nonblocked (if o then empty else Empty)
    >>>.
  Proof.
    iIntros (->) "%Φ (#Hinv & Howner) HΦ".

    wp۰rec.
    wp۰apply+ (ws_hub_fifo٠pop'ｰspecｰowner with "[$Hinv $Howner] HΦ").
  Qed.

  #[local] Lemma ws_hub_fifo٠steal_auxｰspec P_notification P_pred Q_pred t ι (sz : nat) i notification pred :
    (0 ≤ i < sz)%Z →
    <<<
      ws_hub_fifo۰inv t ι sz ∗
      P_notification ∗
      ( ∀ notify,
        P_notification -∗
        WP notify () {{ itype۰unit }} -∗
        WP notification notify {{ res,
          ⌜res = ()%V⌝ ∗
          P_notification
        }}
      ) ∗
      P_pred ∗
      □ (
        P_pred -∗
        WP pred () {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          if b then Q_pred else P_pred
        }}
      )
    | ∀∀ vs,
      ws_hub_fifo۰model t vs
    >>>
      ws_hub_fifo٠steal_aux t #i notification pred @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_fifo۰model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_fifo۰model t vs'
      end
    | RET o;
      P_notification ∗
      if o then P_pred else Q_pred
    >>>.
  Proof.
    iIntros "%Hi %Φ ((:inv) & HP_notification & Hnotification & HP_pred & #Hpred) HΦ".

    iLöb as "HLöb" forall (notification).

    wp۰rec. wp۰load.
    wp۰apply (waiters٠prepare_waitｰspec with "Hwaiters_inv") as "_". 1: done.
    wp۰apply+ (wpｰwand with "(Hnotification HP_notification [])") as (res) "(-> & HP_notification)".
    { wp۰load.
      wp۰apply (waiters٠notifyｰspec with "Hwaiters_inv") => //.
    }
    wp۰apply+ (wpｰwand with "(Hpred HP_pred)") as (res) "(%b & -> & Hb)".
    destruct b; wp۰pures.

    - wp۰load.
      wp۰apply (waiters٠cancel_waitｰspec with "Hwaiters_inv") as (b) "_". 1: done.

      wp۰bind (𝗶𝗳 _ 𝘁𝗵𝗲𝗻 _ 𝗲𝗹𝘀𝗲 _)%E.
      wp۰apply (wpｰwand itype۰unit) as (res) "->".
      { destruct b; wp۰pures. 1: iSteps.
        wp۰load.
        wp۰apply (waiters٠notify_oneｰspec with "Hwaiters_inv") => //.
      }

      iApply fupdｰwp.
      iMod "HΦ" as "(%vs & Hmodel & _ & HΦ)".
      iMod ("HΦ" $! None with "Hmodel") as "HΦ".
      iSteps.

    - awp۰apply+ ws_hub_fifo٠pop'ｰspec. 1: iSteps.
      iApply (aaccｰaupd with "HΦ"). 1: done. iIntros "%vs Hmodel".
      iAaccIntro with "Hmodel". 1: iSteps. iIntros ([v |]) "Hmodel".

      + iRight. iExists (Some v). iFrame. iIntros "!> HΦ !> _".
        wp۰load.
        wp۰apply (waiters٠cancel_waitｰspec with "Hwaiters_inv"). 1: done.
        iSteps.

      + iLeft. iFrame. iIntros "!> HΦ !> _".
        wp۰load.
        wp۰apply (waiters٠commit_waitｰspec with "Hwaiters_inv") as "_". 1: done.
        wp۰apply+ ("HLöb" with "HP_notification [] Hb HΦ"). 1: iSteps.
  Qed.

  Lemma ws_hub_fifo٠steal_untilｰspec P_notification P_pred Q_pred t ι sz i i_ empty max_round_noyield max_round_yield notification pred :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_fifo۰inv t ι sz ∗
      ws_hub_fifo۰owner t i_ Nonblocked empty ∗
      P_notification ∗
      ( ∀ notify,
        P_notification -∗
        WP notify () {{ itype۰unit }} -∗
        WP notification notify {{ res,
          ⌜res = ()%V⌝ ∗
          P_notification
        }}
      ) ∗
      P_pred ∗
      □ (
        P_pred -∗
        WP pred () {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          if b then Q_pred else P_pred
        }}
      )
    | ∀∀ vs,
      ws_hub_fifo۰model t vs
    >>>
      ws_hub_fifo٠steal_until t #i #max_round_noyield #max_round_yield notification pred @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_fifo۰model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_fifo۰model t vs'
      end
    | RET o;
      ws_hub_fifo۰owner t i_ Nonblocked empty ∗
      P_notification ∗
      if o then P_pred else Q_pred
    >>>.
  Proof.
    iIntros (-> _ _) "%Φ (#Hinv & Howner & HP_notification & Hnotification & HP_pred & #Hpred) HΦ".
    iDestruct (ws_hub_fifoｰinvｰowner with "Hinv Howner") as %Hi.

    wp۰rec.

    wp۰apply+ (ws_hub_fifo٠steal_auxｰspec P_notification P_pred Q_pred with "[$Hinv $HP_notification $Hnotification $HP_pred $Hpred]"). 1: lia.
    iApply (atomic_updateｰwand with "HΦ"). iIntros "%vs %o HΦ H".

    iApply ("HΦ" with "[$Howner $H]").
  Qed.

  Lemma ws_hub_fifo٠stealｰspec t ι sz i i_ empty max_round_noyield max_round_yield :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_fifo۰inv t ι sz ∗
      ws_hub_fifo۰owner t i_ Nonblocked empty
    | ∀∀ vs,
      ws_hub_fifo۰model t vs
    >>>
      ws_hub_fifo٠steal t #i #max_round_noyield #max_round_yield @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_fifo۰model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_fifo۰model t vs'
      end
    | RET o;
      ws_hub_fifo۰owner t i_ (if o then Nonblocked else Blocked) empty
    >>>.
  Proof.
    iIntros (-> _ _) "%Φ (#Hinv & Howner) HΦ".
    iDestruct (ws_hub_fifoｰinvｰowner with "Hinv Howner") as %Hi.

    wp۰rec.
    wp۰apply+ (ws_hub_fifo٠begin_inactiveｰspec with "Hinv") as "_".

    wp۰apply+ (ws_hub_fifo٠steal_auxｰspec True True True with "[$Hinv]"). 1: lia.
    { iStep. iSplit. 1: iSteps. iStep 3.
      wp۰apply+ (ws_hub_fifo٠closedｰspec with "Hinv") as ([]) "_".
      all: iSteps.
    }
    iApply (atomic_updateｰwand with "HΦ"). iIntros "%vs %o HΦ _".

    wp۰pures.

    wp۰bind (Match _ _ _ _).
    wp۰apply (wpｰwand itype۰unit) as (res) "->".
    { destruct o as [v |]; wp۰pures.
      - wp۰apply (ws_hub_fifo٠end_inactiveｰspec with "Hinv") => //.
      - wp۰apply (ws_hub_fifo٠notify_allｰspec with "Hinv") => //.
    }

    wp۰pures.

    iApply ("HΦ" with "Howner").
  Qed.

  Lemma ws_hub_fifo٠closeｰspec t ι sz :
    {{{
      ws_hub_fifo۰inv t ι sz
    }}}
      ws_hub_fifo٠close t
    {{{
      RET ();
      True
    }}}.
  Proof.
    apply ws_hub_fifo٠begin_inactiveｰspec.
  Qed.
End ws_hub_fifo۰G.

#[global] Opaque ws_hub_fifo۰inv.
#[global] Opaque ws_hub_fifo۰model.
#[global] Opaque ws_hub_fifo۰owner.

Section ws_hub_fifo۰G.
  Context `{ws_hub_fifo۰G : WsHubFifoG Σ}.

  Implicit Type P P_notification P_pred Q Q_pred : iProp Σ.

  Lemma ws_hub_fifo٠pop_steal_untilｰspec P_notification P_pred Q_pred t ι sz i i_ empty max_round_noyield max_round_yield notification pred :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_fifo۰inv t ι sz ∗
      ws_hub_fifo۰owner t i_ Nonblocked empty ∗
      P_notification ∗
      ( ∀ notify,
        P_notification -∗
        WP notify () {{ itype۰unit }} -∗
        WP notification notify {{ res,
          ⌜res = ()%V⌝ ∗
          P_notification
        }}
      ) ∗
      P_pred ∗
      □ (
        P_pred -∗
        WP pred () {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          if b then Q_pred else P_pred
        }}
      )
    | ∀∀ vs,
      ws_hub_fifo۰model t vs
    >>>
      ws_hub_fifo٠pop_steal_until t #i #max_round_noyield #max_round_yield notification pred @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_fifo۰model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_fifo۰model t vs'
      end
    | empty,
      RET o;
      ws_hub_fifo۰owner t i_ Nonblocked empty ∗
      P_notification ∗
      if o then P_pred else Q_pred
    >>>.
  Proof.
    iIntros (-> Hmax_round_noyield Hmax_round_yield) "%Φ (#Hinv & Howner & HP_notification & Hnotification & HP_pred & #Hpred) HΦ".

    wp۰rec.
    wp۰apply+ (wpｰwand with "(Hpred HP_pred)") as (res) "(%b & -> & Hb)".
    destruct b; wp۰pures.

    - iMod "HΦ" as "(%vs & Hmodel & _ & HΦ)".
      iMod ("HΦ" $! None with "Hmodel") as "HΦ".
      iSteps.

    - awp۰apply+ (ws_hub_fifo٠popｰspec with "[$Hinv $Howner]"). 1: done.
      iApply (aaccｰaupd with "HΦ"). 1: done. iIntros "%vs Hmodel".
      iAaccIntro with "Hmodel". 1: iFrameSteps. iIntros ([v |]) "Hmodel !>".

      + iRight. iExists (Some v). iFrameSteps.

      + iLeft. iFrame. iIntros "HΦ !> Howner {%- Hmax_round_noyield Hmax_round_yield}".

        wp۰apply+ (ws_hub_fifo٠steal_untilｰspec P_notification P_pred Q_pred with "[$Hinv $Howner $HP_notification $Hnotification $Hb $Hpred]"). 1-3: done.
        iApply (atomic_updateｰwand with "HΦ").
        iSteps.
  Qed.

  Lemma ws_hub_fifo٠pop_stealｰspec t ι sz i i_ empty max_round_noyield max_round_yield :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_fifo۰inv t ι sz ∗
      ws_hub_fifo۰owner t i_ Nonblocked empty
    | ∀∀ vs,
      ws_hub_fifo۰model t vs
    >>>
      ws_hub_fifo٠pop_steal t #i #max_round_noyield #max_round_yield @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_fifo۰model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_fifo۰model t vs'
      end
    | empty,
      RET o;
      ws_hub_fifo۰owner t i_ (if o then Nonblocked else Blocked) empty ∗
      if o then
        True
      else
        ⌜empty = Empty⌝
    >>>.
  Proof.
    iIntros (->) "%Hmax_round_noyield %Hmax_round_yield %Φ (#Hinv & Howner) HΦ".

    wp۰rec.

    awp۰apply+ (ws_hub_fifo٠popｰspec with "[$Hinv $Howner]"). 1: done.
    iApply (aaccｰaupd with "HΦ"). 1: done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel". 1: iSteps. iIntros ([v |]) "Hmodel !>".

    - iDestruct "Hmodel" as "(%vs' & -> & Hmodel)".
      iRight. iExists (Some v). iSteps.

    - iLeft. iFrame. iIntros "HΦ !> Howner {%- Hmax_round_noyield Hmax_round_yield}".

      wp۰apply+ (ws_hub_fifo٠stealｰspec with "[$Hinv $Howner]"). 1-3: done.
      iApply (atomic_updateｰwand with "HΦ"). iIntros "%vs %o HΦ Howner".
      iApply ("HΦ" with "[$Howner]").
      destruct o; iFrameSteps.
  Qed.
End ws_hub_fifo۰G.

Require zoo_parabs.ws_hub_fifo__opaque.
