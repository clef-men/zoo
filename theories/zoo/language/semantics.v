Require Import stdpp.gmap.

Require Import zoo.prelude.
Require Export zoo.language.physical_equality.
Require Export zoo.language.metatheory.
Require Export zoo.language.state.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type tag sz : nat.
Implicit Type n m : Z.
Implicit Type l : location.
Implicit Type gen : generativity.
Implicit Type mut : mutability.
Implicit Type lit : literal.
Implicit Type x : binder.
Implicit Type e : expr.
Implicit Type es : list expr.
Implicit Type v w : val.
Implicit Type vs : list val.
Implicit Type br : branch.
Implicit Type brs : list branch.
Implicit Type rec : recursive.
Implicit Type recs : list recursive.

Definition thread_id :=
  nat.
Implicit Type tid : thread_id.

Parameter encode_tag : nat → nat.

Axiom encode_tagｰinj :
  Inj (=) (=) encode_tag.
#[global] Existing Instance encode_tagｰinj.

Definition val۰immediate v :=
  match v with
  | ValLit lit =>
      match lit with
      | LitBool _
      | LitInt _ =>
          true
      | _ =>
          false
      end
  | ValRecs _ _ =>
      false
  | ValBlock _ _ [] =>
      true
  | ValBlock _ _ _ =>
      false
  end.
#[global] Arguments val۰immediate !_ / : assert.

Definition eval_unop op v :=
  match op, v with
  | UnopNeg, ValBool b =>
      Some $ ValBool (￢ b)
  | UnopMinus, ValInt n =>
      Some $ ValInt (- n)
  | UnopIsImmediate, v =>
      Some $ ValBool (val۰immediate v)
  | _, _ =>
      None
  end.
#[global] Arguments eval_unop !_ !_ / : assert.

Definition eval_binop۰int op n1 n2 :=
  match op with
  | BinopPlus =>
      LitInt (n1 + n2)
  | BinopMinus =>
      LitInt (n1 - n2)
  | BinopMult =>
      LitInt (n1 * n2)
  | BinopQuot =>
      LitInt (n1 `quot` n2)
  | BinopRem =>
      LitInt (n1 `rem` n2)
  | BinopLand =>
      LitInt (Z.land n1 n2)
  | BinopLor =>
      LitInt (Z.lor n1 n2)
  | BinopLsl =>
      LitInt (n1 ≪ n2)
  | BinopLsr =>
      LitInt (n1 ≫ n2)
  | BinopLe =>
      LitBool (bool_decide (n1 ≤ n2))
  | BinopLt =>
      LitBool (bool_decide (n1 < n2))
  | BinopGe =>
      LitBool (bool_decide (n1 >= n2))
  | BinopGt =>
      LitBool (bool_decide (n1 > n2))
  end%Z.
#[global] Arguments eval_binop۰int !_ _ _ / : assert.
Definition eval_binop op v1 v2 :=
  match v1, v2 with
  | ValInt n1, ValInt n2 =>
      Some $ ValLit $ eval_binop۰int op n1 n2
  | _, _ =>
      None
  end.
#[global] Arguments eval_binop _ !_ !_ / : assert.

Definition eval_app۰aux recs i rec :=
  subst' rec.1.1 (ValRecs i recs).
Definition eval_app' {A} foldri recs x v e : A :=
  foldri (eval_app۰aux recs) (subst' x v e).
Definition eval_app recs x v e :=
  eval_app' foldri recs x v e recs.

Variant subject :=
  | SubjectLoc l
  | SubjectBlock gen vs.
Implicit Type subj : subject.

Definition subject۰to_val tag subj :=
  match subj with
  | SubjectLoc l =>
      ValLoc l
  | SubjectBlock gen vs =>
      ValBlock gen tag vs
  end.

Fixpoint eval_match tag sz subj x_fb e_fb brs :=
  match brs with
  | [] =>
      Some $ subst' x_fb (subject۰to_val tag subj) e_fb
  | br :: brs =>
      let pat := br.1 in
      if pat.(pattern۰tag) ≟ tag && length pat.(pattern۰fields) ≟ sz then
        let res := subst' pat.(pattern۰as) (subject۰to_val tag subj) br.2 in
        match subj with
        | SubjectLoc l =>
            if forallb (BAnon ≟.) pat.(pattern۰fields) then
              Some res
            else
              None
        | SubjectBlock _ vs =>
            Some $ subst_list pat.(pattern۰fields) vs res
        end
      else
        eval_match tag sz subj x_fb e_fb brs
  end.
#[global] Arguments eval_match _ _ !_ _ _ !_ / : assert.

Definition observation : Set :=
  prophet_id * (val * val).

Inductive base_step tid : expr → state → list observation → expr → state → list expr → Prop :=
  | base_stepｰrec f x e σ :
      base_step
        tid
        (Rec f x e)
        σ
        []
        (Val $ ValRec f x e)
        σ
        []
  | base_stepｰapp i recs rec v σ :
      recs !! i = Some rec →
      base_step
        tid
        (App (Val $ ValRecs i recs) (Val v))
        σ
        []
        (eval_app recs rec.1.2 v rec.2)
        σ
        []
  | base_stepｰlet x v1 e2 σ :
      base_step
        tid
        (Let x (Val v1) e2)
        σ
        []
        (subst' x v1 e2)
        σ
        []
  | base_stepｰunop op v v' σ :
      eval_unop op v = Some v' →
      base_step
        tid
        (Unop op $ Val v)
        σ
        []
        (Val v')
        σ
        []
  | base_stepｰbinop op v1 v2 v' σ :
      eval_binop op v1 v2 = Some v' →
      base_step
        tid
        (Binop op (Val v1) (Val v2))
        σ
        []
        (Val v')
        σ
        []
  | base_stepｰequalｰfail v1 v2 σ :
      v1 ≉ v2 →
      base_step
        tid
        (Equal (Val v1) (Val v2))
        σ
        []
        (Val $ ValBool false)
        σ
        []
  | base_stepｰequalｰsuccess v1 v2 σ :
      v1 ≈ v2 →
      base_step
        tid
        (Equal (Val v1) (Val v2))
        σ
        []
        (Val $ ValBool true)
        σ
        []
  | base_stepｰif b e1 e2 σ :
      base_step
        tid
        (If (Val $ ValBool b) e1 e2)
        σ
        []
        (if b then e1 else e2)
        σ
        []
  | base_stepｰfor n1 n2 e σ :
      base_step
        tid
        (For (Val $ ValInt n1) (Val $ ValInt n2) e)
        σ
        []
        (if decide (n2 ≤ n1)%Z then Unit else Seq (App e (Val $ ValInt n1)) (For (Val $ ValInt (n1 + 1)) (Val $ ValInt n2) e))
        σ
        []
  | base_stepｰalloc tag n σ l :
      (0 ≤ n)%Z →
      state۰alloc_condition l ₊n σ →
      base_step
        tid
        (Alloc (Val $ ValNat tag) (Val $ ValInt n))
        σ
        []
        (Val $ ValLoc l)
        (state۰alloc l (Header tag ₊n) (replicate ₊n ValUnit) σ)
        []
  | base_stepｰblockｰmutable tag es vs σ l :
      0 < length es →
      es = of_vals vs →
      state۰alloc_condition l (length es) σ →
      base_step
        tid
        (Block Mutable tag es)
        σ
        []
        (Val $ ValLoc l)
        (state۰alloc l (Header tag (length es)) vs σ)
        []
  | base_stepｰblockｰimmutableｰnongenerative tag es vs σ :
      es = of_vals vs →
      base_step
        tid
        (Block ImmutableNongenerative tag es)
        σ
        []
        (Val $ ValBlock Nongenerative tag vs)
        σ
        []
  | base_stepｰblockｰimmutableｰgenerativeｰweak tag es vs σ :
      es = of_vals vs →
      base_step
        tid
        (Block ImmutableGenerativeWeak tag es)
        σ
        []
        (Val $ ValBlock (Generative None) tag vs)
        σ
        []
  | base_stepｰblockｰimmutableｰgenerativeｰstrong tag es vs σ bid :
      es = of_vals vs →
      base_step
        tid
        (Block ImmutableGenerativeStrong tag es)
        σ
        []
        (Val $ ValBlock (Generative (Some bid)) tag vs)
        σ
        []
  | base_stepｰmatchｰmutable l hdr x e brs e' σ :
      σ.(state۰headers) !! l = Some hdr →
      eval_match hdr.(header۰tag) hdr.(header۰size) (SubjectLoc l) x e brs = Some e' →
      base_step
        tid
        (Match (Val $ ValLoc l) x e brs)
        σ
        []
        e'
        σ
        []
  | base_stepｰmatchｰimmutable gen tag vs x e brs e' σ :
      eval_match tag (length vs) (SubjectBlock gen vs) x e brs = Some e' →
      base_step
        tid
        (Match (Val $ ValBlock gen tag vs) x e brs)
        σ
        []
        e'
        σ
        []
  | base_stepｰget_tagｰmutable l hdr σ :
      σ.(state۰headers) !! l = Some hdr →
      base_step
        tid
        (GetTag $ Val $ ValLoc l)
        σ
        []
        (Val $ ValNat (encode_tag hdr.(header۰tag)))
        σ
        []
  | base_stepｰget_tagｰimmutable gen tag vs σ :
      0 < length vs →
      base_step
        tid
        (GetTag $ Val $ ValBlock gen tag vs)
        σ
        []
        (Val $ ValNat (encode_tag tag))
        σ
        []
  | base_stepｰget_sizeｰmutable l hdr σ :
      σ.(state۰headers) !! l = Some hdr →
      base_step
        tid
        (GetSize $ Val $ ValLoc l)
        σ
        []
        (Val $ ValNat hdr.(header۰size))
        σ
        []
  | base_stepｰget_sizeｰimmutable gen tag vs σ :
      0 < length vs →
      base_step
        tid
        (GetSize $ Val $ ValBlock gen tag vs)
        σ
        []
        (Val $ ValNat (length vs))
        σ
        []
  | base_stepｰget_fieldｰmutable l fld v σ :
      σ.(state۰heap) !! (l +ₗ fld) = Some v →
      base_step
        tid
        (Load (Val $ ValLoc l) (Val $ ValInt fld))
        σ
        []
        (Val v)
        σ
        []
  | base_stepｰget_fieldｰimmutable gen tag vs (fld : nat) v σ :
      vs !! fld = Some v →
      base_step
        tid
        (Load (Val $ ValBlock gen tag vs) (Val $ ValNat fld))
        σ
        []
        (Val v)
        σ
        []
  | base_stepｰset_field l fld v σ :
      is_Some (σ.(state۰heap) !! (l +ₗ fld)) →
      base_step
        tid
        (Store (Val $ ValLoc l) (Val $ ValInt fld) (Val v))
        σ
        []
        Unit
        (state۰set_location (l +ₗ fld) v σ)
        []
  | base_stepｰxchg l fld v w σ :
      σ.(state۰heap) !! (l +ₗ fld) = Some w →
      base_step
        tid
        (Xchg (Val $ ValTuple [ValLoc l; ValInt fld]) (Val v))
        σ
        []
        (Val w)
        (state۰set_location (l +ₗ fld) v σ)
        []
  | base_stepｰcasｰfail l fld v1 v2 v σ :
      σ.(state۰heap) !! (l +ₗ fld) = Some v →
      v ≉ v1 →
      base_step
        tid
        (CAS (Val $ ValTuple [ValLoc l; ValInt fld]) (Val v1) (Val v2))
        σ
        []
        (Val $ ValBool false)
        σ
        []
  | base_stepｰcasｰsuccess l fld v1 v2 v σ :
      σ.(state۰heap) !! (l +ₗ fld) = Some v →
      v ≈ v1 →
      base_step
        tid
        (CAS (Val $ ValTuple [ValLoc l; ValInt fld]) (Val v1) (Val v2))
        σ
        []
        (Val $ ValBool true)
        (state۰set_location (l +ₗ fld) v2 σ)
        []
  | base_stepｰfaa l fld n m σ :
      σ.(state۰heap) !! (l +ₗ fld) = Some $ ValInt m →
      base_step
        tid
        (FAA (Val $ ValTuple [ValLoc l; ValInt fld]) (Val $ ValInt n))
        σ
        []
        (Val $ ValInt m)
        (state۰set_location (l +ₗ fld) (ValInt (m + n)) σ)
        []
  | base_stepｰfork e σ v :
      val۰immediate v →
      base_step
        tid
        (Fork e)
        σ
        []
        Unit
        (state۰add_local v σ)
        [e]
  | base_stepｰget_local v σ :
      σ.(state۰locals) !! tid = Some v →
      base_step
        tid
        GetLocal
        σ
        []
        (Val v)
        σ
        []
  | base_stepｰset_local v σ :
      is_Some (σ.(state۰locals) !! tid) →
      base_step
        tid
        (SetLocal (Val v))
        σ
        []
        Unit
        (state۰set_local tid v σ)
        []
  | base_stepｰproph σ pid :
      pid ∉ σ.(state۰prophets) →
      base_step
        tid
        Proph
        σ
        []
        (Val $ ValProph pid)
        (state۰add_prophet pid σ)
        []
  | base_stepｰresolve e pid v σ κ w σ' es :
      base_step tid e σ κ (Val w) σ' es →
      base_step
        tid
        (Resolve e (Val $ ValProph pid) (Val v))
        σ
        (κ ++ [(pid, (w, v))])
        (Val w)
        σ'
        es.

Lemma base_stepｰalloc' tid tag n σ :
  let l := state۰fresh σ in
  (0 ≤ n)%Z →
  base_step
    tid
    (Alloc (Val $ ValNat tag) (Val $ ValInt n))
    σ
    []
    (Val $ ValLoc l)
    (state۰alloc l (Header tag ₊n) (replicate ₊n ValUnit) σ)
    [].
Proof.
  intros l Hn.
  apply base_stepｰalloc. 1: done.
  apply state۰alloc_conditionｰfresh.
Qed.
Lemma base_stepｰblockｰmutable' tid tag es vs σ :
  let l := state۰fresh σ in
  0 < length es →
  es = of_vals vs →
  base_step
    tid
    (Block Mutable tag es)
    σ
    []
    (Val $ ValLoc l)
    (state۰alloc l (Header tag (length es)) vs σ)
    [].
Proof.
  intros l Hn ->.
  apply base_stepｰblockｰmutable. 1,2: done.
  apply state۰alloc_conditionｰfresh.
Qed.
Lemma base_stepｰblockｰimmutableｰgenerativeｰstrong' tid tag es vs σ :
  es = of_vals vs →
  base_step
    tid
    (Block ImmutableGenerativeStrong tag es)
    σ
    []
    (Val $ ValBlock (Generative (Some inhabitant)) tag vs)
    σ
    [].
Proof.
  apply base_stepｰblockｰimmutableｰgenerativeｰstrong.
Qed.
Lemma base_stepｰfork' tid e σ :
  base_step
    tid
    (Fork e)
    σ
    []
    Unit
    (state۰add_local inhabitant σ)
    [e].
Proof.
  apply base_stepｰfork. done.
Qed.
Lemma base_stepｰproph' tid σ :
  let pid := fresh σ.(state۰prophets) in
  base_step
    tid
    Proph
    σ
    []
    (Val $ ValProph pid)
    (state۰add_prophet pid σ)
    [].
Proof.
  constructor. apply is_fresh.
Qed.

Inductive ectxi :=
  | CtxApp1 v2
  | CtxApp2 e1
  | CtxLet x e2
  | CtxUnop (op : unop)
  | CtxBinop1 (op : binop) v2
  | CtxBinop2 (op : binop) e1
  | CtxEqual1 v2
  | CtxEqual2 e1
  | CtxIf e1 e2
  | CtxFor1 e2 e3
  | CtxFor2 v1 e3
  | CtxAlloc1 v2
  | CtxAlloc2 e1
  | CtxBlock mut tag es vs
  | CtxMatch x e1 brs
  | CtxGetTag
  | CtxGetSize
  | CtxLoad1 v2
  | CtxLoad2 e1
  | CtxStore1 v2 v3
  | CtxStore2 e1 v3
  | CtxStore3 e1 e2
  | CtxXchg1 v2
  | CtxXchg2 e1
  | CtxCAS0 v1 v2
  | CtxCAS1 e0 v2
  | CtxCAS2 e0 e1
  | CtxFAA1 v2
  | CtxFAA2 e1
  | CtxSetLocal
  | CtxResolve0 (k : ectxi) v1 v2
  | CtxResolve1 e0 v2
  | CtxResolve2 e0 e1.
Implicit Type k : ectxi.

Notation CtxSeq := (
  CtxLet BAnon
)(only parsing
).
Notation CtxTuple := (
  CtxBlock ImmutableNongenerative 0
)(only parsing
).

Fixpoint filli k e : expr :=
  match k with
  | CtxApp1 v2 =>
      App e $ Val v2
  | CtxApp2 e1 =>
      App e1 e
  | CtxLet x e2 =>
      Let x e e2
  | CtxUnop op =>
      Unop op e
  | CtxBinop1 op v2 =>
      Binop op e $ Val v2
  | CtxBinop2 op e1 =>
      Binop op e1 e
  | CtxEqual1 v2 =>
      Equal e $ Val v2
  | CtxEqual2 e1 =>
      Equal e1 e
  | CtxIf e1 e2 =>
      If e e1 e2
  | CtxFor1 e2 e3 =>
      For e e2 e3
  | CtxFor2 v1 e3 =>
      For (Val v1) e e3
  | CtxAlloc1 v2 =>
      Alloc e $ Val v2
  | CtxAlloc2 e1 =>
      Alloc e1 e
  | CtxBlock mut tag es vs =>
      Block mut tag $ es ++ e :: of_vals vs
  | CtxMatch x e1 brs =>
      Match e x e1 brs
  | CtxGetTag =>
      GetTag e
  | CtxGetSize =>
      GetSize e
  | CtxLoad1 v2 =>
      Load e (Val v2)
  | CtxLoad2 e1 =>
      Load e1 e
  | CtxStore1 v2 v3 =>
      Store e (Val v2) (Val v3)
  | CtxStore2 e1 v3 =>
      Store e1 e (Val v3)
  | CtxStore3 e1 e2 =>
      Store e1 e2 e
  | CtxXchg1 v2 =>
      Xchg e $ Val v2
  | CtxXchg2 e1 =>
      Xchg e1 e
  | CtxCAS0 v1 v2 =>
      CAS e (Val v1) (Val v2)
  | CtxCAS1 e0 v2 =>
      CAS e0 e $ Val v2
  | CtxCAS2 e0 e1 =>
      CAS e0 e1 e
  | CtxFAA1 v2 =>
      FAA e $ Val v2
  | CtxFAA2 e1 =>
      FAA e1 e
  | CtxSetLocal =>
      SetLocal e
  | CtxResolve0 k v1 v2 =>
      Resolve (filli k e) (Val v1) (Val v2)
  | CtxResolve1 e0 v2 =>
      Resolve e0 e $ Val v2
  | CtxResolve2 e0 e1 =>
      Resolve e0 e1 e
  end.
#[global] Arguments filli !_ _ / : assert.

Definition ectx :=
  list ectxi.

Definition fill K e :=
  foldl (flip filli) e K.

Definition config : Type :=
  list expr * state.
