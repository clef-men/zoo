Require Import stdpp.gmap.

Require Import zoo.prelude.
Require Export zoo.language.physical_equality.
Require Export zoo.language.metatheory.
Require Export zoo.language.state.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type sz : nat.
Implicit Type n m : Z.
Implicit Type str : string.
Implicit Type tag : tag.
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
Implicit Type hdr : header.
Implicit Type resolve : val * val.
Implicit Type resolves : list (val * val).

Definition thread_id :=
  nat.
Implicit Type tid : thread_id.

Definition literal۰immediate lit :=
  match lit with
  | LitBool _
  | LitChar _
  | LitInt _ =>
      true
  | LitString _
  | LitLoc _
  | LitProph _ =>
      false
  end.
#[global] Arguments literal۰immediate !_ / : assert.

Definition val۰immediate v :=
  match v with
  | ValLit lit =>
      literal۰immediate lit
  | ValRecs _ _ =>
      false
  | ValBlock _ _ [] =>
      true
  | ValBlock _ _ _ =>
      false
  end.
#[global] Arguments val۰immediate !_ / : assert.

Definition eval۰apply۰aux recs i rec e :=
  subst' rec.1.1 (ValRecs i recs) e.
Definition eval۰apply' {A} foldri recs x v e : A :=
  foldri (eval۰apply۰aux recs) (subst' x v e).
Definition eval۰apply recs x v e :=
  eval۰apply' foldri recs x v e recs.

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

Fixpoint eval۰match tag sz subj x_fb e_fb brs :=
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
        eval۰match tag sz subj x_fb e_fb brs
  end.
#[global] Arguments eval۰match _ _ !_ _ _ !_ / : assert.

Definition eval۰unop op v :=
  match op, v with
  | UnopNeg, ValBool b =>
      Some $ LitBool (￢ b)
  | UnopMinus, ValInt n =>
      Some $ LitInt (- n)
  | _, _ =>
      None
  end.
#[global] Arguments eval۰unop !_ !_ / : assert.

Definition eval۰binop op n1 n2 :=
  match op with
  | BinopPlus =>
      LitInt $ n1 + n2
  | BinopMinus =>
      LitInt $ n1 - n2
  | BinopMult =>
      LitInt $ n1 * n2
  | BinopQuot =>
      LitInt $ n1 `quot` n2
  | BinopRem =>
      LitInt $ n1 `rem` n2
  | BinopLand =>
      LitInt $ Z.land n1 n2
  | BinopLor =>
      LitInt $ Z.lor n1 n2
  | BinopLsl =>
      LitInt $ n1 ≪ n2
  | BinopLsr =>
      LitInt $ n1 ≫ n2
  | BinopLe =>
      LitBool $ bool_decide (n1 ≤ n2)
  | BinopLt =>
      LitBool $ bool_decide (n1 < n2)
  | BinopGe =>
      LitBool $ bool_decide (n1 >= n2)
  | BinopGt =>
      LitBool $ bool_decide (n1 > n2)
  end%Z.
#[global] Arguments eval۰binop !_ _ _ / : assert.

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
  | base_stepｰapply i recs rec v σ :
      recs !! i = Some rec →
      base_step
        tid
        (Apply (Val $ ValRecs i recs) (Val v))
        σ
        []
        (eval۰apply recs rec.1.2 v rec.2)
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
  | base_stepｰif b e1 e2 σ :
      base_step
        tid
        (If (Val $ ValBool b) e1 e2)
        σ
        []
        (if b then e1 else e2)
        σ
        []
  | base_stepｰwhile e0 e1 σ :
      base_step
        tid
        (While e0 e1)
        σ
        []
        (If e0 (Seq e1 (While e0 e1)) Unit)
        σ
        []
  | base_stepｰfor n1 n2 e σ :
      base_step
        tid
        (For (Val $ ValInt n1) (Val $ ValInt n2) e)
        σ
        []
        (if decide (n2 ≤ n1)%Z then Unit else Seq (Apply e (Val $ ValInt n1)) (For (Val $ ValInt (n1 + 1)) (Val $ ValInt n2) e))
        σ
        []
  | base_stepｰmatchｰlocation l hdr x e brs e' σ :
      σ.(state۰headers) !! l = Some hdr →
      eval۰match hdr.(header۰tag) hdr.(header۰size) (SubjectLoc l) x e brs = Some e' →
      base_step
        tid
        (Match (Val $ ValLoc l) x e brs)
        σ
        []
        e'
        σ
        []
  | base_stepｰmatchｰblock gen tag vs x e brs e' σ :
      eval۰match tag (length vs) (SubjectBlock gen vs) x e brs = Some e' →
      base_step
        tid
        (Match (Val $ ValBlock gen tag vs) x e brs)
        σ
        []
        e'
        σ
        []
  | base_stepｰunop op v lit σ :
      eval۰unop op v = Some lit →
      base_step
        tid
        (Primitive1 (Unop op) (Val v))
        σ
        []
        (Val $ ValLit lit)
        σ
        []
  | base_stepｰis_immediate v σ :
      base_step
        tid
        (Primitive1 IsImmediate (Val v))
        σ
        []
        (Val $ ValBool (val۰immediate v))
        σ
        []
  | base_stepｰbinop op n1 n2 σ :
      base_step
        tid
        (Primitive2 (Binop op) (Val $ ValInt n1) (Val $ ValInt n2))
        σ
        []
        (Val $ ValLit $ eval۰binop op n1 n2)
        σ
        []
  | base_stepｰstring_get str i chr σ :
      (0 ≤ i)%Z →
      String.get ₊i str = Some chr →
      base_step
        tid
        (Primitive2 StringGet (Val $ ValString str) (Val $ ValInt i))
        σ
        []
        (Val $ ValChar chr)
        σ
        []
  | base_stepｰstring_equal str1 str2 σ :
      base_step
        tid
        (Primitive2 StringEqual (Val $ ValString str1) (Val $ ValString str2))
        σ
        []
        (Val $ ValBool (bool_decide (str1 = str2)))
        σ
        []
  | base_stepｰequalｰfail v1 v2 σ :
      v1 ≉ v2 →
      base_step
        tid
        (Primitive2 Equal (Val v1) (Val v2))
        σ
        []
        (Val $ ValBool false)
        σ
        []
  | base_stepｰequalｰsuccess v1 v2 σ :
      v1 ≈ v2 →
      base_step
        tid
        (Primitive2 Equal (Val v1) (Val v2))
        σ
        []
        (Val $ ValBool true)
        σ
        []
  | base_stepｰblockｰmutable tag es vs σ l :
      0 < length es →
      es = expr۰of_vals vs →
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
      es = expr۰of_vals vs →
      base_step
        tid
        (Block ImmutableNongenerative tag es)
        σ
        []
        (Val $ ValBlock Nongenerative tag vs)
        σ
        []
  | base_stepｰblockｰimmutableｰgenerativeｰweak tag es vs σ :
      es = expr۰of_vals vs →
      base_step
        tid
        (Block ImmutableGenerativeWeak tag es)
        σ
        []
        (Val $ ValBlock (Generative None) tag vs)
        σ
        []
  | base_stepｰblockｰimmutableｰgenerativeｰstrong tag es vs σ bid :
      es = expr۰of_vals vs →
      base_step
        tid
        (Block ImmutableGenerativeStrong tag es)
        σ
        []
        (Val $ ValBlock (Generative (Some bid)) tag vs)
        σ
        []
  | base_stepｰalloc 𝑡𝑎𝑔 tag n σ l :
      tag۰of_Z 𝑡𝑎𝑔 = Some tag →
      (0 ≤ n)%Z →
      state۰alloc_condition l ₊n σ →
      base_step
        tid
        (Primitive2 Alloc (Val $ ValInt 𝑡𝑎𝑔) (Val $ ValInt n))
        σ
        []
        (Val $ ValLoc l)
        (state۰alloc l (Header tag ₊n) (replicate ₊n ValUnit) σ)
        []
  | base_stepｰget_tagｰstring str σ :
      base_step
        tid
        (Primitive1 GetTag (Val $ ValString str))
        σ
        []
        (Val $ ValNat tag۰string)
        σ
        []
  | base_stepｰget_tagｰlocation l hdr σ :
      σ.(state۰headers) !! l = Some hdr →
      base_step
        tid
        (Primitive1 GetTag (Val $ ValLoc l))
        σ
        []
        (Val $ ValTag hdr.(header۰tag))
        σ
        []
  | base_stepｰget_tagｰblock gen tag vs σ :
      0 < length vs →
      base_step
        tid
        (Primitive1 GetTag (Val $ ValBlock gen tag vs))
        σ
        []
        (Val $ ValTag tag)
        σ
        []
  | base_stepｰget_sizeｰlocation l hdr σ :
      σ.(state۰headers) !! l = Some hdr →
      base_step
        tid
        (Primitive1 GetSize (Val $ ValLoc l))
        σ
        []
        (Val $ ValNat hdr.(header۰size))
        σ
        []
  | base_stepｰget_sizeｰblock gen tag vs σ :
      0 < length vs →
      base_step
        tid
        (Primitive1 GetSize (Val $ ValBlock gen tag vs))
        σ
        []
        (Val $ ValNat (length vs))
        σ
        []
  | base_stepｰloadｰlocation l fld v σ :
      σ.(state۰heap) !! (l +ₗ fld) = Some v →
      base_step
        tid
        (Primitive2 Load (Val $ ValLoc l) (Val $ ValInt fld))
        σ
        []
        (Val v)
        σ
        []
  | base_stepｰloadｰblock gen tag vs (fld : nat) v σ :
      vs !! fld = Some v →
      base_step
        tid
        (Primitive2 Load (Val $ ValBlock gen tag vs) (Val $ ValNat fld))
        σ
        []
        (Val v)
        σ
        []
  | base_stepｰstore l fld v σ :
      is_Some (σ.(state۰heap) !! (l +ₗ fld)) →
      base_step
        tid
        (Primitive3 Store (Val $ ValLoc l) (Val $ ValInt fld) (Val v))
        σ
        []
        Unit
        (state۰set_location (l +ₗ fld) v σ)
        []
  | base_stepｰxchg l fld v w σ :
      σ.(state۰heap) !! (l +ₗ fld) = Some w →
      base_step
        tid
        (Primitive2 Xchg (Val $ ValTuple [ValLoc l; ValInt fld]) (Val v))
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
        (Primitive3 CAS (Val $ ValTuple [ValLoc l; ValInt fld]) (Val v1) (Val v2))
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
        (Primitive3 CAS (Val $ ValTuple [ValLoc l; ValInt fld]) (Val v1) (Val v2))
        σ
        []
        (Val $ ValBool true)
        (state۰set_location (l +ₗ fld) v2 σ)
        []
  | base_stepｰfaa l fld n m σ :
      σ.(state۰heap) !! (l +ₗ fld) = Some $ ValInt m →
      base_step
        tid
        (Primitive2 FAA (Val $ ValTuple [ValLoc l; ValInt fld]) (Val $ ValInt n))
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
  | base_stepｰlocal_get v σ :
      σ.(state۰locals) !! tid = Some v →
      base_step
        tid
        (Primitive0 LocalGet)
        σ
        []
        (Val v)
        σ
        []
  | base_stepｰlocal_set v σ :
      is_Some (σ.(state۰locals) !! tid) →
      base_step
        tid
        (Primitive1 LocalSet (Val v))
        σ
        []
        Unit
        (state۰set_local tid v σ)
        []
  | base_stepｰproph σ pid :
      pid ∉ σ.(state۰prophets) →
      base_step
        tid
        (Primitive0 Proph)
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
        es
  | base_stepｰresolve_erasure v0 v1 v2 σ :
      base_step
        tid
        (Primitive3 ResolveErasure (Val v0) (Val v1) (Val v2))
        σ
        []
        (Val v0)
        σ
        [].
#[global] Arguments base_step tid e1 σ1 κ e2 σ2 es : assert.

Lemma base_stepｰalloc' tid 𝑡𝑎𝑔 tag n σ :
  let l := state۰fresh σ in
  tag۰of_Z 𝑡𝑎𝑔 = Some tag →
  (0 ≤ n)%Z →
  base_step
    tid
    (Primitive2 Alloc (Val $ ValInt 𝑡𝑎𝑔) (Val $ ValInt n))
    σ
    []
    (Val $ ValLoc l)
    (state۰alloc l (Header tag ₊n) (replicate ₊n ValUnit) σ)
    [].
Proof.
  intros l Htag Hn.
  apply base_stepｰalloc. 1,2: done.
  apply state۰alloc_conditionｰfresh.
Qed.
Lemma base_stepｰblockｰmutable' tid tag es vs σ :
  let l := state۰fresh σ in
  0 < length es →
  es = expr۰of_vals vs →
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
  es = expr۰of_vals vs →
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
    (Primitive0 Proph)
    σ
    []
    (Val $ ValProph pid)
    (state۰add_prophet pid σ)
    [].
Proof.
  constructor. apply is_fresh.
Qed.

Inductive ectxi :=
  | CtxApply1 v2
  | CtxApply2 e1
  | CtxLet x e2
  | CtxIf e1 e2
  | CtxFor1 e2 e3
  | CtxFor2 v1 e3
  | CtxMatch x e1 brs
  | CtxPrimitive1 (prim : primitive1)
  | CtxPrimitive21 (prim : primitive2) v2
  | CtxPrimitive22 (prim : primitive2) e1
  | CtxPrimitive31 (prim : primitive3) v2 v3
  | CtxPrimitive32 (prim : primitive3) e1 v3
  | CtxPrimitive33 (prim : primitive3) e1 e2
  | CtxBlock mut tag es vs
  | CtxResolve0 (k : ectxi) v1 v2
  | CtxResolve1 e0 v2
  | CtxResolve2 e0 e1.
Implicit Type k : ectxi.

Abbreviation CtxSeq := (
  CtxLet BAnon
)(only parsing
).
Abbreviation CtxTuple := (
  CtxBlock ImmutableNongenerative Tag0
)(only parsing
).

Fixpoint ectxi۰make_resolves resolves k :=
  match resolves with
  | [] =>
      k
  | resolve :: resolves =>
      ectxi۰make_resolves resolves (CtxResolve0 k resolve.1 resolve.2)
  end.
#[global] Arguments ectxi۰make_resolves !_ _ / : assert.

Fixpoint filli k e : expr :=
  match k with
  | CtxApply1 v2 =>
      Apply e (Val v2)
  | CtxApply2 e1 =>
      Apply e1 e
  | CtxLet x e2 =>
      Let x e e2
  | CtxIf e1 e2 =>
      If e e1 e2
  | CtxFor1 e2 e3 =>
      For e e2 e3
  | CtxFor2 v1 e3 =>
      For (Val v1) e e3
  | CtxMatch x e1 brs =>
      Match e x e1 brs
  | CtxPrimitive1 prim =>
      Primitive1 prim e
  | CtxPrimitive21 prim v2 =>
      Primitive2 prim e (Val v2)
  | CtxPrimitive22 prim e1 =>
      Primitive2 prim e1 e
  | CtxPrimitive31 prim v2 v3 =>
      Primitive3 prim e (Val v2) (Val v3)
  | CtxPrimitive32 prim e1 v3 =>
      Primitive3 prim e1 e (Val v3)
  | CtxPrimitive33 prim e1 e2 =>
      Primitive3 prim e1 e2 e
  | CtxBlock mut tag es vs =>
      Block mut tag (es ++ e :: expr۰of_vals vs)
  | CtxResolve0 k v1 v2 =>
      Resolve (filli k e) (Val v1) (Val v2)
  | CtxResolve1 e0 v2 =>
      Resolve e0 e (Val v2)
  | CtxResolve2 e0 e1 =>
      Resolve e0 e1 e
  end.
#[global] Arguments filli !_ _ / : assert.

Definition ectx :=
  list ectxi.
Implicit Type K : ectx.

Definition fill K e :=
  foldl (flip filli) e K.

Definition config : Type :=
  list expr * state.
