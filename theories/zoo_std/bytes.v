Require Import zoo.prelude.
Require Import zoo.base.
Require Export zoo_std.bytes__code.
Require Import zoo_std.bytes__types.
Require Import zoo.options.

Implicit Type chr : ascii.
Implicit Type str : string.
Implicit Type l : bytes_location.

Please Definition bytes٠create : val :=
  𝗳𝘂𝗻 "n" ->
    Primitive1 BytesCreate "n".

Please Definition bytes٠unsafe_get : val :=
  𝗳𝘂𝗻 "t" "i" ->
    Primitive2 BytesGet "t" "i".

Please Definition bytes٠unsafe_set : val :=
  𝗳𝘂𝗻 "t" "i" "chr" ->
    Primitive3 BytesSet "t" "i" "chr".

Please Definition bytes٠equal : val :=
  𝗳𝘂𝗻 "t1" "t2" ->
    "t1" =ᴮ "t2".

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Lemma bytes٠createｰspec n :
    (0 ≤ n)%Z →
    {{{
      True
    }}}
      bytes٠create #n
    {{{
      l str
    , RET #l;
      ⌜String.length str = ₊n⌝ ∗
      l ↦ᴮ str
    }}}.
  Proof.
    iIntros "%Hn %Φ _ HΦ".

    wp۰rec.
    wp۰apply+ (wpｰbytesｰcreate with "[//] HΦ"). 1: done.
  Qed.

  Lemma bytes٠unsafe_getｰspec {l dq str i} chr :
    (0 ≤ i)%Z →
    String.get ₊i str = Some chr →
    {{{
      l ↦ᴮ{dq} str
    }}}
      bytes٠unsafe_get #l #i
    {{{
      RET #chr;
      l ↦ᴮ{dq} str
    }}}.
  Proof.
    iIntros "%Hi %Hlookup %Φ Hl HΦ".

    wp۰rec.
    wp۰apply+ (wpｰbytesｰget with "Hl HΦ"). 1,2: done.
  Qed.

  Lemma bytes٠unsafe_setｰspec {l str i chr} str' :
    (0 ≤ i)%Z →
    string۰set ₊i chr str = Some str' →
    {{{
      l ↦ᴮ str
    }}}
      bytes٠unsafe_set #l #i #chr
    {{{
      RET ();
      l ↦ᴮ str'
    }}}.
  Proof.
    iIntros "%Hi %Hstr' %Φ Hl HΦ".

    wp۰rec.
    wp۰apply+ (wpｰbytesｰset with "Hl HΦ"). 1,2: done.
  Qed.

  Lemma bytes٠equalｰspec l1 dq1 str1 l2 dq2 str2 :
    {{{
      l1 ↦ᴮ{dq1} str1 ∗
      l2 ↦ᴮ{dq2} str2
    }}}
      bytes٠equal #l1 #l2
    {{{
      RET #(bool_decide (str1 = str2));
      l1 ↦ᴮ{dq1} str1 ∗
      l2 ↦ᴮ{dq2} str2
    }}}.
  Proof.
    iIntros "%Φ (Hl1 & Hl2) HΦ".

    wp۰rec.
    wp۰apply+ (wpｰbytesｰequal with "[$Hl1 $Hl2] HΦ").
  Qed.
End zoo۰G.

Require zoo_std.bytes__opaque.

Please opacify.
