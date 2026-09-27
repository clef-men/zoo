Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo.options.

Implicit Type b : bool.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Implicit Type I : iProp Σ.
  Implicit Type Ψ : bool → iProp Σ.

  Lemma whileｰspec I Ψ e0 e1 :
    {{{
      I ∗
      □ (
        I -∗
        WP e0 {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          Ψ b
        }}
      ) ∗
      □ (
        Ψ true -∗
        WP e1 {{ _, I }}
      )
    }}}
      While e0 e1
    {{{
      RET ();
      Ψ false
    }}}.
  Proof.
    iIntros "%Φ (HI & #He0 & #He1) HΦ".

    iLöb as "HLöb".

    wp۰while.
    wp۰apply (wpｰwand with "(He0 HI)") as "%res (%b & -> & HΨ)".
    destruct b; wp۰pures. 2: iSteps.
    wp۰apply (wpｰwand with "(He1 HΨ)") as "%res HI".
    wp۰apply+ ("HLöb" with "HI HΦ").
  Qed.
End zoo۰G.
