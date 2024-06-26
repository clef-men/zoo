From iris.bi Require Export
  bi
  telescopes.
From iris.proofmode Require Import
  tactics
  notation
  reduction.

From diaframe Require Import
  util_classes
  tele_utils
  solve_defs.

From zoo.iris.program_logic Require Import
  wp
  wp_lifting.
From zoo.iris.diaframe Require Import
  symb_exec.defs
  symb_exec.wp.

Import bi.

#[global] Declare Reduction unfold_spec := cbv [
  ReductionStep'
  ReductionTemplateStep
  template_M
  wp_red_cond
  bi_texist
  bi_tforall
  tele_fold
  tele_bind
  tele_app
  snd fst
].

Ltac unfold_spec_goal :=
  match goal with
  | |- ?G =>
    let G' := eval unfold_spec in G in
    change G with G'
  end.

Notation "'SPEC' [ pre ] ⟨ E1 , E2 ⟩ x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    n
    (fupd E1 E2)
    (fupd E2 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Qs%I) .. )) .. )
    e
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg3 E1] )
  (at level 20, n at level 9, E1, E2 at level 9, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 , E2 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 , E2 ⟩ x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    n
    (fupd E1 E2)
    (fupd E2 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, Qs%I) .. )
    e
    (λ x1, .. (λ xn, e') .. )
    [tele_arg3 E1] )
  (at level 20, n at level 9, E1, E2 at level 9, x1 closed binder, xn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 , E2 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 , E2 ⟩ x1 .. xn , {{ Ps } } e {{ y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    1
    (fupd E1 E2)
    (fupd E2 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Qs%I) .. )) .. )
    e
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg3 E1] )
  (at level 20, E1, E2 at level 9, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 , E2 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 , E2 ⟩ x1 .. xn , {{ Ps } } e {{ 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    1
    (fupd E1 E2)
    (fupd E2 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, Qs%I) .. )
    e
    (λ x1, .. (λ xn, e') .. )
    [tele_arg3 E1] )
  (at level 20, E1, E2 at level 9, x1 closed binder, xn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 , E2 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 , E2 ⟩ x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    n
    (fupd E1 E2)
    (fupd E2 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Qs%I) .. )) .. )
    e
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg3 E1] )
  (at level 20, n at level 9, E1, E2 at level 9, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 , E2 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 , E2 ⟩ x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    n
    (fupd E1 E2)
    (fupd E2 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, Qs%I) .. )
    e
    (λ x1, .. (λ xn, e') .. )
    [tele_arg3 E1] )
  (at level 20, n at level 9, E1, E2 at level 9, x1 closed binder, xn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 , E2 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 , E2 ⟩ x1 .. xn , {{ Ps } } e {{ y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    1
    (fupd E1 E2)
    (fupd E2 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Qs%I) .. )) .. )
    e
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg3 E1] )
  (at level 20, E1, E2 at level 9, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 , E2 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 , E2 ⟩ x1 .. xn , {{ Ps } } e {{ 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    1
    (fupd E1 E2)
    (fupd E2 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, Qs%I) .. )
    e
    (λ x1, .. (λ xn, e') .. )
    [tele_arg3 E1] )
  (at level 20, E1, E2 at level 9, x1 closed binder, xn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 , E2 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 , E2 ⟩ x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    n
    (fupd E1 E2)
    (fupd E2 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Qs%I) .. )) .. )
    e
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg3 E1] )
  (at level 20, n at level 9, E1, E2 at level 9, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 , E2 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 , E2 ⟩ x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    n
    (fupd E1 E2)
    (fupd E2 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, Qs%I) .. )
    e
    (λ x1, .. (λ xn, e') .. )
    [tele_arg3 E1] )
  (at level 20, n at level 9, E1, E2 at level 9, x1 closed binder, xn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 , E2 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 , E2 ⟩ x1 .. xn , {{ Ps } } e {{ y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    1
    (fupd E1 E2)
    (fupd E2 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Qs%I) .. )) .. )
    e
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg3 E1] )
  (at level 20, E1, E2 at level 9, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 , E2 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 , E2 ⟩ x1 .. xn , {{ Ps } } e {{ 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    1
    (fupd E1 E2)
    (fupd E2 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, Qs%I) .. )
    e
    (λ x1, .. (λ xn, e') .. )
    [tele_arg3 E1] )
  (at level 20, E1, E2 at level 9, x1 closed binder, xn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 , E2 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 , E2 ⟩ x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    n
    (fupd E1 E2)
    (fupd E2 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Qs%I) .. )) .. )
    e
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg3 E1] )
  (at level 20, n at level 9, E1, E2 at level 9, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 , E2 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 , E2 ⟩ x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    n
    (fupd E1 E2)
    (fupd E2 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, Qs%I) .. )
    e
    (λ x1, .. (λ xn, e') .. )
    [tele_arg3 E1] )
  (at level 20, n at level 9, E1, E2 at level 9, x1 closed binder, xn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 , E2 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 , E2 ⟩ x1 .. xn , {{ Ps } } e {{ y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    1
    (fupd E1 E2)
    (fupd E2 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Qs%I) .. )) .. )
    e
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg3 E1] )
  (at level 20, E1, E2 at level 9, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 , E2 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 , E2 ⟩ x1 .. xn , {{ Ps } } e {{ 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    1
    (fupd E1 E2)
    (fupd E2 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, Qs%I) .. )
    e
    (λ x1, .. (λ xn, e') .. )
    [tele_arg3 E1] )
  (at level 20, E1, E2 at level 9, x1 closed binder, xn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 , E2 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 , E2 ⟩ {{ Ps } } e {{ [ ▷^ n ] y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    n
    (fupd E1 E2)
    (fupd E2 E1)
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    Ps%I
    (λ y1, .. (λ yn, Qs%I) .. )
    e
    (λ y1, .. (λ yn, e') .. )
    [tele_arg3 E1] )
  (at level 20, n at level 9, E1, E2 at level 9, y1 closed binder, yn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 , E2 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 , E2 ⟩ {{ Ps } } e {{ [ ▷^ n ] 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    n
    (fupd E1 E2)
    (fupd E2 E1)
    TeleO
    TeleO
    Ps%I
    Qs%I
    e
    e'
    [tele_arg3 E1] )
  (at level 20, n at level 9, E1, E2 at level 9, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 , E2 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 , E2 ⟩ {{ Ps } } e {{ y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    1
    (fupd E1 E2)
    (fupd E2 E1)
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    Ps%I
    (λ y1, .. (λ yn, Qs%I) .. )
    e
    (λ y1, .. (λ yn, e') .. )
    [tele_arg3 E1] )
  (at level 20, E1, E2 at level 9, y1 closed binder, yn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 , E2 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 , E2 ⟩ {{ Ps } } e {{ 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    1
    (fupd E1 E2)
    (fupd E2 E1)
    TeleO
    TeleO
    Ps%I
    Qs%I
    e
    e'
    [tele_arg3 E1] )
  (at level 20, E1, E2 at level 9, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 , E2 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 , E2 ⟩ {{ Ps } } e {{ [ ▷^ n ] y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    n
    (fupd E1 E2)
    (fupd E2 E1)
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    Ps%I
    (λ y1, .. (λ yn, Qs%I) .. )
    e
    (λ y1, .. (λ yn, e') .. )
    [tele_arg3 E1] )
  (at level 20, n at level 9, E1, E2 at level 9, y1 closed binder, yn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 , E2 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 , E2 ⟩ {{ Ps } } e {{ [ ▷^ n ] 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    n
    (fupd E1 E2)
    (fupd E2 E1)
    TeleO
    TeleO
    Ps%I
    Qs%I
    e
    e'
    [tele_arg3 E1] )
  (at level 20, n at level 9, E1, E2 at level 9, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 , E2 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 , E2 ⟩ {{ Ps } } e {{ y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    1
    (fupd E1 E2)
    (fupd E2 E1)
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    Ps%I
    (λ y1, .. (λ yn, Qs%I) .. )
    e
    (λ y1, .. (λ yn, e') .. )
    [tele_arg3 E1] )
  (at level 20, E1, E2 at level 9, y1 closed binder, yn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 , E2 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 , E2 ⟩ {{ Ps } } e {{ 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    1
    (fupd E1 E2)
    (fupd E2 E1)
    TeleO
    TeleO
    Ps%I
    Qs%I
    e
    e'
    [tele_arg3 E1] )
  (at level 20, E1, E2 at level 9, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 , E2 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 , E2 ⟩ {{ Ps } } e {{ [ ▷^ n ] y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    n
    (fupd E1 E2)
    (fupd E2 E1)
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    Ps%I
    (λ y1, .. (λ yn, Qs%I) .. )
    e
    (λ y1, .. (λ yn, e') .. )
    [tele_arg3 E1] )
  (at level 20, n at level 9, E1, E2 at level 9, y1 closed binder, yn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 , E2 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 , E2 ⟩ {{ Ps } } e {{ [ ▷^ n ] 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    n
    (fupd E1 E2)
    (fupd E2 E1)
    TeleO
    TeleO
    Ps%I
    Qs%I
    e
    e'
    [tele_arg3 E1] )
  (at level 20, n at level 9, E1, E2 at level 9, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 , E2 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 , E2 ⟩ {{ Ps } } e {{ y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    1
    (fupd E1 E2)
    (fupd E2 E1)
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    Ps%I
    (λ y1, .. (λ yn, Qs%I) .. )
    e
    (λ y1, .. (λ yn, e') .. )
    [tele_arg3 E1] )
  (at level 20, E1, E2 at level 9, y1 closed binder, yn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 , E2 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 , E2 ⟩ {{ Ps } } e {{ 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    1
    (fupd E1 E2)
    (fupd E2 E1)
    TeleO
    TeleO
    Ps%I
    Qs%I
    e
    e'
    [tele_arg3 E1] )
  (at level 20, E1, E2 at level 9, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 , E2 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 , E2 ⟩ {{ Ps } } e {{ [ ▷^ n ] y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    n
    (fupd E1 E2)
    (fupd E2 E1)
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    Ps%I
    (λ y1, .. (λ yn, Qs%I) .. )
    e
    (λ y1, .. (λ yn, e') .. )
    [tele_arg3 E1] )
  (at level 20, n at level 9, E1, E2 at level 9, y1 closed binder, yn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 , E2 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 , E2 ⟩ {{ Ps } } e {{ [ ▷^ n ] 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    n
    (fupd E1 E2)
    (fupd E2 E1)
    TeleO
    TeleO
    Ps%I
    Qs%I
    e
    e'
    [tele_arg3 E1] )
  (at level 20, n at level 9, E1, E2 at level 9, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 , E2 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 , E2 ⟩ {{ Ps } } e {{ y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    1
    (fupd E1 E2)
    (fupd E2 E1)
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    Ps%I
    (λ y1, .. (λ yn, Qs%I) .. )
    e
    (λ y1, .. (λ yn, e') .. )
    [tele_arg3 E1] )
  (at level 20, E1, E2 at level 9, y1 closed binder, yn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 , E2 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 , E2 ⟩ {{ Ps } } e {{ 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    1
    (fupd E1 E2)
    (fupd E2 E1)
    TeleO
    TeleO
    Ps%I
    Qs%I
    e
    e'
    [tele_arg3 E1] )
  (at level 20, E1, E2 at level 9, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 , E2 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 ⟩ x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    n
    (fupd E1 E1)
    (fupd E1 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Qs%I) .. )) .. )
    e
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg E1] )
  (at level 20, n at level 9, E1 at level 9, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 ⟩ x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    n
    (fupd E1 E1)
    (fupd E1 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, Qs%I) .. )
    e
    (λ x1, .. (λ xn, e') .. )
    [tele_arg E1] )
  (at level 20, n at level 9, E1 at level 9, x1 closed binder, xn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 ⟩ x1 .. xn , {{ Ps } } e {{ y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    1
    (fupd E1 E1)
    (fupd E1 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Qs%I) .. )) .. )
    e
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg E1] )
  (at level 20, E1 at level 9, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 ⟩ x1 .. xn , {{ Ps } } e {{ 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    1
    (fupd E1 E1)
    (fupd E1 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, Qs%I) .. )
    e
    (λ x1, .. (λ xn, e') .. )
    [tele_arg E1] )
  (at level 20, E1 at level 9, x1 closed binder, xn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 ⟩ x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    n
    (fupd E1 E1)
    (fupd E1 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Qs%I) .. )) .. )
    e
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg E1] )
  (at level 20, n at level 9, E1 at level 9, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 ⟩ x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    n
    (fupd E1 E1)
    (fupd E1 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, Qs%I) .. )
    e
    (λ x1, .. (λ xn, e') .. )
    [tele_arg E1] )
  (at level 20, n at level 9, E1 at level 9, x1 closed binder, xn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 ⟩ x1 .. xn , {{ Ps } } e {{ y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    1
    (fupd E1 E1)
    (fupd E1 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Qs%I) .. )) .. )
    e
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg E1] )
  (at level 20, E1 at level 9, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 ⟩ x1 .. xn , {{ Ps } } e {{ 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    1
    (fupd E1 E1)
    (fupd E1 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, Qs%I) .. )
    e
    (λ x1, .. (λ xn, e') .. )
    [tele_arg E1] )
  (at level 20, E1 at level 9, x1 closed binder, xn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 ⟩ x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    n
    (fupd E1 E1)
    (fupd E1 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Qs%I) .. )) .. )
    e
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg E1] )
  (at level 20, n at level 9, E1 at level 9, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 ⟩ x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    n
    (fupd E1 E1)
    (fupd E1 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, Qs%I) .. )
    e
    (λ x1, .. (λ xn, e') .. )
    [tele_arg E1] )
  (at level 20, n at level 9, E1 at level 9, x1 closed binder, xn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 ⟩ x1 .. xn , {{ Ps } } e {{ y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    1
    (fupd E1 E1)
    (fupd E1 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Qs%I) .. )) .. )
    e
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg E1] )
  (at level 20, E1 at level 9, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 ⟩ x1 .. xn , {{ Ps } } e {{ 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    1
    (fupd E1 E1)
    (fupd E1 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, Qs%I) .. )
    e
    (λ x1, .. (λ xn, e') .. )
    [tele_arg E1] )
  (at level 20, E1 at level 9, x1 closed binder, xn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 ⟩ x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    n
    (fupd E1 E1)
    (fupd E1 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Qs%I) .. )) .. )
    e
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg E1] )
  (at level 20, n at level 9, E1 at level 9, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 ⟩ x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    n
    (fupd E1 E1)
    (fupd E1 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, Qs%I) .. )
    e
    (λ x1, .. (λ xn, e') .. )
    [tele_arg E1] )
  (at level 20, n at level 9, E1 at level 9, x1 closed binder, xn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 ⟩ x1 .. xn , {{ Ps } } e {{ y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    1
    (fupd E1 E1)
    (fupd E1 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Qs%I) .. )) .. )
    e
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg E1] )
  (at level 20, E1 at level 9, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 ⟩ x1 .. xn , {{ Ps } } e {{ 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    1
    (fupd E1 E1)
    (fupd E1 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, Qs%I) .. )
    e
    (λ x1, .. (λ xn, e') .. )
    [tele_arg E1] )
  (at level 20, E1 at level 9, x1 closed binder, xn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 ⟩ {{ Ps } } e {{ [ ▷^ n ] y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    n
    (fupd E1 E1)
    (fupd E1 E1)
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    Ps%I
    (λ y1, .. (λ yn, Qs%I) .. )
    e
    (λ y1, .. (λ yn, e') .. )
    [tele_arg E1] )
  (at level 20, n at level 9, E1 at level 9, y1 closed binder, yn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 ⟩ {{ Ps } } e {{ [ ▷^ n ] 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    n
    (fupd E1 E1)
    (fupd E1 E1)
    TeleO
    TeleO
    Ps%I
    Qs%I
    e
    e'
    [tele_arg E1] )
  (at level 20, n at level 9, E1 at level 9, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 ⟩ {{ Ps } } e {{ y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    1
    (fupd E1 E1)
    (fupd E1 E1)
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    Ps%I
    (λ y1, .. (λ yn, Qs%I) .. )
    e
    (λ y1, .. (λ yn, e') .. )
    [tele_arg E1] )
  (at level 20, E1 at level 9, y1 closed binder, yn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 ⟩ {{ Ps } } e {{ 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    1
    (fupd E1 E1)
    (fupd E1 E1)
    TeleO
    TeleO
    Ps%I
    Qs%I
    e
    e'
    [tele_arg E1] )
  (at level 20, E1 at level 9, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 ⟩ {{ Ps } } e {{ [ ▷^ n ] y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    n
    (fupd E1 E1)
    (fupd E1 E1)
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    Ps%I
    (λ y1, .. (λ yn, Qs%I) .. )
    e
    (λ y1, .. (λ yn, e') .. )
    [tele_arg E1] )
  (at level 20, n at level 9, E1 at level 9, y1 closed binder, yn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 ⟩ {{ Ps } } e {{ [ ▷^ n ] 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    n
    (fupd E1 E1)
    (fupd E1 E1)
    TeleO
    TeleO
    Ps%I
    Qs%I
    e
    e'
    [tele_arg E1] )
  (at level 20, n at level 9, E1 at level 9, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 ⟩ {{ Ps } } e {{ y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    1
    (fupd E1 E1)
    (fupd E1 E1)
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    Ps%I
    (λ y1, .. (λ yn, Qs%I) .. )
    e
    (λ y1, .. (λ yn, e') .. )
    [tele_arg E1] )
  (at level 20, E1 at level 9, y1 closed binder, yn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 ⟩ {{ Ps } } e {{ 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    1
    (fupd E1 E1)
    (fupd E1 E1)
    TeleO
    TeleO
    Ps%I
    Qs%I
    e
    e'
    [tele_arg E1] )
  (at level 20, E1 at level 9, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 ⟩ {{ Ps } } e {{ [ ▷^ n ] y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    n
    (fupd E1 E1)
    (fupd E1 E1)
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    Ps%I
    (λ y1, .. (λ yn, Qs%I) .. )
    e
    (λ y1, .. (λ yn, e') .. )
    [tele_arg E1] )
  (at level 20, n at level 9, E1 at level 9, y1 closed binder, yn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 ⟩ {{ Ps } } e {{ [ ▷^ n ] 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    n
    (fupd E1 E1)
    (fupd E1 E1)
    TeleO
    TeleO
    Ps%I
    Qs%I
    e
    e'
    [tele_arg E1] )
  (at level 20, n at level 9, E1 at level 9, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 ⟩ {{ Ps } } e {{ y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    1
    (fupd E1 E1)
    (fupd E1 E1)
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    Ps%I
    (λ y1, .. (λ yn, Qs%I) .. )
    e
    (λ y1, .. (λ yn, e') .. )
    [tele_arg E1] )
  (at level 20, E1 at level 9, y1 closed binder, yn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] ⟨ E1 ⟩ {{ Ps } } e {{ 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    1
    (fupd E1 E1)
    (fupd E1 E1)
    TeleO
    TeleO
    Ps%I
    Qs%I
    e
    e'
    [tele_arg E1] )
  (at level 20, E1 at level 9, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  ⟨ E1 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 ⟩ {{ Ps } } e {{ [ ▷^ n ] y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    n
    (fupd E1 E1)
    (fupd E1 E1)
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    Ps%I
    (λ y1, .. (λ yn, Qs%I) .. )
    e
    (λ y1, .. (λ yn, e') .. )
    [tele_arg E1] )
  (at level 20, n at level 9, E1 at level 9, y1 closed binder, yn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 ⟩ {{ Ps } } e {{ [ ▷^ n ] 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    n
    (fupd E1 E1)
    (fupd E1 E1)
    TeleO
    TeleO
    Ps%I
    Qs%I
    e
    e'
    [tele_arg E1] )
  (at level 20, n at level 9, E1 at level 9, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 ⟩ {{ Ps } } e {{ y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    1
    (fupd E1 E1)
    (fupd E1 E1)
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    Ps%I
    (λ y1, .. (λ yn, Qs%I) .. )
    e
    (λ y1, .. (λ yn, e') .. )
    [tele_arg E1] )
  (at level 20, E1 at level 9, y1 closed binder, yn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' ⟨ E1 ⟩ {{ Ps } } e {{ 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    1
    (fupd E1 E1)
    (fupd E1 E1)
    TeleO
    TeleO
    Ps%I
    Qs%I
    e
    e'
    [tele_arg E1] )
  (at level 20, E1 at level 9, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  ⟨ E1 ⟩  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    n
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Qs%I) .. )) .. )
    e
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg ⊤] )
  (at level 20, n at level 9, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    n
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, Qs%I) .. )
    e
    (λ x1, .. (λ xn, e') .. )
    [tele_arg ⊤] )
  (at level 20, n at level 9, x1 closed binder, xn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] x1 .. xn , {{ Ps } } e {{ y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    1
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Qs%I) .. )) .. )
    e
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg ⊤] )
  (at level 20, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] x1 .. xn , {{ Ps } } e {{ 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    1
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, Qs%I) .. )
    e
    (λ x1, .. (λ xn, e') .. )
    [tele_arg ⊤] )
  (at level 20, x1 closed binder, xn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    n
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Qs%I) .. )) .. )
    e
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg ⊤] )
  (at level 20, n at level 9, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    n
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, Qs%I) .. )
    e
    (λ x1, .. (λ xn, e') .. )
    [tele_arg ⊤] )
  (at level 20, n at level 9, x1 closed binder, xn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' x1 .. xn , {{ Ps } } e {{ y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    1
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Qs%I) .. )) .. )
    e
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg ⊤] )
  (at level 20, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' x1 .. xn , {{ Ps } } e {{ 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    1
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, Qs%I) .. )
    e
    (λ x1, .. (λ xn, e') .. )
    [tele_arg ⊤] )
  (at level 20, x1 closed binder, xn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    n
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Qs%I) .. )) .. )
    e
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg ⊤] )
  (at level 20, n at level 9, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    n
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, Qs%I) .. )
    e
    (λ x1, .. (λ xn, e') .. )
    [tele_arg ⊤] )
  (at level 20, n at level 9, x1 closed binder, xn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] x1 .. xn , {{ Ps } } e {{ y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    1
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Qs%I) .. )) .. )
    e
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg ⊤] )
  (at level 20, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] x1 .. xn , {{ Ps } } e {{ 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    1
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, Qs%I) .. )
    e
    (λ x1, .. (λ xn, e') .. )
    [tele_arg ⊤] )
  (at level 20, x1 closed binder, xn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    n
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Qs%I) .. )) .. )
    e
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg ⊤] )
  (at level 20, n at level 9, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    n
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, Qs%I) .. )
    e
    (λ x1, .. (λ xn, e') .. )
    [tele_arg ⊤] )
  (at level 20, n at level 9, x1 closed binder, xn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' x1 .. xn , {{ Ps } } e {{ y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    1
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Qs%I) .. )) .. )
    e
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg ⊤] )
  (at level 20, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' x1 .. xn , {{ Ps } } e {{ 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    1
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    (λ x1, .. (λ xn, Ps%I) .. )
    (λ x1, .. (λ xn, Qs%I) .. )
    e
    (λ x1, .. (λ xn, e') .. )
    [tele_arg ⊤] )
  (at level 20, x1 closed binder, xn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] {{ Ps } } e {{ [ ▷^ n ] y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    n
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    Ps%I
    (λ y1, .. (λ yn, Qs%I) .. )
    e
    (λ y1, .. (λ yn, e') .. )
    [tele_arg ⊤] )
  (at level 20, n at level 9, y1 closed binder, yn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] {{ Ps } } e {{ [ ▷^ n ] 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    n
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    TeleO
    TeleO
    Ps%I
    Qs%I
    e
    e'
    [tele_arg ⊤] )
  (at level 20, n at level 9, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] {{ Ps } } e {{ y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    1
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    Ps%I
    (λ y1, .. (λ yn, Qs%I) .. )
    e
    (λ y1, .. (λ yn, e') .. )
    [tele_arg ⊤] )
  (at level 20, y1 closed binder, yn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] {{ Ps } } e {{ 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    1
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    TeleO
    TeleO
    Ps%I
    Qs%I
    e
    e'
    [tele_arg ⊤] )
  (at level 20, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' {{ Ps } } e {{ [ ▷^ n ] y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    n
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    Ps%I
    (λ y1, .. (λ yn, Qs%I) .. )
    e
    (λ y1, .. (λ yn, e') .. )
    [tele_arg ⊤] )
  (at level 20, n at level 9, y1 closed binder, yn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' {{ Ps } } e {{ [ ▷^ n ] 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    n
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    TeleO
    TeleO
    Ps%I
    Qs%I
    e
    e'
    [tele_arg ⊤] )
  (at level 20, n at level 9, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' {{ Ps } } e {{ y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    1
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    Ps%I
    (λ y1, .. (λ yn, Qs%I) .. )
    e
    (λ y1, .. (λ yn, e') .. )
    [tele_arg ⊤] )
  (at level 20, y1 closed binder, yn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' {{ Ps } } e {{ 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    1
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    TeleO
    TeleO
    Ps%I
    Qs%I
    e
    e'
    [tele_arg ⊤] )
  (at level 20, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] {{ Ps } } e {{ [ ▷^ n ] y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    n
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    Ps%I
    (λ y1, .. (λ yn, Qs%I) .. )
    e
    (λ y1, .. (λ yn, e') .. )
    [tele_arg ⊤] )
  (at level 20, n at level 9, y1 closed binder, yn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] {{ Ps } } e {{ [ ▷^ n ] 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    n
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    TeleO
    TeleO
    Ps%I
    Qs%I
    e
    e'
    [tele_arg ⊤] )
  (at level 20, n at level 9, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] {{ Ps } } e {{ y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    1
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    Ps%I
    (λ y1, .. (λ yn, Qs%I) .. )
    e
    (λ y1, .. (λ yn, e') .. )
    [tele_arg ⊤] )
  (at level 20, y1 closed binder, yn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' [ pre ] {{ Ps } } e {{ 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    1
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    TeleO
    TeleO
    Ps%I
    Qs%I
    e
    e'
    [tele_arg ⊤] )
  (at level 20, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC  [ pre ]  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' {{ Ps } } e {{ [ ▷^ n ] y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    n
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    Ps%I
    (λ y1, .. (λ yn, Qs%I) .. )
    e
    (λ y1, .. (λ yn, e') .. )
    [tele_arg ⊤] )
  (at level 20, n at level 9, y1 closed binder, yn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' {{ Ps } } e {{ [ ▷^ n ] 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    n
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    TeleO
    TeleO
    Ps%I
    Qs%I
    e
    e'
    [tele_arg ⊤] )
  (at level 20, n at level 9, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  [ ▷^ n ]  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' {{ Ps } } e {{ y1 .. yn , 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    1
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    Ps%I
    (λ y1, .. (λ yn, Qs%I) .. )
    e
    (λ y1, .. (λ yn, e') .. )
    [tele_arg ⊤] )
  (at level 20, y1 closed binder, yn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC' {{ Ps } } e {{ 'RET' e' ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    1
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    TeleO
    TeleO
    Ps%I
    Qs%I
    e
    e'
    [tele_arg ⊤] )
  (at level 20, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC  '/ ' {{  Ps  } } '/  '  e  '/ ' {{ '[hv'  'RET'  e' ; '/  '  Qs  ']' } } ']'"
).

Notation "'SPEC2' [ pre ] ⟨ E1 , E2 ⟩ x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] 'RET' [ e' ] ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    n
    (fupd E1 E2)
    (fupd E2 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    _
    (λ x1, .. (λ xn, Ps%I) .. )
    Qs%I
    e
    e'
    [tele_arg3 E1] )
  (at level 20, n at level 9, E1, E2 at level 9, x1 closed binder, xn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC2  [ pre ]  ⟨ E1 , E2 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{  [ ▷^ n ]  'RET'  [ e' ] ; '/  '  Qs  } } ']'", only printing
).

Notation "'SPEC2' [ pre ] ⟨ E1 , E2 ⟩ x1 .. xn , {{ Ps } } e {{ 'RET' [ e' ] ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    1
    (fupd E1 E2)
    (fupd E2 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    _
    (λ x1, .. (λ xn, Ps%I) .. )
    Qs%I
    e
    e'
    [tele_arg3 E1] )
  (at level 20, E1, E2 at level 9, x1 closed binder, xn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC2  [ pre ]  ⟨ E1 , E2 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{  'RET'  [ e' ] ; '/  '  Qs  } } ']'", only printing
).

Notation "'SPEC2' ⟨ E1 , E2 ⟩ x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] 'RET' [ e' ] ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    n
    (fupd E1 E2)
    (fupd E2 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    _
    (λ x1, .. (λ xn, Ps%I) .. )
    Qs%I
    e
    e'
    [tele_arg3 E1] )
  (at level 20, n at level 9, E1, E2 at level 9, x1 closed binder, xn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC2  ⟨ E1 , E2 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{  [ ▷^ n ]  'RET'  [ e' ] ; '/  '  Qs  } } ']'", only printing
).

Notation "'SPEC2' ⟨ E1 , E2 ⟩ x1 .. xn , {{ Ps } } e {{ 'RET' [ e' ] ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    1
    (fupd E1 E2)
    (fupd E2 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    _
    (λ x1, .. (λ xn, Ps%I) .. )
    Qs%I
    e
    e'
    [tele_arg3 E1] )
  (at level 20, E1, E2 at level 9, x1 closed binder, xn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC2  ⟨ E1 , E2 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{  'RET'  [ e' ] ; '/  '  Qs  } } ']'", only printing
).

Notation "'SPEC2' [ pre ] ⟨ E1 , E2 ⟩ x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] 'RET' [ e' ] ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    n
    (fupd E1 E2)
    (fupd E2 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    _
    (λ x1, .. (λ xn, Ps%I) .. )
    Qs%I
    e
    e'
    [tele_arg3 E1] )
  (at level 20, n at level 9, E1, E2 at level 9, x1 closed binder, xn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC2  [ pre ]  ⟨ E1 , E2 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{  [ ▷^ n ]  'RET'  [ e' ] ; '/  '  Qs  } } ']'", only printing
).

Notation "'SPEC2' [ pre ] ⟨ E1 , E2 ⟩ x1 .. xn , {{ Ps } } e {{ 'RET' [ e' ] ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    1
    (fupd E1 E2)
    (fupd E2 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    _
    (λ x1, .. (λ xn, Ps%I) .. )
    Qs%I
    e
    e'
    [tele_arg3 E1] )
  (at level 20, E1, E2 at level 9, x1 closed binder, xn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC2  [ pre ]  ⟨ E1 , E2 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{  'RET'  [ e' ] ; '/  '  Qs  } } ']'", only printing
).

Notation "'SPEC2' ⟨ E1 , E2 ⟩ x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] 'RET' [ e' ] ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    n
    (fupd E1 E2)
    (fupd E2 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    _
    (λ x1, .. (λ xn, Ps%I) .. )
    Qs%I
    e
    e'
    [tele_arg3 E1] )
  (at level 20, n at level 9, E1, E2 at level 9, x1 closed binder, xn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC2  ⟨ E1 , E2 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{  [ ▷^ n ]  'RET'  [ e' ] ; '/  '  Qs  } } ']'", only printing
).

Notation "'SPEC2' ⟨ E1 , E2 ⟩ x1 .. xn , {{ Ps } } e {{ 'RET' [ e' ] ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    1
    (fupd E1 E2)
    (fupd E2 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    _
    (λ x1, .. (λ xn, Ps%I) .. )
    Qs%I
    e
    e'
    [tele_arg3 E1] )
  (at level 20, E1, E2 at level 9, x1 closed binder, xn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC2  ⟨ E1 , E2 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{  'RET'  [ e' ] ; '/  '  Qs  } } ']'", only printing
).

Notation "'SPEC2' [ pre ] ⟨ E1 ⟩ x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] 'RET' [ e' ] ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    n
    (fupd E1 E1)
    (fupd E1 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    _
    (λ x1, .. (λ xn, Ps%I) .. )
    Qs%I
    e
    e'
    [tele_arg E1] )
  (at level 20, n at level 9, E1 at level 9, x1 closed binder, xn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC2  [ pre ]  ⟨ E1 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{  [ ▷^ n ]  'RET'  [ e' ] ; '/  '  Qs  } } ']'", only printing
).

Notation "'SPEC2' [ pre ] ⟨ E1 ⟩ x1 .. xn , {{ Ps } } e {{ 'RET' [ e' ] ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    1
    (fupd E1 E1)
    (fupd E1 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    _
    (λ x1, .. (λ xn, Ps%I) .. )
    Qs%I
    e
    e'
    [tele_arg E1] )
  (at level 20, E1 at level 9, x1 closed binder, xn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC2  [ pre ]  ⟨ E1 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{  'RET'  [ e' ] ; '/  '  Qs  } } ']'", only printing
).

Notation "'SPEC2' ⟨ E1 ⟩ x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] 'RET' [ e' ] ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    n
    (fupd E1 E1)
    (fupd E1 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    _
    (λ x1, .. (λ xn, Ps%I) .. )
    Qs%I
    e
    e'
    [tele_arg E1] )
  (at level 20, n at level 9, E1 at level 9, x1 closed binder, xn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC2  ⟨ E1 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{  [ ▷^ n ]  'RET'  [ e' ] ; '/  '  Qs  } } ']'", only printing
).

Notation "'SPEC2' ⟨ E1 ⟩ x1 .. xn , {{ Ps } } e {{ 'RET' [ e' ] ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    1
    (fupd E1 E1)
    (fupd E1 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    _
    (λ x1, .. (λ xn, Ps%I) .. )
    Qs%I
    e
    e'
    [tele_arg E1] )
  (at level 20, E1 at level 9, x1 closed binder, xn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC2  ⟨ E1 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{  'RET'  [ e' ] ; '/  '  Qs  } } ']'", only printing
).

Notation "'SPEC2' [ pre ] ⟨ E1 ⟩ x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] 'RET' [ e' ] ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    n
    (fupd E1 E1)
    (fupd E1 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    _
    (λ x1, .. (λ xn, Ps%I) .. )
    Qs%I
    e
    e'
    [tele_arg E1] )
  (at level 20, n at level 9, E1 at level 9, x1 closed binder, xn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC2  [ pre ]  ⟨ E1 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{  [ ▷^ n ]  'RET'  [ e' ] ; '/  '  Qs  } } ']'", only printing
).

Notation "'SPEC2' [ pre ] ⟨ E1 ⟩ x1 .. xn , {{ Ps } } e {{ 'RET' [ e' ] ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    1
    (fupd E1 E1)
    (fupd E1 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    _
    (λ x1, .. (λ xn, Ps%I) .. )
    Qs%I
    e
    e'
    [tele_arg E1] )
  (at level 20, E1 at level 9, x1 closed binder, xn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC2  [ pre ]  ⟨ E1 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{  'RET'  [ e' ] ; '/  '  Qs  } } ']'", only printing
).

Notation "'SPEC2' ⟨ E1 ⟩ x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] 'RET' [ e' ] ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    n
    (fupd E1 E1)
    (fupd E1 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    _
    (λ x1, .. (λ xn, Ps%I) .. )
    Qs%I
    e
    e'
    [tele_arg E1] )
  (at level 20, n at level 9, E1 at level 9, x1 closed binder, xn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC2  ⟨ E1 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{  [ ▷^ n ]  'RET'  [ e' ] ; '/  '  Qs  } } ']'", only printing
).

Notation "'SPEC2' ⟨ E1 ⟩ x1 .. xn , {{ Ps } } e {{ 'RET' [ e' ] ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    1
    (fupd E1 E1)
    (fupd E1 E1)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    _
    (λ x1, .. (λ xn, Ps%I) .. )
    Qs%I
    e
    e'
    [tele_arg E1] )
  (at level 20, E1 at level 9, x1 closed binder, xn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC2  ⟨ E1 ⟩  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{  'RET'  [ e' ] ; '/  '  Qs  } } ']'", only printing
).

Notation "'SPEC2' [ pre ] x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] 'RET' [ e' ] ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    n
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    _
    (λ x1, .. (λ xn, Ps%I) .. )
    Qs%I
    e
    e'
    [tele_arg ⊤] )
  (at level 20, n at level 9, x1 closed binder, xn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC2  [ pre ]  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{  [ ▷^ n ]  'RET'  [ e' ] ; '/  '  Qs  } } ']'", only printing
).

Notation "'SPEC2' [ pre ] x1 .. xn , {{ Ps } } e {{ 'RET' [ e' ] ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    1
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    _
    (λ x1, .. (λ xn, Ps%I) .. )
    Qs%I
    e
    e'
    [tele_arg ⊤] )
  (at level 20, x1 closed binder, xn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC2  [ pre ]  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{  'RET'  [ e' ] ; '/  '  Qs  } } ']'", only printing
).

Notation "'SPEC2' x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] 'RET' [ e' ] ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    n
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    _
    (λ x1, .. (λ xn, Ps%I) .. )
    Qs%I
    e
    e'
    [tele_arg ⊤] )
  (at level 20, n at level 9, x1 closed binder, xn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC2  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{  [ ▷^ n ]  'RET'  [ e' ] ; '/  '  Qs  } } ']'", only printing
).

Notation "'SPEC2' x1 .. xn , {{ Ps } } e {{ 'RET' [ e' ] ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    1
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    _
    (λ x1, .. (λ xn, Ps%I) .. )
    Qs%I
    e
    e'
    [tele_arg ⊤] )
  (at level 20, x1 closed binder, xn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC2  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{  'RET'  [ e' ] ; '/  '  Qs  } } ']'", only printing
).

Notation "'SPEC2' [ pre ] x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] 'RET' [ e' ] ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    n
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    _
    (λ x1, .. (λ xn, Ps%I) .. )
    Qs%I
    e
    e'
    [tele_arg ⊤] )
  (at level 20, n at level 9, x1 closed binder, xn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC2  [ pre ]  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{  [ ▷^ n ]  'RET'  [ e' ] ; '/  '  Qs  } } ']'", only printing
).

Notation "'SPEC2' [ pre ] x1 .. xn , {{ Ps } } e {{ 'RET' [ e' ] ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    pre%I
    1
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    _
    (λ x1, .. (λ xn, Ps%I) .. )
    Qs%I
    e
    e'
    [tele_arg ⊤] )
  (at level 20, x1 closed binder, xn closed binder, e, Ps, pre, e', Qs at level 200, format
  "'[hv' SPEC2  [ pre ]  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{  'RET'  [ e' ] ; '/  '  Qs  } } ']'", only printing
).

Notation "'SPEC2' x1 .. xn , {{ Ps } } e {{ [ ▷^ n ] 'RET' [ e' ] ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    n
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    _
    (λ x1, .. (λ xn, Ps%I) .. )
    Qs%I
    e
    e'
    [tele_arg ⊤] )
  (at level 20, n at level 9, x1 closed binder, xn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC2  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{  [ ▷^ n ]  'RET'  [ e' ] ; '/  '  Qs  } } ']'", only printing
).

Notation "'SPEC2' x1 .. xn , {{ Ps } } e {{ 'RET' [ e' ] ; Qs } }" :=
  (ReductionStep'
    wp_red_cond
    empty_hyp_first%I
    1
    (fupd ⊤ ⊤)
    (fupd ⊤ ⊤)
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    _
    (λ x1, .. (λ xn, Ps%I) .. )
    Qs%I
    e
    e'
    [tele_arg ⊤] )
  (at level 20, x1 closed binder, xn closed binder, e, Ps, e', Qs at level 200, format
  "'[hv' SPEC2  x1 .. xn ,  '/ ' {{  Ps  } } '/  '  e  '/ ' {{  'RET'  [ e' ] ; '/  '  Qs  } } ']'", only printing
).
