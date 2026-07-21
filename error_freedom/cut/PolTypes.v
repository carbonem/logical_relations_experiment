(** * Actions and session types

    The vocabulary shared by the error notion and the logical
    relation: what a prefix can offer on an endpoint ([act]), when
    two offers meet without going wrong ([compat]), the protocols
    themselves ([sty]), duality, and the bridge from a protocol to
    the action its head prescribes.

    A *runtime error* is two co-endpoints of one session offering
    incompatible capabilities: both outputs, both inputs, or a close
    facing a delegation (the "wrong sort of message" errors).  This
    file fixes the vocabulary; the error predicate itself is
    [PolErr.errP], over the transition families of [PolLTS.v].

    Design note: [compat] is a boolean, so evidence of a mismatch is
    positive and decidable -- a pair of actions plus [erefl].  No
    negated proposition occurs inside the error predicate.  Error freedom
    ([PolErr.error_freeP]) is the one genuinely negative notion in the
    development; the logical relation built on top has positive,
    conditional clauses and meets errors only as the final
    contradiction in adequacy.

    HISTORY.  Split across [PolTypes.v] and [LogRel.v], whose other
    halves -- error and safety over the ≅-calculus, and the
    ≅-based interpretations -- went to [cemetery/]. *)

From mathcomp Require Import all_ssreflect.
From Tait Require Import PolBase.

Set Implicit Arguments.
Unset Strict Implicit.

(** ** Head actions

    The capabilities a prefix can offer on its subject endpoint.  The
    delegated endpoint and the selected label are irrelevant to
    compatibility, so actions carry no payload. *)
Inductive act : Set := AClose | AWait | ADelS | ADelR | ASel | ABra.

(** Compatibility of the actions at the two endpoints of one session:
    close meets wait, delegation send meets delegation receive.
    Everything else -- output/output, input/input, close vs delegation --
    is a communication mismatch. *)
Definition compat (a b : act) : bool :=
  match a, b with
  | AClose, AWait | AWait, AClose | ADelS, ADelR | ADelR, ADelS => true
  | ASel, ABra | ABra, ASel => true
  | _, _ => false
  end.

(** ** Session types

    [SClose]/[SWait] are the two ends of session termination;
    [SSend S1 S2] delegates a channel promised to behave as [S1], then
    continues as [S2]; [SRecv S1 S2] receives a channel assumed to behave
    as [S1], then continues as [S2].  No recursion, no choice (yet), no
    data other than channels. *)
Inductive sty : Set :=
| SClose : sty
| SWait  : sty
| SSend  : sty -> sty -> sty
| SRecv  : sty -> sty -> sty
| SSel   : sty -> sty -> sty
| SBra   : sty -> sty -> sty.

(** Duality: the payload is NOT dualised -- both sides agree on how the
    delegated channel itself will be used by whoever ends up holding it. *)
Fixpoint dual (S : sty) : sty :=
  match S with
  | SClose      => SWait
  | SWait       => SClose
  | SSend S1 S2 => SRecv S1 (dual S2)
  | SRecv S1 S2 => SSend S1 (dual S2)
  | SSel S1 S2  => SBra (dual S1) (dual S2)
  | SBra S1 S2  => SSel (dual S1) (dual S2)
  end.

Lemma dual_involutive S : dual (dual S) = S.
Proof.
  by elim: S
    => [| |S1 _ S2 IH|S1 _ S2 IH|S1 IH1 S2 IH2|S1 IH1 S2 IH2] //=;
    rewrite ?IH ?IH1 ?IH2.
Qed.

(** Bridge to [PolTypes.act]: the action a protocol's head prescribes. *)
Definition head_act (S : sty) : act :=
  match S with
  | SClose     => AClose
  | SWait      => AWait
  | SSend _ _  => ADelS
  | SRecv _ _  => ADelR
  | SSel _ _   => ASel
  | SBra _ _   => ABra
  end.
