(** * Session typing with context splitting

    The typing discipline of Honda--Vasconcelos--Kubo, transposed to
    polarized endpoints: a parallel composition SPLITS its context
    between the two components, and a restriction hands the body BOTH
    ends of a fresh session.

    This is the point of departure from the cut-based system in
    [../cut/Typing.v], where [TP_Par] linked exactly one channel
    and the frames were disjoint.  There, a typed process is a TREE of
    sessions: two components share at most one session, so a cyclic
    dependency cannot be written and deadlock is impossible by
    construction.  Here two components may share as many sessions as
    they like, in particular

      (ν x)(ν y)( x⁺!․ y⁻?․ ∅  ∥  y⁺!․ x⁻?․ ∅ )

    is well typed and deadlocked (see [typed_deadlock] below).  That is
    deliberate: deadlock is not a communication error, and the theorem
    this development proves -- error freedom -- is exactly the property
    that survives the move.

    CONTEXTS MAP ENDPOINTS.  The cut-based system could index contexts
    by NAMES, because its ✓ slot ([Schk]) recorded "both ends of this
    name were linked at the cut here", and the linking cut was unique.
    With splitting the two ends of a session may travel to different
    components, arbitrarily deep, so each endpoint needs its own
    entry: [pctx n := pch n -> option sty].  [Schk] disappears.

    BALANCE.  Nothing forces the two ends of a name in a context to be
    dual -- and indeed a prefix rule breaks it: from [x⁺ : !T.S] and
    [x⁻ : ?T.dual S] the output rule leaves [x⁺ : S] against an
    unchanged [x⁻].  Balance is therefore a PREMISE about the context a
    process is typed in ([balanced], below), not an invariant of
    derivations.  The [balanced_*] lemmas at the end of this file
    record exactly where it is preserved -- everywhere except at a
    prefix whose subject is a both-held name, which is precisely the
    node the semantic bridge will refuse to descend, because such a
    prefix can never fire. *)

From mathcomp Require Import all_ssreflect.
From Tait Require Import Base Types Proc LTS.

Set Implicit Arguments.
Unset Strict Implicit.
Open Scope pol_scope.

(** ** Typing contexts

    An entry [Δ c = Some S] means: this process owns the endpoint [c]
    and will use it according to [S].  [None] means it does not own
    it.  Ownership is linear -- the splitting rule below never gives
    the same endpoint to both components. *)

Definition pctx (n : nat) : Type := pch n -> option sty.

Definition pcempty {n : nat} : pctx n := fun _ => None.

Definition pcupd {n : nat} (c : pch n) (o : option sty) (Δ : pctx n)
  : pctx n :=
  fun d => if d == c then o else Δ d.

Lemma pcupd_eq n (c : pch n) o (Δ : pctx n) : pcupd c o Δ c = o.
Proof. by rewrite /pcupd eqxx. Qed.

Lemma pcupd_neq n (c d : pch n) o (Δ : pctx n) :
  d != c -> pcupd c o Δ d = Δ d.
Proof. rewrite /pcupd. by case: eqP. Qed.

(** ** Splitting

    Every endpoint belongs to exactly one component.  This subsumes
    the two extremes the cut rule could not express: a component may
    take no endpoint at all (independent parallel composition, "mix"),
    and the two ends of MANY sessions may be separated at the same
    node (cycles). *)

Definition psplit {n : nat} (Δ1 Δ2 Δ : pctx n) : Prop :=
  forall c, (Δ1 c = None /\ Δ c = Δ2 c) \/ (Δ2 c = None /\ Δ c = Δ1 c).

(** ** Balanced contexts

    If a context holds both ends of a name, they run dual protocols. *)

Definition balanced {n : nat} (Δ : pctx n) : Prop :=
  forall (x : ch n) T U,
    Δ (x, pos) = Some T -> Δ (x, neg) = Some U -> U = dual T.

(** ** Scope extension

    A restriction binds ONE name and hands the body BOTH of its
    endpoints, at dual protocols. *)
Definition pcnu {n : nat} (T : sty) (Δ : pctx n) : pctx n.+1 :=
  fun c =>
    match c.1 with
    | None => Some (if c.2 is pos then T else dual T)
    | Some x => Δ (x, c.2)
    end.

(** A receive binds one name and owns ONE of its endpoints -- the one
    whose polarity the prefix announces.  The co-endpoint stays with
    whoever else holds it. *)
Definition pcrecv {n : nat} (rd : pol) (T : sty) (Δ : pctx n)
  : pctx n.+1 :=
  fun c =>
    match c.1 with
    | None => if c.2 == rd then Some T else None
    | Some x => Δ (x, c.2)
    end.

(** ** Typing *)

Inductive typedP : forall n, pctx n -> procP n -> Prop :=
| TP_End : forall n (Δ : pctx n),
    (forall c, Δ c = None) ->
    typedP Δ ∅
| TP_Close : forall n (Δ : pctx n) (c : pch n) K,
    Δ c = Some SClose ->
    typedP (pcupd c None Δ) K ->
    typedP Δ (c !․ K)
| TP_Wait : forall n (Δ : pctx n) (c : pch n) K,
    Δ c = Some SWait ->
    typedP (pcupd c None Δ) K ->
    typedP Δ (c ?․ K)
| TP_Del : forall n (Δ : pctx n) (c d : pch n) T S2 K,
    Δ c = Some (SSend T S2) ->
    Δ d = Some T ->
    typedP (pcupd d None (pcupd c (Some S2) Δ)) K ->
    typedP Δ (c ! d ․ K)
| TP_Ins : forall n (Δ : pctx n) (c : pch n) (rd : pol) T S2
    (K : procP n.+1),
    Δ c = Some (SRecv T S2) ->
    typedP (pcrecv rd T (pcupd c (Some S2) Δ)) K ->
    typedP Δ (c ?( rd )․ K)
| TP_Sel : forall n (Δ : pctx n) (c : pch n) (b : bool) S1 S2 K,
    Δ c = Some (SSel S1 S2) ->
    typedP (pcupd c (Some (if b then S1 else S2)) Δ) K ->
    typedP Δ (c ◁ b ․ K)
| TP_Bra : forall n (Δ : pctx n) (c : pch n) S1 S2 K1 K2,
    Δ c = Some (SBra S1 S2) ->
    typedP (pcupd c (Some S1) Δ) K1 ->
    typedP (pcupd c (Some S2) Δ) K2 ->
    typedP Δ (c ▷ ( K1 | K2 ))
| TP_Par : forall n (Δ Δ1 Δ2 : pctx n) P Q,
    psplit Δ1 Δ2 Δ ->
    typedP Δ1 P -> typedP Δ2 Q ->
    typedP Δ (P ∥ Q)
| TP_Res : forall n (Δ : pctx n) (T : sty) (B : procP n.+1),
    typedP (pcnu T Δ) B ->
    typedP Δ ((ν) B).

(** ** Where balance is preserved

    These are the steps the semantic bridge will take.  Deliberately
    absent: a prefix whose subject's co-end is also held.  That is the
    unbalancing step, and it is unreachable -- an internal endpoint has
    no synchronization partner, since transitions synchronize only at
    a parallel composition. *)

Lemma balanced_empty n : balanced (@pcempty n).
Proof. by []. Qed.

Lemma balanced_upd_none n (Δ : pctx n) (c : pch n) :
  balanced Δ -> balanced (pcupd c None Δ).
Proof.
  move=> HB x T U. rewrite /pcupd.
  case: ((x, pos) =P c) => [_|_] //.
  case: ((x, neg) =P c) => [_|_] //.
  exact: HB.
Qed.

(** Updating an endpoint whose co-end is NOT held keeps balance: the
    name in question simply never has both ends. *)
Lemma balanced_upd_sep n (Δ : pctx n) (c : pch n) S :
  balanced Δ -> Δ (pflip c) = None ->
  balanced (pcupd c (Some S) Δ).
Proof.
  move=> HB Hco x T U. rewrite /pcupd.
  case: ((x, pos) =P c) => [Ep|_].
  - case: ((x, neg) =P c) => [Eq|_].
    + by rewrite -Ep in Eq; case: Eq.
    + move=> _. rewrite -Ep /pflip /= in Hco. by rewrite Hco.
  - case: ((x, neg) =P c) => [Eq|_].
    + move=> HT _. rewrite -Eq /pflip /= in Hco. by rewrite Hco in HT.
    + exact: HB.
Qed.

Lemma balanced_split n (Δ1 Δ2 Δ : pctx n) :
  psplit Δ1 Δ2 Δ -> balanced Δ -> balanced Δ1 /\ balanced Δ2.
Proof.
  move=> Hs HB. split=> x T U H1 H2.
  - have E1 : Δ (x, pos) = Some T.
      case: (Hs (x, pos)) => -[Ha Hb]; first by rewrite Ha in H1.
      by rewrite Hb H1.
    have E2 : Δ (x, neg) = Some U.
      case: (Hs (x, neg)) => -[Hc Hd]; first by rewrite Hc in H2.
      by rewrite Hd H2.
    exact: HB E1 E2.
  - have E1 : Δ (x, pos) = Some T.
      case: (Hs (x, pos)) => -[Ha Hb]; last by rewrite Ha in H1.
      by rewrite Hb H1.
    have E2 : Δ (x, neg) = Some U.
      case: (Hs (x, neg)) => -[Hc Hd]; last by rewrite Hc in H2.
      by rewrite Hd H2.
    exact: HB E1 E2.
Qed.

Lemma balanced_pcnu n (Δ : pctx n) T :
  balanced Δ -> balanced (pcnu T Δ).
Proof.
  move=> HB [x|] S U //=.
  - exact: HB.
  - by move=> [<-] [<-].
Qed.

Lemma balanced_pcrecv n (Δ : pctx n) rd T :
  balanced Δ -> balanced (pcrecv rd T Δ).
Proof.
  move=> HB [x|] S U //=; first exact: HB.
  by case: rd => //=.
Qed.

(** ** Examples *)
Section Examples.

(** The canonical cut, still typable: one session, two components. *)
Example typed_close_wait :
  typedP pcempty ((ν) (((zero, pos) !․ ∅) ∥ ((zero, neg) ?․ ∅))
                  : procP 0).
Proof.
  apply: (TP_Res (T := SClose)).
  apply: (TP_Par
    (Δ1 := pcupd (zero, pos) (Some SClose) pcempty)
    (Δ2 := pcupd (zero, neg) (Some SWait) pcempty)).
  - move=> [[x|] r] //=; rewrite /pcupd /pcempty /=.
    case: r => /=; by [right | left].
  - apply: TP_Close; first by rewrite pcupd_eq.
    apply: TP_End => c.
    by rewrite /pcupd /pcempty; do ! case: ifP => [_|->].
  - apply: TP_Wait; first by rewrite pcupd_eq.
    apply: TP_End => c.
    by rewrite /pcupd /pcempty; do ! case: ifP => [_|->].
Qed.

(** What the cut-based system could NOT type: two sessions shared
    across one parallel composition.  The result is a deadlock -- each
    component closes its own session first and then waits on the
    other's -- and it is well typed.  Deadlock is not a communication
    error, so the theorem is unaffected; this is the expressiveness
    the split rule buys, and the reason liveness becomes a real
    question in this system. *)
Example typed_deadlock :
  typedP pcempty
    ((ν) ((ν) ( ((zero, pos) !․ ((one, neg) ?․ ∅))
              ∥ ((one, pos) !․ ((zero, neg) ?․ ∅)) )) : procP 0).
Proof.
  apply: (TP_Res (T := SClose)).
  apply: (TP_Res (T := SClose)).
  apply: (TP_Par
    (Δ1 := pcupd (zero, pos) (Some SClose)
             (pcupd (one, neg) (Some SWait) pcempty))
    (Δ2 := pcupd (one, pos) (Some SClose)
             (pcupd (zero, neg) (Some SWait) pcempty))).
  - move=> [[[x|]|] r] //=; rewrite /pcupd /pcempty /=;
      case: r => /=; by [left | right].
  - apply: TP_Close; first by rewrite pcupd_eq.
    apply: TP_Wait; first by rewrite /pcupd /=.
    apply: TP_End => c.
    by rewrite /pcupd /pcempty; do ! case: ifP => [_|->].
  - apply: TP_Close; first by rewrite pcupd_eq.
    apply: TP_Wait; first by rewrite /pcupd /=.
    apply: TP_End => c.
    by rewrite /pcupd /pcempty; do ! case: ifP => [_|->].
Qed.

End Examples.

(** The deadlock really is one: no internal step is possible.  (Each
    component's head is a close on its OWN session, and the partner
    for that close is behind the other component's head prefix.)  It
    is nevertheless not an error, which is why error freedom survives
    the move to split contexts. *)
Example no_step_deadlock (R : procP 0) :
  ~ ltstP ((ν) ((ν) ( ((zero, pos) !․ ((one, neg) ?․ ∅))
                    ∥ ((one, pos) !․ ((zero, neg) ?․ ∅)) ))) R.
Proof.
  move=> H. pinv H.
  repeat match goal with
  | [ HX : ltstP (PClose _ _) _ |- _ ] => by pinv HX
  | [ HX : ltswP _ (PClose _ _) _ |- _ ] => by pinv HX
  | [ HX : ltsfP _ _ (PClose _ _) _ |- _ ] => by pinv HX
  | [ HX : ltsrP _ _ (PClose _ _) _ |- _ ] => by pinv HX
  | [ HX : ltsbP _ _ (PClose _ _) _ |- _ ] => by pinv HX
  | [ HX : ltsselP _ _ (PClose _ _) _ |- _ ] => by pinv HX
  | [ HX : ltsbrP _ _ (PClose _ _) _ |- _ ] => by pinv HX
  | [ HX : ltstP (PPar _ _) _ |- _ ] => pinv HX
  | [ HX : ltstP (PRes _) _ |- _ ] => pinv HX
  | [ HX : ltscP _ (PClose _ _) _ |- _ ] => pinv HX
  end.
Qed.
