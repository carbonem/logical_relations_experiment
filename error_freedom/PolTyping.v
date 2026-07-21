(** * Session typing for the polarized calculus

    Scheme ported from the user's probabilistic_subtyping/synchronous
    development ([TypingEnv.lean]/[Typing.lean]), stripped of the
    probabilistic content.  Contexts are keyed by NAME; each name
    carries one slot:

      [None]           -- unused
      [Some (Sep ρ S)] -- one endpoint open, polarity ρ, protocol S
      [Some Schk]      -- ✓: both endpoints consumed internally
                          (their [prob q] slot; without probabilities
                          nothing remains to record, so it is bare)

    [T_Par] is the cut: it links EXACTLY ONE channel [z] -- the left
    side holds [z] at [(ρ, T)], the right at [(flip ρ, dual T)] -- and
    the composite records ✓ at [z]; every other name goes wholly to
    one side.  [T_Res] binds a name that is already linked: the body
    is typed with ✓ at the fresh name.

    Delegation sends an OPEN endpoint ([Sep] slot); ✓ is never
    delegated and never split.  The bound-delegation sender that holds
    both ends of its own restriction ([PolLTS.run_bound_deleg]) is
    deliberately outside the typed fragment, as in the source
    development. *)

From mathcomp Require Import all_ssreflect.
From Tait Require Import PolBase PolTypes PolProc PolLTS.

Set Implicit Arguments.
Unset Strict Implicit.
Open Scope pol_scope.

(** ** Slots and contexts *)
Inductive slot : Type :=
| Sep  : pol -> sty -> slot
| Schk : slot.

Definition pctx (n : nat) : Type := ch n -> option slot.

Definition pcupd {n : nat} (x : ch n) (e : option slot) (Δ : pctx n)
  : pctx n :=
  fun y => if y == x then e else Δ y.

Definition pcempty {n : nat} : pctx n := fun _ => None.

(** ** Typing *)
Inductive typedP : forall n, pctx n -> procP n -> Prop :=
| TP_End : forall n (Δ : pctx n),
    (forall x, Δ x = None) ->
    typedP Δ ∅
| TP_Close : forall n (Δ : pctx n) (x : ch n) (r : pol) K,
    Δ x = Some (Sep r SClose) ->
    typedP (pcupd x None Δ) K ->
    typedP Δ ((x, r) !․ K)
| TP_Wait : forall n (Δ : pctx n) (x : ch n) (r : pol) K,
    Δ x = Some (Sep r SWait) ->
    typedP (pcupd x None Δ) K ->
    typedP Δ ((x, r) ?․ K)
| TP_Del : forall n (Δ : pctx n) (x y : ch n) (r rd : pol) T S2 K,
    Δ x = Some (Sep r (SSend T S2)) ->
    Δ y = Some (Sep rd T) ->
    typedP (pcupd y None (pcupd x (Some (Sep r S2)) Δ)) K ->
    typedP Δ ((x, r) ! (y, rd) ․ K)
| TP_Ins : forall n (Δ : pctx n) (x : ch n) (r rd : pol) T S2
    (K : procP n.+1),
    Δ x = Some (Sep r (SRecv T S2)) ->
    typedP (scons (Some (Sep rd T))
              (pcupd x (Some (Sep r S2)) Δ)) K ->
    typedP Δ ((x, r) ?( rd )․ K)
| TP_Par : forall n (Δ Δ1 Δ2 : pctx n) (z : ch n) (r : pol) T P Q,
    typedP Δ1 P -> typedP Δ2 Q ->
    Δ1 z = Some (Sep r T) ->
    Δ2 z = Some (Sep (flipp r) (dual T)) ->
    (forall x, x != z ->
       (Δ1 x = None /\ Δ x = Δ2 x) \/ (Δ2 x = None /\ Δ x = Δ1 x)) ->
    Δ z = Some Schk ->
    typedP Δ (P ∥ Q)
| TP_Res : forall n (Δ : pctx n) (P : procP n.+1),
    typedP (scons (Some Schk) Δ) P ->
    typedP Δ ((ν) P)
| TP_Sel : forall n (Δ : pctx n) (x : ch n) (r : pol) (b : bool)
    S1 S2 K,
    Δ x = Some (Sep r (SSel S1 S2)) ->
    typedP (pcupd x (Some (Sep r (if b then S1 else S2))) Δ) K ->
    typedP Δ ((x, r) ◁ b ․ K)
| TP_Bra : forall n (Δ : pctx n) (x : ch n) (r : pol) S1 S2 K1 K2,
    Δ x = Some (Sep r (SBra S1 S2)) ->
    typedP (pcupd x (Some (Sep r S1)) Δ) K1 ->
    typedP (pcupd x (Some (Sep r S2)) Δ) K2 ->
    typedP Δ ((x, r) ▷ ( K1 | K2 )).

(** ** Examples *)
Section Examples.

(** The canonical cut: [(ν)((0⁺)!․∅ ∥ (0⁻)?․∅)] from the empty
    context.  T_Res introduces ✓ at the bound name; T_Par links it:
    the closer gets [(pos, SClose)], the waiter
    [(neg, dual SClose) = (neg, SWait)]. *)
Example typed_close_wait :
  typedP pcempty ((ν) (((zero, pos) !․ ∅) ∥ ((zero, neg) ?․ ∅)) : procP 0).
Proof.
  apply: TP_Res.
  apply: (TP_Par
    (Δ1 := scons (Some (Sep pos SClose)) pcempty)
    (Δ2 := scons (Some (Sep neg SWait)) pcempty)
    (z := zero) (r := pos) (T := SClose)) => //.
  - apply: TP_Close => //.
    by apply: TP_End => -[[]|].
  - apply: TP_Wait => //.
    by apply: TP_End => -[[]|].
  - by move=> [[]|].
Qed.

(** Free delegation, fully closed:

      (ν y)( (ν c)( c⁺ ! y⁺ ․ c⁺ !․ ∅
                    ∥ c⁻ ?(pos)․ 0⁺ !․ (sh c)⁻ ?․ ∅ )
             ∥ y⁻ ?․ ∅ )

    The sender delegates its [y⁺] endpoint (protocol [SClose]) over
    [c], then closes [c].  The receiver receives a [pos] endpoint,
    closes the received session, then waits on [c].  Outside, the
    other end [y⁻] waits.  The inner cut links [c]; the outer cut
    links [y]; each ν binds a ✓-name. *)
Definition dsender : procP 2 :=
  (zero, pos) ! (one, pos) ․ ((zero, pos) !․ ∅).
Definition drecv : procP 2 :=
  (zero, neg) ?( pos )․ ((zero, pos) !․ ((shift zero, neg) ?․ ∅)).
Definition dwait : procP 1 := (zero, neg) ?․ ∅.

Example typed_free_deleg :
  typedP pcempty ((ν) (((ν) (dsender ∥ drecv)) ∥ dwait)).
Proof.
  (* outer ν introduces ✓ at y (name 0 outside) *)
  apply: TP_Res.
  (* outer par links y: left holds y⁺ (inside its own ν), right y⁻ *)
  apply: (TP_Par
    (Δ1 := scons (Some (Sep pos SClose)) pcempty)
    (Δ2 := scons (Some (Sep neg SWait)) pcempty)
    (z := zero) (r := pos) (T := SClose)) => //; first last.
  - (* frame *) by move=> [[]|].
  - (* right: wait on y⁻ *)
    apply: TP_Wait => //.
    by apply: TP_End => -[[]|].
  - (* left: the inner ν, c gets ✓; y⁺ rides through *)
    apply: TP_Res.
    (* inner par links c = zero (scope 2: 0 = c, 1 = y) *)
    apply: (TP_Par
      (Δ1 := fun w : ch 2 =>
               if w == zero then Some (Sep pos (SSend SClose SClose))
               else if w == one then Some (Sep pos SClose)
               else None)
      (Δ2 := fun w : ch 2 =>
               if w == zero then Some (Sep neg (SRecv SClose SWait))
               else None)
      (z := zero) (r := pos) (T := SSend SClose SClose)) => //.
    + (* sender: delegate y⁺ over c⁺, close c⁺ *)
      apply: (TP_Del (T := SClose) (S2 := SClose)) => //.
      apply: TP_Close => //.
      apply: TP_End => x. rewrite /pcupd. by case: x => [[[]|]|].
    + (* receiver: receive pos endpoint at SClose, close it, wait c⁻ *)
      apply: (TP_Ins (T := SClose) (S2 := SWait)) => //.
      apply: TP_Close => //.
      apply: TP_Wait => //.
      apply: TP_End => x. rewrite /pcupd. by case: x => [[[[]|]|]|].
    + (* frame: y⁺ rides left; everything else empty on both sides *)
      by move=> [[[]|]|] //= _; right.
Qed.

End Examples.
