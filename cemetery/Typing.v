(** * Standard linear session typing for the calculus of [synsem.v]

    Classical-style judgment [Δ ⊢ P]: a process is typed against a
    context assigning a session type to every channel it owns -- no
    distinguished provided channel.  Linearity is enforced the standard
    way: a *split* operator distributes ownership between the components
    of a parallel composition (no linearity predicates).

    Contexts are the semantic contexts [sctx n] of [LogRel.v]
    ([ch n -> option sty], [None] = not owned), so each typing rule pairs
    with the [Vsem] case of the same type constructor, and [T_Res] uses
    the same [cext] as the semantic-cut clause -- the fundamental theorem
    will be a rule-by-rule match:

      [T_Close] / [T_Wait]  ~  [Vsem SClose] / [Vsem SWait]
      [T_Del]               ~  [Vsem (SSend S1 S2)]
      [T_InS]               ~  [Vsem (SRecv S1 S2)]
      [T_Res]               ~  the semantic-cut clause of [Esem]
      [T_Par]               ~  semantic splitting (to be proved)
      [T_End]               ~  vacuous conformance *)

From mathcomp Require Import all_ssreflect.
From Tait Require Import synsem Errors LogRel.

Set Implicit Arguments.
Unset Strict Implicit.

(** ** Context splitting

    [split Δ Δ1 Δ2]: every owned channel of [Δ] goes to exactly one of
    the two sides; channels not owned by [Δ] are owned by neither. *)
Definition split {n : nat} (Δ Δ1 Δ2 : sctx n) : Prop :=
  forall x, (Δ1 x = Δ x /\ Δ2 x = None) \/ (Δ2 x = Δ x /\ Δ1 x = None).

Lemma split_sym n (Δ Δ1 Δ2 : sctx n) : split Δ Δ1 Δ2 -> split Δ Δ2 Δ1.
Proof. by move=> H x; case: (H x) => [[? ?]|[? ?]]; [right | left]. Qed.

(** Splitting off nothing. *)
Lemma split_empty n (Δ : sctx n) : split Δ Δ cempty.
Proof. by move=> x; left. Qed.

(** ** Small context-update laws (used throughout) *)
Lemma cupd_eq n (x : ch n) o (Δ : sctx n) : cupd x o Δ x = o.
Proof. by rewrite /cupd eqxx. Qed.

Lemma cupd_neq n (x y : ch n) o (Δ : sctx n) :
  y != x -> cupd x o Δ y = Δ y.
Proof. by rewrite /cupd => /negbTE ->. Qed.

(** ** The typing judgment *)
Reserved Notation "Δ '⊢' P" (at level 68).
Inductive typed : forall n, sctx n -> proc n -> Prop :=
| T_End : forall n (Δ : sctx n),
    (forall x, Δ x = None) ->
    Δ ⊢ EndP n

| T_Close : forall n (Δ : sctx n) (x : ch n) P,
    Δ x = Some SClose ->
    cupd x None Δ ⊢ P ->
    Δ ⊢ CloseP x P

| T_Wait : forall n (Δ : sctx n) (x : ch n) P,
    Δ x = Some SWait ->
    cupd x None Δ ⊢ P ->
    Δ ⊢ WaitP x P

| T_Del : forall n (Δ : sctx n) (x y : ch n) P S1 S2,
    Δ x = Some (SSend S1 S2) ->
    Δ y = Some S1 ->
    cupd y None (cupd x (Some S2) Δ) ⊢ P ->
    Δ ⊢ DelP x y P

| T_InS : forall n (Δ : sctx n) (x : ch n) (P : proc n.+1) S1 S2,
    Δ x = Some (SRecv S1 S2) ->
    scons (Some S1) (cupd x (Some S2) Δ) ⊢ P ->
    Δ ⊢ InSP x P

| T_Par : forall n (Δ Δ1 Δ2 : sctx n) P Q,
    split Δ Δ1 Δ2 ->
    Δ1 ⊢ P ->
    Δ2 ⊢ Q ->
    Δ ⊢ P ∥ Q

| T_Res : forall n (Δ : sctx n) S (P : proc n.+2),
    cext S Δ ⊢ P ->
    Δ ⊢ (ν) P

where "Δ '⊢' P" := (typed Δ P).

(** Remarks.
    - [T_Del]: [y = x] is impossible ([Δ x] would equal both
      [Some (SSend S1 S2)] and [Some S1], and no type is a strict subterm
      of itself), so no explicit freshness side condition is needed.
    - [T_InS]: the continuation lives one binder deeper; [scons] places
      the received channel at [zero] with the payload type [S1], and the
      subject continues at [shift x] with [S2] -- the same context shift
      the [Vsem (SRecv _ _)] clause performs by substituting the arriving
      name instead.
    - [T_Res]: same orientation as [cext] in the semantic-cut clause:
      [zero ↦ S], [one ↦ dual S].
    - [T_End] is strict (nothing left over): standard linear session
      typing.  The semantic model is weaker (an owned-but-unused channel
      violates no safety), so the fundamental theorem's direction
      [Δ ⊢ P -> Δ ⊨ P] is the interesting one. *)

(** ** Sanity: the canonical good process is typable

    [(ν)(one!․∅ ∥ zero?․∅)] -- close meets wait under the restriction.
    With [cext S], [one : dual S], so [S = SWait]. *)
Example typed_close_wait :
  cempty ⊢ (ν) (CloseP one (EndP 2) ∥ WaitP zero (EndP 2)).
Proof.
  apply: (T_Res (S := SWait)).
  apply: (T_Par (Δ1 := scons None (scons (Some SClose) cempty))
                (Δ2 := scons (Some SWait) (scons None cempty))).
  - (* split: [one] left, [zero] right *)
    by case=> [[[]|]|] /=; [left | right].
  - (* left component: close on [one] *)
    apply: T_Close => //=.
    apply: T_End => z; rewrite /cupd; case: eqP => [//|neq].
    by case: z neq => [[[]|]|] //= neq; case: neq.
  - (* right component: wait on [zero] *)
    apply: T_Wait => //=.
    apply: T_End => z; rewrite /cupd; case: eqP => [//|neq].
    by case: z neq => [[[]|]|] //= neq; case: neq.
Qed.

(** The mismatch [(ν)(one!․∅ ∥ zero!․∅)] is expected to be untypable
    ([one] and [zero] would both need [SClose], but they are dual) --
    provable once the inversion toolkit exists; recorded here as part of
    the roadmap rather than as a definition-level sanity check. *)

Print Assumptions typed_close_wait.
