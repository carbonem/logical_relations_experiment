(** * A logical relation for communication safety

    Analogue, for the session calculus of [synsem.v] and the error notion
    of [Errors.v], of the hereditary-termination relation [HT] of [Tait.v],
    organised like the RSLR of Balzer-Derakshan-Harper-Yao
    ([references/illst.pdf], Fig. 5): a *value interpretation* [Vsem],
    defined by cases on the structure of the session type, mutually with a
    *term interpretation* [Esem] that quantifies over internal runs.

    ** Shape

    A lambda term is observed by running it: [HT] can be a predicate on
    closed terms because a closed term reduces by itself.  A process
    owning one endpoint interacts only together with a peer, and
    delegation keeps changing which channels a process owns.  So, as in
    the RSLR (there: a relation indexed by a sequent [Δ ⊩ K]), the
    relation here is indexed by a *semantic context* [Δ : ch n -> option
    sty], the protocols of all currently owned channels ([None] = not
    owned), and observation means *exposure*: [P' ≅ prefix ∥ frame] is
    exactly the shape a peer needs to form a redex ([R_Close]/[R_Com])
    and the shape [E_Mismatch] needs to form an error.

    - [Esem k Δ P]: along every internal run [P ⇛* P'], (i) every exposed
      prefix sits on an owned channel and performs the head action of its
      protocol ([conform]), (ii) for every owned channel, the exposure
      behaves as the value interpretation of its type prescribes, and
      (iii) descending under a restriction, some protocol governs the
      bound session, dually at its two endpoints (semantic cut).
    - [Vsem E Δ x S P']: by cases on [S] -- the type-structural heart.
      Each case constrains only the exposure shape matching [S]'s head
      (the mismatching shapes are already excluded by [conform]) and
      states the continuation obligation at the updated context, with the
      subterms [S1], [S2] of [S] flowing into the context.

    Reading the four cases against [Tait.v]:
      [SClose]/[SWait] are the base observations (cf. [HT Ans]);
      [SSend S1 S2] is conjunctive, payload *proven* at [S1] (cf. the
      [Prod] clause of [HT]); [SRecv S1 S2] is universal, arriving
      channel *assumed* at [S1] (cf. the [Arr] clause).  This
      assert/assume duality is the "pas de deux" of the RSLR paper.

    ** What the recursion is on

    The clauses are by cases on the type, but the *recursion* is on an
    observation index [k], decremented at each observed event
    (communication or descent under a restriction) -- exactly the RSLR's
    observation index [m] ([illst.pdf] Fig. 5, clauses (11)-(12)): there
    too, [V^{m+1}] invokes [E^m], and types are only matched, never
    recursed on.  Their non-recursive predecessors could instead use
    multiset induction on the types of the sequent; that option exists
    here as well (the four communication clauses strictly shrink the
    total context) but is broken by the semantic-cut clause, whose
    existential protocol is unbounded by [Δ] -- the RSLR does not need
    that clause because its relation is restricted to syntactically
    well-typed configurations (their [Tree]) and its runtime has no
    binder.  Keeping the relation untyped and the calculus's [ν] keeps
    the index.  [⇛*] is quantified *inside* a level: [k] never counts
    reduction steps, so no step arithmetic anywhere.

    ** Polarity

    Everything is positive: conditional clauses with data conclusions.
    In particular [conform] states "exposed ⟹ owned and matching" rather
    than "not mismatching", and no clause mentions [err].  The negative
    notion [safe] enters only through the intended adequacy theorem

        SEM Δ P  ->  safe P

    whose core is definitional: at a restriction the semantic cut gives
    the endpoints protocols [S] and [dual S]; [conform] forces two
    exposed prefixes there to perform [head_act S] and
    [head_act (dual S)]; and dual heads are compatible ([compat_dual]).
    An [E_Mismatch] is therefore unreachable. *)

From mathcomp Require Import all_ssreflect.
From Tait Require Import synsem Errors.

Set Implicit Arguments.
Unset Strict Implicit.

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
| SRecv  : sty -> sty -> sty.

(** Duality: the payload is NOT dualised -- both sides agree on how the
    delegated channel itself will be used by whoever ends up holding it. *)
Fixpoint dual (S : sty) : sty :=
  match S with
  | SClose      => SWait
  | SWait       => SClose
  | SSend S1 S2 => SRecv S1 (dual S2)
  | SRecv S1 S2 => SSend S1 (dual S2)
  end.

Lemma dual_involutive S : dual (dual S) = S.
Proof. by elim: S => [| |S1 _ S2 IH|S1 _ S2 IH] //=; rewrite IH. Qed.

(** Bridge to [Errors.act]: the action a protocol's head prescribes. *)
Definition head_act (S : sty) : act :=
  match S with
  | SClose     => AClose
  | SWait      => AWait
  | SSend _ _  => ADelS
  | SRecv _ _  => ADelR
  end.

(** Dual protocols prescribe compatible actions: the definitional core of
    the future adequacy theorem. *)
Lemma compat_dual S : compat (head_act S) (head_act (dual S)).
Proof. by case: S. Qed.

(** ** Semantic contexts *)
Definition sctx (n : nat) := ch n -> option sty.

(** The empty context: own nothing. *)
Definition cempty {n : nat} : sctx n := fun _ => None.

(** Pointwise update. *)
Definition cupd {n : nat} (x : ch n) (o : option sty) (Δ : sctx n) : sctx n :=
  fun y => if y == x then o else Δ y.

(** Context extension at a restriction: the two fresh endpoints get dual
    protocols ([zero ↦ S], [one ↦ dual S]; the typing rule for [ResP]
    must make the same choice). *)
Definition cext {n : nat} (S : sty) (Δ : sctx n) : sctx n.+2 :=
  scons (Some S) (scons (Some (dual S)) Δ).

(** ** Conformance

    Every exposed prefix sits on an owned channel and performs the head
    action its protocol prescribes.  ([prefix_at] is the head-action
    view of [Errors.v] -- the logical relation and the error predicate
    speak the same language, which is what makes adequacy definitional.) *)
Definition conform {n : nat} (Δ : sctx n) (P' : proc n) : Prop :=
  forall a (x : ch n) F R,
    P' ≅ F ∥ R -> prefix_at a x F ->
    exists S, Δ x = Some S /\ a = head_act S.

(** ** The value interpretation: by cases on the session type

    [E] is the term interpretation one observation deeper.  Each case
    speaks only about the exposure shape matching the head of [S]:
    [conform] has already excluded the other shapes at [x].  The subterms
    of [S] flow into the context: continuation type to the subject,
    payload type to the delegated/received channel. *)
Section ValueInterpretation.

Variable E : forall n : nat, sctx n -> proc n -> Prop.

Definition Vsem {n : nat} (Δ : sctx n) (x : ch n) (S : sty) (P' : proc n)
  : Prop :=
  match S with
  | SClose =>
      (* base: the channel is consumed *)
      forall K R, P' ≅ CloseP x K ∥ R ->
        E (cupd x None Δ) (K ∥ R)
  | SWait =>
      forall K R, P' ≅ WaitP x K ∥ R ->
        E (cupd x None Δ) (K ∥ R)
  | SSend S1 S2 =>
      (* conjunctive / "assert" (cf. [HT (Prod _ _)]): the payload is
         owned, at exactly [S1], and given away; the subject continues
         at [S2] *)
      forall y K R, P' ≅ DelP x y K ∥ R ->
        Δ y = Some S1 /\
        E (cupd y None (cupd x (Some S2) Δ)) (K ∥ R)
  | SRecv S1 S2 =>
      (* universal / "assume" (cf. [HT (Arr _ _)]): the arriving channel
         is a generic fresh name -- the obligation is on the *open*
         continuation, one binder deeper, with the received channel at
         [zero] assumed at [S1] and the frame shifted along.  (A
         quantification over existing unowned names would be vacuous in
         a fully-owned scope and too weak to survive renaming/framing;
         the binder form is generic by construction, and any concrete
         arrival is an instance via the renaming [scons y id_ren].)
         Note the payoff: this is the same context extension as the
         typing rule [T_InS]. *)
      forall K R, P' ≅ InSP x K ∥ R ->
        E (scons (Some S1) (cupd x (Some S2) Δ))
          (K ∥ subst_proc shift R)
  end.

End ValueInterpretation.

(** ** The term interpretation *)
Fixpoint Esem (k : nat) {n : nat} (Δ : sctx n) (P : proc n) {struct k}
  : Prop :=
  match k with
  | 0 => True
  | k.+1 =>
      forall P' : proc n, P ⇛* P' ->
        [/\ conform Δ P',
            forall x S, Δ x = Some S -> Vsem (@Esem k) Δ x S P'
          & forall Q : proc n.+2, P' ≅ (ν) Q ->
              exists S, Esem k (cext S Δ) Q ]
  end.

(** The relation proper: all observation depths. *)
Definition SEM {n : nat} (Δ : sctx n) (P : proc n) : Prop :=
  forall k, Esem k Δ P.

Notation "Δ ⊨ P" := (SEM Δ P) (at level 68).

(** ** Computation laws for [cext] *)
Lemma cext_zero n S (Δ : sctx n) : cext S Δ zero = Some S.
Proof. by []. Qed.

Lemma cext_one n S (Δ : sctx n) : cext S Δ one = Some (dual S).
Proof. by []. Qed.

(** ** Basic properties of the relation

    All of these use the clauses only in the forward direction: the [≅]
    and [⇛*] premises inside [Esem] simply compose. *)

(** [Vsem] is covariant in the underlying term interpretation... *)
Lemma Vsem_mono (E E' : forall n : nat, sctx n -> proc n -> Prop)
  (HEE' : forall n (Δ : sctx n) P, E n Δ P -> E' n Δ P)
  n (Δ : sctx n) (x : ch n) S P' :
  Vsem E Δ x S P' -> Vsem E' Δ x S P'.
Proof.
  case: S => [| |S1 S2|S1 S2] /= HV.
  - move=> K R Hc. apply: HEE'. exact: HV Hc.
  - move=> K R Hc. apply: HEE'. exact: HV Hc.
  - move=> y K R Hc. case: (HV _ _ _ Hc) => Hy HE. split=> //. exact: HEE'.
  - move=> K R Hc. apply: HEE'. exact: HV Hc.
Qed.

(** ...and invariant under [≅] of the observed process. *)
Lemma Vsem_struct (E : forall n : nat, sctx n -> proc n -> Prop)
  n (Δ : sctx n) (x : ch n) S (P' Q' : proc n) :
  P' ≅ Q' -> Vsem E Δ x S P' -> Vsem E Δ x S Q'.
Proof.
  move=> Heq; case: S => [| |S1 S2|S1 S2] /= HV.
  - move=> K R Hc. exact: HV (SC_Trans Heq Hc).
  - move=> K R Hc. exact: HV (SC_Trans Heq Hc).
  - move=> y K R Hc. exact: HV (SC_Trans Heq Hc).
  - move=> K R Hc. exact: HV (SC_Trans Heq Hc).
Qed.

(** [Esem] is antitone in the observation depth: observing less is
    easier. *)
Lemma Esem_antitone k : forall n (Δ : sctx n) (P : proc n),
  Esem k.+1 Δ P -> Esem k Δ P.
Proof.
  elim: k => [//|k IH] n Δ P HE P' Hred.
  case: (HE _ Hred) => C V X; split=> //.
  - move=> x S HxS.
    exact: (Vsem_mono (E := @Esem k.+1) (E' := @Esem k) IH (V _ _ HxS)).
  - move=> Q HQ. case: (X _ HQ) => S HS. exists S. exact: IH.
Qed.

(** [Esem] is invariant under structural congruence: a congruent process
    has the same reducts (up to absorbing the congruence into the first
    step, [struct_mreduce]) and the same exposures (by transitivity in
    the exposure premises). *)
Lemma Esem_struct k n (Δ : sctx n) (P Q : proc n) :
  P ≅ Q -> Esem k Δ P -> Esem k Δ Q.
Proof.
  case: k => [//|k] Heq HE P' Hred.
  case: (struct_mreduce Heq Hred) => [HPP'|HPP'].
  - case: (HE _ (MR_refl _)) => C V X; split.
    + move=> a x F R HFR Hpa. exact: C (SC_Trans HPP' HFR) Hpa.
    + move=> x S HxS. exact: Vsem_struct HPP' (V _ _ HxS).
    + move=> Q0 HQ0. exact: X (SC_Trans HPP' HQ0).
  - exact: HE _ HPP'.
Qed.

(** [Esem] is closed under reduction (forward): the runs of a reduct are
    runs of the source. *)
Lemma Esem_mreduce k n (Δ : sctx n) (P Q : proc n) :
  P ⇛* Q -> Esem k Δ P -> Esem k Δ Q.
Proof.
  case: k => [//|k] Hred HE P' Hred'. exact: HE (mreduce_trans Hred Hred').
Qed.

Lemma SEM_struct n (Δ : sctx n) (P Q : proc n) : P ≅ Q -> Δ ⊨ P -> Δ ⊨ Q.
Proof. move=> Heq HS k. exact: Esem_struct Heq (HS k). Qed.

Lemma SEM_mreduce n (Δ : sctx n) (P Q : proc n) : P ⇛* Q -> Δ ⊨ P -> Δ ⊨ Q.
Proof. move=> Hred HS k. exact: Esem_mreduce Hred (HS k). Qed.

Lemma SEM_step n (Δ : sctx n) (P Q : proc n) : P ⇛ Q -> Δ ⊨ P -> Δ ⊨ Q.
Proof. move=> Hst. exact: SEM_mreduce (mreduce1 Hst). Qed.

(** ** Roadmap (theorems to come, in dependency order)

    - Inversion toolkit: what [≅] and [⇛] can do to an exposed prefix;
      inversion of the semantic-cut clause under junk wrappings (every
      [P'] is [≅ (ν)(∅ ∥ ...)], so that clause is never vacuous --
      benign, but its inversion lemma is real work).
    - [Esem] is antitone in [k]; [SEM] is invariant under [≅] and closed
      under [⇛] (essentially by construction: the premises compose).
    - Adequacy:  [Δ ⊨ P -> safe P]; in particular [cempty ⊨ P -> safe P].
    - Compatibility lemmas, one per typing rule of the (future) session
      type system, each paired with the [Vsem] case of the same type
      constructor, e.g.
        [Δ x = Some SClose -> cupd x None Δ ⊨ P -> Δ ⊨ CloseP x P]
      and the cut/restriction case
        [cext S Δ ⊨ P -> Δ ⊨ (ν) P].
    - Fundamental theorem, by induction on typing derivations, each case
      discharged by its compatibility lemma.  Corollary: well-typed
      closed processes are safe. *)

Print Assumptions compat_dual.
Print Assumptions dual_involutive.
