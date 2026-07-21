(** * The logical relation, over the polarized calculus

    Step-indexed as before ([k] = internal-step budget), organized by
    type structure as before (one value clause per [sty] constructor),
    but over the slot contexts of [PolTyping.v].  The slot design pays
    off twice:

    1. THE CUT CLAUSE IS DETERMINISTIC.  A restriction's body is
       related at [scons (Some Schk) Δ] -- no [exists S].  The ✓ slot
       says "both endpoints live here, dually" without naming the
       protocol, so nothing depends on the observation depth.  (In the
       double-binder development the cut clause was [exists S, ... cext
       S Δ ...], and that [S] depended on [k] -- the non-uniformity
       that blocked sync consumption inside nested restrictions.)

    2. CONTEXTS ARE INVARIANT ALONG τ.  A τ-step synchronizes two
       co-endpoints held by the SAME process, so the subject's name is
       ✓ in Δ (or bound); the internal protocol advances but ✓ does
       not record it.  Sep-slots cannot τ: the process holds one end,
       the co-end is external, and conformance rules out offering it.
       So the step clause keeps Δ -- no context evolution.

    The relation has three clauses: conformance, protocol fidelity,
    invariance.

    CONFORMANCE is two-level.  [conformV] checks the visible surface:
    every offer is at an owned endpoint with the protocol's head
    action, or at a ✓ name; and at a ✓ name the two ends' heads are
    [compat].  [conformD] closes [conformV] under the structure,
    descending through ∥ (same Δ -- conformance is about coverage, not
    linearity) and through ν (extending Δ with ✓, so the body's OWN
    visible level enforces compatibility of the bound name's two
    ends).  Prefixes guard their continuations: a mismatch behind a
    prefix is not an error until the prefix fires, and then the step
    clause re-checks.  [conformD] is the pointwise negation of [errP].

    FIDELITY: for each [Sep ρ S] slot, the value interpretation
    [VsemP] at [(x,ρ)], by cases on [S], with early input: the
    received name is either fresh (extend the context) or the co-end
    of an owned end at the dual type (the two ends fuse into ✓).
    ✓ slots have no fidelity obligations: no external observer can
    synchronize with a ✓ name (its co-end is inside).

    Adequacy is at the end of the file, axiom-free. *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Eqdep_dec PeanoNat.
From Tait Require Import PolBase PolTypes PolProc PolLTS PolErr PolTyping.

Set Implicit Arguments.
Unset Strict Implicit.
Open Scope pol_scope.

(** ** Semantic slots

    The relation's contexts are richer than the typing contexts: the
    check carries its protocol.  [SBoth S] = both endpoints held, the
    [pos] end at [S], the [neg] end at [dual S].  Three independent
    routes force the type onto the ✓ (all discovered as failed proofs):
    a ν-body may delegate the bound name's own end outward (the
    composite's bound-send clause needs the payload type); a component
    may delegate its end of a live link (the receiver then fuses); and
    a bound-delegation sync creates a second live link, so fusing is
    not exotic.  The typing judgment keeps the bare [Schk]; the
    fundamental theorem chooses the [SBoth] types from the derivation.

    Both-slots carry NO value obligations: no external partner can
    ever synchronize with an internal end, so hypothetical visible
    transitions at them need no continuation tracking (this is what
    keeps the dual-pair invariant of [SBoth] from drifting).  Their
    conformance is per-end head agreement, from which mismatch-freedom
    follows by duality.  Internal synchronization at a both-name
    advances its protocol invisibly, so the step clause lets both-slot
    types evolve. *)

Inductive sslot : Type :=
| SSep  : pol -> sty -> sslot
| SBoth : sty -> sslot.

Definition sctxP (n : nat) : Type := ch n -> option sslot.

Definition scupd {n : nat} (x : ch n) (e : option sslot) (Δ : sctxP n)
  : sctxP n :=
  fun y => if y == x then e else Δ y.

Definition scempty {n : nat} : sctxP n := fun _ => None.

(** The protocol of the [r]-end of a session whose [pos] end runs [S]. *)
Definition pole (r : pol) (S : sty) : sty :=
  if r is pos then S else dual S.

Lemma pole_flip r S : pole (flipp r) S = dual (pole r S).
Proof. case: r => //=. by rewrite dual_involutive. Qed.

(** The protocol of one endpoint under a slot, if held. *)
Definition esat (r : pol) (e : sslot) : option sty :=
  match e with
  | SSep r' S0 => if pol_eqb r r' then Some S0 else None
  | SBoth S0 => Some (pole r S0)
  end.

Definition sat {n : nat} (Δ : sctxP n) (c : pch n) : option sty :=
  if Δ c.1 is Some e then esat c.2 e else None.

(** Removing one endpoint from a slot (payload delegated away). *)
Definition econsume (r : pol) (e : sslot) : option sslot :=
  match e with
  | SSep _ _ => None
  | SBoth S0 => Some (SSep (flipp r) (pole (flipp r) S0))
  end.

Lemma scupd_eq n (x : ch n) e (Δ : sctxP n) : scupd x e Δ x = e.
Proof. by rewrite /scupd eqxx. Qed.

Lemma scupd_neq n (x y : ch n) e (Δ : sctxP n) :
  y != x -> scupd x e Δ y = Δ y.
Proof. rewrite /scupd. by case: eqP. Qed.

(** Dual heads are compatible -- the duality moment. *)
Lemma dual_head_compat S :
  compat (head_act S) (head_act (dual S)).
Proof. by case: S. Qed.

(** ** Conformance, level one: the visible surface *)
Definition conformV {n : nat} (Δ : sctxP n) (P : procP n) : Prop :=
  forall a (c : pch n), offersP a c P ->
    exists S, sat Δ c = Some S /\ a = head_act S.

(** ** Conformance, level two: under the structure *)
Fixpoint conformD {n : nat} (Δ : sctxP n) (P : procP n) {struct P} : Prop :=
  conformV Δ P
  /\ match P with
     | PPar P1 P2 => conformD Δ P1 /\ conformD Δ P2
     | PRes B => exists S, conformD (scons (Some (SBoth S)) Δ) B
     | _ => True
     end.

Lemma conformD_V n (Δ : sctxP n) (P : procP n) :
  conformD Δ P -> conformV Δ P.
Proof.
  by case: P => [|c K|c K|B|A B|c r K|c d K|c b K|c K1 K2] [Hv _].
Qed.

Lemma conformD_res n (Δ : sctxP n) (B : procP n.+1) :
  conformD Δ ((ν) B) ->
  exists S, conformD (scons (Some (SBoth S)) Δ) B.
Proof. by case. Qed.

Lemma conformD_parL n (Δ : sctxP n) (P Q : procP n) :
  conformD Δ (P ∥ Q) -> conformD Δ P.
Proof. by case=> _ [H1 _]. Qed.

Lemma conformD_parR n (Δ : sctxP n) (P Q : procP n) :
  conformD Δ (P ∥ Q) -> conformD Δ Q.
Proof. by case=> _ [_ H2]. Qed.

(** ** Internal evolution: a both-name's protocol may advance *)
Definition sevolve {n : nat} (Δ Δ' : sctxP n) : Prop :=
  forall x,
    Δ' x = Δ x
    \/ (exists S S', Δ x = Some (SBoth S) /\ Δ' x = Some (SBoth S')).

Lemma sevolve_refl n (Δ : sctxP n) : sevolve Δ Δ.
Proof. move=> x. by left. Qed.

Lemma sevolve_trans n (Δ1 Δ2 Δ3 : sctxP n) :
  sevolve Δ1 Δ2 -> sevolve Δ2 Δ3 -> sevolve Δ1 Δ3.
Proof.
  move=> H12 H23 x.
  case: (H23 x) => [->|[S2 [S3 [E2 E3]]]]; first exact: H12.
  case: (H12 x) => [E1|[S1 [S2' [E1 E1']]]].
  - right. exists S2, S3. by rewrite -E1.
  - right. exists S1, S3. by rewrite E1.
Qed.

(** ** The value interpretation: one SEPARATE endpoint, one protocol.
    Both-slots have no value obligations. *)
Section ValueP.

Variable E : forall n : nat, sctxP n -> procP n -> Prop.

Definition VsemP {n : nat} (Δ : sctxP n) (c : pch n) (S : sty)
    (P : procP n) : Prop :=
  match S with
  | SClose =>
      forall P', ltscP c P P' -> E (scupd c.1 None Δ) P'
  | SWait =>
      forall P', ltswP c P P' -> E (scupd c.1 None Δ) P'
  | SSend T S2 =>
      (forall (y : ch n) (rd : pol) P',
         ltsfP c (y, rd) P P' ->
         exists e, [/\ Δ y = Some e, esat rd e = Some T
           & E (scupd y (econsume rd e)
                  (scupd c.1 (Some (SSep c.2 S2)) Δ)) P'])
      /\
      (forall (r : pol) (P' : procP n.+1),
         ltsbP c r P P' ->
         E (scons (Some (SSep (flipp r) (dual T)))
              (scupd c.1 (Some (SSep c.2 S2)) Δ)) P')
  | SRecv T S2 =>
      (forall (y : ch n) (rd : pol) P',
        ltsrP c (y, rd) P P' ->
        (Δ y = None ->
           E (scupd y (Some (SSep rd T))
                (scupd c.1 (Some (SSep c.2 S2)) Δ)) P')
        /\
        (Δ y = Some (SSep (flipp rd) (dual T)) ->
           E (scupd y (Some (SBoth (pole rd T)))
                (scupd c.1 (Some (SSep c.2 S2)) Δ)) P'))
      /\
      (forall (rd : pol) (P'' : procP n.+1),
        ltsrP (pshift c) (zero, rd) (psubst shift P) P'' ->
        E (scons (Some (SSep rd T))
             (scupd c.1 (Some (SSep c.2 S2)) Δ)) P'')
  | SSel S1 S2 =>
      forall (b : bool) P', ltsselP c b P P' ->
        E (scupd c.1 (Some (SSep c.2 (if b then S1 else S2))) Δ) P'
  | SBra S1 S2 =>
      (* branching commits internal state: like τ, the both-slots may
         re-choose their protocols per branch *)
      forall (b : bool) P', ltsbrP c b P P' ->
        exists Δ', sevolve Δ Δ' /\
          E (scupd c.1 (Some (SSep c.2 (if b then S1 else S2))) Δ') P'
  end.

End ValueP.

(** ** The term interpretation *)
Fixpoint EsemP (k : nat) {n : nat} (Δ : sctxP n) (P : procP n) {struct k}
  : Prop :=
  match k with
  | 0 => True
  | k.+1 =>
      [/\ conformD Δ P,
          forall (x : ch n) (r : pol) S,
            Δ x = Some (SSep r S) -> VsemP (@EsemP k) Δ (x, r) S P
        & forall P', ltstP P P' ->
            exists Δ', sevolve Δ Δ' /\ EsemP k Δ' P']
  end.

Definition SEMP {n : nat} (Δ : sctxP n) (P : procP n) : Prop :=
  forall k, EsemP k Δ P.

Notation "Δ '⊨p' P" := (SEMP Δ P) (at level 68).

(** ** Basic properties *)

Lemma VsemP_mono (E E' : forall n : nat, sctxP n -> procP n -> Prop)
  (HEE' : forall n (Δ : sctxP n) P, E n Δ P -> E' n Δ P)
  n (Δ : sctxP n) (c : pch n) S P :
  VsemP E Δ c S P -> VsemP E' Δ c S P.
Proof.
  case: S => [| |T S2|T S2|S1 S2|S1 S2] /= HV.
  - move=> P' HT. apply: HEE'. exact: HV HT.
  - move=> P' HT. apply: HEE'. exact: HV HT.
  - case: HV => HVf HVb. split.
    + move=> y rd P' HT. case: (HVf _ _ _ HT) => e [He Hs HE].
      exists e. split=> //. exact: HEE'.
    + move=> r P' HT. apply: HEE'. exact: HVb HT.
  - case: HV => HVc HVs. split.
    + move=> y rd P' HT. case: (HVc _ _ _ HT) => H1 H2. split.
      * move=> Hy. apply: HEE'. exact: H1.
      * move=> Hy. apply: HEE'. exact: H2.
    + move=> rd P'' HT. apply: HEE'. exact: HVs HT.
  - move=> b P' HT. apply: HEE'. exact: HV HT.
  - move=> b P' HT. case: (HV _ _ HT) => Δ' [Hev HE].
    exists Δ'. split=> //. exact: HEE'.
Qed.

Lemma EsemP_antitone k : forall n (Δ : sctxP n) (P : procP n),
  EsemP k.+1 Δ P -> EsemP k Δ P.
Proof.
  elim: k => [//|k IH] n Δ P [C V St]. split=> //.
  - move=> x r S HxS.
    exact: (VsemP_mono (E := @EsemP k.+1) (E' := @EsemP k) IH (V _ _ _ HxS)).
  - move=> P' Hst. case: (St _ Hst) => Δ' [Hev HE].
    exists Δ'. split=> //. exact: IH.
Qed.

Lemma EsemP_step k n (Δ : sctxP n) (P Q : procP n) :
  ltstP P Q -> EsemP k.+1 Δ P ->
  exists Δ', sevolve Δ Δ' /\ EsemP k Δ' Q.
Proof. move=> Hst [_ _ St]. exact: St. Qed.

(** ** Reachability

    Along a walk the context evolves, and the step clause chooses it
    per budget.  What survives is the per-budget family: every reduct
    is related at every budget, at SOME context.  Adequacy needs no
    more, since the error refutation is context-universal. *)
Lemma EsemP_reach n (P Q : procP n) :
  P —τ*→ Q ->
  (forall j, exists Δj : sctxP n, EsemP j Δj P) ->
  forall j, exists Δj : sctxP n, EsemP j Δj Q.
Proof.
  move=> Hred. elim: Hred => {n P Q}
    [n P|n P Q R Hst _ IH] HF j; first exact: HF.
  apply: IH => j'.
  case: (HF j'.+1) => Δ HE.
  case: (EsemP_step Hst HE) => Δ' [_ HE'].
  by exists Δ'.
Qed.

(** ** Adequacy

    The mismatch refutation is a slot analysis through [sat]: a
    missing slot covers nothing, a separate slot covers one polarity,
    and a both-slot covers the two ends at DUAL protocols, whose heads
    are compatible -- the duality moment ([dual_head_compat]). *)
Lemma errP_conformD n (P : procP n) :
  errP P -> forall Δ : sctxP n, ~ conformD Δ P.
Proof.
  move=> H; elim: H => {n P}.
  - (* mismatch at a name *)
    move=> n P x a b Ha Hb Hc Δ HD.
    have C1 := conformD_V HD.
    case: (C1 _ _ Ha) => Sa [HSa Ea].
    case: (C1 _ _ Hb) => Sb [HSb Eb].
    move: HSa HSb. rewrite /sat /=.
    case E : (Δ x) => [[r S|S]|] //.
    + (* separate slot: cannot cover both polarities *)
      case: r E => E /=; first by [].
      by [].
    + (* both slot: dual heads are compatible *)
      move=> -[ESa] -[ESb].
      move: Hc. rewrite Ea Eb -ESa -ESb /=.
      by rewrite dual_head_compat.
  - (* under a restriction *)
    move=> n P _ IH Δ HD.
    case: (conformD_res HD) => S HD'. exact: (IH _ HD').
  - (* left of a parallel *)
    move=> n P Q _ IH Δ HD. exact: (IH _ (conformD_parL HD)).
  - (* right of a parallel *)
    move=> n P Q _ IH Δ HD. exact: (IH _ (conformD_parR HD)).
Qed.

Lemma errP_esemP n (P : procP n) :
  errP P -> forall Δ : sctxP n, ~ EsemP 1 Δ P.
Proof. move=> H Δ [CD _ _]. exact (errP_conformD H CD). Qed.

Theorem adequacyP n (Δ : sctxP n) (P : procP n) : Δ ⊨p P -> error_freeP P.
Proof.
  move=> HS Q HPQ Herr.
  have HF : forall j, exists Δj : sctxP n, EsemP j Δj P.
    move=> j. exists Δ. exact: HS.
  case: (EsemP_reach HPQ HF 1) => Δ' HE.
  exact: (errP_esemP Herr HE).
Qed.

Corollary adequacyP_closed (P : procP 0) : scempty ⊨p P -> error_freeP P.
Proof. exact: adequacyP. Qed.

(** ** Axiom audit *)
Print Assumptions adequacyP.
