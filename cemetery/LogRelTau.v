(** * The logical relation, retargeted to the label-based calculus

    Same architecture as [LogRel.v] (value/term split, context-indexed,
    observation depth), with every ≅-shaped ingredient replaced by its
    syntax-directed counterpart:

    - exposures  [P' ≅ prefix ∥ frame]   ->  transitions of [P']
    - reducts    [P ⇛* P']               ->  [P —τ*→ P']
    - conformance over ≅-decompositions  ->  conformance over [offers]
    - semantic cut [P' ≅ (ν) Q]          ->  syntactic match [P' = (ν) Q]
    - (new) par-descent clause: rigid syntax does not hoist inner
      binders into view, so the relation descends through parallel
      compositions itself, splitting the context.
    - (new) bound-send value clause: delegating one's own bound
      endpoint gives the receiver the [zero] end at the payload type
      [T]; the sender's residue keeps the co-end [one], which must
      behave at [dual T] -- the ⊗-style splitting of ILL logical
      relations, arising here from the label discipline.

    Typing ([Typing.v]) is unchanged; the compatibility pairing
    [T_Close ↦ SClose]-clause etc. carries over verbatim, with
    [T_Del ↦ ltsf]-clause and the [ltsb]-clause covered by [T_Res]'s
    descent (a bound send is a free send at the inner scope). *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Eqdep_dec PeanoNat.
From Tait Require Import synsem Errors LogRel Toolkit LTS Transfer Typing Fundamental Tau.

Set Implicit Arguments.
Unset Strict Implicit.

(** Contexts, updates, [cext], [split], and the session types are
    reused from [LogRel.v]/[Fundamental.v]-era files: [sctx], [cupd],
    [cext], [sty], [dual], [head_act], [compat_dual]. *)

(** ** Conformance: every offer is owned and protocol-headed *)
Definition conformT {n : nat} (Δ : sctx n) (P : proc n) : Prop :=
  forall a (x : ch n),
    offers a x P -> exists S, Δ x = Some S /\ a = head_act S.

(** ** The value interpretation *)
Section ValueT.

Variable E : forall n : nat, sctx n -> proc n -> Prop.

Definition VsemT {n : nat} (Δ : sctx n) (x : ch n) (S : sty) (P' : proc n)
  : Prop :=
  match S with
  | SClose =>
      forall P'', ltsc x P' P'' -> E (cupd x None Δ) P''
  | SWait =>
      forall P'', ltsw x P' P'' -> E (cupd x None Δ) P''
  | SSend T S2 =>
      (forall y P'', ltsf x y P' P'' ->
         Δ y = Some T /\ E (cupd y None (cupd x (Some S2) Δ)) P'')
      /\
      (forall P'', ltsb x P' P'' ->
         E (scons None (scons (Some (dual T)) (cupd x (Some S2) Δ))) P'')
  | SRecv T S2 =>
      forall P'', ltsr x P' P'' ->
        E (scons (Some T) (cupd x (Some S2) Δ)) P''
  end.

End ValueT.

(** ** The term interpretation

    Step-indexed: [k] bounds the number of internal steps still
    budgeted.  At every budget the process must be conformant and its
    visible transitions must follow the protocols; each internal step
    spends one unit.  (A first version indexed by observation depth
    and closed each level under [—τ*→]; that makes the [exists S] of
    the cut clause depend on the depth, and no single [S] serves all
    depths when a synchronization is consumed inside a nested
    restriction.  Spending the index on steps removes the
    quantification: one level, one [S].) *)
Fixpoint EsemT (k : nat) {n : nat} (Δ : sctx n) (P : proc n) {struct k}
  : Prop :=
  match k with
  | 0 => True
  | k.+1 =>
      [/\ conformT Δ P,
          forall (x : ch n) S, Δ x = Some S -> VsemT (@EsemT k) Δ x S P,
          forall P1 P2, P = P1 ∥ P2 ->
            exists Δ1 Δ2,
              [/\ split Δ Δ1 Δ2, EsemT k Δ1 P1 & EsemT k Δ2 P2],
          forall Q : proc n.+2, P = (ν) Q ->
            exists S, EsemT k (cext S Δ) Q
        & forall P', ltst P P' -> EsemT k Δ P']
  end.

Definition SEMT {n : nat} (Δ : sctx n) (P : proc n) : Prop :=
  forall k, EsemT k Δ P.

Notation "Δ '⊨τ' P" := (SEMT Δ P) (at level 68).

(** ** Basic properties *)

Lemma VsemT_mono (E E' : forall n : nat, sctx n -> proc n -> Prop)
  (HEE' : forall n (Δ : sctx n) P, E n Δ P -> E' n Δ P)
  n (Δ : sctx n) (x : ch n) S P' :
  VsemT E Δ x S P' -> VsemT E' Δ x S P'.
Proof.
  case: S => [| |T S2|T S2] /= HV.
  - move=> P'' HT. apply: HEE'. exact: HV HT.
  - move=> P'' HT. apply: HEE'. exact: HV HT.
  - case: HV => HVf HVb. split.
    + move=> y P'' HT. case: (HVf _ _ HT) => Hy HE. split=> //. exact: HEE'.
    + move=> P'' HT. apply: HEE'. exact: HVb HT.
  - move=> P'' HT. apply: HEE'. exact: HV HT.
Qed.

Lemma EsemT_antitone k : forall n (Δ : sctx n) (P : proc n),
  EsemT k.+1 Δ P -> EsemT k Δ P.
Proof.
  elim: k => [//|k IH] n Δ P HE.
  case: HE => C V D X St; split=> //.
  - move=> x S HxS.
    exact: (VsemT_mono (E := @EsemT k.+1) (E' := @EsemT k) IH (V _ _ HxS)).
  - move=> P1 P2 E12. case: (D _ _ E12) => Δ1 [Δ2 [Hs H1 H2]].
    exists Δ1, Δ2. split=> //; exact: IH.
  - move=> Q HQ. case: (X _ HQ) => S HS. exists S. exact: IH.
  - move=> P' Hst. apply: IH. exact: St.
Qed.

(** One internal step spends one unit of the budget. *)
Lemma EsemT_step k n (Δ : sctx n) (P Q : proc n) :
  ltst P Q -> EsemT k.+1 Δ P -> EsemT k Δ Q.
Proof. move=> Hst [_ _ _ _ St]. exact: St. Qed.

Lemma SEMT_ltst n (Δ : sctx n) (P Q : proc n) :
  ltst P Q -> Δ ⊨τ P -> Δ ⊨τ Q.
Proof. move=> Hst HS k. exact: EsemT_step Hst (HS k.+1). Qed.

Lemma SEMT_ltsts n (Δ : sctx n) (P Q : proc n) :
  P —τ*→ Q -> Δ ⊨τ P -> Δ ⊨τ Q.
Proof.
  move=> Hred. elim: Hred Δ => {n P Q} [n P|n P Q R Hst _ IH] Δ HS.
  - exact: HS.
  - apply: IH. exact: SEMT_ltst Hst HS.
Qed.

(** ** Adequacy

    An erroneous process refutes the relation at a budget matching the
    depth of the error, in any context; the relation is preserved
    along internal steps, so a semantically well-typed process can
    never reach one.  No frames, no ≅: the error and the relation
    descend through the same rigid syntax. *)
Lemma errL_esemT n (P : proc n) :
  errL P -> exists m, forall Δ : sctx n, ~ EsemT m Δ P.
Proof.
  move=> H; elim: H => {n P}.
  - (* mismatch at a binder: duality kills it *)
    move=> n B a b Ha Hb Hc.
    exists 2 => Δ HE.
    case: HE => _ _ _ X _.
    case: (X _ erefl) => S HE1.
    case: HE1 => C _ _ _ _.
    case: (C _ _ Ha) => S1 [HS1 Ea].
    case: (C _ _ Hb) => S2 [HS2 Eb].
    move: HS1 HS2. rewrite cext_one cext_zero => -[E1] [E2].
    by move: Hc; rewrite Ea Eb -E1 -E2 compat_sym (compat_dual S).
  - (* under a restriction *)
    move=> n P _ [m IH].
    exists m.+1 => Δ HE.
    case: HE => _ _ _ X _.
    case: (X _ erefl) => S HE'.
    exact: (IH _ HE').
  - (* left of a parallel *)
    move=> n P Q _ [m IH].
    exists m.+1 => Δ HE.
    case: HE => _ _ D _ _.
    case: (D _ _ erefl) => Δ1 [Δ2 [_ H1 _]].
    exact: (IH _ H1).
  - (* right of a parallel *)
    move=> n P Q _ [m IH].
    exists m.+1 => Δ HE.
    case: HE => _ _ D _ _.
    case: (D _ _ erefl) => Δ1 [Δ2 [_ _ H2]].
    exact: (IH _ H2).
Qed.

Theorem adequacyT n (Δ : sctx n) (P : proc n) : Δ ⊨τ P -> safeL P.
Proof.
  move=> HS Q HPQ Herr.
  case: (errL_esemT Herr) => m Hkill.
  apply: (Hkill Δ).
  exact: (SEMT_ltsts HPQ HS m).
Qed.

Corollary adequacyT_closed (P : proc 0) : cempty ⊨τ P -> safeL P.
Proof. exact: adequacyT. Qed.

(** ** Axiom audit *)
Print Assumptions adequacyT.
