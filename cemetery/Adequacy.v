(** * Adequacy: the logical relation entails safety

        Δ ⊨ P  ->  safe P

    The proof needs no inversion of [≅] or [⇛]: it uses the clauses of
    [Esem] only in the forward direction.  The engine is [err_esem]: an
    erroneous process refutes the relation, *in any context and under any
    parallel frame*.  The frame generalisation lets the congruence cases
    of [err] fold their surroundings into the frame ([E_Par] by
    associativity, [E_Res] by scope extrusion), and the mismatch case is
    killed by duality:

    - the semantic-cut clause gives the two endpoints of the offending
      restriction the protocols [S] and [dual S];
    - the conformance clause forces the two exposed prefixes to perform
      [head_act S] and [head_act (dual S)];
    - dual heads are compatible ([compat_dual]) -- contradicting the
      incompatibility witness carried by [E_Mismatch].

    The observation depth needed is finite and structural: two levels for
    a top mismatch, one more per restriction the error sits under. *)

From mathcomp Require Import all_ssreflect.
From Tait Require Import synsem Errors LogRel.

Set Implicit Arguments.
Unset Strict Implicit.

(** An erroneous process is not in the relation -- at some finite depth
    [m], in any context [Δ], under any frame [R]. *)
Lemma err_esem n (P : proc n) :
  err P ->
  exists m, forall (Δ : sctx n) (R : proc n), ~ Esem m Δ (P ∥ R).
Proof.
  move=> H; elim: H => {n P}.
  - (* E_Mismatch: the two exposed prefixes contradict duality *)
    move=> n a b F1 F2 Ha Hb Hc.
    exists 2 => Δ R HE.
    case: (HE _ (MR_refl _)) => _ _ X.
    case: (X _ (SC_Res_Scope (F1 ∥ F2) R)) => S HE1.
    case: (HE1 _ (MR_refl _)) => C _ _.
    case: (C _ _ _ _ (SC_Par_Assoc F1 F2 _) Ha) => S1 [HS1 Ha'].
    have chain2 : (F1 ∥ F2) ∥ (< (shift \o shift) >) R
                    ≅ F2 ∥ (F1 ∥ (< (shift \o shift) >) R).
      apply: SC_Trans (SC_Par_Assoc F2 F1 _).
      exact: SC_Cong_Par (SC_Par_Com F1 F2) (SC_Refl _).
    case: (C _ _ _ _ chain2 Hb) => S2 [HS2 Hb'].
    move: HS1 HS2; rewrite cext_one cext_zero => -[HS1] [HS2].
    by move: Hc; rewrite Ha' Hb' -HS1 -HS2 compat_sym (compat_dual S).
  - (* E_Res: descend through the semantic cut, extruding the frame *)
    move=> n P _ [m IH].
    exists m.+1 => Δ R HE.
    case: (HE _ (MR_refl _)) => _ _ X.
    case: (X _ (SC_Res_Scope P R)) => S HE'.
    exact: (IH _ _ HE').
  - (* E_Par: fold the sibling into the frame *)
    move=> n P Q _ [m IH].
    exists m => Δ R HE.
    exact: (IH _ _ (Esem_struct (SC_Par_Assoc P Q R) HE)).
  - (* E_Struct: transport along the congruence *)
    move=> n P Q Heq _ [m IH].
    exists m => Δ R HE.
    exact: (IH _ _ (Esem_struct (SC_Cong_Par Heq (SC_Refl R)) HE)).
Qed.

(** ** Adequacy *)
Theorem adequacy n (Δ : sctx n) (P : proc n) : Δ ⊨ P -> safe P.
Proof.
  move=> HS Q HPQ Herr.
  case: (err_esem Herr) => m Hkill.
  apply: (Hkill Δ (EndP n)).
  apply: Esem_struct (SC_Sym (SC_Par_Inact Q)) _.
  exact: Esem_mreduce HPQ (HS m).
Qed.

(** In particular, a closed process in the relation at the empty context
    is safe.  (Once the fundamental theorem [Δ ⊢ P -> Δ ⊨ P] exists,
    this yields: well-typed closed processes never reach a communication
    error.) *)
Corollary adequacy_closed (P : proc 0) : cempty ⊨ P -> safe P.
Proof. exact: adequacy. Qed.

(** ** Axiom audit *)
Print Assumptions adequacy.
