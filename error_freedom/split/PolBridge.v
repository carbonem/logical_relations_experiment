(** * Semantic typing, and the bridge from the split-context system

    Two things live here.

    [stypedP] is the semantic typing judgment: the same shape as
    [typedP], but over the SEMANTIC contexts of [PolLogRel.v], which
    record for each NAME whether the process holds one endpoint
    ([SSep ρ S]) or both ([SBoth S], the [pos] end at [S]).  Its
    parallel rule is exactly [dmerge] -- the merge relation the cut
    lemma [combineP] already consumes -- and its restriction rule is
    unchanged from the cut-based development, because "the body holds
    both ends of the fresh session" is what a restriction always
    meant.

    [typed_styped] is the bridge: a well-typed process in a BALANCED
    context is semantically typed at the induced semantic context.

    WHY BALANCE IS A PREMISE, AND WHY THE INDUCTION STILL WORKS.
    Balance ("both ends of a name are dual") is not preserved by the
    prefix rules: from [x⁺ : !T.S] and [x⁻ : ?T.dual S] the output
    rule leaves [x⁺ : S] against an unchanged [x⁻].  So an induction
    that descended everywhere would meet unbalanced contexts, and an
    unbalanced pair has NO semantic slot -- [SSep] is one end and
    [SBoth] is a DUAL pair.

    The way out is that those nodes are unreachable.  A prefix whose
    subject is a both-held name can never fire: its co-endpoint is
    internal, and transitions synchronize only at a parallel
    composition, so no partner exists.  Its continuation is therefore
    dead code, and the relation asks nothing of it -- [SBoth] slots
    carry no value obligation.  The bridge accordingly stops at such a
    node, emitting one of the premise-free [ST_*B] rules below and NOT
    recursing.  Every node it does visit is balanced. *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Eqdep_dec PeanoNat.
From Tait Require Import PolBase PolTypes PolProc PolLTS PolErr PolTyping
  PolLogRel PolEquiv PolCompat PolSem PolComb.

Set Implicit Arguments.
Unset Strict Implicit.
Open Scope pol_scope.

(** ** The semantic context induced by a typing context *)

Definition sctx_of {n : nat} (Δ : pctx n) : sctxP n :=
  fun x =>
    match Δ (x, pos), Δ (x, neg) with
    | Some T, Some _ => Some (SBoth T)
    | Some T, None   => Some (SSep pos T)
    | None,   Some U => Some (SSep neg U)
    | None,   None   => None
    end.

(** Under balance, the [pos] protocol determines both ends. *)
Lemma pole_balanced n (Δ : pctx n) (x : ch n) T r S0 :
  balanced Δ -> Δ (x, pos) = Some T -> Δ (x, r) = Some S0 -> pole r T = S0.
Proof.
  case: r => Hb Hp Hr /=.
  - by rewrite Hp in Hr; case: Hr.
  - by rewrite (Hb _ _ _ Hp Hr).
Qed.

(** A name whose co-endpoint is absent has a separate slot. *)
Lemma sctx_of_sep n (Δ : pctx n) (x : ch n) (r : pol) S0 :
  Δ (x, r) = Some S0 -> Δ (x, flipp r) = None ->
  sctx_of Δ x = Some (SSep r S0).
Proof. case: r => /= Hc Hco; by rewrite /sctx_of Hc Hco. Qed.

(** A name whose co-endpoint is present has a both-slot, and under
    balance its head at either polarity is read off by [pole]. *)
Lemma sctx_of_both n (Δ : pctx n) (x : ch n) (r : pol) S0 U :
  balanced Δ -> Δ (x, r) = Some S0 -> Δ (x, flipp r) = Some U ->
  exists T, sctx_of Δ x = Some (SBoth T) /\ pole r T = S0.
Proof.
  case: r => /= Hb Hc Hco.
  - exists S0. rewrite /sctx_of Hc Hco. by split.
  - exists U. rewrite /sctx_of Hc Hco. split=> //.
    exact: pole_balanced Hb Hco Hc.
Qed.

(** ** How [sctx_of] commutes with the context operations *)

(** Endpoint lookup after an update, as a boolean test on the two
    components. *)
Lemma pcupd_lookup n (Δ : pctx n) (c : pch n) o (x : ch n) (r : pol) :
  pcupd c o Δ (x, r) = if (x == c.1) && (r == c.2) then o else Δ (x, r).
Proof. rewrite /pcupd. by case: c => y r0 /=; rewrite xpair_eqE. Qed.

Lemma sctx_of_upd n (Δ : pctx n) (c : pch n) (o : option sty) x :
  Δ (pflip c) = None ->
  sctx_of (pcupd c o Δ) x
  = scupd c.1 (if o is Some S1 then Some (SSep c.2 S1) else None)
      (sctx_of Δ) x.
Proof.
  move=> Hco. rewrite /sctx_of /scupd !pcupd_lookup.
  case Ex : (x == c.1) => /=; last by [].
  move/eqP: Ex => Ex. rewrite {}Ex in Hco *.
  move: Hco. rewrite /pflip.
  case: c => y [] //= Hco; rewrite Hco; by case: o.
Qed.

(** Clearing one end of a name whose OTHER end is held: the both-slot
    demotes to the surviving separate end.  This is the shape the
    delegation of an internal session leaves behind. *)
Lemma sctx_of_upd_both n (Δ : pctx n) (x : ch n) (r : pol) U z :
  Δ (x, flipp r) = Some U ->
  sctx_of (pcupd (x, r) None Δ) z
  = scupd x (Some (SSep (flipp r) U)) (sctx_of Δ) z.
Proof.
  move=> Hco. rewrite /sctx_of /scupd !pcupd_lookup.
  case Ez : (z == x) => /=; last by [].
  move/eqP: Ez => Ez. rewrite {}Ez in Hco *.
  by case: r Hco => /= Hco; rewrite Hco.
Qed.

Lemma sctx_of_pcnu n (Δ : pctx n) T x :
  sctx_of (pcnu T Δ) x = scons (Some (SBoth T)) (sctx_of Δ) x.
Proof. by case: x. Qed.

Lemma sctx_of_pcrecv n (Δ : pctx n) rd T x :
  sctx_of (pcrecv rd T Δ) x = scons (Some (SSep rd T)) (sctx_of Δ) x.
Proof. by case: x => [y|] //=; case: rd. Qed.

(** A split of a balanced context induces a merge of the semantic
    contexts -- including the case that the cut discipline forbade,
    where the two ends of a session go to opposite sides.  Several
    names may do so at once; [dmerge] has no cardinality bound. *)
Lemma dmerge_of_psplit n (Δ1 Δ2 Δ : pctx n) :
  psplit Δ1 Δ2 Δ -> balanced Δ ->
  dmerge (sctx_of Δ1) (sctx_of Δ2) (sctx_of Δ).
Proof.
  move=> Hs Hb x. rewrite /sctx_of.
  case: (Hs (x, pos)) => -[Hp1 Hp2]; case: (Hs (x, neg)) => -[Hn1 Hn2].
  - (* neither end on the left *)
    apply: Or42. rewrite Hp1 Hn1 Hp2 Hn2. by split.
  - (* pos may be on the right, neg may be on the left *)
    case Ep : (Δ2 (x, pos)) => [Up|]; case En : (Δ1 (x, neg)) => [Tn|].
    + (* a live link, oriented neg-left *)
      have HUp : Up = dual Tn.
        have Ea : Δ (x, pos) = Some Up by rewrite Hp2.
        have Eb : Δ (x, neg) = Some Tn by rewrite Hn2.
        by rewrite (Hb _ _ _ Ea Eb) dual_involutive.
      apply: Or43. exists neg, Tn.
      rewrite ?Hp1 ?Hn1 ?Hp2 ?Hn2 ?Ep ?En /= HUp.
      by split.
    + apply: Or42.
      by rewrite ?Hp1 ?Hn1 ?Hp2 ?Hn2 ?Ep ?En.
    + apply: Or41.
      by rewrite ?Hp1 ?Hn1 ?Hp2 ?Hn2 ?Ep ?En.
    + apply: Or41.
      by rewrite ?Hp1 ?Hn1 ?Hp2 ?Hn2 ?Ep ?En.
  - (* pos may be on the left, neg may be on the right *)
    case Ep : (Δ1 (x, pos)) => [Tp|]; case En : (Δ2 (x, neg)) => [Un|].
    + (* a live link, oriented pos-left *)
      have HUn : Un = dual Tp.
        have Ea : Δ (x, pos) = Some Tp by rewrite Hp2.
        have Eb : Δ (x, neg) = Some Un by rewrite Hn2.
        by rewrite (Hb _ _ _ Ea Eb).
      apply: Or43. exists pos, Tp.
      rewrite ?Hp1 ?Hn1 ?Hp2 ?Hn2 ?Ep ?En /= HUn.
      by split.
    + apply: Or41.
      by rewrite ?Hp1 ?Hn1 ?Hp2 ?Hn2 ?Ep ?En.
    + apply: Or42.
      by rewrite ?Hp1 ?Hn1 ?Hp2 ?Hn2 ?Ep ?En.
    + apply: Or41.
      by rewrite ?Hp1 ?Hn1 ?Hp2 ?Hn2 ?Ep ?En.
  - (* neither end on the right *)
    apply: Or41. rewrite Hp1 Hn1 Hp2 Hn2. by split.
Qed.

(** Reading a both-slot back into the two endpoint entries. *)
Lemma sctx_of_bothE n (Δ : pctx n) (y : ch n) T0 :
  sctx_of Δ y = Some (SBoth T0) ->
  Δ (y, pos) = Some T0 /\ exists U, Δ (y, neg) = Some U.
Proof.
  rewrite /sctx_of.
  case Ep : (Δ (y, pos)) => [Tp|]; case En : (Δ (y, neg)) => [Tn|] //=.
  move=> [E]. split; first by rewrite E.
  by exists Tn.
Qed.

(** A process cannot delegate its own co-endpoint over the very
    session that endpoint belongs to: balance would force
    [T = SRecv T _]. *)
Lemma srecv_neqT T S2 : T = SRecv T S2 -> False.
Proof.
  move=> E. have := f_equal stysz E. rewrite /= => /eqP.
  by rewrite -[X in X == _]addn0 -addnS eqn_add2l.
Qed.

Lemma no_self_payload n (Δ : pctx n) (x : ch n) (r : pol) T S2 :
  balanced Δ -> Δ (x, r) = Some (SSend T S2) ->
  Δ (x, flipp r) = Some T -> False.
Proof.
  case: r => /= Hb Hc Hd.
  - have E := Hb _ _ _ Hc Hd. rewrite /= in E. exact: srecv_neqT E.
  - have E := Hb _ _ _ Hd Hc.
    have E' := f_equal dual E. rewrite dual_involutive /= in E'.
    exact: srecv_neqT (esym E').
Qed.

(** ** Semantic typing

    The separate-subject rules mirror [typedP] one for one.  The
    [ST_*B] rules are the both-subject ones: their subject's
    co-endpoint is held internally, the prefix can never fire, and so
    they constrain only the head of the protocol -- no continuation
    premise. *)

Inductive stypedP : forall m, sctxP m -> procP m -> Prop :=
| ST_End : forall m (Δ : sctxP m),
    (forall x, Δ x = None) -> stypedP Δ ∅
| ST_Close : forall m (Δ : sctxP m) (x : ch m) (r : pol) K,
    Δ x = Some (SSep r SClose) ->
    stypedP (scupd x None Δ) K ->
    stypedP Δ ((x, r) !․ K)
| ST_Wait : forall m (Δ : sctxP m) (x : ch m) (r : pol) K,
    Δ x = Some (SSep r SWait) ->
    stypedP (scupd x None Δ) K ->
    stypedP Δ ((x, r) ?․ K)
| ST_Del : forall m (Δ : sctxP m) (x y : ch m) (r rd : pol) T S2 K,
    Δ x = Some (SSep r (SSend T S2)) ->
    Δ y = Some (SSep rd T) ->
    stypedP (scupd y None (scupd x (Some (SSep r S2)) Δ)) K ->
    stypedP Δ ((x, r) ! (y, rd) ․ K)
(* the payload may itself be an internal session: one end is sent
   away, the co-end stays behind as a separate slot *)
| ST_DelB : forall m (Δ : sctxP m) (x y : ch m) (r rd : pol) T T0 S2 K,
    Δ x = Some (SSep r (SSend T S2)) ->
    Δ y = Some (SBoth T0) ->
    pole rd T0 = T ->
    stypedP (scupd y (Some (SSep (flipp rd) (pole (flipp rd) T0)))
               (scupd x (Some (SSep r S2)) Δ)) K ->
    stypedP Δ ((x, r) ! (y, rd) ․ K)
| ST_Ins : forall m (Δ : sctxP m) (x : ch m) (r rd : pol) T S2
    (K : procP m.+1),
    Δ x = Some (SSep r (SRecv T S2)) ->
    stypedP (scons (Some (SSep rd T)) (scupd x (Some (SSep r S2)) Δ)) K ->
    stypedP Δ ((x, r) ?( rd )․ K)
| ST_Sel : forall m (Δ : sctxP m) (x : ch m) (r : pol) (b : bool) S1 S2 K,
    Δ x = Some (SSep r (SSel S1 S2)) ->
    stypedP (scupd x (Some (SSep r (if b then S1 else S2))) Δ) K ->
    stypedP Δ ((x, r) ◁ b ․ K)
| ST_Bra : forall m (Δ : sctxP m) (x : ch m) (r : pol) S1 S2 K1 K2,
    Δ x = Some (SSep r (SBra S1 S2)) ->
    stypedP (scupd x (Some (SSep r S1)) Δ) K1 ->
    stypedP (scupd x (Some (SSep r S2)) Δ) K2 ->
    stypedP Δ ((x, r) ▷ ( K1 | K2 ))
| ST_Par : forall m (Δ Δ1 Δ2 : sctxP m) P Q,
    dmerge Δ1 Δ2 Δ ->
    stypedP Δ1 P -> stypedP Δ2 Q ->
    stypedP Δ (P ∥ Q)
| ST_Res : forall m (Δ : sctxP m) (S : sty) (B : procP m.+1),
    stypedP (scons (Some (SBoth S)) Δ) B ->
    stypedP Δ ((ν) B)
(* both-subject prefixes: unreachable, so no continuation premise *)
| ST_CloseB : forall m (Δ : sctxP m) (x : ch m) (r : pol) S0 K,
    Δ x = Some (SBoth S0) -> pole r S0 = SClose ->
    stypedP Δ ((x, r) !․ K)
| ST_WaitB : forall m (Δ : sctxP m) (x : ch m) (r : pol) S0 K,
    Δ x = Some (SBoth S0) -> pole r S0 = SWait ->
    stypedP Δ ((x, r) ?․ K)
| ST_DelSubjB : forall m (Δ : sctxP m) (x : ch m) (r : pol) S0 T S2
    (d : pch m) K,
    Δ x = Some (SBoth S0) -> pole r S0 = SSend T S2 ->
    stypedP Δ ((x, r) ! d ․ K)
| ST_InsB : forall m (Δ : sctxP m) (x : ch m) (r rd : pol) S0 T S2
    (K : procP m.+1),
    Δ x = Some (SBoth S0) -> pole r S0 = SRecv T S2 ->
    stypedP Δ ((x, r) ?( rd )․ K)
| ST_SelB : forall m (Δ : sctxP m) (x : ch m) (r : pol) (b : bool)
    S0 S1 S2 K,
    Δ x = Some (SBoth S0) -> pole r S0 = SSel S1 S2 ->
    stypedP Δ ((x, r) ◁ b ․ K)
| ST_BraB : forall m (Δ : sctxP m) (x : ch m) (r : pol) S0 S1 S2 K1 K2,
    Δ x = Some (SBoth S0) -> pole r S0 = SBra S1 S2 ->
    stypedP Δ ((x, r) ▷ ( K1 | K2 )).

(** Semantic contexts are functions, so pointwise equality has to be
    transported by hand -- the development is axiom-free and does not
    assume functional extensionality. *)
Lemma stypedP_ext m (Δ Δ' : sctxP m) (P : procP m) :
  (forall x, Δ x = Δ' x) -> stypedP Δ P -> stypedP Δ' P.
Proof.
  move=> Hd Ht. elim: Ht Δ' Hd => {m Δ P}.
  - move=> m Δ HD Δ' Hd. apply: ST_End => x. by rewrite -Hd.
  - move=> m Δ x r K HxS _ IH Δ' Hd.
    apply: ST_Close; first by rewrite -Hd.
    apply: IH => y. rewrite /scupd. by case: (y == x).
  - move=> m Δ x r K HxS _ IH Δ' Hd.
    apply: ST_Wait; first by rewrite -Hd.
    apply: IH => y. rewrite /scupd. by case: (y == x).
  - move=> m Δ x y r rd T S2 K HxS HyS _ IH Δ' Hd.
    apply: (ST_Del (T := T) (S2 := S2));
      [by rewrite -Hd | by rewrite -Hd |].
    apply: IH => z. rewrite /scupd. case: (z == y) => //. by case: (z == x).
  - move=> m Δ x y r rd T T0 S2 K HxS HyS HT _ IH Δ' Hd.
    apply: (ST_DelB (T := T) (T0 := T0) (S2 := S2));
      [by rewrite -Hd | by rewrite -Hd | by [] |].
    apply: IH => z. rewrite /scupd. case: (z == y) => //. by case: (z == x).
  - move=> m Δ x r rd T S2 K HxS _ IH Δ' Hd.
    apply: (ST_Ins (T := T) (S2 := S2) (rd := rd)); first by rewrite -Hd.
    apply: IH => -[z|] //=. rewrite /scupd. by case: ((z : ch m) == x).
  - move=> m Δ x r b S1 S2 K HxS _ IH Δ' Hd.
    apply: (ST_Sel (S1 := S1) (S2 := S2)); first by rewrite -Hd.
    apply: IH => z. rewrite /scupd. by case: (z == x).
  - move=> m Δ x r S1 S2 K1 K2 HxS _ IH1 _ IH2 Δ' Hd.
    apply: (ST_Bra (S1 := S1) (S2 := S2)); first by rewrite -Hd.
    + apply: IH1 => z. rewrite /scupd. by case: (z == x).
    + apply: IH2 => z. rewrite /scupd. by case: (z == x).
  - move=> m Δ Δ1 Δ2 P Q Hm _ IH1 _ IH2 Δ' Hd.
    apply: (ST_Par (Δ1 := Δ1) (Δ2 := Δ2)).
    + move=> z. rewrite -Hd. exact: Hm.
    + by apply: IH1.
    + by apply: IH2.
  - move=> m Δ S B _ IH Δ' Hd.
    apply: (ST_Res (S := S)). apply: IH => -[z|] //=.
  - move=> m Δ x r S K HxS Hh Δ' Hd.
    apply: ST_CloseB.
    + rewrite -Hd. exact: HxS.
    + exact: Hh.
  - move=> m Δ x r S K HxS Hh Δ' Hd.
    apply: ST_WaitB.
    + rewrite -Hd. exact: HxS.
    + exact: Hh.
  - move=> m Δ x r S T S2 d K HxS Hh Δ' Hd.
    apply: ST_DelSubjB.
    + rewrite -Hd. exact: HxS.
    + exact: Hh.
  - move=> m Δ x r rd S T S2 K HxS Hh Δ' Hd.
    apply: ST_InsB.
    + rewrite -Hd. exact: HxS.
    + exact: Hh.
  - move=> m Δ x r b S S1 S2 K HxS Hh Δ' Hd.
    apply: ST_SelB.
    + rewrite -Hd. exact: HxS.
    + exact: Hh.
  - move=> m Δ x r S S1 S2 K1 K2 HxS Hh Δ' Hd.
    apply: ST_BraB.
    + rewrite -Hd. exact: HxS.
    + exact: Hh.
Qed.

(** ** The bridge *)

Theorem typed_styped m (Δ : pctx m) (P : procP m) :
  typedP Δ P -> balanced Δ -> stypedP (sctx_of Δ) P.
Proof.
  elim=> {m Δ P}.
  - (* ∅ *)
    move=> m Δ HD _. apply: ST_End => x. by rewrite /sctx_of !HD.
  - (* close *)
    move=> m Δ [x r] K Hc _ IH Hb.
    case Hco : (Δ (pflip (x, r))) => [U|].
    + (* both ends held: the prefix can never fire, so stop here *)
      case: (sctx_of_both Hb Hc Hco) => T [ET Eh].
      apply: (ST_CloseB (S0 := T)); [exact: ET | exact: Eh].
    + apply: ST_Close; first exact: (sctx_of_sep Hc Hco).
      apply: stypedP_ext (IH (balanced_upd_none Hb)) => z.
      by rewrite (sctx_of_upd None z Hco).
  - (* wait *)
    move=> m Δ [x r] K Hc _ IH Hb.
    case Hco : (Δ (pflip (x, r))) => [U|].
    + case: (sctx_of_both Hb Hc Hco) => T [ET Eh].
      apply: (ST_WaitB (S0 := T)); [exact: ET | exact: Eh].
    + apply: ST_Wait; first exact: (sctx_of_sep Hc Hco).
      apply: stypedP_ext (IH (balanced_upd_none Hb)) => z.
      by rewrite (sctx_of_upd None z Hco).
  - (* free delegation *)
    move=> m Δ [x r] [y rd] T S2 K Hc Hd _ IH Hb.
    case Hco : (Δ (pflip (x, r))) => [U|].
    + case: (sctx_of_both Hb Hc Hco) => T' [ET Eh].
      apply: ST_DelSubjB; [exact: ET | exact: Eh].
    + (* the subject is separate; the PAYLOAD may still be internal *)
      have Hbal' : balanced (pcupd (y, rd) None
                     (pcupd (x, r) (Some S2) Δ)).
        apply: balanced_upd_none.
        apply: balanced_upd_sep; [exact: Hb | exact: Hco].
      have Hcd : ((y, rd) : pch m) != (x, r).
        apply/eqP => E. rewrite E Hc in Hd. case: Hd => ET.
        by case: (ssend_neqT (esym ET)).
      have Hne : ((y, flipp rd) : pch m) != (x, r).
        apply/eqP => E. case: E => Ey Er.
        move: Hd. rewrite Ey.
        have Erd : rd = flipp r by rewrite -Er flipp_invol.
        rewrite Erd => Hd'.
        exact: (no_self_payload Hb Hc Hd').
      have Hkeep : forall (o : option sty),
          pcupd (x, r) o Δ (y, flipp rd) = Δ (y, flipp rd).
        move=> o. rewrite pcupd_lookup /=.
        case E : ((y == x) && (flipp rd == r)) => //.
        move/andP: E => -[/eqP Ey /eqP Er].
        by move/eqP: Hne; rewrite Ey Er.
      case Hdco : (Δ (pflip (y, rd))) => [Ud|].
      * (* internal payload: one end is sent, the co-end stays behind *)
        case: (sctx_of_both Hb Hd Hdco) => T0 [ET0 Eh0].
        apply: (ST_DelB (T0 := T0));
          [exact: (sctx_of_sep Hc Hco) | exact: ET0 | exact: Eh0 |].
        apply: stypedP_ext (IH Hbal') => z.
        have Hco' : pcupd (x, r) (Some S2) Δ (y, flipp rd) = Some Ud.
          by rewrite Hkeep.
        rewrite (sctx_of_upd_both z Hco') /scupd.
        case Ez : (z == y).
        - congr Some. congr SSep.
          case: (sctx_of_bothE ET0) => EP [U EN].
          have EU : U = dual T0 by exact: Hb EP EN.
          move: Hdco. rewrite /pflip /=.
          case: (rd) => /= Hdco.
          + move: Hdco. rewrite EN => -[<-]. by rewrite EU.
          + move: Hdco. by rewrite EP => -[<-].
        - by rewrite (sctx_of_upd (Some S2) z Hco) /scupd.
      * (* separate payload, exactly as in the cut system *)
        apply: ST_Del;
          [exact: (sctx_of_sep Hc Hco) | exact: (sctx_of_sep Hd Hdco) |].
        apply: stypedP_ext (IH Hbal') => z.
        have Hco' : pcupd (x, r) (Some S2) Δ (pflip (y, rd)) = None.
          by rewrite /pflip /= Hkeep.
        rewrite (sctx_of_upd None z Hco') /scupd.
        case Ez : (z == y) => //.
        by rewrite (sctx_of_upd (Some S2) z Hco) /scupd.
  - (* receive *)
    move=> m Δ [x r] rd T S2 K Hc _ IH Hb.
    case Hco : (Δ (pflip (x, r))) => [U|].
    + case: (sctx_of_both Hb Hc Hco) => T' [ET Eh].
      apply: ST_InsB; [exact: ET | exact: Eh].
    + have Hbal' : balanced (pcrecv rd T (pcupd (x, r) (Some S2) Δ)).
        apply: balanced_pcrecv. apply: balanced_upd_sep; [exact: Hb | exact: Hco].
      apply: ST_Ins; first exact: (sctx_of_sep Hc Hco).
      apply: stypedP_ext (IH Hbal') => z.
      rewrite sctx_of_pcrecv. case: z => [z|] //=.
      by rewrite (sctx_of_upd (Some S2) z Hco).
  - (* selection *)
    move=> m Δ [x r] b S1 S2 K Hc _ IH Hb.
    case Hco : (Δ (pflip (x, r))) => [U|].
    + case: (sctx_of_both Hb Hc Hco) => T' [ET Eh].
      apply: ST_SelB; [exact: ET | exact: Eh].
    + have Hbal' : balanced (pcupd (x, r) (Some (if b then S1 else S2)) Δ).
        apply: balanced_upd_sep; [exact: Hb | exact: Hco].
      apply: ST_Sel; first exact: (sctx_of_sep Hc Hco).
      apply: stypedP_ext (IH Hbal') => z.
      by rewrite (sctx_of_upd (Some (if b then S1 else S2)) z Hco).
  - (* branching *)
    move=> m Δ [x r] S1 S2 K1 K2 Hc _ IH1 _ IH2 Hb.
    case Hco : (Δ (pflip (x, r))) => [U|].
    + case: (sctx_of_both Hb Hc Hco) => T' [ET Eh].
      apply: ST_BraB; [exact: ET | exact: Eh].
    + have Hb1 : balanced (pcupd (x, r) (Some S1) Δ).
        apply: balanced_upd_sep; [exact: Hb | exact: Hco].
      have Hb2 : balanced (pcupd (x, r) (Some S2) Δ).
        apply: balanced_upd_sep; [exact: Hb | exact: Hco].
      apply: ST_Bra; first exact: (sctx_of_sep Hc Hco).
      * apply: stypedP_ext (IH1 Hb1) => z.
        by rewrite (sctx_of_upd (Some S1) z Hco).
      * apply: stypedP_ext (IH2 Hb2) => z.
        by rewrite (sctx_of_upd (Some S2) z Hco).
  - (* parallel: the split becomes a merge *)
    move=> m Δ Δ1 Δ2 P Q Hs _ IH1 _ IH2 Hb.
    case: (balanced_split Hs Hb) => Hb1 Hb2.
    apply: (ST_Par (Δ1 := sctx_of Δ1) (Δ2 := sctx_of Δ2)).
    + exact: dmerge_of_psplit Hs Hb.
    + exact: IH1.
    + exact: IH2.
  - (* restriction *)
    move=> m Δ T B _ IH Hb.
    apply: (ST_Res (S := T)).
    apply: stypedP_ext (IH (balanced_pcnu Hb)) => z.
    exact: sctx_of_pcnu.
Qed.

Print Assumptions typed_styped.

(** A smoke test: the bridge applies to the process the cut discipline
    could not type -- two sessions crossing one parallel composition,
    deadlocked and well typed.  Its semantic context is empty, so the
    fundamental theorem will have to produce the relation at [scempty]
    for a process that is genuinely stuck. *)
Example styped_deadlock :
  stypedP (sctx_of pcempty)
    ((ν) ((ν) ( ((zero, pos) !․ ((one, neg) ?․ ∅))
              ∥ ((one, pos) !․ ((zero, neg) ?․ ∅)) )) : procP 0).
Proof. apply: typed_styped; [exact: typed_deadlock | exact: balanced_empty]. Qed.
