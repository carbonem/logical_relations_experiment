(** * The fundamental theorem, in substitution form

    The direct route -- a standalone contraction lemma for the fuse
    clause of the receive compatibility -- founders on scope
    extrusion: a bound-delegation synchronization at a merged pair
    leaves the image residual [C[(ν)(P' ∥ Q')]] while any preimage
    replay produces [(ν)(C-shifted[...])], and bridging the two
    semantically is exactly the structural-congruence tax this
    development set out to avoid.

    The classical dodge dissolves it: state the fundamental theorem
    for OPEN terms under name substitutions that may MERGE the two
    separate ends of one session into a single both-name (Harper's
    open-terms-with-related-substitutions form).  Then the fuse
    branch of a receive is just the continuation's induction
    hypothesis at the merging substitution [scons y σ], and every
    internal synchronization at a merged pair is discharged at the
    typing-parallel node by [combineP] -- machinery already proven.

    Layout:
    - [eraseS], [vok], [spush]: semantic pre-contexts, valid
      substitutions (collisions only across dual separate ends), and
      the pushforward of a pre-context along a substitution.
    - characterization lemmas for [spush] under [vok];
    - [stypedP]: the semantic typing judgment (typing with the link
      protocols kept), and the bridge from [typedP];
    - the σ-parametric fundamental theorem, by induction on
      [stypedP];
    - end-to-end safety at [σ = id]. *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Eqdep_dec PeanoNat.
From Tait Require Import PolBase PolTypes PolProc PolLTS PolErr PolTyping
  PolLogRel PolEquiv PolCompat PolSem PolComb.

Set Implicit Arguments.
Unset Strict Implicit.
Open Scope pol_scope.

(** ** Erasure: semantic slots to syntactic ones *)

Definition eraseS (o : option sslot) : option slot :=
  match o with
  | None => None
  | Some (SSep ρ S0) => Some (Sep ρ S0)
  | Some (SBoth _) => Some Schk
  end.

(** ** Valid substitutions

    Owned names may collide only in dual separate pairs: the two
    ends of one session becoming a single internal name. *)

Definition vok {m n : nat} (σ : ren m n) (Δs : sctxP m) : Prop :=
  forall x1 x2,
    Δs x1 <> None -> Δs x2 <> None -> σ x1 = σ x2 ->
    x1 = x2
    \/ exists ρ T,
         Δs x1 = Some (SSep ρ T) /\ Δs x2 = Some (SSep (flipp ρ) (dual T)).

Lemma flipp_neq r : flipp r <> r.
Proof. by case: r. Qed.

Lemma eq_shift m (a b : ch m) :
  ((shift a : ch m.+1) == shift b) = (a == b).
Proof. by apply/eqP/eqP => [[]|->]. Qed.

(** No triple collisions: a third owned collider of a dual pair
    would have to be dual to both ends, forcing [flipp ρ = ρ]. *)
Lemma vok_no_triple m n (σ : ren m n) (Δs : sctxP m) x0 x1 x2 ρ T :
  vok σ Δs ->
  Δs x0 = Some (SSep ρ T) ->
  Δs x1 = Some (SSep (flipp ρ) (dual T)) ->
  x0 <> x1 -> σ x0 = σ x1 ->
  Δs x2 <> None -> σ x2 = σ x0 ->
  x2 = x0 \/ x2 = x1.
Proof.
  move=> Hv E0 E1 Hne E01 Hox2 E20.
  case: (Hv x2 x0 Hox2 _ E20); first by rewrite E0.
    by left.
  move=> [ρ' [T' [E2 E0']]].
  rewrite E0 in E0'. case: E0' => Eρ' ET'.
  case: (Hv x2 x1 Hox2 _ _); first by rewrite E1.
    by rewrite E20 E01.
    by right.
  move=> [ρ'' [T'' [E2' E1']]].
  rewrite E2 in E2'. case: E2' => Eρ'' ET''.
  rewrite E1 -Eρ'' -Eρ' in E1'. case: E1' => F _.
  by case: (flipp_neq F).
Qed.

(** ** The pushforward

    The slot of an image name: none if no owned preimage, the slot
    itself if the owned preimage is unique, and the merged both-slot
    if two dual ends collapse onto it. *)

Definition spush {m n : nat} (σ : ren m n) (Δs : sctxP m) : sctxP n :=
  fun w =>
    match find_ch (fun x => (σ x == w) && ~~ oslot_eqb (Δs x) None) with
    | None => None
    | Some x0 =>
        match find_ch (fun x => [&& σ x == w,
                          ~~ oslot_eqb (Δs x) None & x != x0]) with
        | None => Δs x0
        | Some _ =>
            match Δs x0 with
            | Some (SSep ρ T) => Some (SBoth (pole ρ T))
            | e => e
            end
        end
    end.

(** Owned-preimage predicate bookkeeping. *)
Lemma spush_p1 m n (σ : ren m n) (Δs : sctxP m) w x :
  ((σ x == w) && ~~ oslot_eqb (Δs x) None) = true
  <-> σ x = w /\ Δs x <> None.
Proof.
  split.
  - move=> /andP[/eqP -> Ho]. split=> //.
    by case: (oslot_eqP (Δs x) None) Ho.
  - move=> [-> Ho]. rewrite eqxx /=.
    by case: (oslot_eqP (Δs x) None).
Qed.

Lemma spush_none_fwd m n (σ : ren m n) (Δs : sctxP m) w :
  (forall x, σ x = w -> Δs x = None) ->
  spush σ Δs w = None.
Proof.
  move=> H. rewrite /spush.
  case F : (find_ch (fun x => (σ x == w) && ~~ oslot_eqb (Δs x) None))
    => [x0|] //.
  move: (find_ch_sound F) => /spush_p1 [E Ho].
  by case: (Ho (H _ E)).
Qed.

Lemma spush_none_inv m n (σ : ren m n) (Δs : sctxP m) w :
  spush σ Δs w = None ->
  forall x, σ x = w -> Δs x = None.
Proof.
  rewrite /spush.
  case F : (find_ch (fun x => (σ x == w) && ~~ oslot_eqb (Δs x) None))
    => [x0|].
  - case F2 : (find_ch _) => [x1|].
    + move: (find_ch_sound F) => /spush_p1 [_ Ho].
      case E0 : (Δs x0) Ho => [[ρ T|S0]|] Ho //.
    + move: (find_ch_sound F) => /spush_p1 [_ Ho] E.
      by case: (Ho E).
  - move=> _ x Ex.
    case E : (Δs x) => [e|] //.
    have Hp : (σ x == w) && ~~ oslot_eqb (Δs x) None.
      apply/spush_p1. by rewrite E.
    case: (find_ch_complete (p := fun x => (σ x == w)
              && ~~ oslot_eqb (Δs x) None) Hp) => x' F'.
    by rewrite F' in F.
Qed.

(** The solo characterization: a unique owned preimage passes its
    slot through unchanged. *)
Lemma spush_solo m n (σ : ren m n) (Δs : sctxP m) w x :
  σ x = w -> Δs x <> None ->
  (forall x', σ x' = w -> Δs x' <> None -> x' = x) ->
  spush σ Δs w = Δs x.
Proof.
  move=> Ex Ho Huniq. rewrite /spush.
  case F : (find_ch (fun x => (σ x == w) && ~~ oslot_eqb (Δs x) None))
    => [x0|]; last first.
    have Hp : (σ x == w) && ~~ oslot_eqb (Δs x) None.
      by apply/spush_p1.
    case: (find_ch_complete (p := fun x => (σ x == w)
              && ~~ oslot_eqb (Δs x) None) Hp) => x' F'.
    by rewrite F' in F.
  move: (find_ch_sound F) => /spush_p1 [E0 Ho0].
  have Ex0 : x0 = x by apply: Huniq.
  case F2 : (find_ch (fun x' => [&& σ x' == w,
                ~~ oslot_eqb (Δs x') None & x' != x0])) => [x1|].
  - move: (find_ch_sound F2) => /and3P[/eqP E1 Ho1 Hne1].
    have Hox1 : Δs x1 <> None.
      by case: (oslot_eqP (Δs x1) None) Ho1.
    have Ex1 : x1 = x by apply: Huniq.
    move: Hne1. by rewrite Ex1 Ex0 eqxx.
  - by rewrite Ex0.
Qed.

(** The pair characterization: two dual ends merge to the pole. *)
Lemma spush_pair m n (σ : ren m n) (Δs : sctxP m) w x0 x1 ρ T :
  vok σ Δs ->
  σ x0 = w -> σ x1 = w -> x0 <> x1 ->
  Δs x0 = Some (SSep ρ T) ->
  Δs x1 = Some (SSep (flipp ρ) (dual T)) ->
  spush σ Δs w = Some (SBoth (pole ρ T)).
Proof.
  move=> Hv E0 E1 Hne D0 D1. rewrite /spush.
  have Ho0 : Δs x0 <> None by rewrite D0.
  have Ho1 : Δs x1 <> None by rewrite D1.
  case F : (find_ch (fun x => (σ x == w) && ~~ oslot_eqb (Δs x) None))
    => [xa|]; last first.
    have Hp : (σ x0 == w) && ~~ oslot_eqb (Δs x0) None.
      by apply/spush_p1.
    case: (find_ch_complete (p := fun x => (σ x == w)
              && ~~ oslot_eqb (Δs x) None) Hp) => x' F'.
    by rewrite F' in F.
  move: (find_ch_sound F) => /spush_p1 [Ea Hoa].
  have Hxa : xa = x0 \/ xa = x1.
    apply: (vok_no_triple Hv D0 D1 Hne _ Hoa _).
    - by rewrite E0 E1.
    - by rewrite Ea E0.
  have [xb [Eb [Db Hneb]]] :
      exists xb, σ xb = w
        /\ ((Δs xb = Some (SSep ρ T)
             \/ Δs xb = Some (SSep (flipp ρ) (dual T)))
            /\ xb != xa).
    case: Hxa => ->.
    - exists x1. split=> //. split; first by right.
      by apply/eqP => E; apply: Hne.
    - exists x0. split=> //. split; first by left.
      by apply/eqP => E; apply: Hne.
  have Hpb : [&& σ xb == w, ~~ oslot_eqb (Δs xb) None & xb != xa].
    rewrite Eb eqxx Hneb andbT /=.
    by case: (oslot_eqP (Δs xb) None);
      case: Db => ->.
  case F2 : (find_ch (fun x' => [&& σ x' == w,
                ~~ oslot_eqb (Δs x') None & x' != xa])) => [x2|]; last first.
    case: (find_ch_complete (p := fun x' => [&& σ x' == w,
              ~~ oslot_eqb (Δs x') None & x' != xa]) Hpb) => x' F'.
    by rewrite F' in F2.
  case: Hxa => Exa; rewrite Exa.
  - by rewrite D0.
  - by rewrite D1 pole_flip_dual.
Qed.

(** Inversions: what an image slot says about preimages. *)
Lemma spush_sep_inv m n (σ : ren m n) (Δs : sctxP m) w ρ S :
  vok σ Δs ->
  spush σ Δs w = Some (SSep ρ S) ->
  exists x,
    [/\ σ x = w, Δs x = Some (SSep ρ S)
      & forall x', σ x' = w -> Δs x' <> None -> x' = x].
Proof.
  move=> Hv. rewrite /spush.
  case F : (find_ch (fun x => (σ x == w) && ~~ oslot_eqb (Δs x) None))
    => [x0|] //.
  move: (find_ch_sound F) => /spush_p1 [E0 Ho0].
  case F2 : (find_ch (fun x' => [&& σ x' == w,
                ~~ oslot_eqb (Δs x') None & x' != x0])) => [x1|].
  - case E : (Δs x0) => [[ρ' T'|S0]|] //.
  - move=> ED.
    exists x0. split=> //.
    move=> x' Ex' Hox'.
    case Enx : (x' == x0); first by move/eqP: Enx.
    have Hp : [&& σ x' == w, ~~ oslot_eqb (Δs x') None & x' != x0].
      rewrite Ex' eqxx Enx andbT /=.
      by case: (oslot_eqP (Δs x') None).
    case: (find_ch_complete (p := fun x' => [&& σ x' == w,
              ~~ oslot_eqb (Δs x') None & x' != x0]) Hp) => x'' F''.
    by rewrite F'' in F2.
Qed.

Lemma spush_owned_inv m n (σ : ren m n) (Δs : sctxP m) w :
  spush σ Δs w <> None ->
  exists x, σ x = w /\ Δs x <> None.
Proof.
  rewrite /spush.
  case F : (find_ch (fun x => (σ x == w) && ~~ oslot_eqb (Δs x) None))
    => [x0|]; last by [].
  move: (find_ch_sound F) => /spush_p1 [E0 Ho0] _.
  by exists x0.
Qed.

(** ** Semantic typing: the judgment with link protocols kept

    [typedP] erased internal link protocols to a bare ✓; the
    semantic judgment keeps them, recording each internal name as a
    both-slot at the pole of its link type.  The fundamental theorem
    inducts on this judgment; a bridge lemma reads the protocols
    back off a [typedP] derivation. *)

Inductive stypedP : forall m, sctxP m -> procP m -> Prop :=
| ST_End : forall m (Δ : sctxP m),
    (forall x, Δ x = None) ->
    stypedP Δ ∅
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
| ST_Ins : forall m (Δ : sctxP m) (x : ch m) (r rd : pol) T S2
    (K : procP m.+1),
    Δ x = Some (SSep r (SRecv T S2)) ->
    stypedP (scons (Some (SSep rd T))
               (scupd x (Some (SSep r S2)) Δ)) K ->
    stypedP Δ ((x, r) ?( rd )․ K)
| ST_Par : forall m (Δ Δ1 Δ2 : sctxP m) (z : ch m) (r : pol) T P Q,
    stypedP Δ1 P -> stypedP Δ2 Q ->
    Δ1 z = Some (SSep r T) ->
    Δ2 z = Some (SSep (flipp r) (dual T)) ->
    (forall x, x != z ->
       (Δ1 x = None /\ Δ x = Δ2 x) \/ (Δ2 x = None /\ Δ x = Δ1 x)) ->
    Δ z = Some (SBoth (pole r T)) ->
    stypedP Δ (P ∥ Q)
| ST_Res : forall m (Δ : sctxP m) (S : sty) (B : procP m.+1),
    stypedP (scons (Some (SBoth S)) Δ) B ->
    stypedP Δ ((ν) B)
| ST_Sel : forall m (Δ : sctxP m) (x : ch m) (r : pol) (b : bool)
    S1 S2 K,
    Δ x = Some (SSep r (SSel S1 S2)) ->
    stypedP (scupd x (Some (SSep r (if b then S1 else S2))) Δ) K ->
    stypedP Δ ((x, r) ◁ b ․ K)
| ST_Bra : forall m (Δ Δ1' Δ2' : sctxP m) (x : ch m) (r : pol)
    S1 S2 K1 K2,
    Δ x = Some (SSep r (SBra S1 S2)) ->
    sevolve Δ Δ1' ->
    sevolve Δ Δ2' ->
    stypedP (scupd x (Some (SSep r S1)) Δ1') K1 ->
    stypedP (scupd x (Some (SSep r S2)) Δ2') K2 ->
    stypedP Δ ((x, r) ▷ ( K1 | K2 )).

Lemma stypedP_ext m (Δ Δ' : sctxP m) (P : procP m) :
  (forall x, Δ x = Δ' x) ->
  stypedP Δ P -> stypedP Δ' P.
Proof.
  move=> Hd Ht. elim: Ht Δ' Hd => {m Δ P}.
  - move=> m Δ HD Δ' Hd. apply: ST_End => x. by rewrite -Hd.
  - move=> m Δ x r K HxS _ IH Δ' Hd.
    apply: ST_Close; first by rewrite -Hd.
    apply: IH => y. rewrite /scupd.
    by case: (y == x).
  - move=> m Δ x r K HxS _ IH Δ' Hd.
    apply: ST_Wait; first by rewrite -Hd.
    apply: IH => y. rewrite /scupd.
    by case: (y == x).
  - move=> m Δ x y r rd T S2 K HxS HyS _ IH Δ' Hd.
    apply: (ST_Del (T := T) (S2 := S2));
      [by rewrite -Hd | by rewrite -Hd |].
    apply: IH => z. rewrite /scupd.
    case: (z == y) => //. by case: (z == x).
  - move=> m Δ x r rd T S2 K HxS _ IH Δ' Hd.
    apply: (ST_Ins (T := T) (S2 := S2) (rd := rd));
      first by rewrite -Hd.
    apply: IH => -[z|] //=. rewrite /scupd.
    by case: ((z : ch m) == x).
  - move=> m Δ Δ1 Δ2 z r T P Q _ IH1 _ IH2 E1 E2 HF ED Δ' Hd.
    apply: (ST_Par (Δ1 := Δ1) (Δ2 := Δ2) (z := z) (r := r) (T := T))
      => //.
    + exact: IH1.
    + exact: IH2.
    + move=> x Hne. case: (HF x Hne) => -[Ea Eb];
        [left | right]; by rewrite -Hd.
    + by rewrite -Hd.
  - move=> m Δ S B _ IH Δ' Hd.
    apply: (ST_Res (S := S)).
    apply: IH => -[z|] //=.
  - move=> m Δ x r b S1 S2 K HxS _ IH Δ' Hd.
    apply: (ST_Sel (b := b) (S1 := S1) (S2 := S2));
      first by rewrite -Hd.
    apply: IH => z. rewrite /scupd.
    by case: (z == x).
  - move=> m Δ Δ1' Δ2' x r S1 S2 K1 K2 HxS Hev1 Hev2 _ IH1 _ IH2 Δ' Hd.
    apply: (ST_Bra (Δ1' := Δ1') (Δ2' := Δ2') (S1 := S1) (S2 := S2)).
    + by rewrite -Hd.
    + move=> z. case: (Hev1 z) => [E|[S0 [S0' [E E']]]].
      * left. by rewrite E Hd.
      * right. exists S0, S0'. by rewrite -Hd.
    + move=> z. case: (Hev2 z) => [E|[S0 [S0' [E E']]]].
      * left. by rewrite E Hd.
      * right. exists S0, S0'. by rewrite -Hd.
    + exact: IH1.
    + exact: IH2.
Qed.

(** Erasure inversions. *)
Lemma eraseS_none o : eraseS o = None -> o = None.
Proof. by case: o => [[ρ S0|S0]|]. Qed.

Lemma eraseS_sep o ρ S0 : eraseS o = Some (Sep ρ S0) -> o = Some (SSep ρ S0).
Proof. by case: o => [[ρ' S'|S']|] //= -[-> ->]. Qed.

Lemma eraseS_chk o : eraseS o = Some Schk -> exists S0, o = Some (SBoth S0).
Proof. case: o => [[ρ' S'|S']|] //= _. by exists S'. Qed.

(** The bridge: a syntactic derivation admits a semantic refinement
    whose erasure is the syntactic context. *)
Lemma typed_styped m (Γ : pctx m) (P : procP m) :
  typedP Γ P ->
  exists Δs : sctxP m,
    (forall x, eraseS (Δs x) = Γ x) /\ stypedP Δs P.
Proof.
  elim=> {m Γ P}.
  - move=> m Γ HG.
    exists scempty. split; last by apply: ST_End.
    move=> x. by rewrite HG.
  - (* close *)
    move=> m Γ x r K HxS _ [Δs [HE Ht]].
    have Hx0 : Δs x = None.
      apply: eraseS_none. by rewrite HE /pcupd eqxx.
    exists (scupd x (Some (SSep r SClose)) Δs). split.
    + move=> y. rewrite /scupd.
      case Ey : (y == x) => /=.
      * by move/eqP: Ey => ->; rewrite HxS.
      * by rewrite HE /pcupd Ey.
    + apply: (ST_Close (x := x) (r := r)); first by rewrite scupd_eq.
      apply: stypedP_ext Ht => y.
      rewrite /scupd. case Ey : (y == x) => //.
      by move/eqP: Ey => ->; rewrite Hx0.
  - (* wait *)
    move=> m Γ x r K HxS _ [Δs [HE Ht]].
    have Hx0 : Δs x = None.
      apply: eraseS_none. by rewrite HE /pcupd eqxx.
    exists (scupd x (Some (SSep r SWait)) Δs). split.
    + move=> y. rewrite /scupd.
      case Ey : (y == x) => /=.
      * by move/eqP: Ey => ->; rewrite HxS.
      * by rewrite HE /pcupd Ey.
    + apply: (ST_Wait (x := x) (r := r)); first by rewrite scupd_eq.
      apply: stypedP_ext Ht => y.
      rewrite /scupd. case Ey : (y == x) => //.
      by move/eqP: Ey => ->; rewrite Hx0.
  - (* free delegation *)
    move=> m Γ x y r rd T S2 K HxS HyS _ [Δs [HE Ht]].
    have Hxy : (x == y) = false.
      case Exy : (x == y) => //.
      move/eqP: Exy HyS => <-. rewrite HxS => -[_ ET].
      by case: (ssend_neqT (esym ET)).
    have Hy0 : Δs y = None.
      apply: eraseS_none. by rewrite HE /pcupd eqxx.
    have Hx2 : Δs x = Some (SSep r S2).
      apply: eraseS_sep.
      by rewrite HE /pcupd Hxy eqxx.
    exists (scupd x (Some (SSep r (SSend T S2)))
              (scupd y (Some (SSep rd T)) Δs)). split.
    + move=> w. rewrite /scupd.
      case Ewx : (w == x) => /=.
      * by move/eqP: Ewx => ->; rewrite HxS.
      * case Ewy : (w == y) => /=.
        -- by move/eqP: Ewy => ->; rewrite HyS.
        -- by rewrite HE /pcupd Ewy /pcupd Ewx.
    + apply: (ST_Del (x := x) (y := y) (r := r) (rd := rd)
                (T := T) (S2 := S2)).
      * by rewrite scupd_eq.
      * by rewrite /scupd eq_sym Hxy eqxx.
      * apply: stypedP_ext Ht => w.
        rewrite /scupd.
        case Ewy : (w == y) => //=.
        -- by move/eqP: Ewy => ->; rewrite Hy0.
        -- case Ewx : (w == x) => //=.
           by move/eqP: Ewx => ->; rewrite Hx2.
  - (* receive *)
    move=> m Γ x r rd T S2 K HxS _ [Δs [HE Ht]].
    have Hz : Δs zero = Some (SSep rd T).
      exact: eraseS_sep (HE zero).
    have Hx2 : Δs (shift x) = Some (SSep r S2).
      apply: eraseS_sep. by rewrite (HE (shift x)) /= /pcupd eqxx.
    exists (scupd x (Some (SSep r (SRecv T S2)))
              (fun w => Δs (shift w))). split.
    + move=> w. rewrite /scupd.
      case Ewx : (w == x) => /=.
      * by move/eqP: Ewx => ->; rewrite HxS.
      * by rewrite (HE (shift w)) /= /pcupd Ewx.
    + apply: (ST_Ins (x := x) (r := r) (rd := rd) (T := T) (S2 := S2)).
      * by rewrite scupd_eq.
      * apply: stypedP_ext Ht => -[w|] /=; last by rewrite Hz.
        rewrite /scupd.
        case Ewx : ((w : ch m) == x) => //=.
        by move/eqP: Ewx => ->; rewrite Hx2.
  - (* parallel *)
    move=> m Γ Γ1 Γ2 z r T P Q _ [Δs1 [HE1 Ht1]] _ [Δs2 [HE2 Ht2]]
      Hz1 Hz2 HF Hz.
    have Dz1 : Δs1 z = Some (SSep r T).
      apply: eraseS_sep. by rewrite HE1.
    have Dz2 : Δs2 z = Some (SSep (flipp r) (dual T)).
      apply: eraseS_sep. by rewrite HE2.
    exists (fun w => if w == z then Some (SBoth (pole r T))
                     else if Δs1 w is Some e then Some e else Δs2 w).
    split.
    + move=> w.
      case Ewz : (w == z) => /=.
      * by move/eqP: Ewz => ->; rewrite Hz.
      * have Hne : w != z by rewrite Ewz.
        case: (HF _ Hne) => -[Ea Eb].
        -- have D1 : Δs1 w = None.
             apply: eraseS_none. by rewrite HE1.
           by rewrite D1 HE2.
        -- have D2 : Δs2 w = None.
             apply: eraseS_none. by rewrite HE2.
           case E1 : (Δs1 w) => [e|].
           ++ by rewrite -E1 HE1 Eb.
           ++ by rewrite D2 Eb -HE1 E1.
    + apply: (ST_Par (Δ1 := Δs1) (Δ2 := Δs2) (z := z) (r := r)
                (T := T)) => //.
      * move=> w Hne.
        case: (HF _ Hne) => -[Ea Eb].
        -- left. split.
           ++ apply: eraseS_none. by rewrite HE1.
           ++ have D1 : Δs1 w = None.
                apply: eraseS_none. by rewrite HE1.
              by rewrite (negbTE Hne) D1.
        -- right. split.
           ++ apply: eraseS_none. by rewrite HE2.
           ++ have D2 : Δs2 w = None.
                apply: eraseS_none. by rewrite HE2.
              rewrite (negbTE Hne).
              by case E1 : (Δs1 w).
      * by rewrite eqxx.
  - (* restriction *)
    move=> m Γ B _ [Δs [HE Ht]].
    have [S0 Hz] : exists S0, Δs zero = Some (SBoth S0).
      exact: eraseS_chk (HE zero).
    exists (fun w => Δs (shift w)). split.
    + move=> w. exact: (HE (shift w)).
    + apply: (ST_Res (S := S0)).
      by apply: stypedP_ext Ht => -[w|] //=.
  - (* select *)
    move=> m Γ x r b S1 S2 K HxS _ [Δs [HE Ht]].
    have Hx2 : Δs x = Some (SSep r (if b then S1 else S2)).
      apply: eraseS_sep. by rewrite HE /pcupd eqxx.
    exists (scupd x (Some (SSep r (SSel S1 S2))) Δs). split.
    + move=> w. rewrite /scupd.
      case Ewx : (w == x) => /=.
      * by move/eqP: Ewx => ->; rewrite HxS.
      * by rewrite HE /pcupd Ewx.
    + apply: (ST_Sel (b := b) (S1 := S1) (S2 := S2));
        first by rewrite scupd_eq.
      apply: stypedP_ext Ht => w.
      rewrite /scupd. case Ewx : (w == x) => //.
      by move/eqP: Ewx => ->; rewrite Hx2.
  - (* branch *)
    move=> m Γ x r S1 S2 K1 K2 HxS _ [Δs1 [HE1 Ht1]] _ [Δs2 [HE2 Ht2]].
    have Hx1 : Δs1 x = Some (SSep r S1).
      apply: eraseS_sep. by rewrite HE1 /pcupd eqxx.
    have Hx2 : Δs2 x = Some (SSep r S2).
      apply: eraseS_sep. by rewrite HE2 /pcupd eqxx.
    exists (scupd x (Some (SSep r (SBra S1 S2))) Δs1). split.
    + move=> w. rewrite /scupd.
      case Ewx : (w == x) => /=.
      * by move/eqP: Ewx => ->; rewrite HxS.
      * by rewrite HE1 /pcupd Ewx.
    + apply: (ST_Bra
        (Δ1' := scupd x (Some (SSep r (SBra S1 S2))) Δs1)
        (Δ2' := scupd x (Some (SSep r (SBra S1 S2))) Δs2)
        (S1 := S1) (S2 := S2)).
      * by rewrite scupd_eq.
      * exact: sevolve_refl.
      * (* the two branch refinements agree up to both-protocols *)
        move=> w. rewrite /scupd.
        case Ewx : (w == x); first by left.
        have EG : eraseS (Δs2 w) = eraseS (Δs1 w).
          by rewrite HE1 HE2 /pcupd Ewx.
        move: EG.
        case E1 : (Δs1 w) => [[ρ1 T1|T1]|];
          case E2 : (Δs2 w) => [[ρ2 T2|T2]|] => //= EG.
        -- left. by case: EG => -> ->.
        -- right. by exists T1, T2.
        -- by left.
      * apply: stypedP_ext Ht1 => w.
        rewrite /scupd. case Ewx : (w == x) => //.
        by move/eqP: Ewx => ->; rewrite Hx1.
      * apply: stypedP_ext Ht2 => w.
        rewrite /scupd. case Ewx : (w == x) => //.
        by move/eqP: Ewx => ->; rewrite Hx2.
Qed.

Print Assumptions typed_styped.

(** ** Transport primitives for the pushforward *)

Lemma find_ch_ext m (p q : ch m -> bool) :
  (forall x, p x = q x) -> find_ch p = find_ch q.
Proof.
  elim: m p q => [//|m IH] p q Hpq /=.
  rewrite Hpq. case: (q None) => //.
  by rewrite (IH _ (fun z => q (Some z)) (fun z => Hpq (Some z))).
Qed.

(** Only the slots of [w]'s preimages matter to [spush _ _ w]. *)
Lemma spush_irrel m n (σ : ren m n) (Δs Δs' : sctxP m) w :
  (forall x, σ x = w -> Δs' x = Δs x) ->
  spush σ Δs' w = spush σ Δs w.
Proof.
  move=> Hag. rewrite /spush.
  have Hp : forall x, ((σ x == w) && ~~ oslot_eqb (Δs' x) None)
                    = ((σ x == w) && ~~ oslot_eqb (Δs x) None).
    move=> x. case Ex : (σ x == w) => //=.
    by rewrite (Hag _ (eqP Ex)).
  rewrite (find_ch_ext Hp).
  case F : (find_ch (fun x => (σ x == w) && ~~ oslot_eqb (Δs x) None))
    => [x0|] //.
  move: (find_ch_sound F) => /spush_p1 [E0 _].
  have Hp2 : forall x, [&& σ x == w, ~~ oslot_eqb (Δs' x) None & x != x0]
                     = [&& σ x == w, ~~ oslot_eqb (Δs x) None & x != x0].
    move=> x. case Ex : (σ x == w) => //=.
    by rewrite (Hag _ (eqP Ex)).
  rewrite (find_ch_ext Hp2).
  case F2 : (find_ch _) => [x1|]; by rewrite (Hag _ E0).
Qed.

(** ** Validity preservation *)

Lemma vok_upd_none m n (σ : ren m n) (Δs : sctxP m) (x : ch m) :
  vok σ Δs -> vok σ (scupd x None Δs).
Proof.
  move=> Hv x1 x2. rewrite /scupd.
  case E1 : (x1 == x) => //. case E2 : (x2 == x) => //.
  move=> H1 H2 E.
  by case: (Hv _ _ H1 H2 E) => [-> | Hp]; [left | right].
Qed.

Lemma vok_upd_solo m n (σ : ren m n) (Δs : sctxP m) (x : ch m) e :
  vok σ Δs ->
  (forall x', σ x' = σ x -> Δs x' <> None -> x' = x) ->
  vok σ (scupd x (Some e) Δs).
Proof.
  move=> Hv Huniq x1 x2. rewrite /scupd.
  case E1 : (x1 == x); case E2 : (x2 == x).
  - move/eqP: E1 => ->. move/eqP: E2 => ->. by left.
  - move/eqP: E1 => -> _ H2 E. left.
    apply: esym. apply: Huniq H2. by rewrite E.
  - move/eqP: E2 => -> H1 _ E. left.
    exact: Huniq H1.
  - move=> H1 H2 E.
    by case: (Hv _ _ H1 H2 E) => [-> | Hp]; [left | right].
Qed.

Lemma vok_scons_fresh m n (σ : ren m n) (Δs : sctxP m) (y : ch n) e0 :
  vok σ Δs ->
  (forall x, σ x = y -> Δs x = None) ->
  vok (scons y σ) (scons e0 Δs).
Proof.
  move=> Hv Hfr [x1|] [x2|] //=.
  - move=> H1 H2 E.
    by case: (Hv _ _ H1 H2 E) => [-> | Hp]; [left | right].
  - move=> H1 H2 E. by case: (H1 (Hfr _ E)).
  - move=> H1 H2 E. by case: (H2 (Hfr _ (esym E))).
  - move=> _ _ _. by left.
Qed.

Lemma vok_scons_fuse m n (σ : ren m n) (Δs : sctxP m) (y : ch n)
    (xc : ch m) (ρ : pol) T :
  vok σ Δs ->
  σ xc = y ->
  Δs xc = Some (SSep (flipp ρ) (dual T)) ->
  (forall x', σ x' = y -> Δs x' <> None -> x' = xc) ->
  vok (scons y σ) (scons (Some (SSep ρ T)) Δs).
Proof.
  move=> Hv Exc Dxc Huniq [x1|] [x2|] //=.
  - move=> H1 H2 E.
    by case: (Hv _ _ H1 H2 E) => [-> | Hp]; [left | right].
  - move=> H1 _ E. right.
    exists (flipp ρ), (dual T).
    rewrite flipp_invol dual_involutive.
    by rewrite (Huniq _ E H1) Dxc.
  - move=> _ H2 E. right.
    exists ρ, T.
    by rewrite (Huniq _ (esym E) H2) Dxc.
  - move=> _ _ _. by left.
Qed.

Lemma vok_up_scons m n (σ : ren m n) (Δs : sctxP m) e0 :
  vok σ Δs ->
  vok (up_ch σ) (scons e0 Δs).
Proof.
  move=> Hv [x1|] [x2|] //=.
  - move=> H1 H2 E.
    have E' : σ x1 = σ x2.
      exact: (f_equal (fun c : ch n.+1 => if c is Some u then u else σ x1)
                E).
    by case: (Hv _ _ H1 H2 E') => [-> | Hp]; [left | right].
  - move=> _ _ _. by left.
Qed.

(** ** Pushforward against context updates *)

Lemma spush_upd_none_solo m n (σ : ren m n) (Δs : sctxP m) (x : ch m) :
  Δs x <> None ->
  (forall x', σ x' = σ x -> Δs x' <> None -> x' = x) ->
  forall w, spush σ (scupd x None Δs) w
            = scupd (σ x) None (spush σ Δs) w.
Proof.
  move=> Ho Huniq w. rewrite [in RHS]/scupd.
  case Ew : (w == σ x).
  - move/eqP: Ew => ->.
    apply: spush_none_fwd => x' Ex'. rewrite /scupd.
    case Ex : (x' == x) => //.
    case E : (Δs x') => [e'|] //.
    have Ex'' : x' = x by apply: Huniq => //; rewrite E.
    by rewrite Ex'' eqxx in Ex.
  - apply: spush_irrel => x' Ex'. rewrite /scupd.
    case Ex : (x' == x) => //.
    move/eqP: Ex Ex' => -> Ex'.
    by rewrite Ex' eqxx in Ew.
Qed.

Lemma spush_upd_some_solo m n (σ : ren m n) (Δs : sctxP m) (x : ch m) e :
  Δs x <> None ->
  (forall x', σ x' = σ x -> Δs x' <> None -> x' = x) ->
  forall w, spush σ (scupd x (Some e) Δs) w
            = scupd (σ x) (Some e) (spush σ Δs) w.
Proof.
  move=> Ho Huniq w. rewrite [in RHS]/scupd.
  case Ew : (w == σ x).
  - move/eqP: Ew => ->.
    rewrite -[X in _ = X](scupd_eq x (Some e) Δs).
    apply: (spush_solo (x := x)).
    + by [].
    + by rewrite scupd_eq.
    + move=> x' Ex'. rewrite /scupd.
      case Ex : (x' == x); first by move/eqP: Ex.
      move=> Hox'. exact: Huniq.
  - apply: spush_irrel => x' Ex'. rewrite /scupd.
    case Ex : (x' == x) => //.
    move/eqP: Ex Ex' => -> Ex'.
    by rewrite Ex' eqxx in Ew.
Qed.

Lemma spush_upd_none_pair m n (σ : ren m n) (Δs : sctxP m)
    (x xc : ch m) (ρ : pol) T :
  vok σ Δs ->
  x <> xc -> σ x = σ xc ->
  Δs x = Some (SSep ρ T) ->
  Δs xc = Some (SSep (flipp ρ) (dual T)) ->
  forall w, spush σ (scupd x None Δs) w
            = scupd (σ x) (Δs xc) (spush σ Δs) w.
Proof.
  move=> Hv Hne Ecol Dx Dxc w. rewrite [in RHS]/scupd.
  case Ew : (w == σ x).
  - move/eqP: Ew => ->.
    rewrite (spush_solo (x := xc)) => //.
    + rewrite /scupd.
      by case Ec : (xc == x) => //; move/eqP: Ec Hne => ->.
    + rewrite /scupd.
      case Ec : (xc == x); first by move/eqP: Ec Hne => ->.
      by rewrite Dxc.
    + move=> x' Ex'. rewrite /scupd.
      case Ex : (x' == x) => //.
      move=> Hox'.
      have : x' = x \/ x' = xc.
        apply: (vok_no_triple Hv Dx Dxc Hne Ecol Hox').
        by rewrite Ex'.
      case=> // Exx.
      by rewrite Exx eqxx in Ex.
  - apply: spush_irrel => x' Ex'. rewrite /scupd.
    case Ex : (x' == x) => //.
    move/eqP: Ex Ex' => -> Ex'.
    by rewrite Ex' eqxx in Ew.
Qed.

(** ** Pushforward against context extension

    The scan itself descends: with [zero] not a preimage of [w], the
    extended scan reduces to the base scan. *)

Lemma find_ch_shift_pred m (p : ch m.+1 -> bool) :
  p zero = false ->
  find_ch p = omap Some (find_ch (fun z => p (shift z))).
Proof. move=> Hz /=. by rewrite Hz. Qed.

Lemma spush_scons_descent m n (σ : ren m n) (y : ch n) e0
    (Δs : sctxP m) w :
  w <> y ->
  spush (scons y σ) (scons e0 Δs) w = spush σ Δs w.
Proof.
  move=> Hne.
  have Ey : (y == w) = false.
    by apply: negbTE; apply/eqP => E; apply: Hne.
  rewrite {1}/spush.
  rewrite (find_ch_shift_pred (p := fun x => (scons y σ x == w)
             && ~~ oslot_eqb (scons e0 Δs x) None)) /=; last first.
    by rewrite Ey.
  rewrite [in RHS]/spush.
  case F : (find_ch (fun z : ch m =>
              (σ z == w) && ~~ oslot_eqb (Δs z) None)) => [x0|] //=.
  rewrite Ey /=.
  have -> : find_ch (fun z : ch m => [&& σ z == w,
                ~~ oslot_eqb (Δs z) None & (Some z : ch m.+1) != Some x0])
          = find_ch (fun z : ch m => [&& σ z == w,
                ~~ oslot_eqb (Δs z) None & z != x0]).
    apply: find_ch_ext => z. by rewrite (eq_shift z x0).
  by case: (find_ch (fun z : ch m =>
       [&& σ z == w, ~~ oslot_eqb (Δs z) None & z != x0])) => [a|] //=.
Qed.

Lemma spush_shift_comp m n (σ : ren m n) (Δs : sctxP m) v :
  spush (fun x => shift (σ x)) Δs (shift v) = spush σ Δs v.
Proof.
  rewrite /spush.
  have -> : find_ch (fun x => ((shift (σ x) : ch n.+1) == shift v)
                && ~~ oslot_eqb (Δs x) None)
          = find_ch (fun x => (σ x == v) && ~~ oslot_eqb (Δs x) None).
    apply: find_ch_ext => x. by rewrite eq_shift.
  case F : (find_ch (fun x => (σ x == v) && ~~ oslot_eqb (Δs x) None))
    => [x0|] //.
  have -> : find_ch (fun x => [&& (shift (σ x) : ch n.+1) == shift v,
                ~~ oslot_eqb (Δs x) None & x != x0])
          = find_ch (fun x => [&& σ x == v,
                ~~ oslot_eqb (Δs x) None & x != x0]).
    apply: find_ch_ext => x. by rewrite eq_shift.
  by [].
Qed.

Lemma spush_scons_fresh m n (σ : ren m n) (Δs : sctxP m) (y : ch n) e0 :
  (forall x, σ x = y -> Δs x = None) ->
  forall w, spush (scons y σ) (scons e0 Δs) w
            = scupd y e0 (spush σ Δs) w.
Proof.
  move=> Hfr w. rewrite [in RHS]/scupd.
  case Ew : (w == y).
  - move/eqP: Ew => ->.
    case: e0 => [e0|].
    + apply: (spush_solo (x := zero)) => //.
      move=> [x'|] //= Ex' Hox'.
      by case: (Hox' (Hfr _ Ex')).
    + apply: spush_none_fwd => -[x'|] //= Ex'.
      exact: Hfr.
  - rewrite spush_scons_descent //.
    by move=> E; rewrite E eqxx in Ew.
Qed.

Lemma spush_scons_fuse m n (σ : ren m n) (Δs : sctxP m) (y : ch n)
    (xc : ch m) (ρ : pol) T :
  vok (scons y σ) (scons (Some (SSep ρ T)) Δs) ->
  σ xc = y ->
  Δs xc = Some (SSep (flipp ρ) (dual T)) ->
  forall w, spush (scons y σ) (scons (Some (SSep ρ T)) Δs) w
            = scupd y (Some (SBoth (pole ρ T))) (spush σ Δs) w.
Proof.
  move=> Hv Exc Dxc w. rewrite [in RHS]/scupd.
  case Ew : (w == y).
  - move/eqP: Ew => ->.
    apply: (spush_pair (x0 := zero) (x1 := shift xc)) => //.
  - rewrite spush_scons_descent //.
    by move=> E; rewrite E eqxx in Ew.
Qed.

Lemma spush_up_scons m n (σ : ren m n) (Δs : sctxP m) e0 :
  forall w, spush (up_ch σ) (scons e0 Δs) w
            = scons e0 (spush σ Δs) w.
Proof.
  move=> [v|].
  - rewrite /up_ch spush_scons_descent //=.
    exact: spush_shift_comp.
  - case: e0 => [e0|] /=.
    + rewrite /up_ch.
      apply: (spush_solo (x := zero)) => //.
      by move=> [x'|].
    + rewrite /up_ch.
      apply: spush_none_fwd. by move=> [x'|].
Qed.

Print Assumptions spush_up_scons.

(** ** Internal evolution against the pushforward

    [sevolve] changes only both-slot protocols, so it preserves the
    owned set, validity, and the scan structure of [spush]. *)

Lemma sevolve_ownedb m (Δs Δs' : sctxP m) :
  sevolve Δs Δs' ->
  forall x, oslot_eqb (Δs' x) None = oslot_eqb (Δs x) None.
Proof.
  move=> Hev x.
  case: (Hev x) => [->|[S0 [S0' [-> ->]]]] //.
  case: (oslot_eqP (Some (SBoth S0')) None) => //.
  by case: (oslot_eqP (Some (SBoth S0)) None).
Qed.

Lemma vok_sevolve m n (σ : ren m n) (Δs Δs' : sctxP m) :
  vok σ Δs -> sevolve Δs Δs' -> vok σ Δs'.
Proof.
  move=> Hv Hev x1 x2 H1 H2 E.
  have Ho1 : Δs x1 <> None.
    case: (Hev x1) H1 => [<-|[S0 [S0' [Ea _]]]] //. by rewrite Ea.
  have Ho2 : Δs x2 <> None.
    case: (Hev x2) H2 => [<-|[S0 [S0' [Ea _]]]] //. by rewrite Ea.
  case: (Hv _ _ Ho1 Ho2 E) => [-> | ]; first by left.
  move=> [ρ [T [D1 D2]]].
  right. exists ρ, T.
  case: (Hev x1) => [E1|[S0 [S0' [Ea _]]]]; last by rewrite Ea in D1.
  case: (Hev x2) => [E2|[S0 [S0' [Ea _]]]]; last by rewrite Ea in D2.
  by rewrite E1 E2.
Qed.

Lemma spush_sevolve m n (σ : ren m n) (Δs Δs' : sctxP m) :
  vok σ Δs -> sevolve Δs Δs' ->
  forall w, spush σ Δs' w = spush σ Δs w
    \/ (exists S0 S0', spush σ Δs w = Some (SBoth S0)
          /\ spush σ Δs' w = Some (SBoth S0')).
Proof.
  move=> Hv Hev w. rewrite /spush.
  have -> : find_ch (fun x => (σ x == w) && ~~ oslot_eqb (Δs' x) None)
          = find_ch (fun x => (σ x == w) && ~~ oslot_eqb (Δs x) None).
    apply: find_ch_ext => x. by rewrite (sevolve_ownedb Hev).
  case F : (find_ch (fun x => (σ x == w) && ~~ oslot_eqb (Δs x) None))
    => [x0|]; last by left.
  have -> : find_ch (fun x => [&& σ x == w,
                ~~ oslot_eqb (Δs' x) None & x != x0])
          = find_ch (fun x => [&& σ x == w,
                ~~ oslot_eqb (Δs x) None & x != x0]).
    apply: find_ch_ext => x. by rewrite (sevolve_ownedb Hev).
  move: (find_ch_sound F) => /spush_p1 [E0 Ho0].
  case F2 : (find_ch (fun x => [&& σ x == w,
                ~~ oslot_eqb (Δs x) None & x != x0])) => [x1|].
  - (* pair: both slots separate, hence unchanged *)
    move: (find_ch_sound F2) => /and3P[/eqP E1 Ho1b Hne1].
    have Ho1 : Δs x1 <> None.
      by case: (oslot_eqP (Δs x1) None) Ho1b.
    have Hne : x0 <> x1 by move=> E; move: Hne1; rewrite E eqxx.
    case: (Hv x0 x1 Ho0 Ho1 _); first by rewrite E0 E1.
      by move=> E; case: (Hne E).
    move=> [ρ [T [D0 D1]]].
    case: (Hev x0) => [-> |[S0 [S0' [Ea _]]]]; first by left.
    by rewrite Ea in D0.
  - (* solo *)
    case: (Hev x0) => [-> |[S0 [S0' [Ea Eb]]]]; first by left.
    right. exists S0, S0'. by rewrite Ea Eb.
Qed.

Lemma spush_sevolve_sev m n (σ : ren m n) (Δs Δs' : sctxP m) :
  vok σ Δs -> sevolve Δs Δs' ->
  sevolve (spush σ Δs) (spush σ Δs').
Proof.
  move=> Hv Hev w.
  case: (spush_sevolve Hv Hev w) => [->|[S0 [S0' [Ea Eb]]]];
    first by left.
  right. by exists S0, S0'.
Qed.

(** ** Case split: a subject is solo or one end of a merged pair *)

Lemma vok_split m n (σ : ren m n) (Δs : sctxP m) (x : ch m) :
  vok σ Δs -> Δs x <> None ->
  (forall x', σ x' = σ x -> Δs x' <> None -> x' = x)
  \/ (exists xc ρ T,
       [/\ x <> xc, σ xc = σ x,
           Δs x = Some (SSep ρ T),
           Δs xc = Some (SSep (flipp ρ) (dual T))
         & forall x', σ x' = σ x -> Δs x' <> None ->
             x' = x \/ x' = xc]).
Proof.
  move=> Hv Ho.
  case F : (find_ch (fun x' => [&& σ x' == σ x,
              ~~ oslot_eqb (Δs x') None & x' != x])) => [xc|]; last first.
  - left => x' Ex' Hox'.
    case Enx : (x' == x); first by move/eqP: Enx.
    have Hp : [&& σ x' == σ x, ~~ oslot_eqb (Δs x') None & x' != x].
      rewrite Ex' eqxx Enx andbT /=.
      by case: (oslot_eqP (Δs x') None).
    case: (find_ch_complete (p := fun x' => [&& σ x' == σ x,
              ~~ oslot_eqb (Δs x') None & x' != x]) Hp) => x'' F''.
    by rewrite F'' in F.
  - right.
    move: (find_ch_sound F) => /and3P[/eqP Ec Hoc Hnec].
    have Hoxc : Δs xc <> None.
      by case: (oslot_eqP (Δs xc) None) Hoc.
    have Hne : x <> xc.
      by move=> E; move: Hnec; rewrite E eqxx.
    case: (Hv x xc Ho Hoxc (esym Ec)) => [E|[ρ [T [Dx Dxc]]]].
      by case: (Hne E).
    exists xc, ρ, T. split=> // x' Ex' Hox'.
    exact: (vok_no_triple Hv Dx Dxc Hne (esym Ec) Hox' Ex').
Qed.

(** Residual collapse: receiving [y] into the σ-image of the body is
    substituting [scons y σ]. *)
Lemma psubst_recv_collapse m n (σ : ren m n) (y : ch n)
    (K : procP m.+1) :
  psubst (scons y id_ren) (psubst (up_ch σ) K) = psubst (scons y σ) K.
Proof. rewrite psubst_comp. by apply: psubst_ext => -[z|]. Qed.

(** ** σ-compatibility: close *)

Lemma fcompat_close m n (σ : ren m n) (Δs : sctxP m) (x : ch m)
    (r : pol) (K : procP m) :
  vok σ Δs ->
  Δs x = Some (SSep r SClose) ->
  (forall n' (σ' : ren m n'), vok σ' (scupd x None Δs) ->
     SEMP (spush σ' (scupd x None Δs)) (psubst σ' K)) ->
  SEMP (spush σ Δs) (psubst σ ((x, r) !․ K)).
Proof.
  move=> Hv HxS IH.
  have Ho : Δs x <> None by rewrite HxS.
  case: (vok_split Hv Ho)
    => [Huniq|[xc [ρ [T [Hne Ec Dx Dxc Huniq2]]]]].
  - (* solo subject *)
    have Hpush : spush σ Δs (σ x) = Some (SSep r SClose).
      by rewrite (spush_solo (x := x) erefl Ho Huniq) HxS.
    move=> [|k] //. split.
    + split=> //.
      move=> a c Hof. case: (offers_close Hof) => -> -> /=.
      exists SClose. by rewrite /sat /= Hpush /= pol_eqb_refl.
    + move=> w rw S HwS.
      case: S HwS => [| |T' S2'|T' S2'|S1' S2''|S1' S2''] HwS /=.
      * move=> R HT. case: (pinv_c_closeF HT) => Ec' ->.
        move: Ec' => -[E1 E2]. subst w rw.
        apply: EsemP_ext (IH _ _ (vok_upd_none (x := x) Hv) k) => v.
        by rewrite (spush_upd_none_solo Ho Huniq).
      * move=> R HT. by case: (pinv_w_close HT).
      * split.
        -- move=> y' rd' R HT. by case: (pinv_f_close2 HT).
        -- move=> r' R HT. by case: (pinv_b_close HT).
      * split.
        -- move=> y' rd' R HT. by case: (pinv_r_close2 HT).
        -- move=> rd' R HT. by case: (pinv_r_close2 HT).
    + move=> b R HT. by case: (pinv_sel_close HT).
    + move=> b R HT. by case: (pinv_br_close HT).
    + move=> R Hst. by case: (pinv_t_close Hst).
  - (* merged subject: the relation asks nothing beyond conformance *)
    rewrite Dx in HxS. case: HxS => Eρ ET. subst ρ.
    have Hoc : Δs xc <> None by rewrite Dxc.
    have Hpush : spush σ Δs (σ x) = Some (SBoth (pole r SClose)).
      rewrite -ET.
      exact (spush_pair (x0 := x) (x1 := xc) Hv erefl Ec Hne Dx Dxc).
    move=> [|k] //. split.
    + split=> //.
      move=> a c Hof. case: (offers_close Hof) => -> -> /=.
      exists SClose. by rewrite /sat /= Hpush /= pole_invol.
    + move=> w rw S HwS.
      case: S HwS => [| |T' S2'|T' S2'|S1' S2''|S1' S2''] HwS /=.
      * move=> R HT. case: (pinv_c_closeF HT) => Ec' ->.
        move: Ec' => -[E1 E2]. subst w rw.
        by rewrite Hpush in HwS.
      * move=> R HT. by case: (pinv_w_close HT).
      * split.
        -- move=> y' rd' R HT. by case: (pinv_f_close2 HT).
        -- move=> r' R HT. by case: (pinv_b_close HT).
      * split.
        -- move=> y' rd' R HT. by case: (pinv_r_close2 HT).
        -- move=> rd' R HT. by case: (pinv_r_close2 HT).
    + move=> b R HT. by case: (pinv_sel_close HT).
    + move=> b R HT. by case: (pinv_br_close HT).
    + move=> R Hst. by case: (pinv_t_close Hst).
Qed.

Print Assumptions fcompat_close.

(** ** σ-compatibility: wait *)

Lemma fcompat_wait m n (σ : ren m n) (Δs : sctxP m) (x : ch m)
    (r : pol) (K : procP m) :
  vok σ Δs ->
  Δs x = Some (SSep r SWait) ->
  (forall n' (σ' : ren m n'), vok σ' (scupd x None Δs) ->
     SEMP (spush σ' (scupd x None Δs)) (psubst σ' K)) ->
  SEMP (spush σ Δs) (psubst σ ((x, r) ?․ K)).
Proof.
  move=> Hv HxS IH.
  have Ho : Δs x <> None by rewrite HxS.
  case: (vok_split Hv Ho)
    => [Huniq|[xc [ρ [T [Hne Ec Dx Dxc Huniq2]]]]].
  - have Hpush : spush σ Δs (σ x) = Some (SSep r SWait).
      by rewrite (spush_solo (x := x) erefl Ho Huniq) HxS.
    move=> [|k] //. split.
    + split=> //.
      move=> a c Hof. case: (offers_wait Hof) => -> -> /=.
      exists SWait. by rewrite /sat /= Hpush /= pol_eqb_refl.
    + move=> w rw S HwS.
      case: S HwS => [| |T' S2'|T' S2'|S1' S2''|S1' S2''] HwS /=.
      * move=> R HT. by case: (pinv_c_wait HT).
      * move=> R HT. case: (pinv_w_waitF HT) => Ec' ->.
        move: Ec' => -[E1 E2]. subst w rw.
        apply: EsemP_ext (IH _ _ (vok_upd_none (x := x) Hv) k) => v.
        by rewrite (spush_upd_none_solo Ho Huniq).
      * split.
        -- move=> y' rd' R HT. by case: (pinv_f_wait2 HT).
        -- move=> r' R HT. by case: (pinv_b_wait HT).
      * split.
        -- move=> y' rd' R HT. by case: (pinv_r_wait2 HT).
        -- move=> rd' R HT. by case: (pinv_r_wait2 HT).
    + move=> b R HT. by case: (pinv_sel_wait HT).
    + move=> b R HT. by case: (pinv_br_wait HT).
    + move=> R Hst. by case: (pinv_t_wait Hst).
  - rewrite Dx in HxS. case: HxS => Eρ ET. subst ρ.
    have Hpush : spush σ Δs (σ x) = Some (SBoth (pole r SWait)).
      rewrite -ET.
      exact (spush_pair (x0 := x) (x1 := xc) Hv erefl Ec Hne Dx Dxc).
    move=> [|k] //. split.
    + split=> //.
      move=> a c Hof. case: (offers_wait Hof) => -> -> /=.
      exists SWait. by rewrite /sat /= Hpush /= pole_invol.
    + move=> w rw S HwS.
      case: S HwS => [| |T' S2'|T' S2'|S1' S2''|S1' S2''] HwS /=.
      * move=> R HT. by case: (pinv_c_wait HT).
      * move=> R HT. case: (pinv_w_waitF HT) => Ec' ->.
        move: Ec' => -[E1 E2]. subst w rw.
        by rewrite Hpush in HwS.
      * split.
        -- move=> y' rd' R HT. by case: (pinv_f_wait2 HT).
        -- move=> r' R HT. by case: (pinv_b_wait HT).
      * split.
        -- move=> y' rd' R HT. by case: (pinv_r_wait2 HT).
        -- move=> rd' R HT. by case: (pinv_r_wait2 HT).
    + move=> b R HT. by case: (pinv_sel_wait HT).
    + move=> b R HT. by case: (pinv_br_wait HT).
    + move=> R Hst. by case: (pinv_t_wait Hst).
Qed.

(** ** σ-compatibility: free delegation *)

Lemma fcompat_del m n (σ : ren m n) (Δs : sctxP m) (x yp : ch m)
    (r rd : pol) T S2 (K : procP m) :
  vok σ Δs ->
  Δs x = Some (SSep r (SSend T S2)) ->
  Δs yp = Some (SSep rd T) ->
  (forall n' (σ' : ren m n'),
     vok σ' (scupd yp None (scupd x (Some (SSep r S2)) Δs)) ->
     SEMP (spush σ' (scupd yp None (scupd x (Some (SSep r S2)) Δs)))
       (psubst σ' K)) ->
  SEMP (spush σ Δs) (psubst σ ((x, r) ! (yp, rd) ․ K)).
Proof.
  move=> Hv HxS HyS IH.
  have Ho : Δs x <> None by rewrite HxS.
  have Hoy : Δs yp <> None by rewrite HyS.
  have Hxy : x <> yp.
    move=> E. rewrite E HyS in HxS. case: HxS => _ ET.
    by case: (ssend_neqT ET).
  (* the subject and the payload never collide under a valid σ *)
  have Hsxy : σ x <> σ yp.
    move=> E.
    case: (Hv x yp Ho Hoy E) => [Exy|[ρ' [T' [Dx' Dy']]]].
      by case: (Hxy Exy).
    rewrite HxS in Dx'. case: Dx' => _ ET'.
    rewrite HyS -ET' in Dy'. case: Dy' => _ ET''.
    have := f_equal stysz ET''. rewrite /= => /eqP.
    by rewrite -[X in X == _]addn0 -addnS eqn_add2l.
  case: (vok_split Hv Ho)
    => [Huniq|[xc [ρ [T0 [Hne Ec Dx Dxc Huniq2]]]]]; last first.
  - (* merged subject: nothing to show beyond conformance *)
    rewrite Dx in HxS. case: HxS => Eρ ET. subst ρ.
    have Hpush : spush σ Δs (σ x) = Some (SBoth (pole r (SSend T S2))).
      rewrite -ET.
      exact (spush_pair (x0 := x) (x1 := xc) Hv erefl Ec Hne Dx Dxc).
    move=> [|k] //. split.
    + split=> //.
      move=> a c Hof. case: (offers_del Hof) => -> -> /=.
      exists (SSend T S2). by rewrite /sat /= Hpush /= pole_invol.
    + move=> w rw S HwS.
      case: S HwS => [| |T' S2'|T' S2'|S1' S2''|S1' S2''] HwS /=.
      * move=> R HT. by case: (pinv_c_del HT).
      * move=> R HT. by case: (pinv_w_del HT).
      * split.
        -- move=> y' rd' R HT.
           case: (pinv_f_delF HT) => Ec' _ _.
           move: Ec' => -[E1 _]. subst w.
           by rewrite Hpush in HwS.
        -- move=> r' R HT. by case: (pinv_b_del HT).
      * split.
        -- move=> y' rd' R HT. by case: (pinv_r_del HT).
        -- move=> rd' R HT. by case: (pinv_r_del HT).
    + move=> b R HT. by case: (pinv_sel_del HT).
    + move=> b R HT. by case: (pinv_br_del HT).
    + move=> R Hst. by case: (pinv_t_del Hst).
  - (* solo subject *)
    have Hpush : spush σ Δs (σ x) = Some (SSep r (SSend T S2)).
      by rewrite (spush_solo (x := x) erefl Ho Huniq) HxS.
    have HuniqU : forall x', σ x' = σ x ->
        scupd x (Some (SSep r S2)) Δs x' <> None -> x' = x.
      move=> x' Ex'. rewrite /scupd.
      case Enx : (x' == x); first by move/eqP: Enx.
      exact: Huniq.
    move=> [|k] //. split.
    + split=> //.
      move=> a c Hof. case: (offers_del Hof) => -> -> /=.
      exists (SSend T S2).
      by rewrite /sat /= Hpush /= pol_eqb_refl.
    + move=> w rw S HwS.
      case: S HwS => [| |T' S2'|T' S2'|S1' S2''|S1' S2''] HwS /=.
      * move=> R HT. by case: (pinv_c_del HT).
      * move=> R HT. by case: (pinv_w_del HT).
      * split.
        -- (* the delegation itself *)
           move=> y' rd' R HT.
           case: (pinv_f_delF HT) => Ec' Ed' ->.
           move: Ec' Ed' => -[E1 E2] -[E3 E4]. subst w rw y' rd'.
           rewrite Hpush in HwS. case: HwS => ETT ES2. subst T' S2'.
           (* the payload slot: solo or merged *)
           case: (vok_split Hv Hoy)
             => [Huy|[yc [ρy [Ty [Hney Ecy Dy Dyc Huniqy2]]]]].
           ++ (* solo payload *)
              exists (SSep rd T). split.
              ** by rewrite (spush_solo (x := yp) erefl Hoy Huy) HyS.
              ** by rewrite /= pol_eqb_refl.
              ** have Hvk : vok σ
                     (scupd yp None (scupd x (Some (SSep r S2)) Δs)).
                   apply: vok_upd_none.
                   exact: vok_upd_solo Hv Huniq.
                 apply: EsemP_ext (IH _ _ Hvk k) => v.
                 have Huy' : forall x', σ x' = σ yp ->
                     scupd x (Some (SSep r S2)) Δs x' <> None ->
                     x' = yp.
                   move=> x' Ex'. rewrite /scupd.
                   case Enx : (x' == x).
                   +++ move/eqP: Enx Ex' => -> Ex' _.
                       by case: (Hsxy Ex').
                   +++ exact: Huy.
                 rewrite (spush_upd_none_solo (x := yp) _ Huy') /=;
                   last first.
                   rewrite /scupd.
                   case Enx : (yp == x);
                     first by move/eqP: Enx => E; case: (Hxy (esym E)).
                   by rewrite HyS.
                 by rewrite (scupd_under _ _
                      (fun q => spush_upd_some_solo (SSep r S2)
                                  Ho Huniq q)).
           ++ (* merged payload: delegate one end of a live pair *)
              rewrite Dy in HyS. case: HyS => Eρy ETy. subst ρy.
              have Hycx : yc <> x.
                move=> E. apply: Hsxy. by rewrite -E Ecy.
              have Hbyx : (yp : ch m) != x.
                by apply/eqP => E; apply: Hxy; rewrite E.
              have Hbyc : (yc : ch m) != x.
                by apply/eqP => E; apply: Hycx.
              exists (SBoth (pole rd Ty)). split.
              ** exact (spush_pair (x0 := yp) (x1 := yc)
                   Hv erefl Ecy Hney Dy Dyc).
              ** by rewrite /= pole_invol ETy.
              ** have Hvk : vok σ
                     (scupd yp None (scupd x (Some (SSep r S2)) Δs)).
                   apply: vok_upd_none.
                   exact: vok_upd_solo Hv Huniq.
                 apply: EsemP_ext (IH _ _ Hvk k) => v.
                 rewrite (spush_upd_none_pair
                     (Δs := scupd x (Some (SSep r S2)) Δs)
                     (x := yp) (xc := yc) (ρ := rd) (T := Ty)
                     (vok_upd_solo Hv Huniq) Hney (esym Ecy) _ _) //;
                   first last.
                 --- by rewrite (scupd_neq _ _ Hbyc) Dyc.
                 --- by rewrite (scupd_neq _ _ Hbyx) Dy.
                 --- rewrite (scupd_under _ _
                       (fun q => spush_upd_some_solo (SSep r S2)
                                   Ho Huniq q)).
                     rewrite (scupd_neq _ _ Hbyc) Dyc.
                     by rewrite /= pole_flip_pole.
        -- move=> r' R HT. by case: (pinv_b_del HT).
      * split.
        -- move=> y' rd' R HT. by case: (pinv_r_del HT).
        -- move=> rd' R HT. by case: (pinv_r_del HT).
    + move=> b R HT. by case: (pinv_sel_del HT).
    + move=> b R HT. by case: (pinv_br_del HT).
    + move=> R Hst. by case: (pinv_t_del Hst).
Qed.

(** ** σ-compatibility: receive

    The heart of the substitution form.  A fresh object extends σ; a
    fused object -- one whose co-end is already owned -- makes σ
    merge the payload binder with the co-end's preimage, and the
    continuation's induction hypothesis at that merging substitution
    is exactly the fuse obligation.  No standalone contraction lemma
    is needed. *)

Lemma fcompat_ins m n (σ : ren m n) (Δs : sctxP m) (x : ch m)
    (r rd : pol) T S2 (K : procP m.+1) :
  vok σ Δs ->
  Δs x = Some (SSep r (SRecv T S2)) ->
  (forall n' (σ' : ren m.+1 n'),
     vok σ' (scons (Some (SSep rd T)) (scupd x (Some (SSep r S2)) Δs)) ->
     SEMP (spush σ' (scons (Some (SSep rd T))
                       (scupd x (Some (SSep r S2)) Δs)))
       (psubst σ' K)) ->
  SEMP (spush σ Δs) (psubst σ ((x, r) ?( rd )․ K)).
Proof.
  move=> Hv HxS IH.
  have Ho : Δs x <> None by rewrite HxS.
  case: (vok_split Hv Ho)
    => [Huniq|[xc0 [ρ [T0 [Hne Ec Dx Dxc Huniq2]]]]]; last first.
  - (* merged subject *)
    rewrite Dx in HxS. case: HxS => Eρ ET. subst ρ.
    have Hpush : spush σ Δs (σ x) = Some (SBoth (pole r (SRecv T S2))).
      rewrite -ET.
      exact (spush_pair (x0 := x) (x1 := xc0) Hv erefl Ec Hne Dx Dxc).
    move=> [|k] //. split.
    + split=> //.
      move=> a c Hof. case: (offers_ins Hof) => -> -> /=.
      exists (SRecv T S2). by rewrite /sat /= Hpush /= pole_invol.
    + move=> w rw S HwS.
      case: S HwS => [| |T' S2'|T' S2'|S1' S2''|S1' S2''] HwS /=.
      * move=> R HT. by case: (pinv_c_ins HT).
      * move=> R HT. by case: (pinv_w_ins HT).
      * split.
        -- move=> y' rd' R HT. by case: (pinv_f_ins HT).
        -- move=> r' R HT. by case: (pinv_b_ins HT).
      * split.
        -- move=> y' rd' R HT.
           case: (pinv_r_insF HT) => Ec' _ _.
           move: Ec' => -[E1 _]. subst w.
           by rewrite Hpush in HwS.
        -- move=> rd' R HT.
           rewrite /= in HT.
           case: (pinv_r_insF HT) => Ec' _ _.
           move: Ec' => -[E1 _]. subst w.
           by rewrite Hpush in HwS.
    + move=> b R HT. by case: (pinv_sel_ins HT).
    + move=> b R HT. by case: (pinv_br_ins HT).
    + move=> R Hst. by case: (pinv_t_ins Hst).
  - (* solo subject *)
    have Hpush : spush σ Δs (σ x) = Some (SSep r (SRecv T S2)).
      by rewrite (spush_solo (x := x) erefl Ho Huniq) HxS.
    have HuniqU : forall x', σ x' = σ x ->
        scupd x (Some (SSep r S2)) Δs x' <> None -> x' = x.
      move=> x' Ex'. rewrite /scupd.
      case Enx : (x' == x); first by move/eqP: Enx.
      exact: Huniq.
    move=> [|k] //. split.
    + split=> //.
      move=> a c Hof. case: (offers_ins Hof) => -> -> /=.
      exists (SRecv T S2).
      by rewrite /sat /= Hpush /= pol_eqb_refl.
    + move=> w rw S HwS.
      case: S HwS => [| |T' S2'|T' S2'|S1' S2''|S1' S2''] HwS /=.
      * move=> R HT. by case: (pinv_c_ins HT).
      * move=> R HT. by case: (pinv_w_ins HT).
      * split.
        -- move=> y' rd' R HT. by case: (pinv_f_ins HT).
        -- move=> r' R HT. by case: (pinv_b_ins HT).
      * (* the receive *)
        split.
        -- move=> yi rd' R HT.
           case: (pinv_r_insF HT) => Ec' Erd' ->.
           move: Ec' => -[E1 E2]. subst w rw.
           rewrite /= in Erd'. subst rd'.
           rewrite Hpush in HwS. case: HwS => ETT ES2. subst T' S2'.
           rewrite psubst_recv_collapse.
           split.
           ++ (* fresh object *)
              move=> Hy.
              have Hfr := spush_none_inv Hy.
              have Hyx : yi <> σ x.
                move=> E. by rewrite E Hpush in Hy.
              have HfrU : forall x', σ x' = yi ->
                  scupd x (Some (SSep r S2)) Δs x' = None.
                move=> x' Ex'. rewrite /scupd.
                case Enx : (x' == x).
                ** move/eqP: Enx Ex' => -> Ex'.
                   by case: (Hyx (esym Ex')).
                ** exact: Hfr.
              have Hvk : vok (scons yi σ)
                  (scons (Some (SSep rd T))
                     (scupd x (Some (SSep r S2)) Δs)).
                apply: vok_scons_fresh HfrU.
                exact: vok_upd_solo Hv Huniq.
              apply: EsemP_ext (IH _ _ Hvk k) => v.
              rewrite (spush_scons_fresh (Some (SSep rd T))
                         HfrU v).
              rewrite (scupd_under _ _
                (fun q => spush_upd_some_solo (SSep r S2)
                            Ho Huniq q)).
              by [].
           ++ (* fused object: the continuation at the merging σ *)
              move=> Hy.
              case: (spush_sep_inv Hv Hy) => xc [Exc Dxcy Hucy].
              have Hyx : yi <> σ x.
                move=> E. rewrite E Hpush in Hy. case: Hy => _ ED.
                have := f_equal dual ED.
                rewrite dual_involutive /= => ED'.
                by case: (ssend_neqT (esym ED')).
              have Hxcx : xc <> x.
                move=> E. rewrite E HxS in Dxcy. case: Dxcy => _ ED.
                have := f_equal dual ED.
                rewrite dual_involutive /= => ED'.
                by case: (ssend_neqT (esym ED')).
              have Hbxc : (xc : ch m) != x by apply/eqP.
              have HucU : forall x', σ x' = yi ->
                  scupd x (Some (SSep r S2)) Δs x' <> None -> x' = xc.
                move=> x' Ex'. rewrite /scupd.
                case Enx : (x' == x).
                ** move/eqP: Enx Ex' => -> Ex' _.
                   by case: (Hyx (esym Ex')).
                ** exact: Hucy.
              have Hvk : vok (scons yi σ)
                  (scons (Some (SSep rd T))
                     (scupd x (Some (SSep r S2)) Δs)).
                apply: (vok_scons_fuse (xc := xc)) => //.
                +++ exact: vok_upd_solo Hv Huniq.
                +++ by rewrite (scupd_neq _ _ Hbxc) Dxcy.
              apply: EsemP_ext (IH _ _ Hvk k) => v.
              rewrite (spush_scons_fuse (xc := xc) Hvk Exc _ v);
                last first.
                by rewrite (scupd_neq _ _ Hbxc) Dxcy.
              rewrite (scupd_under _ _
                (fun q => spush_upd_some_solo (SSep r S2)
                            Ho Huniq q)).
              by [].
        -- (* shifted object *)
           move=> rd' R HT.
           rewrite /= in HT.
           case: (pinv_r_insF HT) => Ec' Erd' ER.
           move: Ec' => -[E1 E2]. subst w rw.
           rewrite /= in Erd'. subst rd'.
           rewrite Hpush in HwS. case: HwS => ETT ES2. subst T' S2'.
           have ER' : R = psubst (up_ch σ) K.
             rewrite ER !psubst_comp.
             by apply: psubst_ext => -[z|].
           rewrite ER'.
           have Hvk : vok (up_ch σ)
               (scons (Some (SSep rd T))
                  (scupd x (Some (SSep r S2)) Δs)).
             apply: vok_up_scons.
             exact: vok_upd_solo Hv Huniq.
           apply: EsemP_ext (IH _ _ Hvk k) => v.
           rewrite (spush_up_scons σ
                      (scupd x (Some (SSep r S2)) Δs)
                      (Some (SSep rd T)) v).
           case: v => [v|] //=.
           rewrite (spush_upd_some_solo (SSep r S2) Ho Huniq v).
           by [].
    + move=> b R HT. by case: (pinv_sel_ins HT).
    + move=> b R HT. by case: (pinv_br_ins HT).
    + move=> R Hst. by case: (pinv_t_ins Hst).
Qed.

Print Assumptions fcompat_ins.

(** ** σ-compatibility: selection and branching *)

Lemma fcompat_sel m n (σ : ren m n) (Δs : sctxP m) (x : ch m)
    (r : pol) (b : bool) S1 S2 (K : procP m) :
  vok σ Δs ->
  Δs x = Some (SSep r (SSel S1 S2)) ->
  (forall n' (σ' : ren m n'),
     vok σ' (scupd x (Some (SSep r (if b then S1 else S2))) Δs) ->
     SEMP (spush σ' (scupd x (Some (SSep r (if b then S1 else S2))) Δs))
       (psubst σ' K)) ->
  SEMP (spush σ Δs) (psubst σ ((x, r) ◁ b ․ K)).
Proof.
  move=> Hv HxS IH.
  have Ho : Δs x <> None by rewrite HxS.
  case: (vok_split Hv Ho)
    => [Huniq|[xc [ρ [T [Hne Ec Dx Dxc Huniq2]]]]].
  - have Hpush : spush σ Δs (σ x) = Some (SSep r (SSel S1 S2)).
      by rewrite (spush_solo (x := x) erefl Ho Huniq) HxS.
    move=> [|k] //. split.
    + split=> //.
      move=> a c Hof. case: (offers_sel Hof) => -> -> /=.
      exists (SSel S1 S2). by rewrite /sat /= Hpush /= pol_eqb_refl.
    + move=> w rw S HwS.
      case: S HwS => [| |T' S2'|T' S2'|S1' S2''|S1' S2''] HwS /=.
      * move=> R HT. by case: (pinv_c_sel HT).
      * move=> R HT. by case: (pinv_w_sel HT).
      * split.
        -- move=> y' rd' R HT. by case: (pinv_f_sel HT).
        -- move=> r' R HT. by case: (pinv_b_sel HT).
      * split.
        -- move=> y' rd' R HT. by case: (pinv_r_sel HT).
        -- move=> rd' R HT. by case: (pinv_r_sel HT).
      * move=> b' R HT.
        case: (pinv_sel_selF HT) => Ec' Eb ->.
        move: Ec' => -[E1 E2]. subst w rw b'.
        rewrite Hpush in HwS. case: HwS => ES1 ES2. subst S1' S2''.
        apply: EsemP_ext
          (IH _ _ (vok_upd_solo (e := SSep r (if b then S1 else S2))
                     Hv Huniq) k) => v.
        by rewrite (spush_upd_some_solo
             (SSep r (if b then S1 else S2)) Ho Huniq v).
      * move=> b' R HT. by case: (pinv_br_sel HT).
    + move=> R Hst. by case: (pinv_t_sel Hst).
  - rewrite Dx in HxS. case: HxS => Eρ ET. subst ρ.
    have Hpush : spush σ Δs (σ x) = Some (SBoth (pole r (SSel S1 S2))).
      rewrite -ET.
      exact (spush_pair (x0 := x) (x1 := xc) Hv erefl Ec Hne Dx Dxc).
    move=> [|k] //. split.
    + split=> //.
      move=> a c Hof. case: (offers_sel Hof) => -> -> /=.
      exists (SSel S1 S2). by rewrite /sat /= Hpush /= pole_invol.
    + move=> w rw S HwS.
      case: S HwS => [| |T' S2'|T' S2'|S1' S2''|S1' S2''] HwS /=.
      * move=> R HT. by case: (pinv_c_sel HT).
      * move=> R HT. by case: (pinv_w_sel HT).
      * split.
        -- move=> y' rd' R HT. by case: (pinv_f_sel HT).
        -- move=> r' R HT. by case: (pinv_b_sel HT).
      * split.
        -- move=> y' rd' R HT. by case: (pinv_r_sel HT).
        -- move=> rd' R HT. by case: (pinv_r_sel HT).
      * move=> b' R HT.
        case: (pinv_sel_selF HT) => Ec' _ _.
        move: Ec' => -[E1 _]. subst w.
        by rewrite Hpush in HwS.
      * move=> b' R HT. by case: (pinv_br_sel HT).
    + move=> R Hst. by case: (pinv_t_sel Hst).
Qed.

Lemma fcompat_bra m n (σ : ren m n) (Δs Δ1' Δ2' : sctxP m)
    (x : ch m) (r : pol) S1 S2 (K1 K2 : procP m) :
  vok σ Δs ->
  Δs x = Some (SSep r (SBra S1 S2)) ->
  sevolve Δs Δ1' ->
  sevolve Δs Δ2' ->
  (forall n' (σ' : ren m n'),
     vok σ' (scupd x (Some (SSep r S1)) Δ1') ->
     SEMP (spush σ' (scupd x (Some (SSep r S1)) Δ1')) (psubst σ' K1)) ->
  (forall n' (σ' : ren m n'),
     vok σ' (scupd x (Some (SSep r S2)) Δ2') ->
     SEMP (spush σ' (scupd x (Some (SSep r S2)) Δ2')) (psubst σ' K2)) ->
  SEMP (spush σ Δs) (psubst σ ((x, r) ▷ ( K1 | K2 ))).
Proof.
  move=> Hv HxS Hev1 Hev2 IH1 IH2.
  have Ho : Δs x <> None by rewrite HxS.
  have Hx1 : Δ1' x = Some (SSep r (SBra S1 S2)).
    case: (Hev1 x) => [->|[S0 [S0' [E _]]]] //. by rewrite E in HxS.
  have Hx2 : Δ2' x = Some (SSep r (SBra S1 S2)).
    case: (Hev2 x) => [->|[S0 [S0' [E _]]]] //. by rewrite E in HxS.
  have Hv1 := vok_sevolve Hv Hev1.
  have Hv2 := vok_sevolve Hv Hev2.
  have Ho1 : Δ1' x <> None by rewrite Hx1.
  have Ho2 : Δ2' x <> None by rewrite Hx2.
  case: (vok_split Hv Ho)
    => [Huniq|[xc [ρ [T [Hne Ec Dx Dxc Huniq2]]]]].
  - have Hpush : spush σ Δs (σ x) = Some (SSep r (SBra S1 S2)).
      by rewrite (spush_solo (x := x) erefl Ho Huniq) HxS.
    have Huniq1 : forall x', σ x' = σ x -> Δ1' x' <> None -> x' = x.
      move=> x' Ex' Hox'.
      apply: Huniq => //.
      case: (Hev1 x') Hox' => [<-|[S0 [S0' [E _]]]] //.
      by rewrite E.
    have Huniq2' : forall x', σ x' = σ x -> Δ2' x' <> None -> x' = x.
      move=> x' Ex' Hox'.
      apply: Huniq => //.
      case: (Hev2 x') Hox' => [<-|[S0 [S0' [E _]]]] //.
      by rewrite E.
    move=> [|k] //. split.
    + split=> //.
      move=> a c Hof. case: (offers_bra Hof) => -> -> /=.
      exists (SBra S1 S2). by rewrite /sat /= Hpush /= pol_eqb_refl.
    + move=> w rw S HwS.
      case: S HwS => [| |T' S2'|T' S2'|S1' S2''|S1' S2''] HwS /=.
      * move=> R HT. by case: (pinv_c_bra HT).
      * move=> R HT. by case: (pinv_w_bra HT).
      * split.
        -- move=> y' rd' R HT. by case: (pinv_f_bra HT).
        -- move=> r' R HT. by case: (pinv_b_bra HT).
      * split.
        -- move=> y' rd' R HT. by case: (pinv_r_bra HT).
        -- move=> rd' R HT. by case: (pinv_r_bra HT).
      * move=> b' R HT. by case: (pinv_sel_bra HT).
      * (* the branch: commit the chosen refinement *)
        move=> b R HT.
        case: (pinv_br_braF HT) => Ec' ->.
        move: Ec' => -[E1 E2]. subst w rw.
        rewrite Hpush in HwS. case: HwS => ES1 ES2. subst S1' S2''.
        clear HT. case: b.
        -- exists (spush σ Δ1'). split.
             exact: spush_sevolve_sev Hv Hev1.
           apply: EsemP_ext
             (IH1 _ _ (vok_upd_solo (e := SSep r S1) Hv1 Huniq1) k)
             => v.
           by rewrite (spush_upd_some_solo (SSep r S1) Ho1 Huniq1 v).
        -- exists (spush σ Δ2'). split.
             exact: spush_sevolve_sev Hv Hev2.
           apply: EsemP_ext
             (IH2 _ _ (vok_upd_solo (e := SSep r S2) Hv2 Huniq2') k)
             => v.
           by rewrite (spush_upd_some_solo (SSep r S2) Ho2 Huniq2' v).
    + move=> R Hst. by case: (pinv_t_bra Hst).
  - rewrite Dx in HxS. case: HxS => Eρ ET. subst ρ.
    have Hpush : spush σ Δs (σ x) = Some (SBoth (pole r (SBra S1 S2))).
      rewrite -ET.
      exact (spush_pair (x0 := x) (x1 := xc) Hv erefl Ec Hne Dx Dxc).
    move=> [|k] //. split.
    + split=> //.
      move=> a c Hof. case: (offers_bra Hof) => -> -> /=.
      exists (SBra S1 S2). by rewrite /sat /= Hpush /= pole_invol.
    + move=> w rw S HwS.
      case: S HwS => [| |T' S2'|T' S2'|S1' S2''|S1' S2''] HwS /=.
      * move=> R HT. by case: (pinv_c_bra HT).
      * move=> R HT. by case: (pinv_w_bra HT).
      * split.
        -- move=> y' rd' R HT. by case: (pinv_f_bra HT).
        -- move=> r' R HT. by case: (pinv_b_bra HT).
      * split.
        -- move=> y' rd' R HT. by case: (pinv_r_bra HT).
        -- move=> rd' R HT. by case: (pinv_r_bra HT).
      * move=> b' R HT. by case: (pinv_sel_bra HT).
      * move=> b R HT.
        case: (pinv_br_braF HT) => Ec' _.
        move: Ec' => -[E1 _]. subst w.
        by rewrite Hpush in HwS.
    + move=> R Hst. by case: (pinv_t_bra Hst).
Qed.

(** ** σ-compatibility: nil, parallel, restriction *)

Lemma fcompat_end m n (σ : ren m n) (Δs : sctxP m) :
  (forall x, Δs x = None) ->
  SEMP (spush σ Δs) (psubst σ (∅ : procP m)).
Proof.
  move=> HD.
  apply: compat_endP => w.
  apply: spush_none_fwd => x _. exact: HD.
Qed.

Lemma fcompat_res m n (σ : ren m n) (Δs : sctxP m) (S : sty)
    (B : procP m.+1) :
  (forall n' (σ' : ren m.+1 n'),
     vok σ' (scons (Some (SBoth S)) Δs) ->
     SEMP (spush σ' (scons (Some (SBoth S)) Δs)) (psubst σ' B)) ->
  vok σ Δs ->
  SEMP (spush σ Δs) (psubst σ ((ν) B)).
Proof.
  move=> IH Hv k.
  apply: (compat_resP (S := S)).
  have HB := IH _ (up_ch σ) (vok_up_scons (e0 := Some (SBoth S)) Hv) k.
  apply: EsemP_ext HB => v.
  by rewrite (spush_up_scons σ Δs (Some (SBoth S)) v).
Qed.

(** The parallel case: with one substitution on both sides, the
    pushed component contexts merge to the pushed composite.  The
    typing link at [z] becomes a [dmerge] live link. *)

Lemma fcompat_par m n (σ : ren m n) (Δs Δs1 Δs2 : sctxP m)
    (z : ch m) (r : pol) T (P Q : procP m) :
  vok σ Δs ->
  Δs1 z = Some (SSep r T) ->
  Δs2 z = Some (SSep (flipp r) (dual T)) ->
  (forall x, x != z ->
     (Δs1 x = None /\ Δs x = Δs2 x) \/ (Δs2 x = None /\ Δs x = Δs1 x)) ->
  Δs z = Some (SBoth (pole r T)) ->
  (forall n' (σ' : ren m n'), vok σ' Δs1 ->
     SEMP (spush σ' Δs1) (psubst σ' P)) ->
  (forall n' (σ' : ren m n'), vok σ' Δs2 ->
     SEMP (spush σ' Δs2) (psubst σ' Q)) ->
  SEMP (spush σ Δs) (psubst σ (P ∥ Q)).
Proof.
  move=> Hv Dz1 Dz2 HF Dz IH1 IH2.
  (* component ownership embeds into the composite *)
  have Hsub1 : forall x, Δs1 x <> None -> Δs x <> None.
    move=> x Ho1.
    case Exz : (x == z).
    + move/eqP: Exz => ->. by rewrite Dz.
    + have Hne : x != z by rewrite Exz.
      case: (HF _ Hne) => -[Ea Eb]; first by rewrite Ea in Ho1.
      by rewrite Eb.
  have Hsub2 : forall x, Δs2 x <> None -> Δs x <> None.
    move=> x Ho2.
    case Exz : (x == z).
    + move/eqP: Exz => ->. by rewrite Dz.
    + have Hne : x != z by rewrite Exz.
      case: (HF _ Hne) => -[Ea Eb]; last by rewrite Ea in Ho2.
      by rewrite Eb.
  (* slots transfer off the link *)
  have Hslot1 : forall x, x != z -> Δs1 x <> None -> Δs x = Δs1 x.
    move=> x Hne Ho1.
    case: (HF _ Hne) => -[Ea Eb]; first by rewrite Ea in Ho1.
    exact: Eb.
  have Hslot2 : forall x, x != z -> Δs2 x <> None -> Δs x = Δs2 x.
    move=> x Hne Ho2.
    case: (HF _ Hne) => -[Ea Eb]; last by rewrite Ea in Ho2.
    exact: Eb.
  (* component validity *)
  have Hv1 : vok σ Δs1.
    move=> x1 x2 H1 H2 E.
    case: (Hv x1 x2 (Hsub1 _ H1) (Hsub1 _ H2) E) => [-> | ]; first by left.
    move=> [ρ' [T' [Da Db]]].
    have Enz1 : x1 != z.
      apply/eqP => Ez. by rewrite Ez Dz in Da.
    have Enz2 : x2 != z.
      apply/eqP => Ez. by rewrite Ez Dz in Db.
    right. exists ρ', T'.
    by rewrite -(Hslot1 _ Enz1 H1) -(Hslot1 _ Enz2 H2).
  have Hv2 : vok σ Δs2.
    move=> x1 x2 H1 H2 E.
    case: (Hv x1 x2 (Hsub2 _ H1) (Hsub2 _ H2) E) => [-> | ]; first by left.
    move=> [ρ' [T' [Da Db]]].
    have Enz1 : x1 != z.
      apply/eqP => Ez. by rewrite Ez Dz in Da.
    have Enz2 : x2 != z.
      apply/eqP => Ez. by rewrite Ez Dz in Db.
    right. exists ρ', T'.
    by rewrite -(Hslot2 _ Enz1 H1) -(Hslot2 _ Enz2 H2).
  (* the pushed merge *)
  have Hm : dmerge (spush σ Δs1) (spush σ Δs2) (spush σ Δs).
    move=> w.
    case E : (spush σ Δs w) => [e|]; last first.
    - (* composite silent: both components silent *)
      have E1 : spush σ Δs1 w = None.
        apply: spush_none_fwd => x Ex.
        case E1 : (Δs1 x) => [e1|] //.
        have := spush_none_inv E Ex.
        move=> ED. case: (Hsub1 x _ ED). by rewrite E1.
      have E2 : spush σ Δs2 w = None.
        apply: spush_none_fwd => x Ex.
        case E2 : (Δs2 x) => [e2|] //.
        have := spush_none_inv E Ex.
        move=> ED. case: (Hsub2 x _ ED). by rewrite E2.
      apply: Or41. by rewrite E1 E2.
    - (* composite owned at w *)
      have [x0 [Ex0 Hox0]] : exists x0, σ x0 = w /\ Δs x0 <> None.
        apply: spush_owned_inv. by rewrite E.
      case Ez0 : (x0 == z).
      + (* the link name *)
        move/eqP: Ez0 Ex0 Hox0 => -> Ex0 Hox0.
        have Hz1 : Δs1 z <> None by rewrite Dz1.
        have Hz2 : Δs2 z <> None by rewrite Dz2.
        have Huz : forall x', σ x' = w -> Δs x' <> None -> x' = z.
          move=> x' Ex' Hox'.
          case: (Hv x' z Hox' _ _) => //.
            by rewrite Ex' Ex0.
          move=> [ρ' [T' [_ Db]]].
          by rewrite Dz in Db; case: Db.
        have Huz1 : forall x', σ x' = w -> Δs1 x' <> None -> x' = z.
          move=> x' Ex' H1. exact: Huz Ex' (Hsub1 _ H1).
        have Huz2 : forall x', σ x' = w -> Δs2 x' <> None -> x' = z.
          move=> x' Ex' H1. exact: Huz Ex' (Hsub2 _ H1).
        apply: Or43. exists r, T.
        rewrite (spush_solo (x := z) Ex0 Hz1 Huz1) Dz1.
        rewrite (spush_solo (x := z) Ex0 Hz2 Huz2) Dz2.
        by rewrite (spush_solo (x := z) Ex0 Hox0 Huz) Dz in E;
          case: E => <-.
      + (* a frame name *)
        have Hnez : x0 != z by rewrite Ez0.
        (* second composite preimage? *)
        case: (vok_split Hv Hox0)
          => [Huniq|[xc [ρc [Tc [Hnec Ecc Dc0 Dcc Hu2]]]]].
        * (* solo in the composite *)
          case: (HF _ Hnez) => -[Ea Eb].
          -- (* owned by the right component *)
             have Ho2 : Δs2 x0 <> None by rewrite -Eb.
             apply: Or42.
             have E1 : spush σ Δs1 w = None.
               apply: spush_none_fwd => x Ex.
               case E1 : (Δs1 x) => [e1|] //.
               have Exx : x = x0.
                 apply: Huniq; first by rewrite Ex Ex0.
                 apply: Hsub1. by rewrite E1.
               by rewrite Exx Ea in E1.
             have Hu2' : forall x', σ x' = w -> Δs2 x' <> None -> x' = x0.
               move=> x' Ex' H2.
               apply: Huniq; first by rewrite Ex' Ex0.
               exact: Hsub2.
             rewrite E1 (spush_solo (x := x0) Ex0 Ho2 Hu2') -Eb.
             rewrite -Ex0 in E.
             by rewrite (spush_solo (x := x0) erefl Hox0 Huniq) in E;
               rewrite E.
          -- (* owned by the left component *)
             have Ho1 : Δs1 x0 <> None by rewrite -Eb.
             apply: Or41.
             have E2 : spush σ Δs2 w = None.
               apply: spush_none_fwd => x Ex.
               case E2 : (Δs2 x) => [e2|] //.
               have Exx : x = x0.
                 apply: Huniq; first by rewrite Ex Ex0.
                 apply: Hsub2. by rewrite E2.
               by rewrite Exx Ea in E2.
             have Hu1' : forall x', σ x' = w -> Δs1 x' <> None -> x' = x0.
               move=> x' Ex' H1.
               apply: Huniq; first by rewrite Ex' Ex0.
               exact: Hsub1.
             rewrite E2 (spush_solo (x := x0) Ex0 Ho1 Hu1') -Eb.
             rewrite -Ex0 in E.
             by rewrite (spush_solo (x := x0) erefl Hox0 Huniq) in E;
               rewrite E.
        * (* a merged pair in the composite *)
          have Hnczz : xc != z.
            apply/eqP => Ez. by rewrite Ez Dz in Dcc.
          have Hoc : Δs xc <> None by rewrite Dcc.
          (* place each end in its component *)
          have Hplace : forall (xa : ch m) ρa Ta, xa != z ->
              Δs xa = Some (SSep ρa Ta) ->
              (Δs1 xa = Some (SSep ρa Ta) /\ Δs2 xa = None)
              \/ (Δs2 xa = Some (SSep ρa Ta) /\ Δs1 xa = None).
            move=> xa ρa Ta Hnea Da.
            case: (HF _ Hnea) => -[Ea Eb].
            + right. split=> //. by rewrite -Eb.
            + left. split=> //. by rewrite -Eb.
          have Exc0 : σ xc = w by rewrite Ecc Ex0.
          have EC : spush σ Δs w = Some (SBoth (pole ρc Tc)).
            exact (spush_pair (x0 := x0) (x1 := xc)
                     Hv Ex0 Exc0 Hnec Dc0 Dcc).
          rewrite E in EC. case: EC => Ee. subst e.
          case: (Hplace _ _ _ Hnez Dc0) => -[Pa1 Pa2];
            case: (Hplace _ _ _ Hnczz Dcc) => -[Pb1 Pb2].
          -- (* both ends on the left *)
             apply: Or41.
             have E2 : spush σ Δs2 w = None.
               apply: spush_none_fwd => x Ex.
               case E2 : (Δs2 x) => [e2|] //.
               have : x = x0 \/ x = xc.
                 apply: Hu2; first by rewrite Ex Ex0.
                 apply: Hsub2. by rewrite E2.
               by case=> Exx; rewrite Exx ?Pa2 ?Pb2 in E2.
             have E1 : spush σ Δs1 w = Some (SBoth (pole ρc Tc)).
               exact (spush_pair (x0 := x0) (x1 := xc)
                        Hv1 Ex0 Exc0 Hnec Pa1 Pb1).
             split; first exact: E2.
             by rewrite E1.
          -- (* split pair: x0 on the left, xc on the right *)
             apply: Or43. exists ρc, Tc.
             have Ho1 : Δs1 x0 <> None by rewrite Pa1.
             have Ho2 : Δs2 xc <> None by rewrite Pb1.
             have Hu1' : forall x', σ x' = w -> Δs1 x' <> None ->
                 x' = x0.
               move=> x' Ex' H1.
               have : x' = x0 \/ x' = xc.
                 apply: Hu2; first by rewrite Ex' Ex0.
                 exact: Hsub1.
               case=> // Exx. by rewrite Exx Pb2 in H1.
             have Hu2' : forall x', σ x' = w -> Δs2 x' <> None ->
                 x' = xc.
               move=> x' Ex' H2.
               have : x' = x0 \/ x' = xc.
                 apply: Hu2; first by rewrite Ex' Ex0.
                 exact: Hsub2.
               case=> // Exx. by rewrite Exx Pa2 in H2.
             rewrite (spush_solo (x := x0) Ex0 Ho1 Hu1') Pa1.
             rewrite (spush_solo (x := xc) Exc0 Ho2 Hu2') Pb1.
             by split.
          -- (* split pair: xc on the left, x0 on the right *)
             apply: Or43. exists (flipp ρc), (dual Tc).
             have Ho1 : Δs1 xc <> None by rewrite Pb1.
             have Ho2 : Δs2 x0 <> None by rewrite Pa1.
             have Hu1' : forall x', σ x' = w -> Δs1 x' <> None ->
                 x' = xc.
               move=> x' Ex' H1.
               have : x' = x0 \/ x' = xc.
                 apply: Hu2; first by rewrite Ex' Ex0.
                 exact: Hsub1.
               case=> // Exx. by rewrite Exx Pa2 in H1.
             have Hu2' : forall x', σ x' = w -> Δs2 x' <> None ->
                 x' = x0.
               move=> x' Ex' H2.
               have : x' = x0 \/ x' = xc.
                 apply: Hu2; first by rewrite Ex' Ex0.
                 exact: Hsub2.
               case=> // Exx. by rewrite Exx Pb2 in H2.
             rewrite (spush_solo (x := xc) Exc0 Ho1 Hu1') Pb1.
             rewrite (spush_solo (x := x0) Ex0 Ho2 Hu2') Pa1.
             rewrite flipp_invol dual_involutive pole_flip_dual.
             by split.
          -- (* both ends on the right *)
             apply: Or42.
             have E1 : spush σ Δs1 w = None.
               apply: spush_none_fwd => x Ex.
               case E1 : (Δs1 x) => [e1|] //.
               have : x = x0 \/ x = xc.
                 apply: Hu2; first by rewrite Ex Ex0.
                 apply: Hsub1. by rewrite E1.
               by case=> Exx; rewrite Exx ?Pa2 ?Pb2 in E1.
             have E2 : spush σ Δs2 w = Some (SBoth (pole ρc Tc)).
               exact (spush_pair (x0 := x0) (x1 := xc)
                        Hv2 Ex0 Exc0 Hnec Pa1 Pb1).
             split; first exact: E1.
             by rewrite E2.
  (* conclude by the parallel combination *)
  move=> k.
  apply: (combineP (Δ1 := spush σ Δs1) (Δ2 := spush σ Δs2)) => //.
  - exact: IH1.
  - exact: IH2.
Qed.

(** ** The fundamental theorem *)

Theorem fundamentalP m (Δs : sctxP m) (P : procP m) :
  stypedP Δs P ->
  forall n (σ : ren m n), vok σ Δs ->
  SEMP (spush σ Δs) (psubst σ P).
Proof.
  elim=> {m Δs P}.
  - move=> m Δ HD n σ Hv. exact: fcompat_end.
  - move=> m Δ x r K HxS _ IH n σ Hv.
    exact: fcompat_close Hv HxS IH.
  - move=> m Δ x r K HxS _ IH n σ Hv.
    exact: fcompat_wait Hv HxS IH.
  - move=> m Δ x yp r rd T S2 K HxS HyS _ IH n σ Hv.
    exact: fcompat_del Hv HxS HyS IH.
  - move=> m Δ x r rd T S2 K HxS _ IH n σ Hv.
    exact: fcompat_ins Hv HxS IH.
  - move=> m Δ Δ1 Δ2 z r T P Q _ IH1 _ IH2 Dz1 Dz2 HF Dz n σ Hv.
    exact: fcompat_par Hv Dz1 Dz2 HF Dz IH1 IH2.
  - move=> m Δ S B _ IH n σ Hv.
    exact: fcompat_res IH Hv.
  - move=> m Δ x r b S1 S2 K HxS _ IH n σ Hv.
    exact: fcompat_sel Hv HxS IH.
  - move=> m Δ Δ1' Δ2' x r S1 S2 K1 K2 HxS Hev1 Hev2 _ IH1 _ IH2 n σ Hv.
    exact: fcompat_bra Hv HxS Hev1 Hev2 IH1 IH2.
Qed.

Print Assumptions fundamentalP.

(** ** The identity instance *)

Lemma vok_id m (Δs : sctxP m) : vok id_ren Δs.
Proof. move=> x1 x2 _ _ E. by left. Qed.

Lemma spush_id m (Δs : sctxP m) w : spush id_ren Δs w = Δs w.
Proof.
  case E : (Δs w) => [e|].
  - rewrite -E.
    apply: (spush_solo (x := w)) => //; first by rewrite E.
  - have Hfr : forall x : ch m, id_ren x = w -> Δs x = None.
      move=> x Ex. move: Ex. rewrite /id_ren => ->. exact: E.
    exact: (spush_none_fwd Hfr).
Qed.

(** ** End-to-end: typed processes are safe *)

Theorem fundamental_typedP m (Γ : pctx m) (P : procP m) :
  typedP Γ P ->
  exists Δs : sctxP m,
    (forall x, eraseS (Δs x) = Γ x) /\ SEMP Δs P.
Proof.
  move=> Ht.
  case: (typed_styped Ht) => Δs [HE Hst].
  exists Δs. split=> //.
  have := fundamentalP Hst (@vok_id m Δs).
  rewrite psubst_id.
  move=> HS k.
  apply: EsemP_ext (HS k) => v. exact: spush_id.
Qed.

Theorem safe_typedP m (Γ : pctx m) (P : procP m) :
  typedP Γ P -> safeP P.
Proof.
  move=> Ht.
  case: (fundamental_typedP Ht) => Δs [_ HS].
  exact: adequacyP HS.
Qed.

Print Assumptions fundamental_typedP.
Print Assumptions safe_typedP.

(** ** Sanity: a choice cut, typed and hence safe *)

Example choice_cut_typed :
  typedP pcempty
    ((ν) ( ((zero, pos) ◁ true ․ ((zero, pos) !․ ∅))
         ∥ ((zero, neg) ▷ ( ((zero, neg) ?․ ∅)
                          | ((zero, neg) ?․ ∅) )) ) : procP 0).
Proof.
  apply: TP_Res.
  apply: (TP_Par
    (Δ1 := scons (Some (Sep pos (SSel SClose SClose))) pcempty)
    (Δ2 := scons (Some (Sep neg (SBra SWait SWait))) pcempty)
    (z := zero) (r := pos) (T := SSel SClose SClose)) => //.
  - apply: (TP_Sel (b := true) (S1 := SClose) (S2 := SClose)) => //.
    apply: TP_Close.
    { rewrite /pcupd. by case: eqP. }
    apply: TP_End => -[[]|] //=.
  - apply: (TP_Bra (S1 := SWait) (S2 := SWait)) => //.
    + apply: TP_Wait.
      { rewrite /pcupd. by case: eqP. }
      apply: TP_End => -[[]|] //=.
    + apply: TP_Wait.
      { rewrite /pcupd. by case: eqP. }
      apply: TP_End => -[[]|] //=.
  - by move=> [[]|].
Qed.

Example choice_cut_safe :
  safeP ((ν) ( ((zero, pos) ◁ true ․ ((zero, pos) !․ ∅))
             ∥ ((zero, neg) ▷ ( ((zero, neg) ?․ ∅)
                              | ((zero, neg) ?․ ∅) )) ) : procP 0).
Proof. exact: safe_typedP choice_cut_typed. Qed.

Print Assumptions choice_cut_safe.
