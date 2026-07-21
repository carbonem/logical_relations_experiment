(** * σ-parametric compatibility for the split-context system

    The fundamental theorem is stated for OPEN terms under name
    substitutions that may MERGE the two ends of a session
    ([PolBridge.v] supplies the semantic typing it inducts on).  This
    file carries the machinery: valid substitutions [vok], the
    pushforward [spush] of a semantic context along one, and one
    compatibility lemma per semantic typing rule.

    What changed from the cut-based development: [fcompat_par] no
    longer takes a single link plus a disjoint frame.  It takes the
    merge relation [dmerge] itself -- the same one [combineP] consumes
    -- and the work is [dmerge_spush], which pushes a merge forward
    along a substitution.  Two sessions may now cross one parallel
    composition, and a substitution may in addition merge two ends
    that the split had put on OPPOSITE sides: that is the case where
    a live link is created by the substitution rather than by the
    typing. *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Eqdep_dec PeanoNat.
From Tait Require Import PolBase PolTypes PolProc PolLTS PolErr PolTyping
  PolLogRel PolEquiv PolCompat PolSem PolComb PolBridge.

Set Implicit Arguments.
Unset Strict Implicit.
Open Scope pol_scope.

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

Lemma spush_both_inv m n (σ : ren m n) (Δs : sctxP m) w S0 :
  vok σ Δs ->
  spush σ Δs w = Some (SBoth S0) ->
  (exists x,
    [/\ σ x = w, Δs x = Some (SBoth S0)
      & forall x', σ x' = w -> Δs x' <> None -> x' = x])
  \/ (exists x0 x1 ρ T,
       [/\ σ x0 = w, σ x1 = w, x0 <> x1,
           Δs x0 = Some (SSep ρ T) /\ Δs x1 = Some (SSep (flipp ρ) (dual T))
         & S0 = pole ρ T]).
Proof.
  move=> Hv. rewrite /spush.
  case F : (find_ch (fun x => (σ x == w) && ~~ oslot_eqb (Δs x) None))
    => [x0|] //.
  move: (find_ch_sound F) => /spush_p1 [E0 Ho0].
  case F2 : (find_ch (fun x' => [&& σ x' == w,
                ~~ oslot_eqb (Δs x') None & x' != x0])) => [x1|].
  - move: (find_ch_sound F2) => /and3P[/eqP E1 Ho1 Hne1].
    have Hox1 : Δs x1 <> None.
      by case: (oslot_eqP (Δs x1) None) Ho1.
    have Hne : x0 <> x1.
      by move=> E; move: Hne1; rewrite E eqxx.
    case: (Hv x0 x1 Ho0 Hox1 _).
      by rewrite E0 E1.
      by move=> E; case: (Hne E).
    move=> [ρ [T [D0 D1]]].
    rewrite D0. move=> [ES0].
    right. exists x0, x1, ρ, T. by split.
  - move=> ED. left. exists x0. split=> //.
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

(** ** Pushing a merge forward along a substitution

    [combineP] consumes a [dmerge]; the fundamental theorem's parallel
    case must therefore produce one between the PUSHED contexts.  The
    delicate case is the last: the split may have put the two ends of
    a session on opposite sides, and the substitution may in addition
    merge two names -- so a live link can be created by σ rather than
    by the typing. *)

(** Ownership transfers from a component to the composite. *)
Lemma dmerge_ownL n (Δ1 Δ2 Δ : sctxP n) x :
  dmerge Δ1 Δ2 Δ -> Δ1 x <> None -> Δ x <> None.
Proof.
  move=> Hm H1. case: (Hm x).
  - by move=> [_ ->].
  - by move=> [E _]; rewrite E in H1.
  - by move=> [ρ [T [_ _ ->]]].
  - by move=> [E _]; rewrite E in H1.
Qed.

Lemma dmerge_ownR n (Δ1 Δ2 Δ : sctxP n) x :
  dmerge Δ1 Δ2 Δ -> Δ2 x <> None -> Δ x <> None.
Proof.
  move=> Hm H2. case: (Hm x).
  - by move=> [E _]; rewrite E in H2.
  - by move=> [_ ->].
  - by move=> [ρ [T [_ _ ->]]].
  - by move=> [_ [E _]]; rewrite E in H2.
Qed.

(** A separate slot in the composite comes from exactly one side. *)
Lemma dmerge_sepE n (Δ1 Δ2 Δ : sctxP n) x ρ T :
  dmerge Δ1 Δ2 Δ -> Δ x = Some (SSep ρ T) ->
  (Δ1 x = Some (SSep ρ T) /\ Δ2 x = None)
  \/ (Δ2 x = Some (SSep ρ T) /\ Δ1 x = None).
Proof.
  move=> Hm E. case: (Hm x).
  - move=> [E2 ED]. left. by rewrite -ED.
  - move=> [E1 ED]. right. by rewrite -ED.
  - by move=> [ρ' [T' [_ _ ED]]]; rewrite ED in E.
  - by move=> [_ [_ [S0 ED]]]; rewrite ED in E.
Qed.

(** A both-slot in the composite is one side's both-slot, a live
    link, or a tombstone. *)
Lemma dmerge_bothE n (Δ1 Δ2 Δ : sctxP n) x S0 :
  dmerge Δ1 Δ2 Δ -> Δ x = Some (SBoth S0) ->
  [\/ Δ1 x = Some (SBoth S0) /\ Δ2 x = None,
      Δ2 x = Some (SBoth S0) /\ Δ1 x = None,
      exists ρ T, [/\ Δ1 x = Some (SSep ρ T),
                      Δ2 x = Some (SSep (flipp ρ) (dual T))
                    & S0 = pole ρ T]
    | Δ1 x = None /\ Δ2 x = None].
Proof.
  move=> Hm E. case: (Hm x).
  - move=> [E2 ED]. apply: Or41. by rewrite -ED.
  - move=> [E1 ED]. apply: Or42. by rewrite -ED.
  - move=> [ρ [T [Ea Eb ED]]]. apply: Or43. exists ρ, T.
    rewrite ED in E. by case: E => ->.
  - move=> [E1 [E2 _]]. by apply: Or44.
Qed.

(** Validity restricts to the components. *)
Lemma vok_dmergeL m n (σ : ren m n) (Δ1 Δ2 Δ : sctxP m) :
  dmerge Δ1 Δ2 Δ -> vok σ Δ -> vok σ Δ1.
Proof.
  move=> Hm Hv x1 x2 H1 H2 E.
  case: (Hv x1 x2 (dmerge_ownL Hm H1) (dmerge_ownL Hm H2) E) => [->|];
    first by left.
  move=> [ρ [T [Ea Eb]]]. right. exists ρ, T.
  case: (dmerge_sepE Hm Ea) => -[Ea' Ea''];
    last by rewrite Ea'' in H1.
  case: (dmerge_sepE Hm Eb) => -[Eb' Eb''];
    last by rewrite Eb'' in H2.
  by split.
Qed.

Lemma vok_dmergeR m n (σ : ren m n) (Δ1 Δ2 Δ : sctxP m) :
  dmerge Δ1 Δ2 Δ -> vok σ Δ -> vok σ Δ2.
Proof.
  move=> Hm Hv x1 x2 H1 H2 E.
  case: (Hv x1 x2 (dmerge_ownR Hm H1) (dmerge_ownR Hm H2) E) => [->|];
    first by left.
  move=> [ρ [T [Ea Eb]]]. right. exists ρ, T.
  case: (dmerge_sepE Hm Ea) => -[Ea' Ea''];
    first by rewrite Ea'' in H1.
  case: (dmerge_sepE Hm Eb) => -[Eb' Eb''];
    first by rewrite Eb'' in H2.
  by split.
Qed.

(** A component's owned preimages of an image name are among the
    composite's. *)
Lemma spush_none_of_none m n (σ : ren m n) (Δc Δ : sctxP m) w :
  (forall x, Δc x <> None -> Δ x <> None) ->
  spush σ Δ w = None -> spush σ Δc w = None.
Proof.
  move=> Hsub HN. apply: spush_none_fwd => x Ex.
  case E : (Δc x) => [e|] //.
  have : Δ x = None by apply: (spush_none_inv HN).
  move=> ED. case: (Hsub x); by rewrite ?E ?ED.
Qed.

(** The pushforward of a merge.  Read the composite's slot above [w]:
    it is empty, a separate slot with a unique owned preimage, or a
    both-slot -- and a both-slot arises either from a single preimage
    (which the merge then explains) or from a σ-merged dual pair,
    whose two names the split may have sent to opposite sides. *)
Lemma dmerge_spush m n (σ : ren m n) (Δ1 Δ2 Δ : sctxP m) :
  dmerge Δ1 Δ2 Δ -> vok σ Δ ->
  dmerge (spush σ Δ1) (spush σ Δ2) (spush σ Δ).
Proof.
  move=> Hm Hv w.
  have Hv1 := vok_dmergeL Hm Hv.
  have Hv2 := vok_dmergeR Hm Hv.
  have HsubL : forall x, Δ1 x <> None -> Δ x <> None.
    move=> x. exact: dmerge_ownL Hm.
  have HsubR : forall x, Δ2 x <> None -> Δ x <> None.
    move=> x. exact: dmerge_ownR Hm.
  case E : (spush σ Δ w) => [e|]; last first.
  - (* nothing owned above w *)
    apply: Or41.
    by rewrite (spush_none_of_none HsubL E) (spush_none_of_none HsubR E).
  - case: e E => [ρ T|S0] E.
    + (* separate slot: a unique owned preimage, on one side *)
      case: (spush_sep_inv Hv E) => x [Ex Dx Hu].
      have HuL : forall x', σ x' = w -> Δ1 x' <> None -> x' = x.
        move=> x' Ex' Ho. apply: Hu => //. exact: HsubL.
      have HuR : forall x', σ x' = w -> Δ2 x' <> None -> x' = x.
        move=> x' Ex' Ho. apply: Hu => //. exact: HsubR.
      case: (dmerge_sepE Hm Dx) => -[D1 D2].
      * have Ho1 : Δ1 x <> None by rewrite D1.
        apply: Or41. split.
        -- apply: spush_none_fwd => x' Ex'.
           case Ec : (Δ2 x') => [e'|] //.
           have Ho : Δ2 x' <> None by rewrite Ec.
           by rewrite (HuR x' Ex' Ho) D2 in Ec.
        -- by rewrite (spush_solo Ex Ho1 HuL) D1.
      * have Ho2 : Δ2 x <> None by rewrite D1.
        apply: Or42. split.
        -- apply: spush_none_fwd => x' Ex'.
           case Ec : (Δ1 x') => [e'|] //.
           have Ho : Δ1 x' <> None by rewrite Ec.
           by rewrite (HuL x' Ex' Ho) D2 in Ec.
        -- by rewrite (spush_solo Ex Ho2 HuR) D1.
    + (* both-slot *)
      case: (spush_both_inv Hv E) => [[x [Ex Dx Hu]]|].
      * (* one preimage: the merge explains the slot *)
        have HuL : forall x', σ x' = w -> Δ1 x' <> None -> x' = x.
          move=> x' Ex' Ho. apply: Hu => //. exact: HsubL.
        have HuR : forall x', σ x' = w -> Δ2 x' <> None -> x' = x.
          move=> x' Ex' Ho. apply: Hu => //. exact: HsubR.
        have HnL : Δ1 x = None -> spush σ Δ1 w = None.
          move=> D1. apply: spush_none_fwd => x' Ex'.
          case Ec : (Δ1 x') => [e'|] //.
          have Ho : Δ1 x' <> None by rewrite Ec.
          by rewrite (HuL x' Ex' Ho) D1 in Ec.
        have HnR : Δ2 x = None -> spush σ Δ2 w = None.
          move=> D2. apply: spush_none_fwd => x' Ex'.
          case Ec : (Δ2 x') => [e'|] //.
          have Ho : Δ2 x' <> None by rewrite Ec.
          by rewrite (HuR x' Ex' Ho) D2 in Ec.
        case: (dmerge_bothE Hm Dx).
        -- move=> [D1 D2]. have Ho1 : Δ1 x <> None by rewrite D1.
           apply: Or41. split; first exact: HnR.
           by rewrite (spush_solo Ex Ho1 HuL) D1.
        -- move=> [D2 D1]. have Ho2 : Δ2 x <> None by rewrite D2.
           apply: Or42. split; first exact: HnL.
           by rewrite (spush_solo Ex Ho2 HuR) D2.
        -- move=> [ρ [T [D1 D2 ES]]].
           have Ho1 : Δ1 x <> None by rewrite D1.
           have Ho2 : Δ2 x <> None by rewrite D2.
           apply: Or43. exists ρ, T.
           rewrite (spush_solo Ex Ho1 HuL) (spush_solo Ex Ho2 HuR) D1 D2.
           by rewrite ES.
        -- move=> [D1 D2]. apply: Or44.
           split; first exact: HnL. split; first exact: HnR.
           by exists S0.
      * (* a σ-merged dual pair: the split may separate its two ends *)
        move=> [x0 [x1 [ρ [T [Ex0 Ex1 Hne [D0 D1] ES]]]]].
        have Hcol : σ x0 = σ x1 by rewrite Ex0 Ex1.
        have Honly : forall x', σ x' = w -> Δ x' <> None ->
            x' = x0 \/ x' = x1.
          move=> x' Ex' Ho.
          apply: (vok_no_triple Hv D0 D1 Hne Hcol Ho).
          by rewrite Ex' Ex0.
        case: (dmerge_sepE Hm D0) => -[A0 B0];
          case: (dmerge_sepE Hm D1) => -[A1 B1].
        -- (* both ends on the left *)
           apply: Or41. split.
           ++ apply: spush_none_fwd => x' Ex'.
              case Ec : (Δ2 x') => [e'|] //.
              have Ho : Δ x' <> None by apply: HsubR; rewrite Ec.
              by case: (Honly x' Ex' Ho) => Exx; rewrite Exx ?B0 ?B1 in Ec.
           ++ by rewrite (spush_pair Hv1 Ex0 Ex1 Hne A0 A1) ES.
        -- (* x0 left, x1 right: σ creates the link across the par *)
           have Ho1 : Δ1 x0 <> None by rewrite A0.
           have Ho2 : Δ2 x1 <> None by rewrite A1.
           have HuL : forall x', σ x' = w -> Δ1 x' <> None -> x' = x0.
             move=> x' Ex' Ho.
             case: (Honly x' Ex' (HsubL _ Ho)) => // Exx.
             by rewrite Exx B1 in Ho.
           have HuR : forall x', σ x' = w -> Δ2 x' <> None -> x' = x1.
             move=> x' Ex' Ho.
             case: (Honly x' Ex' (HsubR _ Ho)) => // Exx.
             by rewrite Exx B0 in Ho.
           apply: Or43. exists ρ, T.
           rewrite (spush_solo Ex0 Ho1 HuL) (spush_solo Ex1 Ho2 HuR).
           rewrite A0 A1. by rewrite ES.
        -- (* x0 right, x1 left *)
           have Ho1 : Δ1 x1 <> None by rewrite A1.
           have Ho2 : Δ2 x0 <> None by rewrite A0.
           have HuL : forall x', σ x' = w -> Δ1 x' <> None -> x' = x1.
             move=> x' Ex' Ho.
             case: (Honly x' Ex' (HsubL _ Ho)) => // Exx.
             by rewrite Exx B0 in Ho.
           have HuR : forall x', σ x' = w -> Δ2 x' <> None -> x' = x0.
             move=> x' Ex' Ho.
             case: (Honly x' Ex' (HsubR _ Ho)) => // Exx.
             by rewrite Exx B1 in Ho.
           apply: Or43. exists (flipp ρ), (dual T).
           rewrite (spush_solo Ex1 Ho1 HuL) (spush_solo Ex0 Ho2 HuR).
           rewrite A0 A1 flipp_invol dual_involutive ES.
           by rewrite -pole_flip_dual.
        -- (* both ends on the right *)
           apply: Or42. split.
           ++ apply: spush_none_fwd => x' Ex'.
              case Ec : (Δ1 x') => [e'|] //.
              have Ho : Δ x' <> None by apply: HsubL; rewrite Ec.
              by case: (Honly x' Ex' Ho) => Exx; rewrite Exx ?B0 ?B1 in Ec.
           ++ by rewrite (spush_pair Hv2 Ex0 Ex1 Hne A0 A1) ES.
Qed.

(** ** σ-compatibility: parallel composition

    With the pushforward in hand this is immediate -- the cut lemma
    does all the work, and it never needed the single-link
    restriction. *)
Lemma fcompat_par m n (σ : ren m n) (Δs Δs1 Δs2 : sctxP m)
    (P Q : procP m) :
  vok σ Δs ->
  dmerge Δs1 Δs2 Δs ->
  (forall n' (σ' : ren m n'), vok σ' Δs1 ->
     SEMP (spush σ' Δs1) (psubst σ' P)) ->
  (forall n' (σ' : ren m n'), vok σ' Δs2 ->
     SEMP (spush σ' Δs2) (psubst σ' Q)) ->
  SEMP (spush σ Δs) (psubst σ (P ∥ Q)).
Proof.
  move=> Hv Hm IH1 IH2 k.
  apply: (combineP (Δ1 := spush σ Δs1) (Δ2 := spush σ Δs2)).
  - exact: dmerge_spush Hm Hv.
  - exact: (IH1 _ _ (vok_dmergeL Hm Hv) k).
  - exact: (IH2 _ _ (vok_dmergeR Hm Hv) k).
Qed.

Print Assumptions dmerge_spush.
Print Assumptions fcompat_par.
