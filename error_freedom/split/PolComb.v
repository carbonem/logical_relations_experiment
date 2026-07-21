(** * Combination lemmas: restriction, parallel, fuse

    The structural half of the pipeline towards the fundamental
    theorem.  This file grows in phases:

    Phase A (this part): inversion of every transition family at a
    restriction, the [scupd]/[scons] commutations, a [swap01]
    equivariance kit, and [compat_resP] -- the semantic counterpart
    of the ν-rule: a body related at a both-slot yields a related
    restriction.  The delicate clauses are the two that cross the
    binder: bound delegation of the restricted name itself
    ([PB_Open], where the both-slot is consumed into the separate
    co-residual by [econsume]) and the shifted-receive conjunct
    (which tunnels through the binder by a [swap01] conjugation). *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Eqdep_dec PeanoNat.
From Tait Require Import PolBase PolTypes PolProc PolLTS PolErr
  PolTyping PolLogRel PolEquiv PolSem.

Set Implicit Arguments.
Unset Strict Implicit.
Open Scope pol_scope.

(** ** Inversion at a restriction *)

Lemma pinv_c_resF n (c : pch n) (B : procP n.+1) R :
  ltscP c ((ν) B) R ->
  exists B', R = (ν) B' /\ ltscP (pshift c) B B'.
Proof. move=> H. pinv H. by eexists; split; last eassumption. Qed.

Lemma pinv_w_resF n (c : pch n) (B : procP n.+1) R :
  ltswP c ((ν) B) R ->
  exists B', R = (ν) B' /\ ltswP (pshift c) B B'.
Proof. move=> H. pinv H. by eexists; split; last eassumption. Qed.

Lemma pinv_f_resF n (c d : pch n) (B : procP n.+1) R :
  ltsfP c d ((ν) B) R ->
  exists B', R = (ν) B' /\ ltsfP (pshift c) (pshift d) B B'.
Proof. move=> H. pinv H. by eexists; split; last eassumption. Qed.

Lemma pinv_r_resF n (c d : pch n) (B : procP n.+1) R :
  ltsrP c d ((ν) B) R ->
  exists B', R = (ν) B' /\ ltsrP (pshift c) (pshift d) B B'.
Proof. move=> H. pinv H. by eexists; split; last eassumption. Qed.

Lemma pinv_b_resF n (c : pch n) (r : pol) (B : procP n.+1)
    (R : procP n.+1) :
  ltsbP c r ((ν) B) R ->
  ltsfP (pshift c) (zero, r) B R
  \/ exists B'', R = (ν) (psubst (swap_ch zero one) B'')
       /\ ltsbP (pshift c) r B B''.
Proof.
  move=> H. pinv H; first by left.
  right. by eexists; split; last eassumption.
Qed.

Lemma pinv_sel_resF n (c : pch n) b (B : procP n.+1) R :
  ltsselP c b ((ν) B) R ->
  exists B', R = (ν) B' /\ ltsselP (pshift c) b B B'.
Proof. move=> H. pinv H. by eexists; split; last eassumption. Qed.

Lemma pinv_br_resF n (c : pch n) b (B : procP n.+1) R :
  ltsbrP c b ((ν) B) R ->
  exists B', R = (ν) B' /\ ltsbrP (pshift c) b B B'.
Proof. move=> H. pinv H. by eexists; split; last eassumption. Qed.

Lemma pinv_t_resF n (B : procP n.+1) R :
  ltstP ((ν) B) R ->
  exists B', R = (ν) B' /\ ltstP B B'.
Proof. move=> H. pinv H. by eexists; split; last eassumption. Qed.

(** ** Context plumbing: [scupd] against [scons] *)

Lemma scupd_shift_scons n (w : ch n) e a (Δ : sctxP n) x :
  scupd (shift w) e (scons a Δ) x = scons a (scupd w e Δ) x.
Proof.
  case: x => [x|] //=; rewrite /scupd //=.
  have -> : ((Some x : ch n.+1) == shift w) = ((x : ch n) == w).
    by apply/eqP/eqP => [[]|->].
  by [].
Qed.

Lemma scupd_zero_scons n e a (Δ : sctxP n) x :
  scupd zero e (scons a Δ) x = scons e Δ x.
Proof. by case: x. Qed.

Lemma scupd_under n (x : ch n) e (D1 D2 : sctxP n) :
  (forall y, D1 y = D2 y) ->
  forall z, scupd x e D1 z = scupd x e D2 z.
Proof. move=> H z. rewrite /scupd. case: (z == x) => //. Qed.

(** Two updates at shifted names over a [scons]. *)
Lemma ctx_comm2 n (w1 w2 : ch n) e1 e2 a (Δ : sctxP n) z :
  scupd (shift w1) e1 (scupd (shift w2) e2 (scons a Δ)) z
  = scons a (scupd w1 e1 (scupd w2 e2 Δ)) z.
Proof.
  rewrite (scupd_under _ _ (fun q => scupd_shift_scons w2 e2 a Δ q)).
  exact: scupd_shift_scons.
Qed.

(** A zero update over a shifted update over a [scons]. *)
Lemma ctx_comm2z n (w2 : ch n) e1 e2 a (Δ : sctxP n) z :
  scupd zero e1 (scupd (shift w2) e2 (scons a Δ)) z
  = scons e1 (scupd w2 e2 Δ) z.
Proof.
  rewrite (scupd_under _ _ (fun q => scupd_shift_scons w2 e2 a Δ q)).
  exact: scupd_zero_scons.
Qed.

(** ** The [swap01] kit *)

Lemma swap01K n (x : ch n.+2) : swap_ch zero one (swap_ch zero one x) = x.
Proof. by case: x => [[x|]|]. Qed.

Lemma psubst_swap01K n (X : procP n.+2) :
  psubst (swap_ch zero one) (psubst (swap_ch zero one) X) = X.
Proof.
  rewrite psubst_comp -[RHS]psubst_id.
  apply: psubst_ext => x. exact: swap01K.
Qed.

Lemma psubst_up_shift n (B : procP n.+1) :
  psubst (up_ch shift) B = psubst (swap_ch zero one) (psubst shift B).
Proof. rewrite psubst_comp. by apply: psubst_ext => -[x|]. Qed.

Lemma agree_swap01 n (a b : option sslot) (Δ : sctxP n) :
  agree (swap_ch zero one) (scons a (scons b Δ)) (scons b (scons a Δ)).
Proof. move=> [[x|]|] /=; by right. Qed.

Lemma inj_swap01 n (Δ : sctxP n.+2) : inj_on (swap_ch zero one) Δ.
Proof.
  move=> x1 x2 _ _ E.
  by rewrite -(swap01K x1) -(swap01K x2) E.
Qed.

Lemma EsemP_swap01 k n (a b : option sslot) (Δ : sctxP n)
    (X : procP n.+2) :
  EsemP k (scons a (scons b Δ)) X ->
  EsemP k (scons b (scons a Δ)) (psubst (swap_ch zero one) X).
Proof. apply: EsemP_ren; [exact: agree_swap01 | exact: inj_swap01]. Qed.

(** ** Compatibility: restriction

    A body related under a fresh both-slot gives a related
    restriction.  Uniform in the budget; the head protocol [S] and
    the frame both evolve along internal steps, so everything but
    [k] is generalized in the induction. *)

Lemma compat_resP k :
  forall n (Δ : sctxP n) (S : sty) (B : procP n.+1),
  EsemP k (scons (Some (SBoth S)) Δ) B ->
  EsemP k Δ ((ν) B).
Proof.
  elim: k => [//|k IH] n Δ S B [CB VB StB].
  have CVB := conformD_V CB.
  split.
  - (* conformance *)
    split; last by exists S.
    move=> a c Hof.
    have HofB : offersP a (pshift c) B.
      case: a Hof => /=.
      + move=> [R HT]. case: (pinv_c_resF HT) => B' [_ HB'].
        by exists B'.
      + move=> [R HT]. case: (pinv_w_resF HT) => B' [_ HB'].
        by exists B'.
      + move=> [[d [R HT]]|[r [R HT]]].
        * case: (pinv_f_resF HT) => B' [_ HB'].
          by left; exists (pshift d), B'.
        * case: (pinv_b_resF HT) => [HB'|[B'' [_ HB'']]].
          -- by left; exists (zero, r), R.
          -- by right; exists r, B''.
      + move=> [d [R HT]]. case: (pinv_r_resF HT) => B' [_ HB'].
        by exists (pshift d), B'.
      + move=> [b [R HT]]. case: (pinv_sel_resF HT) => B' [_ HB'].
        by exists b, B'.
      + move=> [b [R HT]]. case: (pinv_br_resF HT) => B' [_ HB'].
        by exists b, B'.
    case: (CVB _ _ HofB) => S' [HS' Ha].
    by exists S'.
  - (* value dispatch *)
    move=> x r S0 HxS.
    have VBx : VsemP (@EsemP k) (scons (Some (SBoth S)) Δ)
        (shift x, r) S0 B.
      by apply: VB.
    move: VBx.
    case: S0 HxS => [| |T S2|T S2|S1' S2'|S1' S2'] HxS /= VBx.
    + (* close *)
      move=> P' HT. case: (pinv_c_resF HT) => B' [-> HB'].
      apply: IH.
      apply: EsemP_ext (VBx _ HB') => y.
      exact: scupd_shift_scons.
    + (* wait *)
      move=> P' HT. case: (pinv_w_resF HT) => B' [-> HB'].
      apply: IH.
      apply: EsemP_ext (VBx _ HB') => y.
      exact: scupd_shift_scons.
    + (* send *)
      case: VBx => VBf VBb. split.
      * (* free payload *)
        move=> y rd P' HT.
        case: (pinv_f_resF HT) => B' [-> HB'].
        case: (VBf _ _ _ HB') => e [He Hes HE].
        exists e. split=> //.
        apply: IH.
        apply: EsemP_ext HE => z.
        exact: ctx_comm2.
      * (* bound: two sources *)
        move=> r' P' HT.
        case: (pinv_b_resF HT) => [HB'|[B'' [-> HB'']]].
        -- (* PB_Open: the restricted name itself is delegated *)
           case: (VBf _ _ _ HB') => e [He Hes HE].
           move: He => /= -[Ee]. subst e.
           move: Hes => /= -[ET].
           apply: EsemP_ext HE => z.
           by rewrite ctx_comm2z /= -ET -pole_flip.
        -- (* PB_Res: delegation from under the binder *)
           have HE := VBb _ _ HB''.
           have HE1 : EsemP k
               (scons (Some (SSep (flipp r') (dual T)))
                  (scons (Some (SBoth S))
                     (scupd x (Some (SSep r S2)) Δ)))
               B''.
             apply: EsemP_ext HE => z.
             case: z => [z|] //=. exact: scupd_shift_scons.
           apply: IH.
           exact: (EsemP_swap01 HE1).
    + (* receive *)
      case: VBx => VBf VBs. split.
      * (* free object *)
        move=> y rd P' HT.
        case: (pinv_r_resF HT) => B' [-> HB'].
        case: (VBf _ _ _ HB') => Hfresh Hfuse.
        split.
        -- move=> Hy.
           apply: IH.
           apply: EsemP_ext (Hfresh Hy) => z.
           exact: ctx_comm2.
        -- move=> Hy.
           apply: IH.
           apply: EsemP_ext (Hfuse Hy) => z.
           exact: ctx_comm2.
      * (* shifted object: tunnel through the binder *)
        move=> rd P'' HT.
        rewrite /= in HT.
        case: (pinv_r_resF HT) => B'' [-> HB''].
        rewrite psubst_up_shift in HB''.
        have HB2 := ltsrP_ren HB'' (swap_ch zero one).
        rewrite psubst_swap01K in HB2.
        have Esub : pren (swap_ch zero one) (pshift (pshift (x, r)))
            = pshift (pshift (x, r)) by [].
        have Eobj : pren (swap_ch zero one) ((one, rd) : pch n.+2)
            = ((zero, rd) : pch n.+2) by [].
        rewrite Esub Eobj in HB2.
        have HE := VBs _ _ HB2.
        have HE1 : EsemP k
            (scons (Some (SSep rd T))
               (scons (Some (SBoth S))
                  (scupd x (Some (SSep r S2)) Δ)))
            (psubst (swap_ch zero one) B'').
          apply: EsemP_ext HE => z.
          case: z => [z|] //=. exact: scupd_shift_scons.
        have HE2 := EsemP_swap01 HE1.
        rewrite psubst_swap01K in HE2.
        apply: IH.
        exact: HE2.
    + (* select *)
      move=> b P' HT. case: (pinv_sel_resF HT) => B' [-> HB'].
      apply: IH.
      apply: EsemP_ext (VBx _ _ HB') => y.
      exact: scupd_shift_scons.
    + (* branch: the body's internal re-choice restricts *)
      move=> b P' HT. case: (pinv_br_resF HT) => B' [-> HB'].
      case: (VBx _ _ HB') => Δ'p [Hev HE].
      have [S'' Ez] : exists S'', Δ'p zero = Some (SBoth S'').
        case: (Hev zero) => [-> /=|[Sa [Sb [_ ->]]]]; by eexists.
      exists (fun z => Δ'p (shift z)). split.
      * move=> z. case: (Hev (shift z)) => [-> /=|]; first by left.
        move=> [Sa [Sb [Ea Eb]]]. right. by exists Sa, Sb.
      * apply: (IH _ _ S'').
        apply: EsemP_ext HE => z.
        have Hsp : forall q, Δ'p q
            = scons (Some (SBoth S'')) (fun z0 => Δ'p (shift z0)) q.
          by move=> [q|] //=.
        rewrite (scupd_under _ _ Hsp z).
        exact: scupd_shift_scons.
  - (* internal step *)
    move=> P' HT.
    case: (pinv_t_resF HT) => B' [-> HB'].
    case: (StB _ HB') => Δ'p [Hev HE].
    have [S'' Ez] : exists S'', Δ'p zero = Some (SBoth S'').
      case: (Hev zero) => [-> /=|[Sa [Sb [_ ->]]]]; by eexists.
    exists (fun x => Δ'p (shift x)). split.
    + move=> x. case: (Hev (shift x)) => [-> /=|]; first by left.
      move=> [Sa [Sb [Ea Eb]]]. right. by exists Sa, Sb.
    + apply: IH.
      apply: EsemP_ext HE => z.
      by case: z => [z|] //=; rewrite Ez.
Qed.

Print Assumptions compat_resP.

(** ** Phase B: parallel composition *)

(** *** Inversion at a parallel, with residual shapes *)

Lemma pinv_c_parF n (c : pch n) (P Q : procP n) R :
  ltscP c (P ∥ Q) R ->
  (exists P', R = P' ∥ Q /\ ltscP c P P')
  \/ (exists Q', R = P ∥ Q' /\ ltscP c Q Q').
Proof.
  move=> H. pinv H; [left | right]; by eexists; split; last eassumption.
Qed.

Lemma pinv_w_parF n (c : pch n) (P Q : procP n) R :
  ltswP c (P ∥ Q) R ->
  (exists P', R = P' ∥ Q /\ ltswP c P P')
  \/ (exists Q', R = P ∥ Q' /\ ltswP c Q Q').
Proof.
  move=> H. pinv H; [left | right]; by eexists; split; last eassumption.
Qed.

Lemma pinv_f_parF n (c d : pch n) (P Q : procP n) R :
  ltsfP c d (P ∥ Q) R ->
  (exists P', R = P' ∥ Q /\ ltsfP c d P P')
  \/ (exists Q', R = P ∥ Q' /\ ltsfP c d Q Q').
Proof.
  move=> H. pinv H; [left | right]; by eexists; split; last eassumption.
Qed.

Lemma pinv_r_parF n (c d : pch n) (P Q : procP n) R :
  ltsrP c d (P ∥ Q) R ->
  (exists P', R = P' ∥ Q /\ ltsrP c d P P')
  \/ (exists Q', R = P ∥ Q' /\ ltsrP c d Q Q').
Proof.
  move=> H. pinv H; [left | right]; by eexists; split; last eassumption.
Qed.

Lemma pinv_b_parF n (c : pch n) (r : pol) (P Q : procP n)
    (R : procP n.+1) :
  ltsbP c r (P ∥ Q) R ->
  (exists P', R = P' ∥ psubst shift Q /\ ltsbP c r P P')
  \/ (exists Q', R = psubst shift P ∥ Q' /\ ltsbP c r Q Q').
Proof.
  move=> H. pinv H; [left | right]; by eexists; split; last eassumption.
Qed.

Lemma pinv_sel_parF n (c : pch n) b (P Q : procP n) R :
  ltsselP c b (P ∥ Q) R ->
  (exists P', R = P' ∥ Q /\ ltsselP c b P P')
  \/ (exists Q', R = P ∥ Q' /\ ltsselP c b Q Q').
Proof.
  move=> H. pinv H; [left | right]; by eexists; split; last eassumption.
Qed.

Lemma pinv_br_parF n (c : pch n) b (P Q : procP n) R :
  ltsbrP c b (P ∥ Q) R ->
  (exists P', R = P' ∥ Q /\ ltsbrP c b P P')
  \/ (exists Q', R = P ∥ Q' /\ ltsbrP c b Q Q').
Proof.
  move=> H. pinv H; [left | right]; by eexists; split; last eassumption.
Qed.

Lemma pinv_t_parF n (P Q : procP n) R :
  ltstP (P ∥ Q) R ->
  [\/ exists P', R = P' ∥ Q /\ ltstP P P',
      exists Q', R = P ∥ Q' /\ ltstP Q Q',
      exists c P' Q', R = P' ∥ Q'
        /\ ltscP c P P' /\ ltswP (pflip c) Q Q'
    | exists c P' Q', R = P' ∥ Q'
        /\ ltswP (pflip c) P P' /\ ltscP c Q Q' ]
  \/
  [\/ exists c d P' Q', R = P' ∥ Q'
        /\ ltsfP c d P P' /\ ltsrP (pflip c) d Q Q',
      exists c d P' Q', R = P' ∥ Q'
        /\ ltsrP (pflip c) d P P' /\ ltsfP c d Q Q',
      exists c r (P' : procP n.+1) Q', R = (ν) (P' ∥ Q')
        /\ ltsbP c r P P'
        /\ ltsrP (pshift (pflip c)) (zero, r) (psubst shift Q) Q'
    | exists c r P' (Q' : procP n.+1), R = (ν) (P' ∥ Q')
        /\ ltsrP (pshift (pflip c)) (zero, r) (psubst shift P) P'
        /\ ltsbP c r Q Q' ]
  \/
  ((exists c b P' Q', R = P' ∥ Q'
      /\ ltsselP c b P P' /\ ltsbrP (pflip c) b Q Q')
   \/ (exists c b P' Q', R = P' ∥ Q'
      /\ ltsbrP (pflip c) b P P' /\ ltsselP c b Q Q')).
Proof.
  move=> H. pinv H.
  - by left; apply: Or41; eexists; split; last eassumption.
  - by left; apply: Or42; eexists; split; last eassumption.
  - by left; apply: Or43; do 3 eexists;
      split; last split; try eassumption.
  - by left; apply: Or44; do 3 eexists;
      split; last split; try eassumption.
  - by right; left; apply: Or41; do 4 eexists;
      split; last split; try eassumption.
  - by right; left; apply: Or42; do 4 eexists;
      split; last split; try eassumption.
  - by right; left; apply: Or43; do 4 eexists;
      split; last split; try eassumption.
  - by right; left; apply: Or44; do 4 eexists;
      split; last split; try eassumption.
  - by right; right; left; do 4 eexists;
      split; last split; try eassumption.
  - by right; right; right; do 4 eexists;
      split; last split; try eassumption.
Qed.

(** *** Semantic context merge

    Pointwise relation between two component contexts and the
    context of their parallel composition.  Either a slot belongs to
    one side (the other silent), or the two sides hold the separate
    ends of one live link (merged to a both-slot), or both are
    silent under a stale both-slot (a tombstone left by a finished
    internal session). *)

Definition dmerge {n : nat} (Δ1 Δ2 Δ : sctxP n) : Prop :=
  forall x,
    [\/ Δ2 x = None /\ Δ x = Δ1 x,
        Δ1 x = None /\ Δ x = Δ2 x,
        exists ρ T,
          [/\ Δ1 x = Some (SSep ρ T),
              Δ2 x = Some (SSep (flipp ρ) (dual T))
            & Δ x = Some (SBoth (pole ρ T))]
      | Δ1 x = None /\ Δ2 x = None
          /\ exists S0, Δ x = Some (SBoth S0) ].

Lemma pole_flip_dual r T : pole (flipp r) (dual T) = pole r T.
Proof. case: r => //=. by rewrite dual_involutive. Qed.

Lemma dmerge_sleL n (Δ1 Δ2 Δ : sctxP n) :
  dmerge Δ1 Δ2 Δ -> forall x, sle (Δ1 x) (Δ x).
Proof.
  move=> Hm x. case: (Hm x).
  - move=> [_ ->]. exact: sle_refl.
  - move=> [-> _]. exact: sle_none.
  - move=> [ρ [T [-> _ ->]]]. exact: sle_both.
  - move=> [-> _]. exact: sle_none.
Qed.

Lemma dmerge_sleR n (Δ1 Δ2 Δ : sctxP n) :
  dmerge Δ1 Δ2 Δ -> forall x, sle (Δ2 x) (Δ x).
Proof.
  move=> Hm x. case: (Hm x).
  - move=> [-> _]. exact: sle_none.
  - move=> [_ ->]. exact: sle_refl.
  - move=> [ρ [T [_ -> ->]]].
    rewrite -[pole ρ T]pole_flip_dual. exact: sle_both.
  - move=> [_ [-> _]]. exact: sle_none.
Qed.

(** A one-sided internal evolution pushes through the merge without
    touching the composite context. *)
Lemma dmerge_sevL n (Δ1 Δ1' Δ2 Δ : sctxP n) :
  dmerge Δ1 Δ2 Δ -> sevolve Δ1 Δ1' ->
  exists Δ', sevolve Δ Δ' /\ dmerge Δ1' Δ2 Δ'.
Proof.
  move=> Hm Hev.
  exists (fun x => if oslot_eqb (Δ1' x) (Δ1 x) then Δ x else Δ1' x).
  split.
  - move=> x. case: (oslot_eqP (Δ1' x) (Δ1 x)) => [_|Hne]; first by left.
    case: (Hev x) => [E|[Sa [Sb [Ea Eb]]]]; first by rewrite E in Hne.
    right. case: (Hm x).
    + move=> [_ ED]. exists Sa, Sb. by rewrite ED.
    + move=> [E1 _]. by rewrite E1 in Ea.
    + move=> [ρ [T [E1 _ _]]]. by rewrite E1 in Ea.
    + move=> [E1 _]. by rewrite E1 in Ea.
  - move=> x. case: (oslot_eqP (Δ1' x) (Δ1 x)) => [Esame|Hne].
    + case: (Hm x).
      * move=> [E2 ED]. apply: Or41. by rewrite Esame.
      * move=> [E1 ED]. apply: Or42. by rewrite Esame.
      * move=> [ρ [T [E1 E2 ED]]]. apply: Or43.
        exists ρ, T. by rewrite Esame.
      * move=> [E1 [E2 ED]]. apply: Or44. by rewrite Esame.
    + case: (Hev x) => [E|[Sa [Sb [Ea Eb]]]]; first by rewrite E in Hne.
      case: (Hm x).
      * move=> [E2 _]. by apply: Or41.
      * move=> [E1 _]. by rewrite E1 in Ea.
      * move=> [ρ [T [E1 _ _]]]. by rewrite E1 in Ea.
      * move=> [E1 _]. by rewrite E1 in Ea.
  Qed.

Lemma dmerge_sevR n (Δ1 Δ2 Δ2' Δ : sctxP n) :
  dmerge Δ1 Δ2 Δ -> sevolve Δ2 Δ2' ->
  exists Δ', sevolve Δ Δ' /\ dmerge Δ1 Δ2' Δ'.
Proof.
  move=> Hm Hev.
  exists (fun x => if oslot_eqb (Δ2' x) (Δ2 x) then Δ x else Δ2' x).
  split.
  - move=> x. case: (oslot_eqP (Δ2' x) (Δ2 x)) => [_|Hne]; first by left.
    case: (Hev x) => [E|[Sa [Sb [Ea Eb]]]]; first by rewrite E in Hne.
    right. case: (Hm x).
    + move=> [E2 _]. by rewrite E2 in Ea.
    + move=> [_ ED]. exists Sa, Sb. by rewrite ED.
    + move=> [ρ [T [_ E2 _]]]. by rewrite E2 in Ea.
    + move=> [_ [E2 _]]. by rewrite E2 in Ea.
  - move=> x. case: (oslot_eqP (Δ2' x) (Δ2 x)) => [Esame|Hne].
    + case: (Hm x).
      * move=> [E2 ED]. apply: Or41. by rewrite Esame.
      * move=> [E1 ED]. apply: Or42. by rewrite Esame.
      * move=> [ρ [T [E1 E2 ED]]]. apply: Or43.
        exists ρ, T. by rewrite Esame.
      * move=> [E1 [E2 ED]]. apply: Or44. by rewrite Esame.
    + case: (Hev x) => [E|[Sa [Sb [Ea Eb]]]]; first by rewrite E in Hne.
      case: (Hm x).
      * move=> [E2 _]. by rewrite E2 in Ea.
      * move=> [E1 _]. by apply: Or42.
      * move=> [ρ [T [_ E2 _]]]. by rewrite E2 in Ea.
      * move=> [_ [E2 _]]. by rewrite E2 in Ea.
Qed.

(** Pointwise update congruence for the merge. *)
Lemma dmerge_upd n (Δ1 Δ2 Δ : sctxP n) (x : ch n) o1 o2 o :
  dmerge Δ1 Δ2 Δ ->
  [\/ o2 = None /\ o = o1,
      o1 = None /\ o = o2,
      exists ρ T,
        [/\ o1 = Some (SSep ρ T),
            o2 = Some (SSep (flipp ρ) (dual T))
          & o = Some (SBoth (pole ρ T))]
    | o1 = None /\ o2 = None /\ exists S0, o = Some (SBoth S0) ] ->
  dmerge (scupd x o1 Δ1) (scupd x o2 Δ2) (scupd x o Δ).
Proof.
  move=> Hm Ho y. rewrite /scupd.
  by case: (y == x); [exact: Ho | exact: Hm].
Qed.

(** One-sided updates: only one component (and the composite)
    changes; the disjunct speaks about the other side's current
    slot. *)
Lemma dmerge_updL n (Δ1 Δ2 Δ : sctxP n) (x : ch n) o1 o :
  dmerge Δ1 Δ2 Δ ->
  [\/ Δ2 x = None /\ o = o1,
      o1 = None /\ o = Δ2 x,
      exists ρ T,
        [/\ o1 = Some (SSep ρ T),
            Δ2 x = Some (SSep (flipp ρ) (dual T))
          & o = Some (SBoth (pole ρ T))]
    | o1 = None /\ Δ2 x = None /\ exists S0, o = Some (SBoth S0) ] ->
  dmerge (scupd x o1 Δ1) Δ2 (scupd x o Δ).
Proof.
  move=> Hm Ho y. rewrite /scupd.
  case E : ((y : ch n) == x); last exact: Hm.
  move/eqP: E => ->. exact: Ho.
Qed.

Lemma dmerge_updR n (Δ1 Δ2 Δ : sctxP n) (x : ch n) o2 o :
  dmerge Δ1 Δ2 Δ ->
  [\/ o2 = None /\ o = Δ1 x,
      Δ1 x = None /\ o = o2,
      exists ρ T,
        [/\ Δ1 x = Some (SSep ρ T),
            o2 = Some (SSep (flipp ρ) (dual T))
          & o = Some (SBoth (pole ρ T))]
    | Δ1 x = None /\ o2 = None /\ exists S0, o = Some (SBoth S0) ] ->
  dmerge Δ1 (scupd x o2 Δ2) (scupd x o Δ).
Proof.
  move=> Hm Ho y. rewrite /scupd.
  case E : ((y : ch n) == x); last exact: Hm.
  move/eqP: E => ->. exact: Ho.
Qed.

Lemma dmerge_scons n (Δ1 Δ2 Δ : sctxP n) o1 o2 o :
  dmerge Δ1 Δ2 Δ ->
  [\/ o2 = None /\ o = o1,
      o1 = None /\ o = o2,
      exists ρ T,
        [/\ o1 = Some (SSep ρ T),
            o2 = Some (SSep (flipp ρ) (dual T))
          & o = Some (SBoth (pole ρ T))]
    | o1 = None /\ o2 = None /\ exists S0, o = Some (SBoth S0) ] ->
  dmerge (scons o1 Δ1) (scons o2 Δ2) (scons o Δ).
Proof. move=> Hm Ho [y|] /=; [exact: Hm | exact: Ho]. Qed.

(** *** Ownership and synchronization-subject facts *)

Lemma pol_eqb_true a b : pol_eqb a b = true -> a = b.
Proof. by case: a; case: b. Qed.

Lemma offers_owned n (Δ : sctxP n) (P : procP n) a (c : pch n) :
  conformV Δ P -> offersP a c P -> Δ c.1 <> None.
Proof.
  move=> CV Hof. case: (CV _ _ Hof) => S [HS _].
  move: HS. rewrite /sat. by case: (Δ c.1).
Qed.

(** At a synchronization subject both sides are owned, so the acting
    side holds a separate slot of its own polarity whose head
    prescribes the action. *)
Lemma sync_subjL n (Δ1 Δ2 Δ : sctxP n) (P : procP n) a (c : pch n) :
  dmerge Δ1 Δ2 Δ -> conformV Δ1 P -> offersP a c P ->
  Δ2 c.1 <> None ->
  exists Sh, Δ1 c.1 = Some (SSep c.2 Sh) /\ a = head_act Sh.
Proof.
  move=> Hm CV Hof H2.
  case: (CV _ _ Hof) => S [HS Ha].
  move: HS. rewrite /sat. case E : (Δ1 c.1) => [e|] //.
  case: e E => [ρ S0|S0] E /=.
  - case Er : (pol_eqb c.2 ρ) => // -[ES]. subst S0.
    exists S. rewrite (pol_eqb_true Er). by split.
  - case: (Hm c.1).
    + move=> [E2 _]. by case: (H2 E2).
    + move=> [E1 _]. by rewrite E1 in E.
    + move=> [ρ' [T' [E1 _ _]]]. by rewrite E1 in E.
    + move=> [E1 _]. by rewrite E1 in E.
Qed.

Lemma sync_subjR n (Δ1 Δ2 Δ : sctxP n) (Q : procP n) a (c : pch n) :
  dmerge Δ1 Δ2 Δ -> conformV Δ2 Q -> offersP a c Q ->
  Δ1 c.1 <> None ->
  exists Sh, Δ2 c.1 = Some (SSep c.2 Sh) /\ a = head_act Sh.
Proof.
  move=> Hm CV Hof H1.
  case: (CV _ _ Hof) => S [HS Ha].
  move: HS. rewrite /sat. case E : (Δ2 c.1) => [e|] //.
  case: e E => [ρ S0|S0] E /=.
  - case Er : (pol_eqb c.2 ρ) => // -[ES]. subst S0.
    exists S. rewrite (pol_eqb_true Er). by split.
  - case: (Hm c.1).
    + move=> [E2 _]. by rewrite E2 in E.
    + move=> [E1 _]. by case: (H1 E1).
    + move=> [ρ' [T' [_ E2 _]]]. by rewrite E2 in E.
    + move=> [_ [E2 _]]. by rewrite E2 in E.
Qed.

(** Both sides owned at one name: it is a live link, and the shapes
    are locked to each other. *)
Lemma dmerge_live n (Δ1 Δ2 Δ : sctxP n) (x : ch n) e1 e2 :
  dmerge Δ1 Δ2 Δ -> Δ1 x = Some e1 -> Δ2 x = Some e2 ->
  exists ρ T,
    [/\ e1 = SSep ρ T, e2 = SSep (flipp ρ) (dual T)
      & Δ x = Some (SBoth (pole ρ T))].
Proof.
  move=> Hm E1 E2. case: (Hm x).
  - move=> [E2' _]. by rewrite E2' in E2.
  - move=> [E1' _]. by rewrite E1' in E1.
  - move=> [ρ [T [E1' E2' ED]]]. exists ρ, T.
    rewrite E1' in E1. rewrite E2' in E2.
    case: E1 => <-. case: E2 => <-. by split.
  - move=> [E1' _]. by rewrite E1' in E1.
Qed.

Lemma pole_flip_pole r T : pole (flipp r) (pole r T) = dual T.
Proof. by rewrite pole_flip pole_invol. Qed.

Lemma dual_pole_flip r S : dual (pole (flipp r) S) = pole r S.
Proof. by rewrite -pole_flip flipp_invol. Qed.

(** ** The parallel combination *)

Lemma combineP k :
  forall n (Δ1 Δ2 Δ : sctxP n) (P Q : procP n),
  dmerge Δ1 Δ2 Δ ->
  EsemP k Δ1 P -> EsemP k Δ2 Q ->
  EsemP k Δ (P ∥ Q).
Proof.
  elim: k => [//|k IH] n Δ1 Δ2 Δ P Q Hm HP HQ.
  case: (HP) => C1 V1 St1. case: (HQ) => C2 V2 St2.
  have CV1 := conformD_V C1. have CV2 := conformD_V C2.
  have HPk := EsemP_antitone HP. have HQk := EsemP_antitone HQ.
  split.
  - (* conformance *)
    have CD1 : conformD Δ P by apply: conformD_sle C1; exact: dmerge_sleL.
    have CD2 : conformD Δ Q by apply: conformD_sle C2; exact: dmerge_sleR.
    split; last by split.
    move=> a c Hof.
    have HofC : offersP a c P \/ offersP a c Q.
      case: a Hof => /=.
      + move=> [R HT]. case: (pinv_c_parF HT) => -[R' [_ HR']];
          [left | right]; by exists R'.
      + move=> [R HT]. case: (pinv_w_parF HT) => -[R' [_ HR']];
          [left | right]; by exists R'.
      + move=> [[d [R HT]]|[r [R HT]]].
        * case: (pinv_f_parF HT) => -[R' [_ HR']];
            [left | right]; by left; exists d, R'.
        * case: (pinv_b_parF HT) => -[R' [_ HR']];
            [left | right]; by right; exists r, R'.
      + move=> [d [R HT]]. case: (pinv_r_parF HT) => -[R' [_ HR']];
          [left | right]; by exists d, R'.
      + move=> [b [R HT]]. case: (pinv_sel_parF HT) => -[R' [_ HR']];
          [left | right]; by exists b, R'.
      + move=> [b [R HT]]. case: (pinv_br_parF HT) => -[R' [_ HR']];
          [left | right]; by exists b, R'.
    case: HofC => Hof'.
    + exact: (conformD_V CD1) _ _ Hof'.
    + exact: (conformD_V CD2) _ _ Hof'.
  - (* value dispatch *)
    move=> x r S HxS.
    have Hside : (Δ1 x = Some (SSep r S) /\ Δ2 x = None)
              \/ (Δ2 x = Some (SSep r S) /\ Δ1 x = None).
      case: (Hm x).
      + move=> [E2 ED]. left. by rewrite -ED.
      + move=> [E1 ED]. right. by rewrite -ED.
      + move=> [ρ [T [_ _ ED]]]. by rewrite ED in HxS.
      + move=> [_ [_ [S0 ED]]]. by rewrite ED in HxS.
    case: Hside => -[HL HN].
    + (* the left component owns the endpoint *)
      move: (V1 _ _ _ HL). clear HL.
      case: S HxS => [| |T S2|T S2|S1 S2|S1 S2] HxS /= VP.
      * (* close *)
        move=> R HT. case: (pinv_c_parF HT) => -[R' [-> HR']]; last first.
          have Hof2 : offersP AClose (x, r) Q by exists R'.
          by case: (offers_owned CV2 Hof2 HN).
        apply: (IH _ _ _ _ _ _ _ (VP _ HR') HQk).
        apply: dmerge_updL Hm _. apply: Or41. by split.
      * (* wait *)
        move=> R HT. case: (pinv_w_parF HT) => -[R' [-> HR']]; last first.
          have Hof2 : offersP AWait (x, r) Q by exists R'.
          by case: (offers_owned CV2 Hof2 HN).
        apply: (IH _ _ _ _ _ _ _ (VP _ HR') HQk).
        apply: dmerge_updL Hm _. apply: Or41. by split.
      * (* send *)
        case: VP => VPf VPb. split.
        -- (* free payload *)
           move=> y rd R HT.
           case: (pinv_f_parF HT) => -[R' [-> HR']]; last first.
             have Hof2 : offersP ADelS (x, r) Q by left; exists (y, rd), R'.
             by case: (offers_owned CV2 Hof2 HN).
           case: (VPf _ _ _ HR') => e1 [He1 Hes1 HE1].
           case: (Hm y).
           ++ (* payload slot on the left *)
              move=> [E2y EDy].
              exists e1. rewrite EDy. split=> //.
              apply: (IH _ _ _ _ _ _ _ HE1 HQk).
              apply: dmerge_updL _ _; last by apply: Or41; split.
              apply: dmerge_updL Hm _. apply: Or41. by split.
           ++ (* payload owned right: the sender must own it -- dead *)
              move=> [E1y _]. by rewrite E1y in He1.
           ++ (* payload is a live link: delegate our end outward *)
              move=> [ρy [Ty [E1y E2y EDy]]].
              rewrite E1y in He1. case: He1 => Ee1.
              rewrite -Ee1 /= in Hes1.
              move: Hes1. case Er : (pol_eqb rd ρy) => // -[ETy].
              move: (pol_eqb_true Er) => Erd. subst ρy Ty.
              exists (SBoth (pole rd T)). rewrite EDy. split=> //.
                by rewrite /= pole_invol.
              apply: (IH _ _ _ _ _ _ _ HE1 HQk).
              apply: dmerge_updL _ _; last first.
                apply: Or42. split; first by rewrite -Ee1.
                by rewrite E2y /= pole_flip_pole.
              apply: dmerge_updL Hm _. apply: Or41. by split.
           ++ move=> [E1y _]. by rewrite E1y in He1.
        -- (* bound payload *)
           move=> r' R HT.
           case: (pinv_b_parF HT) => -[R' [-> HR']]; last first.
             have Hof2 : offersP ADelS (x, r) Q by right; exists r', R'.
             by case: (offers_owned CV2 Hof2 HN).
           have HE1 := VPb _ _ HR'.
           apply: (IH _ _ _ _ _ _ _ HE1 (EsemP_shift None HQk)).
           apply: dmerge_scons _ _; last by apply: Or41; split.
           apply: dmerge_updL Hm _. apply: Or41. by split.
      * (* receive *)
        case: VP => VPf VPs. split.
        -- (* free object *)
           move=> y rd R HT.
           case: (pinv_r_parF HT) => -[R' [-> HR']]; last first.
             have Hof2 : offersP ADelR (x, r) Q by exists (y, rd), R'.
             by case: (offers_owned CV2 Hof2 HN).
           case: (VPf _ _ _ HR') => Hfresh Hfuse.
           split.
           ++ (* fresh *)
              move=> Hy.
              have [H1y H2y] : Δ1 y = None /\ Δ2 y = None.
                case: (Hm y).
                ** move=> [E2y EDy]. by rewrite -EDy Hy.
                ** move=> [E1y EDy]. by rewrite -EDy Hy.
                ** move=> [ρy [Ty [_ _ EDy]]]. by rewrite EDy in Hy.
                ** move=> [_ [_ [S0 EDy]]]. by rewrite EDy in Hy.
              apply: (IH _ _ _ _ _ _ _ (Hfresh H1y) HQk).
              apply: dmerge_updL _ _; last by apply: Or41; split.
              apply: dmerge_updL Hm _. apply: Or41. by split.
           ++ (* the received name's co-end is owned here *)
              move=> Hy.
              case: (Hm y).
              ** (* co-end inside the left component: its own fuse *)
                 move=> [E2y EDy]. rewrite EDy in Hy.
                 apply: (IH _ _ _ _ _ _ _ (Hfuse Hy) HQk).
                 apply: dmerge_updL _ _; last by apply: Or41; split.
                 apply: dmerge_updL Hm _. apply: Or41. by split.
              ** (* co-end on the right: a link forms across the par *)
                 move=> [E1y EDy]. rewrite EDy in Hy.
                 apply: (IH _ _ _ _ _ _ _ (Hfresh E1y) HQk).
                 apply: dmerge_updL _ _; last first.
                   apply: Or43. exists rd, T. by split.
                 apply: dmerge_updL Hm _. apply: Or41. by split.
              ** move=> [ρy [Ty [_ _ EDy]]]. by rewrite EDy in Hy.
              ** move=> [_ [_ [S0 EDy]]]. by rewrite EDy in Hy.
        -- (* shifted object *)
           move=> rd R HT.
           rewrite /= in HT.
           case: (pinv_r_parF HT) => -[R' [-> HR']]; last first.
             have HofS : offersP ADelR (pshift (x, r)) (psubst shift Q)
               by exists (zero, rd), R'.
             case: (offersP_ren_inv HofS) => cq [Ecq Hofq].
             have Excq : cq = (x, r).
               case: cq Ecq Hofq => cqn cqr /= -[E1 E2] _.
               case: E1 => E1. by rewrite -E1 -E2.
             rewrite Excq in Hofq.
             by case: (offers_owned CV2 Hofq HN).
           have HE1 := VPs _ _ HR'.
           apply: (IH _ _ _ _ _ _ _ HE1 (EsemP_shift None HQk)).
           apply: dmerge_scons _ _; last by apply: Or41; split.
           apply: dmerge_updL Hm _. apply: Or41. by split.
      * (* select *)
        move=> b R HT.
        case: (pinv_sel_parF HT) => -[R' [-> HR']]; last first.
          have Hof2 : offersP ASel (x, r) Q by exists b, R'.
          by case: (offers_owned CV2 Hof2 HN).
        apply: (IH _ _ _ _ _ _ _ (VP _ _ HR') HQk).
        apply: dmerge_updL Hm _. apply: Or41. by split.
      * (* branch *)
        move=> b R HT.
        case: (pinv_br_parF HT) => -[R' [-> HR']]; last first.
          have Hof2 : offersP ABra (x, r) Q by exists b, R'.
          by case: (offers_owned CV2 Hof2 HN).
        case: (VP _ _ HR') => Δ1' [Hev1 HE1].
        case: (dmerge_sevL Hm Hev1) => Δmid [HevD HmMid].
        exists Δmid. split=> //.
        apply: (IH _ _ _ _ _ _ _ HE1 HQk).
        apply: dmerge_updL HmMid _. apply: Or41. by split.
    + (* the right component owns the endpoint *)
      move: (V2 _ _ _ HL). clear HL.
      case: S HxS => [| |T S2|T S2|S1 S2|S1 S2] HxS /= VQ.
      * (* close *)
        move=> R HT. case: (pinv_c_parF HT) => -[R' [-> HR']].
          have Hof1 : offersP AClose (x, r) P by exists R'.
          by case: (offers_owned CV1 Hof1 HN).
        apply: (IH _ _ _ _ _ _ _ HPk (VQ _ HR')).
        apply: dmerge_updR Hm _. apply: Or42. by split.
      * (* wait *)
        move=> R HT. case: (pinv_w_parF HT) => -[R' [-> HR']].
          have Hof1 : offersP AWait (x, r) P by exists R'.
          by case: (offers_owned CV1 Hof1 HN).
        apply: (IH _ _ _ _ _ _ _ HPk (VQ _ HR')).
        apply: dmerge_updR Hm _. apply: Or42. by split.
      * (* send *)
        case: VQ => VQf VQb. split.
        -- move=> y rd R HT.
           case: (pinv_f_parF HT) => -[R' [-> HR']].
             have Hof1 : offersP ADelS (x, r) P by left; exists (y, rd), R'.
             by case: (offers_owned CV1 Hof1 HN).
           case: (VQf _ _ _ HR') => e2 [He2 Hes2 HE2].
           case: (Hm y).
           ++ move=> [E2y _]. by rewrite E2y in He2.
           ++ move=> [E1y EDy].
              exists e2. rewrite EDy. split=> //.
              apply: (IH _ _ _ _ _ _ _ HPk HE2).
              apply: dmerge_updR _ _; last by apply: Or42; split.
              apply: dmerge_updR Hm _. apply: Or42. by split.
           ++ (* live link: the right side delegates its end outward *)
              move=> [ρy [Ty [E1y E2y EDy]]].
              rewrite E2y in He2. case: He2 => Ee2.
              rewrite -Ee2 /= in Hes2.
              move: Hes2. case Er : (pol_eqb rd (flipp ρy)) => // -[ETy].
              move: (pol_eqb_true Er) => Erd.
              exists (SBoth (pole ρy Ty)). rewrite EDy. split=> //.
                by rewrite /= Erd pole_flip_pole ETy.
              apply: (IH _ _ _ _ _ _ _ HPk HE2).
              apply: dmerge_updR _ _; last first.
                apply: Or41. split; first by rewrite -Ee2.
                rewrite E1y /= Erd flipp_invol pole_invol.
                by [].
              apply: dmerge_updR Hm _. apply: Or42. by split.
           ++ move=> [_ [E2y _]]. by rewrite E2y in He2.
        -- move=> r' R HT.
           case: (pinv_b_parF HT) => -[R' [-> HR']].
             have Hof1 : offersP ADelS (x, r) P by right; exists r', R'.
             by case: (offers_owned CV1 Hof1 HN).
           have HE2 := VQb _ _ HR'.
           apply: (IH _ _ _ _ _ _ _ (EsemP_shift None HPk) HE2).
           apply: dmerge_scons _ _; last by apply: Or42; split.
           apply: dmerge_updR Hm _. apply: Or42. by split.
      * (* receive *)
        case: VQ => VQf VQs. split.
        -- move=> y rd R HT.
           case: (pinv_r_parF HT) => -[R' [-> HR']].
             have Hof1 : offersP ADelR (x, r) P by exists (y, rd), R'.
             by case: (offers_owned CV1 Hof1 HN).
           case: (VQf _ _ _ HR') => Hfresh Hfuse.
           split.
           ++ move=> Hy.
              have [H1y H2y] : Δ1 y = None /\ Δ2 y = None.
                case: (Hm y).
                ** move=> [E2y EDy]. by rewrite -EDy Hy.
                ** move=> [E1y EDy]. by rewrite -EDy Hy.
                ** move=> [ρy [Ty [_ _ EDy]]]. by rewrite EDy in Hy.
                ** move=> [_ [_ [S0 EDy]]]. by rewrite EDy in Hy.
              apply: (IH _ _ _ _ _ _ _ HPk (Hfresh H2y)).
              apply: dmerge_updR _ _; last by apply: Or42; split.
              apply: dmerge_updR Hm _. apply: Or42. by split.
           ++ move=> Hy.
              case: (Hm y).
              ** (* co-end on the left: a link forms across the par *)
                 move=> [E2y EDy]. rewrite EDy in Hy.
                 apply: (IH _ _ _ _ _ _ _ HPk (Hfresh E2y)).
                 apply: dmerge_updR _ _; last first.
                   apply: Or43. exists (flipp rd), (dual T).
                   rewrite flipp_invol dual_involutive pole_flip_dual.
                   by split.
                 apply: dmerge_updR Hm _. apply: Or42. by split.
              ** (* co-end inside the right component *)
                 move=> [E1y EDy]. rewrite EDy in Hy.
                 apply: (IH _ _ _ _ _ _ _ HPk (Hfuse Hy)).
                 apply: dmerge_updR _ _; last by apply: Or42; split.
                 apply: dmerge_updR Hm _. apply: Or42. by split.
              ** move=> [ρy [Ty [_ _ EDy]]]. by rewrite EDy in Hy.
              ** move=> [_ [_ [S0 EDy]]]. by rewrite EDy in Hy.
        -- move=> rd R HT.
           rewrite /= in HT.
           case: (pinv_r_parF HT) => -[R' [-> HR']].
             have HofS : offersP ADelR (pshift (x, r)) (psubst shift P)
               by exists (zero, rd), R'.
             case: (offersP_ren_inv HofS) => cp [Ecp Hofp].
             have Excp : cp = (x, r).
               case: cp Ecp Hofp => cpn cpr /= -[E1 E2] _.
               case: E1 => E1. by rewrite -E1 -E2.
             rewrite Excp in Hofp.
             by case: (offers_owned CV1 Hofp HN).
           have HE2 := VQs _ _ HR'.
           apply: (IH _ _ _ _ _ _ _ (EsemP_shift None HPk) HE2).
           apply: dmerge_scons _ _; last by apply: Or42; split.
           apply: dmerge_updR Hm _. apply: Or42. by split.
      * (* select *)
        move=> b R HT.
        case: (pinv_sel_parF HT) => -[R' [-> HR']].
          have Hof1 : offersP ASel (x, r) P by exists b, R'.
          by case: (offers_owned CV1 Hof1 HN).
        apply: (IH _ _ _ _ _ _ _ HPk (VQ _ _ HR')).
        apply: dmerge_updR Hm _. apply: Or42. by split.
      * (* branch *)
        move=> b R HT.
        case: (pinv_br_parF HT) => -[R' [-> HR']].
          have Hof1 : offersP ABra (x, r) P by exists b, R'.
          by case: (offers_owned CV1 Hof1 HN).
        case: (VQ _ _ HR') => Δ2' [Hev2 HE2].
        case: (dmerge_sevR Hm Hev2) => Δmid [HevD HmMid].
        exists Δmid. split=> //.
        apply: (IH _ _ _ _ _ _ _ HPk HE2).
        apply: dmerge_updR HmMid _. apply: Or42. by split.
  - (* internal step *)
    move=> R HT.
    have Hc8 := pinv_t_parF HT.
    case: Hc8
      => [[Hc8|Hc8|Hc8|Hc8]|[[Hc8|Hc8|Hc8|Hc8]|[Hc8|Hc8]]].
    all: move: Hc8.
    + (* τ on the left *)
      move=> [P' [-> HP']].
      case: (St1 _ HP') => Δ1' [Hev1 HE1].
      case: (dmerge_sevL Hm Hev1) => Δ' [HevD Hm'].
      exists Δ'. split=> //.
      exact: (IH _ _ _ _ _ _ Hm' HE1 HQk).
    + (* τ on the right *)
      move=> [Q' [-> HQ']].
      case: (St2 _ HQ') => Δ2' [Hev2 HE2].
      case: (dmerge_sevR Hm Hev2) => Δ' [HevD Hm'].
      exists Δ'. split=> //.
      exact: (IH _ _ _ _ _ _ Hm' HPk HE2).
    + (* close/wait *)
      move=> [c [P' [Q' [-> [HcP HwQ]]]]].
      have HofP : offersP AClose c P by exists P'.
      have HofQ : offersP AWait (pflip c) Q by exists Q'.
      have Hown2 : Δ2 c.1 <> None.
        exact: offers_owned CV2 HofQ.
      have Hown1 : Δ1 c.1 <> None.
        exact: offers_owned CV1 HofP.
      case: (sync_subjL Hm CV1 HofP Hown2) => ShP [E1c EaP].
      case: (sync_subjR Hm CV2 HofQ Hown1) => ShQ [E2c EaQ].
      case: ShP EaP E1c => // _ E1c. case: ShQ EaQ E2c => // _ E2c.
      rewrite (surjective_pairing c) in HcP.
      have HE1 := V1 _ _ _ E1c _ HcP.
      have HE2 := V2 _ _ _ E2c _ HwQ.
      exists Δ. split; first exact: sevolve_refl.
      apply: (IH _ _ _ _ _ _ _ HE1 HE2).
      move=> y. rewrite /scupd.
      case Ey : ((y : ch n) == c.1); last exact: Hm.
      move/eqP: Ey => ->.
      case: (dmerge_live Hm E1c E2c) => ρ [T [_ _ EDc]].
      apply: Or44. split=> //. split=> //. rewrite EDc. by eexists.
    + (* wait/close *)
      move=> [c [P' [Q' [-> [HwP HcQ]]]]].
      have HofP : offersP AWait (pflip c) P by exists P'.
      have HofQ : offersP AClose c Q by exists Q'.
      have Hown2 : Δ2 c.1 <> None.
        exact: offers_owned CV2 HofQ.
      have Hown1 : Δ1 c.1 <> None.
        exact: offers_owned CV1 HofP.
      case: (sync_subjL Hm CV1 HofP Hown2) => ShP [E1c EaP].
      case: (sync_subjR Hm CV2 HofQ Hown1) => ShQ [E2c EaQ].
      case: ShP EaP E1c => // _ E1c. case: ShQ EaQ E2c => // _ E2c.
      rewrite (surjective_pairing c) in HcQ.
      have HE1 := V1 _ _ _ E1c _ HwP.
      have HE2 := V2 _ _ _ E2c _ HcQ.
      exists Δ. split; first exact: sevolve_refl.
      apply: (IH _ _ _ _ _ _ _ HE1 HE2).
      move=> y. rewrite /scupd.
      case Ey : ((y : ch n) == c.1); last exact: Hm.
      move/eqP: Ey => ->.
      case: (dmerge_live Hm E1c E2c) => ρ [T [_ _ EDc]].
      apply: Or44. split=> //. split=> //. rewrite EDc. by eexists.
    + (* free delegation, left sends *)
        move=> [c [d [P' [Q' [-> [HfP HrQ]]]]]].
        case: d HfP HrQ => dy dr HfP HrQ.
        have HofP : offersP ADelS c P by left; exists (dy, dr), P'.
        have HofQ : offersP ADelR (pflip c) Q by exists (dy, dr), Q'.
        have Hown2 : Δ2 c.1 <> None.
          exact: offers_owned CV2 HofQ.
        have Hown1 : Δ1 c.1 <> None.
          exact: offers_owned CV1 HofP.
        case: (sync_subjL Hm CV1 HofP Hown2) => ShP [E1c EaP].
        case: (sync_subjR Hm CV2 HofQ Hown1) => ShQ [E2c EaQ].
        case: ShP EaP E1c => // Tp Sp _ E1c.
        case: ShQ EaQ E2c => // Tq Sq _ E2c.
        have [ETq ESq] : Tq = Tp /\ Sq = dual Sp.
          case: (dmerge_live Hm E1c E2c) => ρ [T [Ea Eb _]].
          case: Ea => Eρ ET. rewrite -Eρ -ET /= in Eb.
          by case: Eb.
        subst Tq Sq.
        rewrite (surjective_pairing c) in HfP.
        case: (V1 _ _ _ E1c) => /= VPf _.
        case: (VPf _ _ _ HfP) => e1 [He1 Hes1 HE1].
        case: (V2 _ _ _ E2c) => /= VQf _.
        case: (VQf _ _ _ HrQ) => Hfresh Hfuse.
        (* the payload cannot be the subject *)
        have Hdc : dy <> c.1.
          move=> E. rewrite E E1c in He1. case: He1 => Ee1.
          rewrite -Ee1 /= in Hes1. move: Hes1.
          case: (pol_eqb dr c.2) => // -[ET].
          exact: ssend_neqT (esym ET).
        have Ebdc : (dy == c.1) = false.
          by apply: negbTE; apply/eqP.
        have EDc : Δ c.1 = Some (SBoth (pole c.2 (SSend Tp Sp))).
          case: (dmerge_live Hm E1c E2c) => ρ [T [Ea _ EDc0]].
          case: Ea => Eρ ET. by rewrite -Eρ -ET in EDc0.
        case: (Hm dy).
        -- (* payload slot lives on the left *)
           move=> [E2dy EDdy].
           have HE2 := Hfresh E2dy.
           exists (scupd c.1 (Some (SBoth (pole c.2 Sp))) Δ). split.
             move=> z. rewrite /scupd.
             case Ez : ((z : ch n) == c.1); last by left.
             move/eqP: Ez => ->. right. rewrite EDc. by do 2 eexists.
           apply: (IH _ _ _ _ _ _ _ HE1 HE2).
           move=> y. rewrite /scupd.
           case Ey : ((y : ch n) == dy).
           ++ move/eqP: Ey => Ey. subst y. rewrite Ebdc.
              case: e1 He1 Hes1 HE1 => [ρ1 T1|S0] He1 /= Hes1 HE1.
              ** move: Hes1. case Er : (pol_eqb dr ρ1) => // -[ET1].
                 move: (pol_eqb_true Er) => Erd. subst ρ1 T1.
                 apply: Or42. split=> //.
                 by rewrite EDdy He1.
              ** move: Hes1 => -[ES0].
                 apply: Or43.
                 exists (flipp dr), (pole (flipp dr) S0).
                 rewrite flipp_invol pole_invol dual_pole_flip ES0.
                 split=> //.
                 by rewrite EDdy He1.
           ++ case Eyc : ((y : ch n) == c.1); last exact: Hm.
              move/eqP: Eyc => Eyc. subst y.
              apply: Or43. exists c.2, Sp. by split.
        -- move=> [E1dy _]. by rewrite E1dy in He1.
        -- (* payload is a live link: it fuses on the right *)
           move=> [ρy [Ty [E1dy E2dy EDdy]]].
           rewrite E1dy in He1. case: He1 => Ee1.
           rewrite -Ee1 /= in Hes1.
           move: Hes1. case Er : (pol_eqb dr ρy) => // -[ETy].
           move: (pol_eqb_true Er) => Erd. subst ρy Ty.
           have Hguard : Δ2 dy = Some (SSep (flipp dr) (dual Tp))
             by rewrite E2dy.
           have HE2 := Hfuse Hguard.
           exists (scupd c.1 (Some (SBoth (pole c.2 Sp))) Δ). split.
             move=> z. rewrite /scupd.
             case Ez : ((z : ch n) == c.1); last by left.
             move/eqP: Ez => ->. right. rewrite EDc. by do 2 eexists.
           apply: (IH _ _ _ _ _ _ _ HE1 HE2).
           move=> y. rewrite /scupd.
           case Ey : ((y : ch n) == dy).
           ++ move/eqP: Ey => Ey. subst y. rewrite Ebdc.
              apply: Or42. split; first by rewrite -Ee1.
              by rewrite EDdy.
           ++ case Eyc : ((y : ch n) == c.1); last exact: Hm.
              move/eqP: Eyc => Eyc. subst y.
              apply: Or43. exists c.2, Sp. by split.
        -- move=> [E1dy _]. by rewrite E1dy in He1.
    + (* free delegation, right sends *)
        move=> [c [d [P' [Q' [-> [HrP HfQ]]]]]].
        case: d HrP HfQ => dy dr HrP HfQ.
        have HofP : offersP ADelR (pflip c) P by exists (dy, dr), P'.
        have HofQ : offersP ADelS c Q by left; exists (dy, dr), Q'.
        have Hown2 : Δ2 c.1 <> None.
          exact: offers_owned CV2 HofQ.
        have Hown1 : Δ1 c.1 <> None.
          exact: offers_owned CV1 HofP.
        case: (sync_subjL Hm CV1 HofP Hown2) => ShP [E1c EaP].
        case: (sync_subjR Hm CV2 HofQ Hown1) => ShQ [E2c EaQ].
        case: ShP EaP E1c => // Tp Sp _ E1c.
        case: ShQ EaQ E2c => // Tq Sq _ E2c.
        have [ETq ESq] : Tp = Tq /\ Sp = dual Sq.
          case: (dmerge_live Hm E1c E2c) => ρ [T [Ea Eb _]].
          case: Ea => Eρ ET. rewrite -Eρ -ET /= in Eb.
          case: Eb => _ -[ETT ESS]. split; first exact: esym ETT.
          by rewrite ESS dual_involutive.
        subst Tp Sp.
        rewrite (surjective_pairing c) in HfQ.
        case: (V2 _ _ _ E2c) => /= VQf _.
        case: (VQf _ _ _ HfQ) => e2 [He2 Hes2 HE2].
        case: (V1 _ _ _ E1c) => /= VPf _.
        case: (VPf _ _ _ HrP) => Hfresh Hfuse.
        have Hdc : dy <> c.1.
          move=> E. rewrite E E2c in He2. case: He2 => Ee2.
          rewrite -Ee2 /= in Hes2. move: Hes2.
          case: (pol_eqb dr c.2) => // -[ET].
          exact: ssend_neqT (esym ET).
        have Ebdc : (dy == c.1) = false.
          by apply: negbTE; apply/eqP.
        have EDc : Δ c.1
            = Some (SBoth (pole (flipp c.2) (SRecv Tq (dual Sq)))).
          case: (dmerge_live Hm E1c E2c) => ρ [T [Ea _ EDc0]].
          case: Ea => Eρ ET. by rewrite -Eρ -ET in EDc0.
        case: (Hm dy).
        -- move=> [E2dy _]. by rewrite E2dy in He2.
        -- (* payload slot lives on the right *)
           move=> [E1dy EDdy].
           have HE1 := Hfresh E1dy.
           exists (scupd c.1
                     (Some (SBoth (pole (flipp c.2) (dual Sq)))) Δ).
           split.
             move=> z. rewrite /scupd.
             case Ez : ((z : ch n) == c.1); last by left.
             move/eqP: Ez => ->. right. rewrite EDc. by do 2 eexists.
           apply: (IH _ _ _ _ _ _ _ HE1 HE2).
           move=> y. rewrite /scupd.
           case Ey : ((y : ch n) == dy).
           ++ move/eqP: Ey => Ey. subst y. rewrite Ebdc.
              case: e2 He2 Hes2 HE2 => [ρ2 T2|S0] He2 /= Hes2 HE2.
              ** move: Hes2. case Er : (pol_eqb dr ρ2) => // -[ET2].
                 move: (pol_eqb_true Er) => Erd. subst ρ2 T2.
                 apply: Or41. split=> //.
                 by rewrite EDdy He2.
              ** move: Hes2 => -[ES0].
                 apply: Or43.
                 exists dr, Tq.
                 rewrite -ES0 pole_flip pole_invol.
                 split=> //.
                 by rewrite EDdy He2.
           ++ case Eyc : ((y : ch n) == c.1); last exact: Hm.
              move/eqP: Eyc => Eyc. subst y.
              apply: Or43. exists (flipp c.2), (dual Sq).
              rewrite flipp_invol dual_involutive. by split.
        -- (* live link: it fuses on the left *)
           move=> [ρy [Ty [E1dy E2dy EDdy]]].
           rewrite E2dy in He2. case: He2 => Ee2.
           rewrite -Ee2 /= in Hes2.
           move: Hes2. case Er : (pol_eqb dr (flipp ρy)) => // -[ETy].
           move: (pol_eqb_true Er) => Erd.
           have Hguard : Δ1 dy = Some (SSep (flipp dr) (dual Tq)).
             rewrite E1dy Erd flipp_invol -ETy dual_involutive.
             by [].
           have HE1 := Hfuse Hguard.
           exists (scupd c.1
                     (Some (SBoth (pole (flipp c.2) (dual Sq)))) Δ).
           split.
             move=> z. rewrite /scupd.
             case Ez : ((z : ch n) == c.1); last by left.
             move/eqP: Ez => ->. right. rewrite EDc. by do 2 eexists.
           apply: (IH _ _ _ _ _ _ _ HE1 HE2).
           move=> y. rewrite /scupd.
           case Ey : ((y : ch n) == dy).
           ++ move/eqP: Ey => Ey. subst y. rewrite Ebdc.
              apply: Or41. split; first by rewrite -Ee2.
              rewrite EDdy. congr Some. congr SBoth.
              by rewrite Erd -ETy pole_flip_dual.
           ++ case Eyc : ((y : ch n) == c.1); last exact: Hm.
              move/eqP: Eyc => Eyc. subst y.
              apply: Or43. exists (flipp c.2), (dual Sq).
              rewrite flipp_invol dual_involutive. by split.
        -- move=> [_ [E2dy _]]. by rewrite E2dy in He2.
    + (* bound delegation, left opens *)
        move=> [c [r' [P' [Q' [-> [HbP HrQ]]]]]].
        have HofP : offersP ADelS c P by right; exists r', P'.
        have HofQS : offersP ADelR (pshift (pflip c)) (psubst shift Q)
          by exists (zero, r'), Q'.
        case: (offersP_ren_inv HofQS) => cq [Ecq Hofq].
        have Excq : cq = pflip c.
          case: cq Ecq Hofq => cqn cqr /= -[E1 E2] _.
          case: E1 => E1. by rewrite -E1 -E2.
        rewrite Excq in Hofq.
        have Hown2 : Δ2 c.1 <> None.
          exact: offers_owned CV2 Hofq.
        have Hown1 : Δ1 c.1 <> None.
          exact: offers_owned CV1 HofP.
        case: (sync_subjL Hm CV1 HofP Hown2) => ShP [E1c EaP].
        case: (sync_subjR Hm CV2 Hofq Hown1) => ShQ [E2c EaQ].
        case: ShP EaP E1c => // Tp Sp _ E1c.
        case: ShQ EaQ E2c => // Tq Sq _ E2c.
        have [ETq ESq] : Tq = Tp /\ Sq = dual Sp.
          case: (dmerge_live Hm E1c E2c) => ρ [T [Ea Eb _]].
          case: Ea => Eρ ET. rewrite -Eρ -ET /= in Eb.
          by case: Eb.
        subst Tq Sq.
        rewrite (surjective_pairing c) in HbP.
        case: (V1 _ _ _ E1c) => /= _ VPb.
        have HE1 := VPb _ _ HbP.
        case: (V2 _ _ _ E2c) => /= _ VQs.
        have HE2 := VQs _ _ HrQ.
        exists (scupd c.1 (Some (SBoth (pole c.2 Sp))) Δ).
        split.
          move=> y. rewrite /scupd.
          case Ey : ((y : ch n) == c.1); last by left.
          move/eqP: Ey => ->. right.
          case: (dmerge_live Hm E1c E2c) => ρ [T [_ _ EDc]].
          rewrite EDc. by do 2 eexists.
        apply: (compat_resP (S := pole (flipp r') (dual Tp))).
        apply: (IH _ _ _ _ _ _ _ HE1 HE2).
        apply: dmerge_scons _ _; last first.
          apply: Or43. exists (flipp r'), (dual Tp).
          rewrite flipp_invol dual_involutive. by split.
        apply: dmerge_upd _ _; last first.
          apply: Or43. exists c.2, Sp. by split.
        exact: Hm.
    + (* bound delegation, right opens *)
        move=> [c [r' [P' [Q' [-> [HrP HbQ]]]]]].
        have HofQ : offersP ADelS c Q by right; exists r', Q'.
        have HofPS : offersP ADelR (pshift (pflip c)) (psubst shift P)
          by exists (zero, r'), P'.
        case: (offersP_ren_inv HofPS) => cp [Ecp Hofp].
        have Excp : cp = pflip c.
          case: cp Ecp Hofp => cpn cpr /= -[E1 E2] _.
          case: E1 => E1. by rewrite -E1 -E2.
        rewrite Excp in Hofp.
        have Hown2 : Δ2 c.1 <> None.
          exact: offers_owned CV2 HofQ.
        have Hown1 : Δ1 c.1 <> None.
          exact: offers_owned CV1 Hofp.
        case: (sync_subjL Hm CV1 Hofp Hown2) => ShP [E1c EaP].
        case: (sync_subjR Hm CV2 HofQ Hown1) => ShQ [E2c EaQ].
        case: ShP EaP E1c => // Tp Sp _ E1c.
        case: ShQ EaQ E2c => // Tq Sq _ E2c.
        have [ETq ESq] : Tp = Tq /\ Sp = dual Sq.
          case: (dmerge_live Hm E1c E2c) => ρ [T [Ea Eb _]].
          case: Ea => Eρ ET. rewrite -Eρ -ET /= in Eb.
          case: Eb => _ -[ETT ESS]. split; first exact: esym ETT.
          by rewrite ESS dual_involutive.
        subst Tp Sp.
        rewrite (surjective_pairing c) in HbQ.
        case: (V2 _ _ _ E2c) => /= _ VQb.
        have HE2 := VQb _ _ HbQ.
        case: (V1 _ _ _ E1c) => /= _ VPs.
        have HE1 := VPs _ _ HrP.
        exists (scupd c.1 (Some (SBoth (pole (flipp c.2) (dual Sq)))) Δ).
        split.
          move=> y. rewrite /scupd.
          case Ey : ((y : ch n) == c.1); last by left.
          move/eqP: Ey => ->. right.
          case: (dmerge_live Hm E1c E2c) => ρ [T [_ _ EDc]].
          rewrite EDc. by do 2 eexists.
        apply: (compat_resP (S := pole r' Tq)).
        apply: (IH _ _ _ _ _ _ _ HE1 HE2).
        apply: dmerge_scons _ _; last first.
          apply: Or43. exists r', Tq. by split.
        apply: dmerge_upd _ _; last first.
          apply: Or43. exists (flipp c.2), (dual Sq).
          rewrite flipp_invol dual_involutive pole_flip_dual.
          by split.
        exact: Hm.
    + (* select against branch *)
      move=> [c [b [P' [Q' [-> [HsP HbQ]]]]]].
      have HofP : offersP ASel c P by exists b, P'.
      have HofQ : offersP ABra (pflip c) Q by exists b, Q'.
      have Hown2 : Δ2 c.1 <> None.
        exact: offers_owned CV2 HofQ.
      have Hown1 : Δ1 c.1 <> None.
        exact: offers_owned CV1 HofP.
      case: (sync_subjL Hm CV1 HofP Hown2) => ShP [E1c EaP].
      case: (sync_subjR Hm CV2 HofQ Hown1) => ShQ [E2c EaQ].
      case: ShP EaP E1c => // S1 S2 _ E1c.
      case: ShQ EaQ E2c => // S1' S2' _ E2c.
      have [ES1 ES2] : S1' = dual S1 /\ S2' = dual S2.
        case: (dmerge_live Hm E1c E2c) => ρ [T [Ea Eb _]].
        case: Ea => Eρ ET. rewrite -Eρ -ET /= in Eb.
        by case: Eb => -> ->.
      subst S1' S2'.
      rewrite (surjective_pairing c) in HsP.
      have HE1 := V1 _ _ _ E1c _ _ HsP.
      case: (V2 _ _ _ E2c _ _ HbQ) => Δ2' [Hev2 HE2].
      case: (dmerge_sevR Hm Hev2) => Δmid [HevD HmMid].
      exists (scupd c.1
                (Some (SBoth (pole c.2 (if b then S1 else S2)))) Δmid).
      split.
        apply: sevolve_trans HevD _.
        move=> y. rewrite /scupd.
        case Ey : ((y : ch n) == c.1); last by left.
        move/eqP: Ey => ->. right.
        have E2m : Δ2 c.1 = Δ2' c.1.
          case: (Hev2 c.1) => [E|[S0 [S0' [E _]]]] //.
          by rewrite E in E2c.
        case: (HmMid c.1).
        - move=> [E2n _]. by rewrite -E2m E2c in E2n.
        - move=> [E1n _]. by rewrite E1c in E1n.
        - move=> [ρ' [T' [_ _ EDm]]]. rewrite EDm. by do 2 eexists.
        - move=> [E1n _]. by rewrite E1c in E1n.
      apply: (IH _ _ _ _ _ _ _ HE1 HE2).
      move=> y. rewrite /scupd.
      case Ey : ((y : ch n) == c.1); last exact: HmMid.
      move/eqP: Ey => _.
      apply: Or43. exists c.2, (if b then S1 else S2).
      by split => //; case: (b).
    + (* branch against select *)
      move=> [c [b [P' [Q' [-> [HbP HsQ]]]]]].
      have HofP : offersP ABra (pflip c) P by exists b, P'.
      have HofQ : offersP ASel c Q by exists b, Q'.
      have Hown2 : Δ2 c.1 <> None.
        exact: offers_owned CV2 HofQ.
      have Hown1 : Δ1 c.1 <> None.
        exact: offers_owned CV1 HofP.
      case: (sync_subjL Hm CV1 HofP Hown2) => ShP [E1c EaP].
      case: (sync_subjR Hm CV2 HofQ Hown1) => ShQ [E2c EaQ].
      case: ShP EaP E1c => // S1 S2 _ E1c.
      case: ShQ EaQ E2c => // S1' S2' _ E2c.
      have [ES1 ES2] : S1 = dual S1' /\ S2 = dual S2'.
        case: (dmerge_live Hm E1c E2c) => ρ [T [Ea Eb _]].
        case: Ea => Eρ ET. rewrite -Eρ -ET /= in Eb.
        case: Eb => _ -[E1' E2']. split.
        - by rewrite E1' dual_involutive.
        - by rewrite E2' dual_involutive.
      subst S1 S2.
      rewrite (surjective_pairing c) in HsQ.
      case: (V1 _ _ _ E1c _ _ HbP) => Δ1' [Hev1 HE1].
      case: (dmerge_sevL Hm Hev1) => Δmid [HevD HmMid].
      have HE2 := V2 _ _ _ E2c _ _ HsQ.
      exists (scupd c.1
                (Some (SBoth (pole (flipp c.2)
                                (if b then dual S1' else dual S2'))))
                Δmid).
      split.
        apply: sevolve_trans HevD _.
        move=> y. rewrite /scupd.
        case Ey : ((y : ch n) == c.1); last by left.
        move/eqP: Ey => ->. right.
        have E1m : Δ1 c.1 = Δ1' c.1.
          case: (Hev1 c.1) => [E|[S0 [S0' [E _]]]] //.
          by rewrite E in E1c.
        case: (HmMid c.1).
        - move=> [E2n _]. by rewrite E2c in E2n.
        - move=> [E1n _]. by rewrite -E1m E1c in E1n.
        - move=> [ρ' [T' [_ _ EDm]]]. rewrite EDm. by do 2 eexists.
        - move=> [E1n _]. by rewrite -E1m E1c in E1n.
      apply: (IH _ _ _ _ _ _ _ HE1 HE2).
      move=> y. rewrite /scupd.
      case Ey : ((y : ch n) == c.1); last exact: HmMid.
      move/eqP: Ey => _.
      apply: Or43.
      exists (flipp c.2), (if b then dual S1' else dual S2').
      split => //.
      by case: (b) => /=; rewrite flipp_invol dual_involutive.
Qed.

Print Assumptions combineP.
