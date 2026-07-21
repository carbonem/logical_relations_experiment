(** * Communication errors for the polarized calculus

    An error is a mismatch between the two endpoints of one session:
    the [pos] and [neg] endpoints of a name are both offered, with
    incompatible actions (close against close, send against send,
    close against delegation, ...).  [act] and [compat] are unchanged
    from [PolTypes.v].

    Because co-endpoints are syntactic ([pflip]) and communication
    happens at ∥, a mismatch is a property of ANY process at ANY
    visible name -- free names included -- not only at a restriction,
    as it was in the double-binder development ([Tau.v]'s [errL]).
    [EP_Mismatch] therefore carries no ν; the descent constructors
    [EP_Res]/[EP_ParL]/[EP_ParR] only serve to reach mismatches that
    are invisible from the outside because their name is bound by an
    inner restriction.

    [offersP a c P]: [P] can perform action [a] at endpoint [c],
    observed through the transition families -- so an offer sees
    through parallel composition and through restrictions that do not
    bind [c]'s name. *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Eqdep_dec PeanoNat.
From Tait Require Import PolBase PolTypes PolProc PolLTS.

Set Implicit Arguments.
Unset Strict Implicit.
Open Scope pol_scope.

(** ** Offers: observable capability at an endpoint *)
Definition offersP {n : nat} (a : act) (c : pch n) (P : procP n) : Prop :=
  match a with
  | AClose => exists P', ltscP c P P'
  | AWait  => exists P', ltswP c P P'
  | ADelS  => (exists d P', ltsfP c d P P')
              \/ (exists r (P' : procP n.+1), ltsbP c r P P')
  | ADelR  => exists d P', ltsrP c d P P'
  | ASel   => exists b P', ltsselP c b P P'
  | ABra   => exists b P', ltsbrP c b P P'
  end.

(** Offers lift through parallel composition and restriction. *)
Lemma offersP_liftL n a (c : pch n) (A B : procP n) :
  offersP a c A -> offersP a c (A ∥ B).
Proof.
  case: a => /=.
  - move=> [R HT]. by exists (R ∥ B); apply: PC_ParL.
  - move=> [R HT]. by exists (R ∥ B); apply: PW_ParL.
  - move=> [[d [R HT]]|[r [R HT]]].
    + by left; exists d, (R ∥ B); apply: PF_ParL.
    + by right; exists r, (R ∥ psubst shift B); apply: PB_ParL.
  - move=> [d [R HT]]. by exists d, (R ∥ B); apply: PR_ParL.
  - move=> [b [R HT]]. by exists b, (R ∥ B); apply: PS_ParL.
  - move=> [b [R HT]]. by exists b, (R ∥ B); apply: PBR_ParL.
Qed.

Lemma offersP_liftR n a (c : pch n) (A B : procP n) :
  offersP a c B -> offersP a c (A ∥ B).
Proof.
  case: a => /=.
  - move=> [R HT]. by exists (A ∥ R); apply: PC_ParR.
  - move=> [R HT]. by exists (A ∥ R); apply: PW_ParR.
  - move=> [[d [R HT]]|[r [R HT]]].
    + by left; exists d, (A ∥ R); apply: PF_ParR.
    + by right; exists r, (psubst shift A ∥ R); apply: PB_ParR.
  - move=> [d [R HT]]. by exists d, (A ∥ R); apply: PR_ParR.
  - move=> [b [R HT]]. by exists b, (A ∥ R); apply: PS_ParR.
  - move=> [b [R HT]]. by exists b, (A ∥ R); apply: PBR_ParR.
Qed.

Lemma offersP_liftRes n a (c : pch n) (B : procP n.+1) :
  offersP a (pshift c) B -> offersP a c ((ν) B).
Proof.
  case: a => /=.
  - move=> [R HT]. by exists ((ν) R); apply: PC_Res.
  - move=> [R HT]. by exists ((ν) R); apply: PW_Res.
  - move=> [[d [R HT]]|[r [R HT]]].
    + case: d HT => -[dn|] dr HT.
      * left. exists (dn, dr), ((ν) R). exact (@PF_Res _ c (dn, dr) _ _ HT).
      * right. exists dr, R. exact (PB_Open HT).
    + right. exists r, ((ν) (psubst (swap_ch zero one) R)).
      exact: PB_Res HT.
  - move=> [d [R HT]].
    case: (ltsrP_any_name HT (shift c.1)) => R' HT'.
    exists (c.1, d.2), ((ν) R').
    exact (@PR_Res _ c (c.1, d.2) _ _ HT').
  - move=> [b [R HT]]. by exists b, ((ν) R); apply: PS_Res.
  - move=> [b [R HT]]. by exists b, ((ν) R); apply: PBR_Res.
Qed.

(** ** Errors *)
Inductive errP : forall n, procP n -> Prop :=
| EP_Mismatch : forall n (P : procP n) (x : ch n) a b,
    offersP a (x, pos) P -> offersP b (x, neg) P -> compat a b = false ->
    errP P
| EP_Res : forall n (P : procP n.+1),
    errP P -> errP ((ν) P)
| EP_ParL : forall n (P Q : procP n),
    errP P -> errP (P ∥ Q)
| EP_ParR : forall n (P Q : procP n),
    errP Q -> errP (P ∥ Q).

(** ** Error freedom: no reachable error *)
Definition error_freeP {n : nat} (P : procP n) : Prop :=
  forall Q, P —τ*→ Q -> ~ errP Q.

(** ** Examples *)
Section Examples.

(** Two closes on the co-endpoints of a FREE name: an error, no ν
    involved.  (In the double-binder calculus this was not even
    expressible as a mismatch.) *)
Example err_close_close_free (n : nat) (x : ch n) K1 K2 :
  errP (((x, pos) !․ K1) ∥ ((x, neg) !․ K2)).
Proof.
  apply: (@EP_Mismatch _ _ x AClose AClose) => //.
  - by eexists; apply: PC_ParL; exact: PC_Pfx.
  - by eexists; apply: PC_ParR; exact: PC_Pfx.
Qed.

(** The same mismatch under its restriction: reached by [EP_Res],
    then it is a mismatch of the body at the bound name [zero]. *)
Example err_close_close_bound K1 K2 :
  errP ((ν) (((zero, pos) !․ K1) ∥ ((zero, neg) !․ K2)) : procP 0).
Proof. apply: EP_Res. exact: err_close_close_free. Qed.

(** Output against delegation: also a mismatch. *)
Example err_close_del (n : nat) (x : ch n) (d : pch n) K1 K2 :
  errP (((x, pos) !․ K1) ∥ ((x, neg) ! d ․ K2)).
Proof.
  apply: (@EP_Mismatch _ _ x AClose ADelS) => //.
  - by eexists; apply: PC_ParL; exact: PC_Pfx.
  - by left; do 2 eexists; apply: PF_ParR; exact: PF_Pfx.
Qed.

(** A well-matched pair is NOT an error: the only offers are close at
    [(x,pos)] and wait at [(x,neg)], and those are compatible. *)
Example not_err_close_wait (x : ch 1) K1 K2 :
  ~ errP (((x, pos) !․ K1) ∥ ((x, neg) ?․ K2)).
Proof.
  have det : forall a (c : pch 1),
      offersP a c (((x, pos) !․ K1) ∥ ((x, neg) ?․ K2)) ->
      (a = AClose /\ c = (x, pos)) \/ (a = AWait /\ c = (x, neg)).
    move=> a c. case: a => /=.
    - case=> R HT. case: (pinv_c_par HT) => [[R' H']|[R' H']].
      + left. split=> //. exact: pinv_c_close H'.
      + by case: (pinv_c_wait H').
    - case=> R HT. case: (pinv_w_par HT) => [[R' H']|[R' H']].
      + by case: (pinv_w_close H').
      + right. split=> //. exact: pinv_w_wait H'.
    - case=> [[d [R HT]]|[r [R HT]]].
      + case: (pinv_f_par HT) => [[R' H']|[R' H']];
          [by case: (pinv_f_close H') | by case: (pinv_f_wait H')].
      + case: (pinv_b_par HT) => [[R' H']|[R' H']];
          [by case: (pinv_b_close H') | by case: (pinv_b_wait H')].
    - case=> d [R HT]. case: (pinv_r_par HT) => [[R' H']|[R' H']];
        [by case: (pinv_r_close H') | by case: (pinv_r_wait H')].
    - case=> b [R HT]. case: (pinv_sel_par HT) => [[R' H']|[R' H']];
        [by case: (pinv_sel_close H') | by case: (pinv_sel_wait H')].
    - case=> b [R HT]. case: (pinv_br_par HT) => [[R' H']|[R' H']];
        [by case: (pinv_br_close H') | by case: (pinv_br_wait H')].
  have detL : forall a (c : pch 1),
      offersP a c ((x, pos) !․ K1) -> a = AClose /\ c = (x, pos).
    move=> a c. case: a => /=.
    - case=> R HT. split=> //. exact: pinv_c_close HT.
    - case=> R HT. by case: (pinv_w_close HT).
    - case=> [[d [R HT]]|[r [R HT]]];
        [by case: (pinv_f_close HT) | by case: (pinv_b_close HT)].
    - case=> d [R HT]. by case: (pinv_r_close HT).
    - case=> b [R HT]. by case: (pinv_sel_close HT).
    - case=> b [R HT]. by case: (pinv_br_close HT).
  have detR : forall a (c : pch 1),
      offersP a c ((x, neg) ?․ K2) -> a = AWait /\ c = (x, neg).
    move=> a c. case: a => /=.
    - case=> R HT. by case: (pinv_c_wait HT).
    - case=> R HT. split=> //. exact: pinv_w_wait HT.
    - case=> [[d [R HT]]|[r [R HT]]];
        [by case: (pinv_f_wait HT) | by case: (pinv_b_wait HT)].
    - case=> d [R HT]. by case: (pinv_r_wait HT).
    - case=> b [R HT]. by case: (pinv_sel_wait HT).
    - case=> b [R HT]. by case: (pinv_br_wait HT).
  move=> H. pinv H.
  - (* mismatch on the par itself: the only offers are close(x,pos)
       and wait(x,neg), which are compatible *)
    match goal with
    | [ Ha : offersP ?a _ _, Hb : offersP ?b _ _,
        Hc : compat ?a ?b = false |- _ ] =>
        case: (det _ _ Ha) => -[Ea Ec]; case: (det _ _ Hb) => -[Eb Ec'];
        subst;
        by [ discriminate Hc
           | (move: Ec => -[_ E]; discriminate E)
           | (move: Ec' => -[_ E]; discriminate E) ]
    end.
  - (* inside the close prefix: both offers would sit at (x,pos) *)
    match goal with [ HX : errP _ |- _ ] => pinv HX end;
    match goal with
    | [ Ha : offersP _ _ _, Hb : offersP _ _ _ |- _ ] =>
        case: (detL _ _ Ha) => _ Ec; case: (detL _ _ Hb) => _ Ec';
        by [ (move: Ec => -[_ E]; discriminate E)
           | (move: Ec' => -[_ E]; discriminate E) ]
    end.
  - (* inside the wait prefix: both offers would sit at (x,neg) *)
    match goal with [ HX : errP _ |- _ ] => pinv HX end;
    match goal with
    | [ Ha : offersP _ _ _, Hb : offersP _ _ _ |- _ ] =>
        case: (detR _ _ Ha) => _ Ec; case: (detR _ _ Hb) => _ Ec';
        by [ (move: Ec => -[_ E]; discriminate E)
           | (move: Ec' => -[_ E]; discriminate E) ]
    end.
Qed.

End Examples.
